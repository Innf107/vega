module Vega.Compilation.PatternMatching (
    CaseTree (..),
    RecursiveCaseTree (..),
    toRecursive,
    compileMatch,
    compileMatchRecursive,
    serializeSubPatterns,
    traverseLeavesWithBoundVars,
) where

import Data.Foldable1 (foldl1')
import Data.Map qualified as Map
import Data.Sequence (Seq (..))
import Data.Unique (Unique)
import Effectful
import Relude hiding (NonEmpty)
import Vega.Debug (showHeadConstructor)
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Panic (panic)
import Vega.Pretty ((<+>))
import Vega.Seq.NonEmpty
import Vega.Syntax

data RecursiveCaseTree goal
    = Done goal
    | Continue (CaseTree (RecursiveCaseTree goal))
    deriving (Generic, Functor, Foldable)

data CaseTree goal
    = Leaf goal
    | ConstructorCase
        -- We use Map instead of HashMap to get a faster unionWith operation
        -- (with HashMap, merging would have been quadratic in the number of constructors)
        { constructors :: Map Name (Int, RecursiveCaseTree goal)
        }
    | OrDefault (CaseTree goal) goal
    | TupleCase Int (RecursiveCaseTree goal)
    | BindVar LocalName (CaseTree goal)
    deriving (Generic, Functor, Foldable)

toRecursive :: CaseTree goal -> RecursiveCaseTree goal
toRecursive caseTree = Continue (fmap Done caseTree)

mergeRecursive :: RecursiveCaseTree goal -> RecursiveCaseTree goal -> RecursiveCaseTree goal
mergeRecursive (Done goal) _ = Done goal
mergeRecursive (Continue tree) (Done goal) = Continue (merge tree (Leaf (Done goal)))
mergeRecursive (Continue tree1) (Continue tree2) = Continue (merge tree1 tree2)

merge :: CaseTree goal -> CaseTree goal -> CaseTree goal
merge tree1 tree2 = case (tree1, tree2) of
    (Leaf expr1, _) -> Leaf expr1
    (OrDefault{}, _) -> tree1
    (_, Leaf expr1) -> OrDefault tree1 expr1
    -- We rely on the property that variable names are unique across branches and bubble the variable bindings outwards
    (_, OrDefault tree2 body) -> OrDefault (merge tree1 tree2) body
    (BindVar var tree1, tree2) -> BindVar var (merge tree1 tree2)
    (_, BindVar var tree2) -> BindVar var (merge tree1 tree2)
    (ConstructorCase{constructors = constructors1}, _) -> case tree2 of
        ConstructorCase{constructors = constructors2} -> do
            let merge (count1, cont1) (count2, cont2)
                    | count1 /= count2 = panic "trying to merge case trees with different parameter counts for the same constructor"
                    | otherwise = (count1, mergeRecursive cont1 cont2)
            ConstructorCase{constructors = Map.unionWith merge constructors1 constructors2}
        _ -> invalidMergeCombination tree1 tree2
    (TupleCase size1 continuation1, _) -> case tree2 of
        TupleCase size2 continuation2
            | size1 == size2 -> TupleCase size1 (mergeRecursive continuation1 continuation2)
        _ -> invalidMergeCombination tree1 tree2

invalidMergeCombination :: forall goal. (HasCallStack) => CaseTree goal -> CaseTree goal -> CaseTree goal
invalidMergeCombination tree1 tree2 =
    panic $
        "Trying to merge incompatible case trees"
            -- We need the coerce since the bare type variable trips up overlapping instance resolution
            <+> showHeadConstructor (coerce @_ @(CaseTree (Identity goal)) tree1)
            <+> "and"
            <+> showHeadConstructor (coerce @_ @(CaseTree (Identity goal)) tree2)
            <> ". This should have been a type error."

mergeAll :: NonEmpty (CaseTree goal) -> CaseTree goal
mergeAll caseTrees = foldl1' merge (toNonEmptyList caseTrees)

compileMatch :: NonEmpty (Pattern Typed, goal) -> CaseTree goal
compileMatch patterns = mergeAll $ fmap (uncurry compileSinglePattern) patterns

compileMatchRecursive :: NonEmpty (Pattern Typed, goal) -> RecursiveCaseTree goal
compileMatchRecursive patterns = Continue $ compileMatch (fmap (\(pattern_, goal) -> (pattern_, Done goal)) patterns)

compileSinglePattern :: Pattern Typed -> goal -> CaseTree goal
compileSinglePattern pattern_ goal = case pattern_ of
    WildcardPattern{} -> Leaf goal
    VarPattern _ name -> BindVar name (Leaf goal)
    AsPattern _ inner name -> BindVar name (compileSinglePattern inner goal)
    ConstructorPattern{constructor, subPatterns} -> do
        let subTree = serializeSubPatterns subPatterns goal
        ConstructorCase
            { constructors = [(constructor, (length subPatterns, subTree))]
            }
    TuplePattern _ subPatterns -> do
        let subTree = serializeSubPatterns subPatterns goal
        TupleCase (length subPatterns) subTree
    TypePattern _ inner _ -> compileSinglePattern inner goal
    OrPattern _ alternatives -> do
        mergeAll $ fmap (\pattern_ -> compileSinglePattern pattern_ goal) alternatives

serializeSubPatterns :: Seq (Pattern Typed) -> goal -> (RecursiveCaseTree goal)
serializeSubPatterns patterns goal = case patterns of
    Empty -> Done goal
    (pattern_ :<| rest) -> do
        let treeForRemainingElements = serializeSubPatterns rest goal
        Continue $ compileSinglePattern pattern_ treeForRemainingElements

traverseLeavesWithBoundVars :: forall goal f. (Applicative f) => RecursiveCaseTree goal -> (Seq LocalName -> goal -> f ()) -> f ()
traverseLeavesWithBoundVars tree onLeaf = goRecursive [] onLeaf tree
  where
    goRecursive :: forall goal. Seq LocalName -> (Seq LocalName -> goal -> f ()) -> RecursiveCaseTree goal -> f ()
    goRecursive boundVars onLeaf = \case
        Done goal -> onLeaf boundVars goal
        Continue subTree -> go boundVars (\boundVars goal -> goRecursive boundVars onLeaf goal) subTree

    go :: forall goal. Seq LocalName -> (Seq LocalName -> goal -> f ()) -> CaseTree goal -> f ()
    go boundVars onLeaf = \case
        OrDefault subTree default_ ->
            -- ApplicativeDo doesn't work here for some reason??
            go boundVars onLeaf subTree
                *> onLeaf boundVars default_
        Leaf goal -> onLeaf boundVars goal
        ConstructorCase{constructors} -> do
            for_ constructors \(_, subTree) -> do
                goRecursive boundVars onLeaf subTree
        TupleCase _ subTree -> goRecursive boundVars onLeaf subTree
        BindVar name subTree -> do
            go (boundVars :|> name) onLeaf subTree
