module Vega.Compilation.PatternMatching (
    CaseTree (..),
    compileMatch,
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
import Vega.Pretty (Ann, Doc, Pretty, align, indent, keyword, lparen, number, pretty, rparen, vsep, (<+>))
import Vega.Seq.NonEmpty
import Vega.Syntax

data CaseTree goal
    = Leaf goal
    | ConstructorCase
        -- We use Map instead of HashMap to get a faster unionWith operation
        -- (with HashMap, merging would have been quadratic in the number of constructors)
        { constructors :: Map Name (Int, CaseTree goal)
        , default_ :: Maybe (CaseTree goal)
        }
    | TupleCase Int (CaseTree goal)
    | -- Bind a scrutinee to a variable without consuming it
      BindVar LocalName (CaseTree goal)
    | -- Consume a scrutinee and unconditionally continue
      Ignore (CaseTree goal)
    deriving (Generic, Functor, Foldable)

merge :: forall goal. CaseTree goal -> CaseTree goal -> CaseTree goal
merge tree1 tree2 = case (tree1, tree2) of
    (Leaf leaf, _) -> Leaf leaf
    (_, Leaf _) -> panic $ "trying to merge " <> showHeadConstructor (coerce @_ @(CaseTree (Identity goal)) tree1) <> " with leaf"
    (Ignore subTree1, Ignore subTree2) -> Ignore (merge subTree1 subTree2)
    (Ignore ignoreSubTree, ConstructorCase{constructors, default_}) -> do
        let mergedConstructors = fmap (\(count, subTree) -> (count, merge (replicateIgnore count ignoreSubTree) subTree)) constructors
        let mergedDefault = case default_ of
                Nothing -> Just ignoreSubTree
                Just defaultSubTree -> Just (merge ignoreSubTree defaultSubTree)
        ConstructorCase{constructors = mergedConstructors, default_ = mergedDefault}
    (ConstructorCase{constructors, default_}, Ignore ignoreSubTree) -> do
        let mergedConstructors = fmap (\(count, subTree) -> (count, merge subTree (replicateIgnore count ignoreSubTree))) constructors
        let mergedDefault = case default_ of
                Nothing -> Just ignoreSubTree
                Just defaultSubTree -> Just (merge defaultSubTree ignoreSubTree)
        ConstructorCase{constructors = mergedConstructors, default_ = mergedDefault}
    (Ignore ignoreSubTree, TupleCase count tupleSubTree) ->
        TupleCase count (merge (replicateIgnore count ignoreSubTree) tupleSubTree)
    (TupleCase count tupleSubTree, Ignore ignoreSubTree) ->
        TupleCase count (merge tupleSubTree (replicateIgnore count ignoreSubTree))
    (BindVar name1 subTree1, BindVar name2 subTree2) ->
        BindVar name1 (BindVar name2 (merge subTree1 subTree2))
    (tree, BindVar name subTree) ->
        BindVar name (merge tree subTree)
    (BindVar name subTree, tree) ->
        BindVar name (merge subTree tree)
    ( ConstructorCase{constructors = constructors1, default_ = default1}
        , ConstructorCase{constructors = constructors2, default_ = default2}
        ) -> do
            let mergeConstructor constructorName (count1, subTree1) (count2, subTree2)
                    | count1 /= count2 = panic $ "Data constructor " <> prettyName DataConstructorKind constructorName <> " applied to different argument counts (" <> number count1 <> " vs " <> number count2 <> ")"
                    | otherwise = (count1, merge subTree1 subTree2)
            let mergedDefault = case (default1, default2) of
                    (_, Nothing) -> default1
                    (Nothing, _) -> default2
                    (Just tree1, Just tree2) -> Just (merge tree1 tree2)
            ConstructorCase{constructors = Map.unionWithKey mergeConstructor constructors1 constructors2, default_ = mergedDefault}
    (TupleCase count1 subTree1, TupleCase count2 subTree2)
        | count1 /= count2 -> panic $ "Tuple applied to different numbers of arguments (" <> number count1 <> " vs " <> number count2 <> ")"
        | otherwise -> TupleCase count1 (merge subTree1 subTree2)
    (ConstructorCase{}, TupleCase{}) -> invalidMergeCombination tree1 tree2
    (TupleCase{}, ConstructorCase{}) -> invalidMergeCombination tree1 tree2

replicateIgnore :: Int -> CaseTree a -> CaseTree a
replicateIgnore 0 subTree = subTree
replicateIgnore n subTree
    | n < 0 = error "replicateIgnore: negative argument"
    | otherwise = Ignore (replicateIgnore (n - 1) subTree)

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
compileMatch patterns = mergeAll $ fmap (\(pattern_, goal) -> compileSinglePattern pattern_ (Leaf goal)) patterns

compileSinglePattern :: Pattern Typed -> CaseTree goal -> CaseTree goal
compileSinglePattern pattern_ leaf = case pattern_ of
    WildcardPattern{} -> Ignore leaf
    VarPattern _ name -> BindVar name (Ignore leaf)
    AsPattern _ inner name -> BindVar name (compileSinglePattern inner leaf)
    ConstructorPattern{constructor, subPatterns} -> do
        let subTree = serializeSubPatternsWithLeaf subPatterns leaf
        ConstructorCase
            { constructors = [(constructor, (length subPatterns, subTree))]
            , default_ = Nothing
            }
    TuplePattern _ subPatterns -> do
        let subTree = serializeSubPatternsWithLeaf subPatterns leaf
        TupleCase (length subPatterns) subTree
    TypePattern _ inner _ -> compileSinglePattern inner leaf
    OrPattern _ alternatives -> do
        mergeAll $ fmap (\pattern_ -> compileSinglePattern pattern_ leaf) alternatives

serializeSubPatternsWithLeaf :: Seq (Pattern Typed) -> CaseTree goal -> (CaseTree goal)
serializeSubPatternsWithLeaf patterns leaf = case patterns of
    Empty -> leaf
    (rest :|> pattern_) -> do
        serializeSubPatternsWithLeaf rest (compileSinglePattern pattern_ leaf)

serializeSubPatterns :: Seq (Pattern Typed) -> goal -> CaseTree goal
serializeSubPatterns patterns goal = serializeSubPatternsWithLeaf patterns (Leaf goal)

traverseLeavesWithBoundVars :: forall goal f. (Applicative f) => CaseTree goal -> (Seq LocalName -> goal -> f ()) -> f ()
traverseLeavesWithBoundVars tree onLeaf = go [] onLeaf tree
  where
    go :: forall goal. Seq LocalName -> (Seq LocalName -> goal -> f ()) -> CaseTree goal -> f ()
    go boundVars onLeaf = \case
        Leaf goal -> onLeaf boundVars goal
        ConstructorCase{constructors} -> do
            for_ constructors \(_, subTree) -> do
                go boundVars onLeaf subTree
        TupleCase _ subTree -> go boundVars onLeaf subTree
        BindVar name subTree -> do
            go (boundVars :|> name) onLeaf subTree
        Ignore subTree -> go boundVars onLeaf subTree

instance (Pretty goal) => Pretty (CaseTree goal) where
    pretty = \case
        Leaf goal -> keyword "Leaf" <+> pretty goal
        BindVar name subTree -> keyword "BindVar" <+> prettyLocal VarKind name <> prettySubTree subTree
        ConstructorCase{constructors} -> do
            let prettyCase (name, (count, subTree)) = do
                    prettyName DataConstructorKind name <> lparen "(" <> number count <> rparen ")" <> prettySubTree subTree
            keyword "ConstructorCase"
                <> "\n"
                <> indent 2 (align $ vsep (fmap prettyCase (Map.toList constructors)))
        TupleCase count subTree ->
            keyword "TupleCase" <> lparen "(" <> number count <> rparen ")" <> prettySubTree subTree
        Ignore subTree -> keyword "Ignore" <+> prettySubTree subTree

prettySubTree :: (Pretty a) => a -> Doc Ann
prettySubTree subTree = "\n" <> indent 2 (align $ pretty subTree)