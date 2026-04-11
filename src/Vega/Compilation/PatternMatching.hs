module Vega.Compilation.PatternMatching (
    CaseTree (..),
    compileMatch,
    serializeSubPatterns,
    traverseLeavesWithBoundVars,
) where

import Control.Exception (assert)
import Data.Map qualified as Map
import Data.Sequence (Seq (..))
import Relude hiding (NonEmpty, Type)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Debug (showHeadConstructor)
import Vega.Panic (panic)
import Vega.Pretty (Ann, Doc, Pretty, align, indent, intercalateDoc, keyword, lparen, number, pretty, rparen, vsep, (<+>))
import Vega.Seq.NonEmpty
import Vega.Syntax

data CaseTree goal
    = Leaf goal
    | ConstructorCase
        -- We use Map instead of HashMap to get a faster unionWith operation
        -- (with HashMap, merging would have been quadratic in the number of constructors)
        { constructors :: Map Name (Seq Representation, CaseTree goal)
        , scrutineeRepresentation :: Type
        , default_ :: Maybe (CaseTree goal)
        }
    | IntCase
        { cases :: Map Int (CaseTree goal)
        , default_ :: Maybe (CaseTree goal)
        }
    | TupleCase (Seq Representation) (CaseTree goal)
    | -- Bind a scrutinee to a variable without consuming it
      BindVar {name :: LocalName, representation :: Type, next :: CaseTree goal}
    | -- Consume a scrutinee and unconditionally continue
      Ignore (CaseTree goal)
    deriving (Generic, Functor, Foldable)

-- TODO: not super happy about keeping representation as vega types here

merge :: forall goal. CaseTree goal -> CaseTree goal -> CaseTree goal
merge tree1 tree2 = case (tree1, tree2) of
    (Leaf leaf, _) -> Leaf leaf
    (_, Leaf _) -> panic $ "trying to merge " <> showHeadConstructor (coerce @_ @(CaseTree (Identity goal)) tree1) <> " with leaf"
    (Ignore subTree1, Ignore subTree2) -> Ignore (merge subTree1 subTree2)
    (Ignore ignoreSubTree, ConstructorCase{scrutineeRepresentation, constructors, default_}) -> do
        let mergedConstructors =
                fmap
                    ( \(representations, subTree) ->
                        (representations, merge (replicateIgnore (length representations) ignoreSubTree) subTree)
                    )
                    constructors
        let mergedDefault = case default_ of
                Nothing -> Just ignoreSubTree
                Just defaultSubTree -> Just (merge ignoreSubTree defaultSubTree)
        ConstructorCase{scrutineeRepresentation, constructors = mergedConstructors, default_ = mergedDefault}
    (ConstructorCase{scrutineeRepresentation, constructors, default_}, Ignore ignoreSubTree) -> do
        let mergedConstructors =
                fmap
                    ( \(representations, subTree) ->
                        (representations, merge subTree (replicateIgnore (length representations) ignoreSubTree))
                    )
                    constructors
        let mergedDefault = case default_ of
                Nothing -> Just ignoreSubTree
                Just defaultSubTree -> Just (merge defaultSubTree ignoreSubTree)
        ConstructorCase{scrutineeRepresentation, constructors = mergedConstructors, default_ = mergedDefault}
    ( ConstructorCase{scrutineeRepresentation, constructors = constructors1, default_ = default1}
        , ConstructorCase{scrutineeRepresentation = _, constructors = constructors2, default_ = default2}
        ) -> do
            let mergeConstructor constructorName (representations1, subTree1) (representations2, subTree2)
                    -- we can't really check that the representations actually match here
                    | length representations1 /= length representations2 =
                        panic $
                            "Data constructor "
                                <> prettyName DataConstructorKind constructorName
                                <> " applied to different argument  ("
                                <> lparen "["
                                <> intercalateDoc ", " (fmap pretty representations1)
                                <> rparen "]"
                                <> " vs "
                                <> lparen "["
                                <> intercalateDoc ", " (fmap pretty representations2)
                                <> rparen "]"
                                <> ")"
                    | otherwise = (representations1, merge subTree1 subTree2)
            let mergedDefault = case (default1, default2) of
                    (_, Nothing) -> default1
                    (Nothing, _) -> default2
                    (Just tree1, Just tree2) -> Just (merge tree1 tree2)
            -- We assume that the representations match here. Ideally we would have a sanity check but
            -- since representations are still vega-level types at this stage we can't actually check them for equality
            -- that easily
            ConstructorCase
                { scrutineeRepresentation
                , constructors = Map.unionWithKey mergeConstructor constructors1 constructors2
                , default_ = mergedDefault
                }
    (Ignore ignoreSubTree, IntCase{cases, default_}) -> do
        let mergedCases = fmap (\subTree -> merge ignoreSubTree subTree) cases
        let mergedDefault = case default_ of
                Nothing -> Just ignoreSubTree
                Just defaultSubTree -> Just (merge ignoreSubTree defaultSubTree)
        IntCase{cases = mergedCases, default_ = mergedDefault}
    (IntCase{cases, default_}, Ignore ignoreSubTree) -> do
        let mergedCases = fmap (\subTree -> merge subTree ignoreSubTree) cases
        let mergedDefault = case default_ of
                Nothing -> Just ignoreSubTree
                Just defaultSubTree -> Just (merge defaultSubTree ignoreSubTree)
        IntCase{cases = mergedCases, default_ = mergedDefault}
    (IntCase{cases = cases1, default_ = default1}, IntCase{cases = cases2, default_ = default2}) -> do
        let mergedCases = Map.unionWith merge cases1 cases2

        let mergedDefault = case (default1, default2) of
                (_, Nothing) -> default1
                (Nothing, _) -> default2
                (Just default1, Just default2) -> Just (merge default1 default2)
        IntCase{cases = mergedCases, default_ = mergedDefault}
    (Ignore ignoreSubTree, TupleCase representations tupleSubTree) ->
        TupleCase representations (merge (replicateIgnore (length representations) ignoreSubTree) tupleSubTree)
    (TupleCase representations tupleSubTree, Ignore ignoreSubTree) ->
        TupleCase representations (merge tupleSubTree (replicateIgnore (length representations) ignoreSubTree))
    (BindVar name1 rep1 subTree1, BindVar name2 rep2 subTree2) -> BindVar name1 rep1 (BindVar name2 rep2 (merge subTree1 subTree2))
    (tree, BindVar name rep subTree) ->
        BindVar name rep (merge tree subTree)
    (BindVar name rep subTree, tree) ->
        BindVar name rep (merge subTree tree)
    (TupleCase count1 subTree1, TupleCase count2 subTree2)
        | length count1 /= length count2 -> panic $ "Tuple applied to different numbers of arguments (" <> number (length count1) <> " vs " <> number (length count2) <> ")"
        | otherwise -> TupleCase count1 (merge subTree1 subTree2)
    (ConstructorCase{}, TupleCase{}) -> invalidMergeCombination tree1 tree2
    (TupleCase{}, ConstructorCase{}) -> invalidMergeCombination tree1 tree2
    (IntCase{}, ConstructorCase{}) -> invalidMergeCombination tree1 tree2
    (ConstructorCase{}, IntCase{}) -> invalidMergeCombination tree1 tree2
    (TupleCase{}, IntCase{}) -> invalidMergeCombination tree1 tree2
    (IntCase{}, TupleCase{}) -> invalidMergeCombination tree1 tree2

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
mergeAll caseTrees = foldl1' merge caseTrees

compileMatch :: NonEmpty (Pattern Typed, goal) -> CaseTree goal
compileMatch patterns = mergeAll $ fmap (\(pattern_, goal) -> compileSinglePattern pattern_ (Leaf goal)) patterns

compileSinglePattern :: Pattern Typed -> CaseTree goal -> CaseTree goal
compileSinglePattern pattern_ leaf = case pattern_ of
    WildcardPattern{} -> Ignore leaf
    VarPattern{loc = _, ext = rep, name, isShadowed = _} -> BindVar{name = name, representation = rep, next = Ignore leaf}
    -- TODO: we assume that the intLiteral is in range for an Int here (we should probably enforce that in the renamer)
    IntLiteralPattern{loc = _, intLiteral} -> IntCase{cases = [(fromIntegral intLiteral, leaf)], default_ = Nothing}
    StringLiteralPattern{} -> undefined
    DoubleLiteralPattern{} -> undefined
    AsPattern _loc rep inner name -> BindVar{name = name, representation = rep, next = compileSinglePattern inner leaf}
    ConstructorPattern{constructorExt, constructor, subPatterns} -> assert (length constructorExt.parameterRepresentations == length subPatterns) do
        let subTree = serializeSubPatternsWithLeaf subPatterns leaf
        ConstructorCase
            { scrutineeRepresentation = constructorExt.returnRepresentation
            , constructors = [(constructor, (constructorExt.parameterRepresentations, subTree))]
            , default_ = Nothing
            }
    TuplePattern{loc = _, tupleSubPatterns} -> do
        let subTree = serializeSubPatternsWithLeaf (fmap fst tupleSubPatterns) leaf
        TupleCase (fmap snd tupleSubPatterns) subTree
    RecordPattern{loc = _, fields} -> do
        undefined
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

traverseLeavesWithBoundVars :: forall goal f. (Monad f) => CaseTree goal -> (Seq LocalName -> goal -> f ()) -> f ()
traverseLeavesWithBoundVars tree onLeaf = go [] onLeaf tree
  where
    go :: forall goal. Seq LocalName -> (Seq LocalName -> goal -> f ()) -> CaseTree goal -> f ()
    go boundVars onLeaf = \case
        Leaf goal -> onLeaf boundVars goal
        IntCase{cases, default_} -> do
            for_ cases \subTree -> do
                go boundVars onLeaf subTree
            for_ default_ (go boundVars onLeaf)
        ConstructorCase{constructors, default_} -> do
            for_ constructors \(_, subTree) -> do
                go boundVars onLeaf subTree
            for_ default_ (go boundVars onLeaf)
        TupleCase _ subTree -> go boundVars onLeaf subTree
        BindVar name _rep subTree -> do
            go (boundVars :|> name) onLeaf subTree
        Ignore subTree -> go boundVars onLeaf subTree

instance (Pretty goal) => Pretty (CaseTree goal) where
    pretty = \case
        Leaf goal -> keyword "Leaf" <+> pretty goal
        BindVar name rep subTree -> keyword "BindVar" <+> prettyLocal VarKind name <> pretty rep <> prettySubTree subTree
        IntCase{cases, default_} -> do
            let prettyCase (int, subTree) = do
                    number int <> prettySubTree subTree
            keyword "ConstructorCase"
                <> "\n"
                <> indent 2 (align $ vsep (fmap prettyCase (Map.toList cases)))
        ConstructorCase{constructors, default_} -> do
            let prettyCase (name, (representations, subTree)) = do
                    prettyName DataConstructorKind name <> lparen "(" <> intercalateDoc ", " (fmap pretty representations) <> rparen ") -> " <> prettySubTree subTree
            keyword "ConstructorCase"
                <> "\n"
                <> indent 2 (align $ vsep (fmap prettyCase (Map.toList constructors)))
                <> case default_ of
                    Nothing -> mempty
                    Just defaultTree -> "\n" <> indent 2 (align $ keyword "default" <+> pretty defaultTree)
        TupleCase representations subTree ->
            keyword "TupleCase" <> lparen "(" <> intercalateDoc ", " (fmap pretty representations) <> rparen ")" <> prettySubTree subTree
        Ignore subTree -> keyword "Ignore" <+> prettySubTree subTree

prettySubTree :: (Pretty a) => a -> Doc Ann
prettySubTree subTree = "\n" <> indent 2 (align $ pretty subTree)