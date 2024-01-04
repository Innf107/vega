module Vega.Pattern (lowerCase) where

import Vega.Prelude
import Vega.Syntax
import Vega.Trace
import Vega.Util

import Vega.Eval (CoreExpr)

import Data.Vector qualified as Vector
import Vega.Monad.Unique (MonadUnique (freshName))
import Vega.Name (PrettyIdent (..), ident)
import Vega.Pretty

-- TODO: Oh god, dependent pattern matching is going to make this... difficult

-- Pattern matrices are represented as vectors (rows) of pattern columns
type PatternMatrix = Vector (Vector (CorePattern (Fix CorePattern)), CoreExpr)

prettyMatrix :: PatternMatrix -> Doc Ann
prettyMatrix matrix = align $ vsep (fmap prettyRow matrix)
  where
    prettyRow (patterns, expr) = "|" <+> intercalateMap " | " pretty patterns <+> "|" <+> keyword "->" <+> pretty expr

isWildcard :: CorePattern subPattern -> Bool
isWildcard = \case
    CVarPat _ -> True
    CWildcardPat -> True
    _ -> False

-- TODO: This is linear in the width of the pattern matrix. Maybe it should use Seq s instead
decomposeConstructor :: CorePattern subpattern -> PatternMatrix -> PatternMatrix
decomposeConstructor pattern matrix = Vector.mapMaybe (\(row, coreExpr) -> (,coreExpr) <$> decomposeRow row) matrix
  where
    decomposeRow row = case Vector.uncons row of
        Nothing -> error "trying to decompose a matrix without columns"
        Just (CVarPat _, rest) -> case pattern of
            CVarPat _ -> error "variable pattern in decomposeConstructor"
            CWildcardPat -> error "wildcard pattern in decomposeConstructor"
            CIntPat _ -> Just rest
            CStringPat _ -> Just rest
            CTuplePat subpatterns -> Just (Vector.replicate (length subpatterns) CWildcardPat <> rest)
        Just (CWildcardPat, rest) -> case pattern of
            CVarPat _ -> error "variable pattern in decomposeConstructor"
            CWildcardPat -> error "wildcard pattern in decomposeConstructor"
            CIntPat _ -> Just rest
            CStringPat _ -> Just rest
            CTuplePat subpatterns -> Just (Vector.replicate (length subpatterns) CWildcardPat <> rest)
        Just (CIntPat int, rest) -> case pattern of
            CIntPat int2 | int == int2 -> Just rest
            _ -> Nothing
        Just (CStringPat str, rest) -> case pattern of
            CStringPat str2 | str == str2 -> Just rest
            _ -> Nothing
        Just (CTuplePat subpatterns, rest) -> case pattern of
            -- lengths are assumed to be the same since this has already been type checked
            CTuplePat conSubPatterns -> do
                assertM (length subpatterns == length conSubPatterns)
                Just (coerce subpatterns <> rest)
            _ -> Nothing

decomposeWildcard :: Name -> PatternMatrix -> PatternMatrix
decomposeWildcard scrutinee matrix = Vector.mapMaybe decomposeRow matrix
  where
    decomposeRow (patterns, core) = case Vector.uncons patterns of
        Nothing -> error "trying to decompose a matrix without columns"
        Just (CWildcardPat, rest) -> Just (rest, core)
        Just (CVarPat varName, rest) -> Just (rest, CLet varName (CVar scrutinee) core)
        Just (CIntPat _, _) -> Nothing
        Just (CStringPat _, _) -> Nothing
        Just (CTuplePat _, _) -> Nothing

-- TODO: does this duplicate the body? it really shouldn't!
lowerCase :: forall m. (MonadUnique m, MonadTrace m) => (Vector (CorePattern (Fix CorePattern), CoreExpr)) -> Name -> m CoreExpr
lowerCase branches scrutinee = go (fmap (\(pattern, expr) -> ([pattern], expr)) branches) [scrutinee]
  where
    go :: PatternMatrix -> Seq Name -> m CoreExpr
    go matrix scrutinees = do
        trace Patterns ("go: " <> keyword "case" <+> "(" <> intercalateMap "," ident scrutinees <> ")" <+> keyword "of\n" <+> prettyMatrix matrix)
        case (matrix, scrutinees) of
            (Vector.uncons -> Nothing, _) ->
                -- TODO: This *should* never be reachable if we assume that matches are exhaustive but we still need to
                -- emit a core expression
                pure (CLiteral (StringLit "UNREACHABLE!!! OH NO SOMETHING REALLY BAD HAPPENED"))
            (Vector.uncons -> Just (([], body), _), []) -> pure body
            (Vector.uncons -> Just ((row, body), _), scrutinees)
                | Vector.all isWildcard row -> do
                    let makeBinding pattern scrutinee = case pattern of
                            CVarPat varName -> CLet varName (CVar scrutinee)
                            _ -> id

                    let addBindings = compose $ Vector.zipWith makeBinding row (viaList scrutinees)

                    pure $ addBindings body
            (matrix, scrutinee :<| restScrutinees) -> case nonWildcardPatternsInFirstColumn matrix of
                [] -> do
                    let updateRow (patterns, body) = case Vector.uncons patterns of
                            Just (matchedPattern, restPatterns) -> do
                                case patternVar matchedPattern of
                                    Just name -> (restPatterns, CLet name (CVar scrutinee) body)
                                    Nothing -> (restPatterns, body)
                            Nothing -> error "no columns in non-empty pattern row"
                    go (fmap (updateRow) matrix) restScrutinees
                patterns -> do
                    matchedSubtrees <- forM patterns \pattern -> do
                        (pattern, subVars) <- subPatternsToVars pattern
                        subtree <- go (decomposeConstructor pattern matrix) (viaList subVars <> restScrutinees)
                        pure (pattern, subtree)
                    trace Patterns
                        $ "matched:\n"
                        <> align
                            ( vsep
                                $ fmap
                                    ( \(pattern, expr) ->
                                        pretty (coerce pattern :: CorePattern PrettyIdent) <+> keyword "->" <+> pretty expr
                                    )
                                    matchedSubtrees
                            )
                    unmatchedSubtree <- go (decomposeWildcard scrutinee matrix) restScrutinees
                    trace Patterns $ "unmatched:" <+> pretty unmatchedSubtree
                    pure $ CCase (CVar scrutinee) (matchedSubtrees <> [(CWildcardPat, unmatchedSubtree)])
            (_, Empty) -> error "empty scrutinees matched against pattern matrix"

    nonWildcardPatternsInFirstColumn :: PatternMatrix -> Vector (CorePattern (Fix CorePattern))
    nonWildcardPatternsInFirstColumn matrix =
        Vector.mapMaybe
            ( \case
                (Vector.uncons -> Just (pattern, _), _coreExpr)
                    | isWildcard pattern -> Nothing
                    | otherwise -> Just pattern
                _ -> error "empty pattern matrix"
            )
            matrix

    patternVar :: CorePattern f -> Maybe Name
    patternVar = \case
        CVarPat name -> Just name
        _ -> Nothing

    subPatternsToVars :: CorePattern (Fix CorePattern) -> m (CorePattern Name, Vector Name)
    subPatternsToVars pattern = case pattern of
        CWildcardPat -> pure (CWildcardPat, [])
        CVarPat name -> pure (CVarPat name, [])
        CIntPat int -> pure (CIntPat int, [])
        CStringPat str -> pure (CStringPat str, [])
        CTuplePat subpatterns -> do
            subpatternNames <- traverse (\_ -> freshName "x") subpatterns
            pure (CTuplePat subpatternNames, subpatternNames)
