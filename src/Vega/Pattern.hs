module Vega.Pattern (lowerCase) where

import Vega.Prelude
import Vega.Syntax
import Vega.Util

import Vega.Eval (CoreExpr)

import Data.Vector qualified as Vector
import Vega.Monad.Unique (MonadUnique (freshName))

-- TODO: Oh god, dependent pattern matching is going to make this... difficult

-- Pattern matrices are represented as vectors (rows) of pattern columns
type PatternMatrix = Vector (Vector (CorePattern (Fix CorePattern)), CoreExpr)

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

decomposeWildcard :: PatternMatrix -> PatternMatrix
decomposeWildcard matrix = Vector.mapMaybe (\(row, core) -> (,core) <$> decomposeRow row) matrix
  where
    decomposeRow row = case Vector.uncons row of
        Nothing -> error "trying to decompose a matrix without columns"
        Just (CWildcardPat, rest) -> Just rest
        Just (CVarPat _, rest) -> Just rest
        Just (CIntPat _, _) -> Nothing
        Just (CStringPat _, _) -> Nothing
        Just (CTuplePat _, _) -> Nothing

lowerCase :: forall m. (MonadUnique m) => (Vector (CorePattern (Fix CorePattern), CoreExpr)) -> Name -> m CoreExpr
lowerCase branches scrutinee = go (fmap (\(pattern, expr) -> ([pattern], expr)) branches) [scrutinee]
  where
    go :: PatternMatrix -> Seq Name -> m CoreExpr
    go (Vector.uncons -> Nothing) _ =
        -- TODO: This *should* never be reachable if we assume that matches are exhaustive but we still need to
        -- emit a core expression
        pure (CLiteral (StringLit "UNREACHABLE!!! OH NO SOMETHING REALLY BAD HAPPENED"))
    go (Vector.uncons -> Just (([], body), _)) [] = pure body
    go (Vector.uncons -> Just ((row, body), _)) scrutinees
        | Vector.all isWildcard row = do
            let makeBinding pattern scrutinee = case pattern of
                    CVarPat varName -> CLet varName (CVar scrutinee)
                    _ -> id

            let addBindings = compose $ Vector.zipWith makeBinding row (viaList scrutinees)

            pure $ addBindings body
    go matrix (scrutinee :<| restScrutinees) = case nonWildcardPatternsInFirstColumn matrix of
        [] ->
            -- TODO: bind variables?
            go (fmap (first Vector.tail) matrix) restScrutinees
        patterns -> do
            matchedSubtrees <- forM patterns \pattern -> do
                (pattern, subVars) <- subPatternsToVars pattern
                subtree <- go (decomposeConstructor pattern matrix) (viaList subVars <> restScrutinees)
                pure (pattern, subtree)
            unmatchedSubtree <- go (decomposeWildcard matrix) restScrutinees
            -- TODO: variables??
            pure $ CCase (CVar scrutinee) (matchedSubtrees <> [(CWildcardPat, unmatchedSubtree)])
    go _ Empty = error "empty scrutinees matched against pattern matrix"

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

    subPatternsToVars :: CorePattern (Fix CorePattern) -> m (CorePattern Name, Vector Name)
    subPatternsToVars pattern = case pattern of
        CWildcardPat -> pure (CWildcardPat, [])
        CVarPat name -> pure (CVarPat name, [])
        CIntPat int -> pure (CIntPat int, [])
        CStringPat str -> pure (CStringPat str, [])
        CTuplePat subpatterns -> do
            subpatternNames <- traverse (\_ -> freshName "x") subpatterns
            pure (CTuplePat subpatternNames, subpatternNames)
