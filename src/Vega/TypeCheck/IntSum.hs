{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Vega.TypeCheck.IntSum (IntSum, freshIntSum, readIntSum, readIntSumNonDestructive, zero, scale, add, subtract, reduceZero, asIntSumMaybe, asIntSum) where

import Data.List qualified as List
import Data.Traversable (for)
import Effectful (Eff, (:>))
import Effectful.Dispatch.Static (unsafeEff_)
import Relude hiding (subtract)
import System.IO.Unsafe (unsafePerformIO)
import {-# SOURCE #-} Vega.Effect.Meta.Static (BindMeta, ReadMeta, followMetas, followMetasWithoutPathCompression, readMeta)
import Vega.Loc (Loc)
import Vega.MultiSet (MultiSet)
import Vega.MultiSet qualified as MultiSet
import Vega.Syntax (IntSum (..), Type (..))
import {-# SOURCE #-} Vega.Syntax qualified as Vega
import Vega.Util qualified as Util

freshIntSum ::
    (BindMeta :> es) =>
    Int ->
    MultiSet Vega.MetaVar ->
    MultiSet Vega.Skolem ->
    MultiSet Vega.LocalName ->
    Eff es Vega.IntSum
freshIntSum literal metas skolems variables = do
    literal <- unsafeEff_ $ newIORef literal
    metas <- unsafeEff_ $ newIORef metas
    skolems <- unsafeEff_ $ newIORef skolems
    variables <- unsafeEff_ $ newIORef variables
    pure (MkIntSum{literal, metas, skolems, variables})

-- | Read the elements of an IntSum without following any meta variables
readIntSumRaw :: (ReadMeta :> es) => Vega.IntSum -> Eff es (Int, MultiSet Vega.MetaVar, MultiSet Vega.Skolem, MultiSet Vega.LocalName)
readIntSumRaw sum = unsafeEff_ do
    literal <- readIORef sum.literal
    metas <- readIORef sum.metas
    skolems <- readIORef sum.skolems
    variables <- readIORef sum.variables
    pure (literal, metas, skolems, variables)

readIntSumNonDestructive :: (ReadMeta :> es) => Vega.IntSum -> Eff es (Int, MultiSet Vega.MetaVar, MultiSet Vega.Skolem, MultiSet Vega.LocalName)
readIntSumNonDestructive sum = do
    (literal, metas, skolems, variables) <- readIntSumRaw sum
    (bound, unbound) <- Util.partitionMapM (\(meta, multiplicity) -> fmap (,multiplicity) <$> readMeta meta) (MultiSet.toMultiplicityList metas)
    (addedLiterals, addedMetas, addedSkolems, addedVariables) <-
        List.unzip4 <$> for bound \(type_, count) -> do
            (newLiteral, newMetas, newSkolems, newVariables) <-
                asIntSumNonDestructive type_ >>= \case
                    Just x -> pure x
                    _ -> undefined
            pure
                ( count * newLiteral
                , MultiSet.scaleMultiplicity count newMetas
                , MultiSet.scaleMultiplicity count newSkolems
                , MultiSet.scaleMultiplicity count newVariables
                )
    pure
        ( literal + Relude.sum addedLiterals
        , foldl' MultiSet.union (MultiSet.fromMultiplicityList unbound) addedMetas
        , foldl' MultiSet.union skolems addedSkolems
        , foldl' MultiSet.union variables addedVariables
        )

readIntSum :: (ReadMeta :> es, BindMeta :> es) => Vega.IntSum -> Eff es (Int, MultiSet Vega.MetaVar, MultiSet Vega.Skolem, MultiSet Vega.LocalName)
readIntSum sum = do
    (literal, metas, skolems, variables) <- readIntSumNonDestructive sum
    unsafeEff_ $ writeIORef sum.literal literal
    unsafeEff_ $ writeIORef sum.metas metas
    unsafeEff_ $ writeIORef sum.skolems skolems
    unsafeEff_ $ writeIORef sum.variables variables
    pure (literal, metas, skolems, variables)

zero :: IntSum
zero = unsafePerformIO do
    literal <- newIORef 0
    variables <- newIORef []
    skolems <- newIORef []
    metas <- newIORef []
    pure (MkIntSum{literal, variables, skolems, metas})
{-# NOINLINE zero #-}

-- It's not a massive deal if this is inlined since all it does is call `newIORef` but we still
-- don't need to repeat all the newIORefs

scale :: (ReadMeta :> es, BindMeta :> es) => Int -> IntSum -> Eff es IntSum
scale amount sum = do
    (literal, variables, skolems, metas) <- readIntSum sum
    freshIntSum
        (amount * literal)
        (MultiSet.scaleMultiplicity amount variables)
        (MultiSet.scaleMultiplicity amount skolems)
        (MultiSet.scaleMultiplicity amount metas)

add :: (ReadMeta :> es, BindMeta :> es) => IntSum -> IntSum -> Eff es IntSum
add sum1 sum2 = do
    (literal1, metas1, skolems1, variables1) <- readIntSum sum1
    (literal2, metas2, skolems2, variables2) <- readIntSum sum2
    freshIntSum
        (literal1 + literal2)
        (MultiSet.union metas1 metas2)
        (MultiSet.union skolems1 skolems2)
        (MultiSet.union variables1 variables2)

subtract :: (ReadMeta :> es, BindMeta :> es) => IntSum -> IntSum -> Eff es IntSum
subtract sum1 sum2 = do
    (literal1, variables1, skolems1, metas1) <- readIntSum sum1
    (literal2, variables2, skolems2, metas2) <- readIntSum sum2
    freshIntSum
        (literal1 - literal2)
        (MultiSet.union variables1 (MultiSet.negate variables2))
        (MultiSet.union skolems1 (MultiSet.negate skolems2))
        (MultiSet.union metas1 (MultiSet.negate metas2))

{- | Reduce a sum σ interpreted as the equation σ = 0.
In particular, if there exists an n ∈ N s.t. pure σ = scale n σ' then `reduceZero σ = pure σ'
-}
reduceZero :: (ReadMeta :> es, BindMeta :> es) => IntSum -> Eff es IntSum
reduceZero sum = do
    (literal, metas, skolems, variables) <- readIntSum sum
    let commonGCD = foldl' gcd literal (MultiSet.multiplicities metas <> MultiSet.multiplicities skolems <> MultiSet.multiplicities variables)
    if commonGCD == 1
        then
            pure sum
        else
            freshIntSum
                (literal `div` commonGCD)
                (MultiSet.mapMultiplicityNonZero (`div` commonGCD) metas)
                (MultiSet.mapMultiplicityNonZero (`div` commonGCD) skolems)
                (MultiSet.mapMultiplicityNonZero (`div` commonGCD) variables)

asIntSumNonDestructive :: (ReadMeta :> es) => Vega.Type -> Eff es (Maybe (Int, MultiSet Vega.MetaVar, MultiSet Vega.Skolem, MultiSet Vega.LocalName))
asIntSumNonDestructive type_ =
    followMetasWithoutPathCompression type_ >>= \case
        IntSum sum -> Just <$> readIntSumNonDestructive sum
        MetaVar meta -> pure $ Just (0, fromList [meta], mempty, mempty)
        Skolem skolem -> pure $ Just (0, mempty, fromList [skolem], mempty)
        TypeVar name -> pure $ Just (0, mempty, mempty, fromList [name])
        _ -> pure Nothing

asIntSumMaybe :: (ReadMeta :> es, BindMeta :> es) => Vega.Type -> Eff es (Maybe IntSum)
asIntSumMaybe type_ =
    followMetas type_ >>= \case
        IntSum sum -> pure (Just sum)
        MetaVar meta -> Just <$> freshIntSum 0 (fromList [meta]) mempty mempty
        Skolem skolem -> Just <$> freshIntSum 0 mempty (fromList [skolem]) mempty
        TypeVar name -> Just <$> freshIntSum 0 mempty mempty (fromList [name])
        _ -> pure Nothing

asIntSum :: (ReadMeta :> es, BindMeta :> es) => Loc -> Vega.Type -> Eff es IntSum
asIntSum loc type_ =
    asIntSumMaybe type_ >>= \case
        Just sum -> pure sum
        Nothing -> undefined loc
