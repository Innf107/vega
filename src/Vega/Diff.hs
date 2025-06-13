{-# LANGUAGE UndecidableInstances #-}

module Vega.Diff (DiffChange (..), diffDeclarations, reportNewModule) where

import Relude hiding (Type, evalState, get, put)

import Vega.Syntax

import Effectful
import GHC.Generics

import Data.HashMap.Strict qualified as HashMap
import Effectful.Writer.Static.Local (execWriter, tell)
import Vega.Loc (Loc)

import Data.Sequence qualified as Seq
import Effectful.State.Static.Local (evalState, get, put)
import Vega.Util qualified as Util

data DiffChange
    = Added (Declaration Parsed)
    | Removed GlobalName
    | Changed (Declaration Parsed)

reportNewModule :: ParsedModule -> Seq DiffChange
reportNewModule MkParsedModule{declarations} = fmap Added declarations

diffDeclarations :: Seq (Declaration Parsed) -> HashMap GlobalName (Declaration Parsed) -> Eff es (Seq DiffChange)
diffDeclarations declarations allPreviousDeclarations = evalState allPreviousDeclarations $ execWriter @(Seq DiffChange) $ do
    for_ declarations \declaration -> do
        previousDeclarations :: HashMap GlobalName (Declaration Parsed) <- get
        case HashMap.lookup declaration.name previousDeclarations of
            Nothing -> tell @(Seq _) [Added declaration]
            Just previousDeclaration -> do
                -- TODO: avoid the double traversal here
                put (HashMap.delete declaration.name previousDeclarations)
                case diff declaration previousDeclaration of
                    True -> do
                        tell @(Seq _) [Changed declaration]
                    False -> pure ()
    -- If there are any declarations left that we didn't hit in the new ones, these must have been removed
    remainingHashMap :: HashMap GlobalName (Declaration Parsed) <- get
    tell (Seq.fromList (map Removed (HashMap.keys remainingHashMap)))

class DiffGen f where
    diffGen :: f x -> f x -> Bool

instance (DiffGen f, DiffGen g) => DiffGen (f :+: g) where
    diffGen (L1 x) (L1 y) = diffGen x y
    diffGen (R1 x) (R1 y) = diffGen x y
    diffGen _ _ = True

instance (DiffGen f, DiffGen g) => DiffGen (f :*: g) where
    diffGen (x1 :*: x2) (y1 :*: y2) = diffGen x1 y1 || diffGen x2 y2

instance (DiffGen f) => DiffGen (M1 _type _meta f) where
    diffGen (M1 x) (M1 y) = diffGen x y

instance {-# OVERLAPPING #-} DiffGen (K1 _i Loc) where
    diffGen _ _ = False

instance (Diff c) => DiffGen (K1 _i c) where
    diffGen (K1 x) (K1 y) = diff x y

instance DiffGen U1 where
    diffGen U1 U1 = False

instance (Generic x, DiffGen (Rep x)) => Diff (Generically x) where
    diff (Generically x) (Generically y) = diffGen (from x) (from y)

newtype DiffFromEq a = MkDiffFromEq a

instance (Eq a) => Diff (DiffFromEq a) where
    diff (MkDiffFromEq x) (MkDiffFromEq y) = x /= y

newtype IgnoredInDiff a = MkIgnoredInDiff a

instance Diff (IgnoredInDiff a) where
    diff _ _ = False

class Diff a where
    -- | Check if two values differ *for the purposes of recompilation checking*. In particular, this will
    --         *ignore* source locations and other meta data
    diff :: a -> a -> Bool

instance (Diff a) => Diff (Seq a) where
    diff seq1 seq2 =
        (Seq.length seq1 /= Seq.length seq2)
            || Util.seqAny2 diff seq1 seq2

deriving via Generically (Maybe a) instance (Diff a) => Diff (Maybe a)
deriving via Generically (Either a b) instance (Diff a, Diff b) => Diff (Either a b)
deriving via Generically (a, b) instance (Diff a, Diff b) => Diff (a, b)

deriving via Generically (Declaration Parsed) instance Diff (Declaration Parsed)
deriving via Generically (DeclarationSyntax Parsed) instance Diff (DeclarationSyntax Parsed)
deriving via Generically (Expr Parsed) instance Diff (Expr Parsed)
deriving via Generically (Statement Parsed) instance Diff (Statement Parsed)
deriving via Generically (Pattern Parsed) instance Diff (Pattern Parsed)
deriving via Generically (MatchCase Parsed) instance Diff (MatchCase Parsed)
deriving via Generically BinaryOperator instance Diff BinaryOperator
deriving via Generically (TypeVarBinderS Parsed) instance Diff (TypeVarBinderS Parsed)
deriving via Generically (TypeSyntax Parsed) instance Diff (TypeSyntax Parsed)
deriving via Generically (KindSyntax Parsed) instance Diff (KindSyntax Parsed)
deriving via Generically LocalName instance Diff LocalName
deriving via Generically GlobalName instance Diff GlobalName
deriving via Generically Name instance Diff Name
deriving via Generically ModuleName instance Diff ModuleName

deriving via DiffFromEq Text instance Diff Text
deriving via DiffFromEq Int instance Diff Int
deriving via DiffFromEq Integer instance Diff Integer
deriving via DiffFromEq Rational instance Diff Rational

deriving via IgnoredInDiff Loc instance Diff Loc
