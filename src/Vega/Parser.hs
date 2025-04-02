{-# LANGUAGE NoOverloadedLists #-}

module Vega.Parser (Parser, module_) where

import Relude hiding (many)

import Vega.Syntax

import Data.Sequence (Seq (..))
import GHC.IsList (Item)
import Text.Megaparsec hiding (Token, many, sepBy, sepBy1, single)
import Text.Megaparsec qualified as MegaParsec
import Vega.Lexer as Lexer (Token (..))
import Vega.Loc (Loc (MkLoc), getLoc)

data AdditionalParseError
    = MismatchedFunctionName
        { typeSignature :: Text
        , definition :: Text
        }
    | UnknowNamedKind Text
    deriving (Show, Eq, Ord, Generic)

newtype ParserEnv = MkParserEnv
    { moduleName :: Text
    }

type Parser = ReaderT ParserEnv (Parsec AdditionalParseError [(Token, Loc)])

globalNameForCurrentModule :: Text -> Parser GlobalName
globalNameForCurrentModule name = do
    MkParserEnv{moduleName} <- ask
    pure (MkGlobalName{moduleName, name})

single :: Token -> Parser Loc
single target = MegaParsec.token match (fromList [undefined])
  where
    match = \case
        (token, loc) | token == target -> Just loc
        _ -> Nothing

identifierWithLoc :: Parser (Text, Loc)
identifierWithLoc = token matchIdentifier (fromList [Label (fromList "identifier")])
  where
    matchIdentifier = \case
        (Ident ident, loc) -> Just (ident, loc)
        _ -> Nothing

identifier :: Parser Text
identifier = fmap fst identifierWithLoc

constructorWithLoc :: Parser (Text, Loc)
constructorWithLoc = token matchConstructor (fromList [Label (fromList "constructor")])
  where
    matchConstructor = \case
        (Constructor ident, loc) -> Just (ident, loc)
        _ -> Nothing

constructor :: Parser Text
constructor = fmap fst constructorWithLoc

many :: (IsList l, Item l ~ a, MonadPlus m) => m a -> m l
many parser = fromList <$> MegaParsec.many parser

many1 :: (IsList l, Item l ~ a, MonadPlus m) => m a -> m l
many1 parser = do
    first <- parser
    rest <- many parser
    pure $ fromList (first : rest)

sepBy :: (MonadPlus m, IsList l, Item l ~ a) => m a -> m sep -> m l
sepBy item separator = fromList <$> MegaParsec.sepBy item separator

sepBy1 :: (MonadPlus m, IsList l, Item l ~ a) => m a -> m sep -> m l
sepBy1 item separator = fromList <$> MegaParsec.sepBy1 item separator

-- Why is this not in megaparsec?
chainl1 :: (MonadPlus m) => m a -> m (a -> a -> a) -> m a
chainl1 parser between = do
    first <- parser
    rest <- many @[_] (liftA2 (,) between parser)
    pure $ foldl' (\left (operator, right) -> left `operator` right) first rest

module_ :: Parser ParsedModule
module_ = do
    imports <- many import_
    declarations <- many declaration
    pure (MkParsedModule{imports, declarations})

declaration :: Parser (Declaration Parsed)
declaration =
    choice
        [ defineFunction
        , defineVariantType
        ]

defineFunction :: Parser (Declaration Parsed)
defineFunction = do
    (name, startLoc) <- identifierWithLoc
    _ <- single Colon
    typeSignature <- type_
    definitionName <- identifier

    when (name /= definitionName) do
        registerFancyFailure
            ( fromList
                [ ErrorCustom
                    ( MismatchedFunctionName
                        { typeSignature = name
                        , definition = definitionName
                        }
                    )
                ]
            )

    _ <- single LParen
    parameters <- pattern_ `sepBy` (single Comma)
    _ <- single RParen
    _ <- single Equals
    body <- expr
    name <- globalNameForCurrentModule name
    pure
        ( MkDeclaration
            { name
            , syntax =
                DefineFunction
                    { typeSignature
                    , parameters
                    , body
                    }
            , loc = startLoc <> undefined -- getLoc body
            }
        )

defineVariantType :: Parser (Declaration Parsed)
defineVariantType = do
    startLoc <- single Data
    name <- constructor
    typeParameters <- option (fromList []) (arguments identifier)
    _ <- single Equals
    _ <- optional (single Pipe)
    constructors <- constructorDefinition `sepBy1` (single Pipe)
    let endLoc = case constructors of
            Empty -> error "sepBy returned empty?"
            (_ :|> (_, _, endLoc)) -> endLoc

    name <- globalNameForCurrentModule name
    pure
        ( MkDeclaration
            { name = name
            , syntax =
                DefineVariantType
                    { typeParameters
                    , constructors = fmap (\(name, arguments, _) -> (name, arguments)) constructors
                    }
            , loc = startLoc <> endLoc
            }
        )
  where
    constructorDefinition = do
        (name, startLoc) <- constructorWithLoc
        (dataArguments, endLoc) <- option (fromList [], startLoc) (argumentsWithLoc type_)
        pure (name, dataArguments, startLoc <> endLoc)

-- TODO: '(' type ')', '(' kind ')'
type_ :: Parser (TypeSyntax Parsed)
type_ =
    choice
        [ chainl1 type1 (single Arrow *> pure (\type1 type2 -> PureFunctionS (getLoc type1 <> getLoc type2) (fromList [type1]) type2))
        , chainl1 type1 (effectArrow >>= \effect -> pure (\type1 type2 -> FunctionS undefined (fromList [type1]) effect type2))
        ]
  where
    type1 = do
        typeConstructor <- type2
        applications <- many @[_] $ argumentsWithLoc type_
        pure
            $ foldl'
                (\constr (arguments, endLoc) -> TypeApplicationS (getLoc typeConstructor <> endLoc) constr arguments)
                typeConstructor
                applications
    type2 =
        choice
            [ -- typeApplication
              forall_
            , do
                (name, loc) <- constructorWithLoc
                applications <- many @[_] (argumentsWithLoc type_)
                pure
                    $ foldl'
                        (\constr (args, loc) -> TypeApplicationS (getLoc constr <> loc) constr args)
                        (TypeConstructorS loc name)
                        applications
            , do
                (name, loc) <- identifierWithLoc
                pure $ TypeVarS loc name
            , do
                (parameters, loc) <- argumentsWithLoc type_
                choice
                    [ do
                        _ <- single Arrow
                        result <- type_
                        pure (PureFunctionS (loc <> getLoc result) parameters result)
                    , do
                        effect <- effectArrow
                        result <- type_
                        pure (FunctionS (loc <> getLoc result) parameters effect result)
                    ]
            ]

effectArrow :: Parser (EffectSyntax Parsed)
effectArrow = do
    _ <- single EffArrowStart
    effect <- type_
    _ <- single EffArrowEnd
    pure effect

forall_ :: Parser (TypeSyntax Parsed)
forall_ = do
    startLoc <- single Lexer.Forall
    vars <- many1 (typeVarBinder)
    _ <- single Lexer.Period
    remainingType <- type_
    pure (ForallS (startLoc <> getLoc remainingType) vars remainingType)

typeVarBinder :: Parser (TypeVarBinderS Parsed)
typeVarBinder =
    choice
        [ do
            (varName, loc) <- identifierWithLoc
            pure (MkTypeVarBinderS{loc, varName, kind = Nothing})
        , do
            startLoc <- single LParen
            varName <- identifier
            _ <- single Colon
            varKind <- kind
            endLoc <- single RParen
            pure (MkTypeVarBinderS{loc = startLoc <> endLoc, varName, kind = Just varKind})
        ]

kind :: Parser (KindSyntax Parsed)
kind = do
    chainl1 kind1 (single Arrow *> pure (\kind1 kind2 -> ArrowKindS (getLoc kind1 <> getLoc kind2) (fromList [kind1]) kind2))
  where
    kind1 =
        choice
            [ do
                (namedKind, loc) <- constructorWithLoc
                case namedKind of
                    "Type" -> pure $ TypeS loc
                    "Effect" -> pure $ EffectS loc
                    _ -> customFailure (UnknowNamedKind namedKind)
            , do
                (parameterKinds, startLoc) <- argumentsWithLoc kind
                _ <- single Arrow
                result <- kind
                pure (ArrowKindS (startLoc <> getLoc result) parameterKinds result)
            ]

pattern_ :: Parser (Pattern Parsed)
pattern_ = undefined

expr :: Parser (Expr Parsed)
expr = undefined

import_ :: Parser Import
import_ = empty

argumentsWithLoc :: Parser a -> Parser (Seq a, Loc)
argumentsWithLoc parser = do
    startLoc <- single LParen
    args <- parser `sepBy` (single Comma)
    endLoc <- single RParen
    pure (args, startLoc <> endLoc)

arguments :: Parser a -> Parser (Seq a)
arguments parser = fmap fst $ argumentsWithLoc parser
