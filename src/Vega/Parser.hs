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
import Vega.Syntax qualified as Syntax

data AdditionalParseError
    = MismatchedFunctionName
        { typeSignature :: Text
        , definition :: Text
        }
    | UnknowNamedKind Text
    | TupleKind (Seq (KindSyntax Parsed))
    deriving stock (Eq, Ord, Generic)

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

stringLit :: Parser (Text, Loc)
stringLit = MegaParsec.token match (fromList [Label (fromList "string literal")])
  where
    match = \case
        (Lexer.StringLiteral text, loc) -> Just (text, loc)
        _ -> Nothing

intLit :: Parser (Integer, Loc)
intLit = MegaParsec.token match (fromList [Label (fromList "integer literal")])
  where
    match = \case
        (Lexer.IntLiteral int, loc) -> Just (int, loc)
        _ -> Nothing

floatLit :: Parser (Rational, Loc)
floatLit = MegaParsec.token match (fromList [Label (fromList "float literal")])
  where
    match = \case
        (Lexer.FloatLiteral float, loc) -> Just (float, loc)
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
            , loc = startLoc <> getLoc body
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

type_ :: Parser (TypeSyntax Parsed)
type_ =
    choice
        [ chainl1 type1 (single Arrow *> pure (\type1 type2 -> PureFunctionS (getLoc type1 <> getLoc type2) (fromList [type1]) type2))
        , chainl1 type1 (effectArrow >>= \effect -> pure (\type1 type2 -> FunctionS (getLoc type1 <> getLoc type2) (fromList [type1]) effect type2))
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
                    , do
                        case parameters of
                            (type_ :<| Empty) -> pure type_
                            parameters -> pure (TupleS loc parameters)
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

                choice
                    [ do
                        _ <- single Arrow
                        result <- kind
                        pure (ArrowKindS (startLoc <> getLoc result) parameterKinds result)
                    , case parameterKinds of
                        (kind :<| _) -> pure kind
                        _ -> customFailure (TupleKind parameterKinds)
                    ]
            ]

pattern_ :: Parser (Pattern Parsed)
pattern_ = do
    firstPattern <- pattern1
    rest <- many (single Pipe *> pattern1)
    case rest of
        Empty -> pure firstPattern
        (_ :|> lastPattern) -> pure (OrPattern (getLoc firstPattern <> getLoc lastPattern) (firstPattern :<| rest))
  where
    pattern1 =
        choice
            [ do
                inner <- pattern2
                _ <- single As
                (name, endLoc) <- identifierWithLoc
                pure (AsPattern (getLoc inner <> endLoc) inner name)
            , do
                inner <- pattern2
                _ <- single Colon
                typeSignature <- type_
                pure (TypePattern (getLoc inner <> getLoc typeSignature) inner typeSignature)
            , pattern2
            ]
    pattern2 =
        choice
            [ do
                (name, loc) <- identifierWithLoc
                pure (VarPattern loc name)
            , do
                (name, startLoc) <- constructorWithLoc
                subPatterns <- optional (argumentsWithLoc pattern_)
                case subPatterns of
                    Nothing -> pure $ ConstructorPattern startLoc name (fromList [])
                    Just (subPatterns, endLoc) -> pure $ ConstructorPattern (startLoc <> endLoc) name subPatterns
            , do
                (patterns, loc) <- argumentsWithLoc pattern_
                case patterns of
                    (pattern_ :<| Empty) -> pure pattern_
                    _ -> pure $ TuplePattern loc patterns
            ]

expr :: Parser (Expr Parsed)
expr = exprLogical
  where
    makeBinOp operator = \expr1 expr2 -> BinaryOperator (getLoc expr1 <> getLoc expr2) expr1 operator expr2

    exprLogical =
        exprCompare
            `chainl1` choice
                [ single DoubleAmpersand *> pure (makeBinOp And)
                , single DoublePipe *> pure (makeBinOp Or)
                ]

    exprCompare =
        exprAdd
            `chainl1` choice
                [ single Lexer.Less *> pure (makeBinOp Syntax.Less)
                , single Lexer.LessEqual *> pure (makeBinOp Syntax.LessEqual)
                , single Lexer.DoubleEqual *> pure (makeBinOp Syntax.Equal)
                , single Lexer.NotEqual *> pure (makeBinOp Syntax.NotEqual)
                , single Lexer.GreaterEqual *> pure (makeBinOp Syntax.GreaterEqual)
                , single Lexer.Greater *> pure (makeBinOp Syntax.Greater)
                ]

    exprAdd =
        exprMultiply
            `chainl1` choice
                [ single Lexer.Plus *> pure (makeBinOp Syntax.Add)
                , single Lexer.Minus *> pure (makeBinOp Syntax.Subtract)
                ]

    exprMultiply =
        exprFun
            `chainl1` choice
                [ single Lexer.Asterisk *> pure (makeBinOp Syntax.Multiply)
                , single Lexer.Slash *> pure (makeBinOp Syntax.Divide)
                ]
    exprFun = do
        funExpr <- exprLeaf
        applications <- many @[_] functionApplication
        pure $ foldl' (\expr application -> application expr) funExpr applications
    exprLeaf =
        choice
            [ do
                (name, loc) <- identifierWithLoc
                pure (Var loc name)
            , do
                (name, loc) <- constructorWithLoc
                pure (DataConstructor loc name)
            , do
                startLoc <- single Lexer.Lambda
                parameters <- many pattern_
                _ <- single Arrow
                body <- expr
                pure (Syntax.Lambda (startLoc <> getLoc body) parameters body)
            , do
                (literal, loc) <- stringLit
                pure (Syntax.StringLiteral loc literal)
            , do
                (integer, loc) <- intLit
                pure (Syntax.IntLiteral loc integer)
            , do
                (float, loc) <- floatLit
                pure (Syntax.DoubleLiteral loc float)
            , do
                (elements, loc) <- argumentsWithLoc expr
                case elements of
                    (expr :<| Empty) -> pure expr
                    _ -> pure (TupleLiteral loc elements)
            , do
                startLoc <- single Lexer.If
                condition <- expr
                _ <- single Lexer.Then
                thenBranch <- expr
                _ <- single Lexer.Else
                elseBranch <- expr
                pure (Syntax.If{loc = startLoc <> getLoc elseBranch, condition, thenBranch, elseBranch})
            , do
                startLoc <- single Lexer.LBrace
                statements <- fromList <$> statement `sepEndBy` (single Lexer.Comma)
                endLoc <- single Lexer.RBrace
                pure (SequenceBlock (startLoc <> endLoc) statements)
            , do
                startLoc <- single Lexer.Match
                scrutinee <- expr
                _ <- single LBrace
                cases <- fromList <$> matchCase `sepEndBy` (single Lexer.Semicolon)
                endLoc <- single RBrace
                pure (Syntax.Match{loc = startLoc <> endLoc, scrutinee, cases})
            ]

matchCase :: Parser (MatchCase Parsed)
matchCase = do
    pattern_ <- pattern_
    _ <- single Arrow
    body <- expr
    pure (MkMatchCase{loc = getLoc pattern_ <> getLoc body, pattern_, body})

statement :: Parser (Statement Parsed)
statement = undefined

functionApplication :: Parser (Expr Parsed -> Expr Parsed)
functionApplication =
    choice
        [ do
            (args, endLoc) <- argumentsWithLoc expr
            pure (\inner -> Application (getLoc inner <> endLoc) inner args)
        , do
            _ <- single LBracket
            typeArguments <- type_ `sepBy` (single Comma)
            endLoc <- single RBracket
            pure (\inner -> VisibleTypeApplication (getLoc inner <> endLoc) inner typeArguments)
        ]

import_ :: Parser Import
import_ = undefined

argumentsWithLoc :: Parser a -> Parser (Seq a, Loc)
argumentsWithLoc parser = do
    startLoc <- single LParen
    args <- parser `sepBy` (single Comma)
    endLoc <- single RParen
    pure (args, startLoc <> endLoc)

arguments :: Parser a -> Parser (Seq a)
arguments parser = fmap fst $ argumentsWithLoc parser
