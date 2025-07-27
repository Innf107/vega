{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoOverloadedLists #-}

module Vega.Parser (Parser, AdditionalParseError (..), parse) where

import Relude hiding (NonEmpty, many)

import Vega.Syntax hiding (forall_)

import Data.Sequence (Seq (..))
import Data.Text qualified as Text
import GHC.IsList (Item)
import Text.Megaparsec hiding (Token, many, parse, sepBy, sepBy1, sepEndBy, single)
import Text.Megaparsec qualified as MegaParsec
import Vega.Lexer.Token as Lexer (Token (..))
import Vega.Loc (HasLoc, Loc (MkLoc, endColumn, endLine, file, startColumn, startLine), getLoc)
import Vega.Seq.NonEmpty (NonEmpty (..), pattern (:<||))
import Vega.Seq.NonEmpty qualified as NonEmpty
import Vega.Syntax qualified as Syntax

data AdditionalParseError
    = MismatchedFunctionName
        { loc :: Loc
        , typeSignature :: Text
        , definition :: Text
        }
    | UnknowNamedKind Loc Text
    | NonVarInFunctionDefinition Loc
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (HasLoc)

newtype ParserEnv = MkParserEnv
    { moduleName :: ModuleName
    }

type Parser = ReaderT ParserEnv (Parsec AdditionalParseError [(Token, Loc)])

globalNamesForCurrentModule :: Text -> Parser (DeclarationName, GlobalName)
globalNamesForCurrentModule name = do
    MkParserEnv{moduleName} <- ask
    pure (MkDeclarationName{moduleName, name}, MkGlobalName{moduleName, name})

single :: Token -> Parser Loc
single target = MegaParsec.token match (fromList [Tokens (fromList [(target, dummyLoc)])])
  where
    match = \case
        (token, loc) | token == target -> Just loc
        _ -> Nothing
    dummyLoc = MkLoc{startLine = 0, startColumn = 0, endLine = 0, endColumn = 0, file = "<<dummy>>"}

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

many1Seq :: (MonadPlus m) => m a -> m (NonEmpty a)
many1Seq parser = do
    first <- parser
    rest <- many parser
    pure $ (first :<|| rest)

sepBy :: (MonadPlus m, IsList l, Item l ~ a) => m a -> m sep -> m l
sepBy item separator = fromList <$> MegaParsec.sepBy item separator

sepBy1 :: (MonadPlus m) => m a -> m sep -> m (NonEmpty a)
sepBy1 item separator =
    MegaParsec.sepBy1 item separator >>= \case
        [] -> error "sepBy1 returned empty list"
        (x : xs) -> pure (x :<|| fromList xs)

sepEndBy :: (MonadPlus m, IsList l, Item l ~ a) => m a -> m sep -> m l
sepEndBy item separator = fromList <$> MegaParsec.sepEndBy item separator

-- Why is this not in megaparsec?
chainl1 :: (MonadPlus m) => m a -> m (a -> a -> a) -> m a
chainl1 parser between = do
    first <- parser
    rest <- many @[_] (liftA2 (,) between parser)
    pure $ foldl' (\left (operator, right) -> left `operator` right) first rest

parse :: ModuleName -> FilePath -> [(Token, Loc)] -> Either (ParseErrorBundle [(Token, Loc)] AdditionalParseError) ParsedModule
parse moduleName filePath tokens = do
    let parserEnv = MkParserEnv{moduleName}
    MegaParsec.parse (runReaderT (module_ <* single EOF) parserEnv) filePath tokens

module_ :: Parser ParsedModule
module_ = do
    imports <- import_ `sepEndBy` (single Semicolon)
    declarations <- declaration `sepEndBy` (single Semicolon)
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
    _ <- single Semicolon
    definitionName <- identifier

    when (name /= definitionName) do
        registerFancyFailure
            ( fromList
                [ ErrorCustom
                    ( MismatchedFunctionName
                        { loc = startLoc
                        , typeSignature = name
                        , definition = definitionName
                        }
                    )
                ]
            )

    declaredTypeParameters <- option Empty do
        _ <- single LBracket
        parameters <- (swap <$> identifierWithLoc) `sepBy` (single Comma)
        _ <- single RBracket
        pure parameters

    _ <- single LParen
    parameters <- pattern_ `sepBy` (single Comma)
    _ <- single RParen
    _ <- single Equals
    body <- expr
    (declarationName, name) <- globalNamesForCurrentModule name

    pure
        ( MkDeclaration
            { name = declarationName
            , syntax =
                DefineFunction
                    { name
                    , typeSignature
                    , declaredTypeParameters
                    , parameters
                    , body
                    }
            , loc = startLoc <> getLoc body
            }
        )

-- TODO: allow empty definitions
defineVariantType :: Parser (Declaration Parsed)
defineVariantType = do
    startLoc <- single Data
    name <- constructor
    typeParameters <- option (fromList []) (arguments typeVarBinder)
    _ <- single Equals
    _ <- optional (single Pipe)
    constructors <- constructorDefinition `sepBy1` (single Pipe)
    let endLoc = case constructors of
            (_ :||> (_, _, endLoc)) -> endLoc

    (declarationName, name) <- globalNamesForCurrentModule name
    pure
        ( MkDeclaration
            { name = declarationName
            , syntax =
                DefineVariantType
                    { name
                    , typeParameters
                    , constructors = fmap (\(name, arguments, loc) -> (loc, name, arguments)) (NonEmpty.toSeq constructors)
                    }
            , loc = startLoc <> endLoc
            }
        )
  where
    constructorDefinition = do
        (name, startLoc) <- constructorWithLoc
        (_, globalName) <- globalNamesForCurrentModule name

        (dataArguments, endLoc) <- option (fromList [], startLoc) (argumentsWithLoc type_)
        pure (globalName, dataArguments, startLoc <> endLoc)

-- TODO: (k1 + ... + kn), (k1 * .. * kn)
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
        pure $
            foldl'
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
                case name of
                    -- TODO: this doesn't allow using `Type` as a bare type constructor
                    "Type" -> case applications of
                        [(rep :<| Empty, appLoc)] -> pure (TypeS (loc <> appLoc) rep)
                        _ -> undefined
                    _ -> do
                        let constructor = case name of
                                "Effect" -> EffectS loc
                                "Rep" -> RepS loc
                                "Unit" -> UnitRepS loc
                                "Empty" -> EmptyRepS loc
                                "Boxed" -> BoxedRepS loc
                                "IntRep" -> IntRepS loc
                                "Kind" -> KindS loc
                                _ -> TypeConstructorS loc name
                        pure $
                            foldl'
                                (\constr (args, loc) -> TypeApplicationS (getLoc constr <> loc) constr args)
                                constructor
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
    vars <- many1Seq typeVarBinder
    _ <- single Lexer.Period
    remainingType <- type_
    pure (ForallS (startLoc <> getLoc remainingType) vars remainingType)

typeVarBinder :: Parser (ForallBinderS Parsed)
typeVarBinder =
    do
        monomorphization <- monomorphization
        choice
            [ do
                (varName, loc) <- identifierWithLoc
                pure (UnspecifiedBinderS{loc, varName, monomorphization})
            , do
                startLoc <- single LParen
                varName <- identifier
                _ <- single Colon
                varKind <- kind
                endLoc <- single RParen
                pure (TypeVarBinderS{loc = startLoc <> endLoc, monomorphization, varName, kind = varKind, visibility = Visible})
            , do
                startLoc <- single LBrace
                varName <- identifier
                _ <- single Colon
                varKind <- kind
                endLoc <- single RBrace
                pure (TypeVarBinderS{loc = startLoc <> endLoc, monomorphization, varName, kind = varKind, visibility = Inferred})
            ]

kind :: Parser (KindSyntax Parsed)
kind = type_

monomorphization :: Parser Monomorphization
monomorphization =
    choice
        [ single Asterisk *> pure Monomorphized
        , pure Parametric
        ]

pattern_ :: Parser (Pattern Parsed)
pattern_ = do
    firstPattern <- pattern1
    rest <- many (single Pipe *> pattern1)
    case rest of
        Empty -> pure firstPattern
        (_ :|> lastPattern) -> pure (OrPattern (getLoc firstPattern <> getLoc lastPattern) (firstPattern :<| rest))
  where
    pattern1 = do
        inner <- pattern2
        choice
            [ do
                _ <- single As
                (name, endLoc) <- identifierWithLoc
                pure (AsPattern (getLoc inner <> endLoc) inner name)
            , do
                _ <- single Colon
                typeSignature <- type_
                pure (TypePattern (getLoc inner <> getLoc typeSignature) inner typeSignature)
            , pure inner
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
            , do
                loc <- single Underscore
                pure (WildcardPattern loc)
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
                choice
                    [ do
                        _ <- single LBracket
                        typeArguments <- type_ `sepBy` (single Comma)
                        endLoc <- single RBracket
                        pure (VisibleTypeApplication (loc <> endLoc) name typeArguments)
                    , pure (Var loc name)
                    ]
            , do
                (name, loc) <- constructorWithLoc
                pure (DataConstructor loc name)
            , do
                startLoc <- single Lexer.Lambda
                typeParameters <- option Empty do
                    single LBracket
                    parameters <- (swap <$> identifierWithLoc) `sepBy` single Comma
                    single RBracket
                    pure parameters
                parameters <- many pattern_
                _ <- single Arrow
                body <- expr
                pure (Syntax.Lambda (startLoc <> getLoc body) typeParameters parameters body)
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
                statements <- fromList <$> statement `sepEndBy` (single Lexer.Semicolon)
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
statement =
    choice
        [ let_
        , do
            startLoc <- single Lexer.Use
            pattern_ <- pattern_
            rhs <- expr
            pure (Syntax.Use (startLoc <> getLoc rhs) pattern_ rhs)
        , do
            exprToRun <- expr
            pure (Run (getLoc exprToRun) exprToRun)
        ]

let_ :: Parser (Statement Parsed)
let_ = do
    startLoc <- single Lexer.Let
    boundPattern <- pattern_
    choice
        [ -- let x = e
          do
            _ <- single Lexer.Equals
            rhs <- expr
            pure (Syntax.Let (startLoc <> getLoc rhs) boundPattern rhs)
        , -- let f(x, y) = e
          do
            params <- arguments pattern_
            _ <- single Lexer.Equals
            rhs <- expr
            case boundPattern of
                VarPattern _ varName -> pure $ Syntax.LetFunction (startLoc <> getLoc rhs) varName Nothing params rhs
                _ -> customFailure (NonVarInFunctionDefinition (getLoc boundPattern))
        , -- let f : Int -> Int; let f(x) = x
          do
            _ <- single Lexer.Colon
            typeSig <- type_
            _ <- single Lexer.Semicolon
            _ <- single Lexer.Let
            name <- identifier
            params <- arguments pattern_
            _ <- single Lexer.Equals
            rhs <- expr
            pure (Syntax.LetFunction (startLoc <> getLoc rhs) name (Just typeSig) params rhs)
        ]

functionApplication :: Parser (Expr Parsed -> Expr Parsed)
functionApplication = do
    (partialArgs, endLoc) <-
        argumentsWithLoc $
            choice
                [ Just <$> expr
                , single Underscore *> pure Nothing
                ]
    case sequence partialArgs of
        Nothing -> pure (\inner -> PartialApplication (getLoc inner <> endLoc) inner partialArgs)
        Just args -> pure (\inner -> Application (getLoc inner <> endLoc) inner args)

import_ :: Parser Import
import_ = do
    startLoc <- single Lexer.Import
    (module_, _loc) <- moduleName
    choice
        [ do
            _ <- single As
            (importedAs, endLoc) <- constructorWithLoc
            pure
                ( ImportQualified
                    { loc = startLoc <> endLoc
                    , moduleName = module_
                    , importedAs
                    }
                )
        , do
            (identifiers, endLoc) <- argumentsWithLoc (identifier <|> constructor)
            pure (ImportUnqualified (startLoc <> endLoc) module_ identifiers)
        ]

moduleName :: Parser (ParsedModuleName, Loc)
moduleName = do
    packageName <- optional $ try $ (identifierWithLoc <|> constructorWithLoc) <* single Colon

    subModules <- (identifierWithLoc <|> constructorWithLoc) `sepBy1` (single Slash)

    case packageName of
        Nothing ->
            pure
                ( MkParsedModuleName{package = Nothing, subModules = fmap fst subModules}
                , snd (NonEmpty.first subModules) <> snd (NonEmpty.last subModules)
                )
        Just (package, startLoc) ->
            pure
                ( MkParsedModuleName
                    { package = Just (MkPackageName package)
                    , subModules = fmap fst subModules
                    }
                , startLoc <> snd (NonEmpty.last subModules)
                )

argumentsWithLoc :: Parser a -> Parser (Seq a, Loc)
argumentsWithLoc parser = do
    startLoc <- single LParen
    args <- parser `sepBy` (single Comma)
    endLoc <- single RParen
    pure (args, startLoc <> endLoc)

arguments :: Parser a -> Parser (Seq a)
arguments parser = fmap fst $ argumentsWithLoc parser
