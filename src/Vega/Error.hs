{-# LANGUAGE RecordWildCards #-}

module Vega.Error (
    LexicalError (..),
    CompilationError (..),
    RenameError (..),
    RenameErrorSet (..),
    TypeError (..),
    TypeErrorSet (..),
    DriverError (..),
    renderCompilationError,
    ErrorMessage (..),
    ErrorMessageWithLoc (..),
    PlainErrorMessage (..),
    prettyErrorWithLoc,
) where

import Relude hiding (Type)

import Data.List.NonEmpty qualified as NonEmpty
import Data.Sequence (Seq (..))
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Text.Megaparsec (ErrorFancy (..), ErrorItem (..), ParseError (..), ParseErrorBundle)
import Text.Megaparsec.Error (ParseErrorBundle (..))
import Vega.Lexer.Token (Token)
import Vega.Loc (HasLoc, Loc (..), getLoc)
import Vega.Panic qualified as Panic
import Vega.Parser (AdditionalParseError (..))
import Vega.Parser qualified as Parser
import Vega.Pretty (Ann, Doc, Pretty (pretty), align, emphasis, errorText, globalIdentText, intercalateDoc, keyword, localIdentText, note, number, plain, vsep, (<+>))
import Vega.Syntax (GlobalName (..), Kind, LocalName, MetaVar, NameKind (..), Type (Tuple), prettyGlobal, prettyGlobalText, prettyLocal)
import Vega.Util (viaList)

data CompilationError
    = LexicalError LexicalError
    | ParseError (ParseErrorBundle [(Token, Loc)] AdditionalParseError)
    | RenameError RenameError
    | TypeError TypeError
    | DriverError DriverError
    | Panic SomeException
    deriving stock (Generic)

data LexicalError
    = UnexpectedCharacter Loc Char
    | UnterminatedStringLiteral Loc
    | InvalidStringEscape Loc Char
    | EmptyHexEscape Loc
    | MoreLayoutBlocksClosedThanOpened Loc

data RenameError
    = NameNotFound
        { loc :: Loc
        , name :: Text
        , nameKind :: NameKind
        }
    | AmbiguousGlobal
        { loc :: Loc
        , name :: Text
        , nameKind :: NameKind
        , candidates :: HashSet GlobalName
        }
    | InaccessibleGlobal
        { loc :: Loc
        , name :: Text
        , nameKind :: NameKind
        , candidates :: HashSet GlobalName
        }
    | TypeVariableNotFound
        { loc :: Loc
        , name :: Text
        }
    deriving stock (Generic)
    deriving anyclass (HasLoc)

newtype RenameErrorSet = MkRenameErrorSet (Seq RenameError)

data TypeError
    = FunctionDefinedWithIncorrectNumberOfArguments
        { loc :: Loc
        , functionName :: GlobalName
        , expectedType :: Type
        , expectedNumberOfArguments :: Int
        , numberOfDefinedParameters :: Int
        }
    | LambdaDefinedWithIncorrectNumberOfArguments
        { loc :: Loc
        , expectedType :: Type
        , expected :: Int
        , actual :: Int
        }
    | FunctionAppliedToIncorrectNumberOfArgs
        { loc :: Loc
        , functionType :: Type
        , expected :: Int
        , actual :: Int
        }
    | TuplePatternOfIncorrectNumberOfArgs
        { loc :: Loc
        , expected :: Int
        , actual :: Int
        , expectedType :: Type
        }
    | TupleLiteralOfIncorrectNumberOfArgs
        { loc :: Loc
        , expected :: Int
        , actual :: Int
        , expectedType :: Type
        }
    | ConstructorPatternOfIncorrectNumberOfArgs
        { loc :: Loc
        , actual :: Int
        , expectedTypes :: Seq Type
        }
    | UnableToUnify
        { loc :: Loc
        , expectedType :: Type
        , actualType :: Type
        }
    | TypeConstructorAppliedToIncorrectNumberOfArguments
        { loc :: Loc
        , type_ :: Type
        , kind :: Kind
        , expectedNumber :: Int
        , actualNumber :: Int
        }
    | ParametricVariableInMono
        { loc :: Loc
        , varName :: LocalName
        , fullType :: Maybe Type
        }
    | TryingToBindTooManyTypeParameters
        { loc :: Loc
        , boundCount :: Int
        , actualCount :: Int
        , type_ :: Type
        }
    | TypeApplicationWithTooFewParameters
        { loc :: Loc
        , typeArgumentCount :: Int
        , instantiatedType :: Type
        , parameterCount :: Int
        }
    | OccursCheckViolation
        { loc :: Loc
        , expectedType :: Type
        , actualType :: Type
        , meta :: MetaVar
        }
    deriving stock (Generic)
    deriving anyclass (HasLoc)

newtype TypeErrorSet = MkTypeErrorSet (Seq TypeError)
    deriving stock (Generic)

data DriverError
    = EntryPointNotFound GlobalName
    deriving stock (Generic)

data ErrorMessageWithLoc = MkErrorMessageWithLoc
    { location :: Loc
    , contents :: Doc Ann
    }

data PlainErrorMessage = MkPlainErrorMessage
    { contents :: Doc Ann
    }
    deriving stock (Generic)

data ErrorMessage
    = ErrorWithLoc ErrorMessageWithLoc
    | PlainError PlainErrorMessage

maxDisplayedLineCount :: Int
maxDisplayedLineCount = 5

extractRange :: (MonadIO io) => Loc -> io (Doc Ann)
extractRange loc = do
    lines <- Text.lines . decodeUtf8 <$> readFileBS (toString loc.file)

    let (isTooLong, lineCount) =
            if (loc.endLine - loc.startLine + 1) <= maxDisplayedLineCount
                then (False, loc.endLine - loc.startLine + 1)
                else (True, maxDisplayedLineCount)

    let linePadding = Vector.maximum (fmap (length @[] . show) [loc.startLine .. (loc.startLine + lineCount - 1)])

    -- - 1 because loc lines are 1-based
    let extractedLines = fromList $ take lineCount $ drop (loc.startLine - 1) lines

    let separatorWithLine lineNumber = keyword (Text.justifyRight linePadding ' ' (show lineNumber)) <> " " <> keyword "┃ "

    let highlightLine lineIndex line = do
            let (nonHighlightedStart, rest) =
                    if lineIndex == 0
                        then Text.splitAt (loc.startColumn - 1) line
                        else ("", line)
            let (highlighted, nonHighlightedEnd) =
                    if lineIndex == (length extractedLines - 1)
                        then Text.splitAt (loc.endColumn - Text.length nonHighlightedStart - 1) rest
                        else (rest, "")
            separatorWithLine (lineIndex + loc.startLine)
                <> plain nonHighlightedStart
                <> errorText highlighted
                <> plain nonHighlightedEnd

    let codeLines = vsep $ Vector.imap highlightLine extractedLines

    -- we only show an underline if there is a single line
    let underline = case lineCount of
            1 -> plain (Text.replicate (loc.startColumn - 1) " ") <> errorText (Text.replicate (loc.endColumn - loc.startColumn) "▔")
            _ | isTooLong -> errorText "..."
            _ -> ""

    let separator = plain (Text.replicate linePadding " ") <> " " <> keyword "┃ "

    pure $
        vsep @Vector
            [ separator
            , codeLines
            , separator <> underline
            ]

instance Pretty PlainErrorMessage where
    pretty message = errorText "ERROR:" <+> message.contents

prettyErrorWithLoc :: (MonadIO io) => ErrorMessageWithLoc -> io (Doc Ann)
prettyErrorWithLoc MkErrorMessageWithLoc{location, contents} = do
    code <- extractRange location
    pure $
        pretty location
            <> ": "
            <> errorText "ERROR:"
            <> "\n"
            <> contents
            <> "\n"
            <> code

prettyNameKind :: NameKind -> Doc Ann
prettyNameKind =
    emphasis . \case
        VarKind -> "variable"
        TypeConstructorKind -> "type constructor"
        DataConstructorKind -> "data constructor"

renderCompilationError :: CompilationError -> Seq ErrorMessage
renderCompilationError = \case
    LexicalError error -> undefined
    ParseError error -> fmap ErrorWithLoc $ generateParseErrorMessages error
    RenameError error -> pure $ ErrorWithLoc $ MkErrorMessageWithLoc (getLoc error) $ case error of
        NameNotFound{name, nameKind} -> align do
            emphasis "Unbound" <+> prettyNameKind nameKind <+> prettyGlobalText nameKind name
        AmbiguousGlobal{name, nameKind, candidates} ->
            align do
                emphasis "Ambiguous" <+> prettyNameKind nameKind <+> prettyGlobalText nameKind name <> "\n"
                <> "  The following definitions are in scope:\n"
                <> "    "
                <> align (intercalateDoc "\n" $ fmap (\candidate -> emphasis "-" <+> prettyGlobal nameKind candidate) (toList candidates))
        InaccessibleGlobal{name, nameKind, candidates} ->
            align do
                emphasis "Inaccessible" <+> prettyNameKind nameKind <+> prettyGlobalText nameKind name <> "\n"
                <> "  The following definitions are available but not imported:\n"
                <> "    "
                <> align (intercalateDoc "\n" $ fmap (\candidate -> emphasis "-" <+> prettyGlobal nameKind candidate) (toList candidates))
        TypeVariableNotFound{name} -> align do
            emphasis "Unbound type variable" <+> prettyGlobalText VarKind name
    TypeError error -> pure $ ErrorWithLoc $ MkErrorMessageWithLoc (getLoc error) $ case error of
        FunctionDefinedWithIncorrectNumberOfArguments
            { loc = _
            , functionName
            , expectedType
            , expectedNumberOfArguments
            , numberOfDefinedParameters
            } ->
                align $
                    emphasis "Function defined with incorrect number of parameters\n"
                        <> "  "
                        <> align
                            ( emphasis "The function "
                                <> globalIdentText functionName.name
                                <> emphasis " is declared with"
                                    <+> pluralNumber emphasis numberOfDefinedParameters "parameter"
                                <> emphasis "\n  but its type suggests that it should have "
                                <> number expectedNumberOfArguments
                                <> "\n"
                                <> "    Expected type: "
                                <> pretty expectedType
                            )
        LambdaDefinedWithIncorrectNumberOfArguments
            { loc = _
            , expectedType
            , expected
            , actual
            } -> undefined
        FunctionAppliedToIncorrectNumberOfArgs
            { loc = _
            , functionType
            , expected
            , actual
            } ->
                emphasis "Function is applied to" <+> pluralNumber emphasis actual "argument" <+> emphasis "but its type expects" <+> number expected
                    <> "\n    In an application of a function of type" <+> pretty functionType
        TuplePatternOfIncorrectNumberOfArgs
            { loc = _
            , expected
            , actual
            , expectedType
            } ->
                align $
                    emphasis "Tuple pattern binds" <+> pluralNumber emphasis actual "element" <+> emphasis "but its type expects it to bind" <+> number expected
                        <> "\n    The pattern is expected to have type" <+> pretty expectedType
        TupleLiteralOfIncorrectNumberOfArgs
            { loc = _
            , expected
            , actual
            , expectedType
            } ->
                align $
                    emphasis "Tuple literal has" <+> pluralNumber emphasis actual "element" <+> emphasis "but its type expects it to have" <+> number expected
                        <> "\n    The tuple is expected to have type" <+> pretty expectedType
        ConstructorPatternOfIncorrectNumberOfArgs{loc = _, actual, expectedTypes} ->
            align $
                emphasis "Constructor pattern binds" <+> pluralNumber emphasis actual "parameter" <+> emphasis "but its type expects it to bind" <+> number (length expectedTypes)
                    <> "\n    The parameters are supposed to have types" <+> pretty (Tuple expectedTypes)
        UnableToUnify
            { loc = _
            , expectedType
            , actualType
            } ->
                align $
                    emphasis "Type mismatch\n"
                        <> "  Unable to unify\n"
                        <> "    "
                        <> emphasis "expected"
                            <+> "type"
                            <+> pretty expectedType
                        <> "\n"
                        <> "      "
                        <> emphasis "actual"
                            <+> "type"
                            <+> pretty actualType
        TypeConstructorAppliedToIncorrectNumberOfArguments
            { loc = _
            , type_
            , kind
            , expectedNumber
            , actualNumber
            } ->
                align $
                    emphasis "Type constructor applied to an incorrect number of arguments.\n"
                        <> emphasis "  expected     " <+> pluralNumber emphasis expectedNumber "argument"
                        <> "\n"
                        <> emphasis "  but received " <+> number actualNumber
                        <> "\n"
                        <> "    In an application of type" <+> pretty type_
                        <> "\n"
                        <> "      which has kind " <+> pretty kind
        ParametricVariableInMono
            { loc = _
            , varName
            , fullType
            } ->
                align $
                    emphasis "Parametric type variable" <+> prettyLocal VarKind varName <+> emphasis "cannot be monomorphized\n"
                        <> "  Only type variables bound in monomorphizable bindings can appear in kinds of bound type variables\n"
                        <> "  or be used to instantiate monomorphizable bindings"
                        <> case fullType of
                            Nothing -> mempty
                            Just type_ ->
                                "\n    Trying to unify type" <+> pretty type_
                                    <> "\n    with a monomorphizable type parameter"
        TryingToBindTooManyTypeParameters{loc = _, type_, boundCount, actualCount = 0} ->
            align $
                emphasis "Trying to bind" <+> pluralNumber emphasis boundCount "type parameter" <+> emphasis "of the" <+> emphasis "monomorphic type"
                    <> "\n  "
                    <> pretty type_
        TryingToBindTooManyTypeParameters{loc = _, type_, boundCount, actualCount} ->
            align $
                emphasis "Trying to bind" <+> pluralNumber emphasis boundCount "type parameter" <+> emphasis "of a type that only has" <+> number actualCount
                    <> "\n  While trying to bind type parameters of type" <+> pretty type_
        TypeApplicationWithTooFewParameters{loc = _, parameterCount = 0, typeArgumentCount, instantiatedType} ->
            align $
                emphasis "Trying to apply" <+> pluralNumber emphasis typeArgumentCount "type argument" <+> emphasis "to a monomorphic type"
                    <> "\n  In a type application of type" <+> pretty instantiatedType
        TypeApplicationWithTooFewParameters{loc = _, parameterCount, typeArgumentCount, instantiatedType} ->
            align $
                emphasis "Trying to apply" <+> pluralNumber emphasis typeArgumentCount "type argument" <+> emphasis "to a type that only expects" <+> number parameterCount
                    <> "\n  In a type application of type" <+> pretty instantiatedType
        OccursCheckViolation{loc = _, expectedType, actualType, meta} -> do
            align $
                emphasis "Occurs check violation\n"
                    <> "  Unable to unify\n"
                    <> "    "
                    <> emphasis "expected"
                        <+> "type"
                        <+> pretty expectedType
                    <> "\n"
                    <> "      "
                    <> emphasis "actual"
                        <+> "type"
                        <+> pretty actualType
                    <> "\n    because the meta variable" <+> pretty meta <+> "occurs in both"
    DriverError error -> pure $ case error of
        EntryPointNotFound entryPoint ->
            PlainError $
                MkPlainErrorMessage $
                    align $
                        emphasis "Missing entry point "
                            <> prettyGlobal VarKind entryPoint
                            <> "\n"
                            <> note "  Note: To change the entry point, set the" <+> localIdentText "entry-point" <+> note "field in your "
                            <> keyword "vega.yaml"
                            <> note " file"
    Panic exception -> do
        let message = case fromException @Panic.Panic exception of
                Just (Panic.Panic callStack prettyMessage) -> prettyMessage <> "\n" <> align (Panic.prettyCallStack callStack)
                Nothing -> emphasis (show exception)

        pure $ PlainError $ MkPlainErrorMessage $ align $ errorText "PANIC (the 'impossible' happened): " <> message

pluralNumber :: (Text -> Doc Ann) -> Int -> Text -> Doc Ann
pluralNumber render 1 text = number @Int 1 <+> render text
pluralNumber render n text = number n <+> render (text <> "s")

differenceDirection :: Int -> Int -> Text
differenceDirection expected actual
    | expected < actual = "too many"
    | expected > actual = "too few"
    -- Technically this case shouldn't happen unless we have an error, but it's nice to have anyway
    | otherwise = "the same number of"

generateParseErrorMessages :: ParseErrorBundle [(Token, Loc)] Parser.AdditionalParseError -> Seq ErrorMessageWithLoc
generateParseErrorMessages (ParseErrorBundle{bundleErrors, bundlePosState = _bundlePosState}) =
    foldMap generateParseErrorMessage (viaList @_ @(Seq _) bundleErrors)

generateParseErrorMessage :: ParseError [(Token, Loc)] Parser.AdditionalParseError -> Seq ErrorMessageWithLoc
generateParseErrorMessage = \case
    TrivialError _offset (Just actual) expected -> do
        let location = errorItemLocation actual
        [ MkErrorMessageWithLoc
                { location
                , contents =
                    "    Expected: "
                        <> prettyExpected expected
                        <> "\n      Actual: "
                        <> prettyErrorItem actual
                }
            ]
    TrivialError _offset Nothing _expected -> error $ "trivial parse error without actual tokens"
    FancyError _offset errors ->
        fromList $ map generateFancyParseErrorMessage (toList errors)

generateFancyParseErrorMessage :: ErrorFancy Parser.AdditionalParseError -> ErrorMessageWithLoc
generateFancyParseErrorMessage = \case
    ErrorFail message -> error $ "fail called in parser: " <> toText message
    ErrorIndentation{} -> error $ "ErrorIndentation arising from parser"
    ErrorCustom error ->
        MkErrorMessageWithLoc
            { location = getLoc error
            , contents =
                "Parse Error:" <+> case error of
                    MismatchedFunctionName{typeSignature, definition} -> undefined
                    _ -> undefined
            }

prettyErrorItem :: ErrorItem (Token, Loc) -> Doc Ann
prettyErrorItem (Tokens tokens) = foldMap (pretty . fst) tokens
prettyErrorItem (Label chars) = plain (viaList chars)
prettyErrorItem EndOfInput = plain "end of input"

prettyExpected :: Set (ErrorItem (Token, Loc)) -> Doc Ann
prettyExpected tokens = go (viaList @_ @(Seq _) tokens)
  where
    go Empty = ""
    go (Empty :|> last) = prettyErrorItem last
    go (rest :|> last) =
        intercalateDoc ", " (fmap prettyErrorItem rest) <> ", or " <> prettyErrorItem last

errorItemLocation :: ErrorItem (Token, Loc) -> Loc
errorItemLocation (Tokens tokens) = snd (NonEmpty.head tokens) <> snd (NonEmpty.last tokens)
errorItemLocation (Label _) = error $ "'Label' in actual part of parse error"
errorItemLocation EndOfInput = undefined
