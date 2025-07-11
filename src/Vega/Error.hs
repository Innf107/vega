{-# LANGUAGE RecordWildCards #-}

module Vega.Error (
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

import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Vega.Loc (HasLoc, Loc (..), getLoc)
import Vega.Pretty (Ann, Doc, Pretty (pretty), align, emphasis, errorText, globalIdentText, keyword, localIdentText, note, number, plain, vsep, (<+>))
import Vega.Syntax (GlobalName (..), Kind, NameKind (..), Type, prettyGlobal, prettyGlobalText)

data CompilationError
    = RenameError RenameError
    | TypeError TypeError
    | DriverError DriverError
    deriving stock (Generic)

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
    | KindMismatch
        { loc :: Loc
        , expectedKind :: Kind
        , actualKind :: Kind
        }
    | UnableToUnify
        { loc :: Loc
        , expectedType :: Type
        , actualType :: Type
        }
    | ApplicationOfNonFunctionKind
        { loc :: Loc
        , kind :: Kind
        }
    | TypeConstructorAppliedToIncorrectNumberOfArguments
        { loc :: Loc
        , type_ :: Type
        , kind :: Kind
        , expectedNumber :: Int
        , actualNumber :: Int
        }
    deriving stock (Generic)
    deriving anyclass (HasLoc)

newtype TypeErrorSet = MkTypeErrorSet (Seq TypeError)

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
prettyNameKind = emphasis . \case
    VarKind -> "variable"
    TypeConstructorKind -> "type constructor"
    DataConstructorKind -> "data constructor"

renderCompilationError :: CompilationError -> ErrorMessage
renderCompilationError = \case
    RenameError error -> ErrorWithLoc $ MkErrorMessageWithLoc (getLoc error) $ case error of
        NameNotFound{name, nameKind} -> align do
            prettyNameKind nameKind <+> prettyGlobalText nameKind name <+> emphasis"not found"
        AmbiguousGlobal{} -> undefined
        InaccessibleGlobal{name, nameKind, candidates} -> align do
            emphasis "Inaccessible" <+> prettyNameKind nameKind <+> prettyGlobalText nameKind name <> "\n"
            <> "  The following definitions are available but not imported:\n"
            <> "    " <> align (foldMap (\candidate -> emphasis "-" <+> prettyGlobal nameKind candidate <> "\n") candidates)
        TypeVariableNotFound{} -> undefined
    TypeError error -> ErrorWithLoc $ MkErrorMessageWithLoc (getLoc error) $ case error of
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
                            ( "The function "
                                <> globalIdentText functionName.name
                                <> " is declared with"
                                <> "  "
                                <> number numberOfDefinedParameters
                                <> "parameters\n"
                                <> "  but its type suggests that it should have "
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
            } -> undefined
        -- TODO: special case this a little and provide some nicer error messages
        KindMismatch
            { loc = _
            , expectedKind
            , actualKind
            } ->
                align $
                    emphasis "Kind mismatch\n"
                        <> "  Unable to unify\n"
                        <> "    "
                        <> emphasis "expected" <+> "kind    "
                        <> pretty expectedKind
                        <> "\n"
                        <> "    with" <+> emphasis "actual" <+> "kind "
                        <> pretty actualKind
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
        ApplicationOfNonFunctionKind
            { loc = _
            , kind
            } ->
                align $
                    emphasis "Trying to apply a type of non-function kind" <+> pretty kind
        TypeConstructorAppliedToIncorrectNumberOfArguments
            { loc = _
            , type_
            , kind
            , expectedNumber
            , actualNumber
            } ->
                align $
                    emphasis "Type constructor applied to an incorrect number of arguments.\n"
                        <> emphasis "  expected     " <+> number expectedNumber <+> "arguments\n"
                        <> emphasis "  but received " <+> number actualNumber
                        <> "\n"
                        <> "    In an application of type" <+> pretty type_
                        <> "\n"
                        <> "      which has kind " <+> pretty kind
    DriverError error -> case error of
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