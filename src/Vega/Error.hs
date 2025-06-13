{-# LANGUAGE RecordWildCards #-}

module Vega.Error (Error (..), RenameError (..), TypeError (..), printParseErrors) where

import Relude hiding (Type)

import Effectful

import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.Show (ShowS)
import Relude.List.NonEmpty qualified as NonEmpty
import Text.Megaparsec (
    ErrorFancy (ErrorCustom, ErrorFail, ErrorIndentation),
    ParseError (FancyError, TrivialError),
    ParseErrorBundle (ParseErrorBundle),
    PosState (pstateSourcePos),
    SourcePos,
    TraversableStream,
    VisualStream,
    errorOffset,
 )
import Text.Megaparsec.Error (ErrorItem (..), ParseErrorBundle (..))
import Text.Megaparsec.Stream (TraversableStream (..))
import Vega.Lexer (Token)
import Vega.Loc (HasLoc, Loc (..), getLoc)
import Vega.Parser (AdditionalParseError (MismatchedFunctionName))
import Vega.Parser qualified as Parser
import Vega.Pretty (Ann, Doc, defaultPrettyANSIIConfig, errorDoc, intercalateDoc, keyword, plain, pretty, prettyANSII, vsep, (<+>))
import Vega.Syntax (GlobalName, Type)
import Vega.Util (viaList)

data Error

data RenameError

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
    deriving stock (Generic)
    deriving anyclass (HasLoc)

data ErrorMessage = MkErrorMessage
    { location :: Loc
    , contents :: Doc Ann
    }

printParseErrors :: (IOE :> es) => ParseErrorBundle [(Token, Loc)] Parser.AdditionalParseError -> Eff es ()
printParseErrors errors = do
    let ?config = defaultPrettyANSIIConfig
    let messages = generateParseErrorMessages errors
    for_ messages \message -> do
        doc <- withErrorLocation message
        putTextLn $ prettyANSII $ doc

generateParseErrorMessages :: ParseErrorBundle [(Token, Loc)] Parser.AdditionalParseError -> Seq ErrorMessage
generateParseErrorMessages (ParseErrorBundle{bundleErrors, bundlePosState = _bundlePosState}) =
    foldMap generateParseErrorMessage (viaList @_ @(Seq _) bundleErrors)

generateParseErrorMessage :: ParseError [(Token, Loc)] Parser.AdditionalParseError -> Seq ErrorMessage
generateParseErrorMessage = \case
    TrivialError _offset (Just actual) expected -> do
        let location = errorItemLocation actual
        [ MkErrorMessage
                { location
                , contents =
                    "    Expected: "
                        <> prettyExpected expected
                        <> "\n      Actual: "
                        <> prettyErrorItem actual
                }
            ]
    TrivialError _offset Nothing expected -> error $ "trivial parse error without actual tokens"
    FancyError _offset errors ->
        fromList $ map generateFancyParseErrorMessage (toList errors)

generateFancyParseErrorMessage :: ErrorFancy Parser.AdditionalParseError -> ErrorMessage
generateFancyParseErrorMessage = \case
    ErrorFail message -> error $ "fail called in parser: " <> toText message
    ErrorIndentation{} -> error $ "ErrorIndentation arising from parser"
    ErrorCustom error ->
        MkErrorMessage
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

withErrorLocation :: (MonadIO io) => ErrorMessage -> io (Doc Ann)
withErrorLocation MkErrorMessage{location, contents} = do
    code <- extractRange location
    pure $
        pretty location
            <> ": "
            <> errorDoc "ERROR:"
            <> "\n"
            <> contents
            <> "\n"
            <> code

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
                <> errorDoc highlighted
                <> plain nonHighlightedEnd

    let codeLines = vsep $ Vector.imap highlightLine extractedLines

    -- we only show an underline if there is a single line
    let underline = case lineCount of
            1 -> plain (Text.replicate (loc.startColumn - 1) " ") <> errorDoc (Text.replicate (loc.endColumn - loc.startColumn) "▔")
            _ | isTooLong -> errorDoc "..."
            _ -> ""

    let separator = plain (Text.replicate linePadding " ") <> " " <> keyword "┃ "

    pure $
        vsep @Vector
            [ separator
            , codeLines
            , separator <> underline
            ]