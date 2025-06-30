module Vega.Error.ParseError (generateParseErrorMessages) where

import Relude

import Data.Sequence (Seq (..))
import Relude.List.NonEmpty qualified as NonEmpty
import Text.Megaparsec (
    ErrorFancy (ErrorCustom, ErrorFail, ErrorIndentation),
    ParseError (FancyError, TrivialError),
 )
import Text.Megaparsec.Error (ErrorItem (..), ParseErrorBundle (..))
import Vega.Lexer (Token)
import Vega.Loc (Loc (..), getLoc)
import Vega.Parser (AdditionalParseError (MismatchedFunctionName))
import Vega.Parser qualified as Parser
import Vega.Pretty (Ann, Doc, intercalateDoc, plain, pretty, (<+>))
import Vega.Util (viaList)

import Vega.Error (ErrorMessageWithLoc (..))

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
    TrivialError _offset Nothing expected -> error $ "trivial parse error without actual tokens"
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
