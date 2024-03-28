module Vega.Error (extractRange) where

import Vega.Prelude

import Vega.Loc
import Vega.Pretty

import Data.Text qualified as Text

extractRange :: (MonadIO io) => Loc -> io (Doc Ann)
extractRange loc = do
    lines <- Text.lines . decodeUtf8 <$> readFileBS (toString loc.fileName)

    -- - 1 because loc lines are 1-based
    let extractedLine = case drop (loc.startLine - 1) lines of
            -- Something has gone wrong, but we don't want to crash here
            -- since we still want the user to see the remaining error message
            -- TODO: figure out some way to print a warning here
            [] -> ""
            (line : _) -> line

    let (nonHighlighted, remainingLine) = Text.splitAt (loc.startColumn - 1) extractedLine

    let (highlighted, nonHighlightedRest) =
            if loc.endLine > loc.startLine
                then (remainingLine, "")
                else Text.splitAt (loc.endColumn - loc.startColumn) remainingLine

    let lineText = show loc.startLine

    let separatorWithLine = keyword lineText <> " " <> keyword "┃ "
    let separator = plain (Text.map (\_ -> ' ') lineText) <> " " <> keyword "┃ "

    pure
        $ separator <> "\n"
        <> separatorWithLine
        <> plain nonHighlighted
        <> errorDoc highlighted
        <> plain nonHighlightedRest
        <> plain "\n"
        <> separator
        <> plain (Text.map (\_ -> ' ') nonHighlighted)
        <> errorDoc (Text.map (\_ -> '▔') highlighted)
