module Vega.Driver (parseRenameTypeCheck) where

import Vega.Prelude
import Vega.Syntax
import Vega.Pretty
import Vega.Util (Untagged(..))
import Vega.Loc (HasLoc)

import Vega.Lexer qualified as Lexer
import Vega.Parser qualified as Parser
import Vega.Rename qualified as Rename
import Vega.Infer qualified as Infer

data VegaError
    = LexicalError Lexer.LexError
    | ParseError Parser.ParseError
    | RenameError Rename.RenameError
    | TypeError Infer.TypeError
    deriving (Generic) 
    deriving (Pretty) via (Untagged VegaError)
    deriving (HasLoc) via (Untagged VegaError)

parseRenameTypeCheck :: FilePath -> Text -> IO (Either (Seq VegaError) (Vector CoreDeclaration))
parseRenameTypeCheck filename code = runExceptT do
    tokens <- case Lexer.run filename code of
        Left error -> throwError [LexicalError error]
        Right tokens -> pure tokens
    parsed <- case Parser.runParseM $ Parser.parse tokens of
        Left error -> throwError [ParseError error]
        Right parsed -> pure parsed
    renamed <- liftIO (Rename.rename parsed) >>= \case
        Left errors -> throwError (fmap RenameError errors)
        Right renamed -> pure renamed
    
    liftIO (Infer.typecheck renamed) >>= \case
        Left error -> throwError [TypeError error]
        Right core -> pure core

