module Vega.Driver (
    parseRenameTypeCheck,
    compile,
    DriverConfig (..),
) where

import Vega.Eval (CoreDeclaration)
import Vega.Loc (HasLoc)
import Vega.Prelude
import Vega.Pretty
import Vega.Util (Untagged (..), viaList)

import Control.Monad.Writer (MonadWriter (tell), WriterT (..))
import Data.These (These (..))
import Vega.Compile.CoreToMIR qualified as CoreToMIR
import Vega.Compile.LIRTox86_64 qualified as LIRTox86_64
import Vega.Compile.MIRToLIR qualified as MirToLIR
import Vega.CoreLint qualified as CoreLint
import Vega.Infer qualified as Infer
import Vega.Lexer qualified as Lexer
import Vega.Parser qualified as Parser
import Vega.Rename qualified as Rename
import Vega.Trace (TraceAction)

data VegaError
    = LexicalError Lexer.LexError
    | ParseError Parser.ParseError
    | RenameError Rename.RenameError
    | TypeError Infer.TypeError
    deriving (Generic)
    deriving (Pretty, HasLoc) via (Untagged VegaError)

data VegaWarning
    = CoreLintError CoreLint.LintError
    deriving (Generic)
    deriving (Pretty) via (Untagged VegaWarning)

data DriverConfig = MkDriverConfig
    { enableCoreLint :: Bool
    }
    deriving (Show)

parseRenameTypeCheck
    :: (?traceAction :: TraceAction IO, ?driverConfig :: DriverConfig)
    => FilePath
    -> Text
    -> IO (Either (Seq VegaError) (Vector CoreDeclaration), Seq VegaWarning)
parseRenameTypeCheck filename code = runWriterT $ runExceptT do
    tokens <- case Lexer.run filename code of
        Left error -> throwError [LexicalError error]
        Right tokens -> pure tokens
    parsed <- case Parser.runParseM $ Parser.parse tokens of
        Left error -> throwError [ParseError error]
        Right parsed -> pure parsed
    renamed <-
        liftIO (Rename.rename parsed) >>= \case
            Left errors -> throwError (fmap RenameError errors)
            Right renamed -> pure renamed

    liftIO (Infer.typecheck renamed) >>= \case
        This errors -> throwError (fmap TypeError (viaList errors))
        These errors _core -> throwError (fmap TypeError (viaList errors))
        That core -> do
            when (?driverConfig.enableCoreLint) do
                errors <- liftIO $ CoreLint.lint core
                tell (fmap CoreLintError errors)
            pure core

compile :: Vector CoreDeclaration -> IO Text
compile core = do
    mir <- CoreToMIR.coreToMIR core
    lir <- MirToLIR.mirToLIR mir
    LIRTox86_64.compile lir
    undefined