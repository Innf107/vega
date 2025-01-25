module Vega.Driver (rebuildTrackedModules, rebuildOnlyFiles) where

import Effectful
import Effectful.FileSystem (FileSystem, doesFileExist)
import Relude hiding (trace, Driver)
import Vega.Diff qualified as Diff
import Vega.Effect.LastKnownDeclarations (LastKnownDeclarations)
import Vega.Effect.LastKnownDeclarations qualified as LastKnownDeclarations
import Vega.Parser qualified as Parser
import Vega.Syntax
import Vega.Trace

{- | Try to rebuild all files currently known to the build system.
This still only rebuilds files that actually changed since the last access.
-}
rebuildTrackedModules :: Eff es ()
rebuildTrackedModules = undefined

{- | Only try to rebuild some files.
This is useful for things like watch mode or LSP servers that already know
which files have changed.
-}
rebuildOnlyFiles :: (IOE :> es, FileSystem :> es, LastKnownDeclarations :> es) => Seq FilePath -> Eff es ()
rebuildOnlyFiles files = do
    for_ files \filePath -> do
        doesFileExist filePath >>= \case
            False -> do
                trace Driver $ "File removed: " <> toText filePath
                undefined
            True -> do
                contents <- decodeUtf8 <$> readFileBS filePath
                let !parsedModule = Parser.parse filePath contents
                LastKnownDeclarations.getDeclarations filePath >>= \case
                    Nothing -> do
                        trace Driver $ "File added: " <> toText filePath
                        undefined
                    Just previous -> do
                        trace Driver $ "File modified: " <> toText filePath
                        diff <- Diff.diffDeclarations parsedModule.declarations previous
                        undefined
