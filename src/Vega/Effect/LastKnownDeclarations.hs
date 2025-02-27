module Vega.Effect.LastKnownDeclarations where

import Relude

import Vega.Syntax hiding (Effect)

import Effectful
import Effectful.Dispatch.Dynamic (send)

-- TODO: add modification time for files
data LastKnownDeclarations :: Effect where
    GetDeclarations :: FilePath -> LastKnownDeclarations m (Maybe (HashMap GlobalName (Declaration Parsed)))
    AddOrReplaceDeclaration :: FilePath -> Declaration Parsed -> LastKnownDeclarations m ()
    RemoveDeclaration :: FilePath -> GlobalName -> LastKnownDeclarations m ()
    
type instance DispatchOf LastKnownDeclarations = Dynamic

getDeclarations :: LastKnownDeclarations :> es => FilePath -> Eff es (Maybe (HashMap GlobalName (Declaration Parsed)))
getDeclarations path = send (GetDeclarations path)

-- TODO
