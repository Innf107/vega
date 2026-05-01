{-# LANGUAGE TemplateHaskell #-}

module Vega.Runtime (runtimeArchive) where

import Data.ByteString (ByteString)
import Data.FileEmbed (embedFile)

-- This is defined in its own module because loading it in HLS makes its memory usage explode for some reason
runtimeArchive :: ByteString
runtimeArchive = $(embedFile ".build/libvega_runtime.a")
