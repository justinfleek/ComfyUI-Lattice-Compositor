-- | PureScript bindings for Nix WASM host interface
--
-- Main module that re-exports everything needed to write PureScript packages
-- that compile to WASM for use with call-package.
module Straylight.Nix where

import Straylight.Nix.Value (Value, nixWasmInit)
import Straylight.Nix.Derivation (Drv, drvToNixAttrs)

-- Re-export everything needed for package definitions
import Straylight.Nix.Syntax
import Straylight.Nix.Types
import Straylight.Nix.Value
