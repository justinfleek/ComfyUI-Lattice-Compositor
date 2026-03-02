-- | PureScript wrapper module for WASM export
--
-- This is the PureScript equivalent of WrapperMain.hs.
-- It imports the user's Pkg module and exports the pkg function
-- for use with builtins.wasm.
--
-- User files should follow this pattern:
--   module Pkg where
--   import Straylight.Nix.Package
--   
--   pkg :: Drv
--   pkg = mkDerivation [...]
module Main where

import Prelude

import Effect (Effect)
import Pkg (pkg)
import Straylight.Nix.Derivation (drvToNixAttrs)
import Straylight.Nix.Value (Value, nixWasmInit)

-- | Initialize the WASM plugin
-- Called by builtins.wasm as "nix_wasm_init_v1"
-- PureScript functions are exported by default when compiled to WASM
-- The compiler/backend will handle the export name mapping
initPlugin :: Effect Unit
initPlugin = nixWasmInit

-- | Export the package specification
-- Called by builtins.wasm as "pkg"
-- PureScript functions are exported by default when compiled to WASM
pkgExport :: Value -> Effect Value
pkgExport _args = drvToNixAttrs pkg
