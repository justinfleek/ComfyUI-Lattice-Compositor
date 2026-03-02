-- | Single-file package support for call-package (PureScript)
--
-- This module re-exports everything needed to write a typed package
-- definition in a single .purs file.
--
-- Usage:
--   module Pkg where
--   import Straylight.Nix.Package
--   
--   pkg :: Drv
--   pkg = mkDerivation
--     [ pname "my-package"
--     , version "1.0.0"
--     , src $ fetchFromGitHub
--         [ owner "org"
--         , repo "my-package"
--         , rev "v1.0.0"
--         , hash "sha256-..."
--         ]
--     , cmake []
--     , description "My typed package"
--     , license "mit"
--     ]
module Straylight.Nix.Package (
  -- Re-export everything from Straylight.Nix
  module Straylight.Nix,
  -- Core types
  Drv,
  Value,
  -- Package definition
  mkDerivation,
  -- Marshaling
  drvToNixAttrs,
  -- Initialization
  nixWasmInit
) where

import Straylight.Nix
import Straylight.Nix.Derivation (Drv, drvToNixAttrs)
import Straylight.Nix.Value (Value, nixWasmInit)

