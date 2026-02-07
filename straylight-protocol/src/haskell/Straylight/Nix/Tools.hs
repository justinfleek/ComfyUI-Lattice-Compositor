{-# LANGUAGE OverloadedStrings #-}

{- | Typed build tools for Nix derivation phases.

This module re-exports all typed tool APIs. Use qualified imports for clarity:

@
import qualified Straylight.Nix.Tools as Tools
import qualified Straylight.Nix.Tools.Jq as Jq
import qualified Straylight.Nix.Tools.PatchElf as PatchElf
import qualified Straylight.Nix.Tools.Install as Install
import qualified Straylight.Nix.Tools.Substitute as Sub

postInstall
    [ Jq.query Jq.defaults { Jq.rawOutput = True } ".name" "package.json"
    , PatchElf.setRpath "bin/myapp" [PatchElf.rpathOut "lib"]
    , Install.bin "build/myapp" "bin/myapp"
    , Sub.inPlace "config.h" [Sub.replace "@PREFIX@" "$out"]
    ]
@

Tool dependencies are automatically tracked - no manual nativeBuildInputs needed.
-}
module Straylight.Nix.Tools (
    -- * Tool modules
    module Straylight.Nix.Tools.Jq,
    module Straylight.Nix.Tools.PatchElf,
    module Straylight.Nix.Tools.Install,
    module Straylight.Nix.Tools.Substitute,
) where

import Straylight.Nix.Tools.Install
import Straylight.Nix.Tools.Jq
import Straylight.Nix.Tools.PatchElf
import Straylight.Nix.Tools.Substitute
