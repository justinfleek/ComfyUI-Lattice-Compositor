{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Straylight.Script.Tools
Description : Typed CLI tool wrappers for Straylight.Script

This module collects typed wrappers for common CLI tools.
Import tools qualified to avoid name conflicts:

@
import Straylight.Script
import qualified Straylight.Script.Tools.Rg as Rg
import qualified Straylight.Script.Tools.Fd as Fd
import qualified Straylight.Script.Tools.Bat as Bat

main = script $ do
  -- Search for TODOs
  matches <- Rg.rg Rg.defaults { Rg.ignoreCase = True } "TODO" ["."]

  -- Find Haskell files
  files <- Fd.findByExt "hs" ["."]

  -- Display a file with syntax highlighting
  Bat.bat_ Bat.defaults { Bat.language = Just "haskell" } ["src/Main.hs"]
@

== Available tools

=== Search & Find
  * "Straylight.Script.Tools.Rg" - ripgrep (fast regex search)
  * "Straylight.Script.Tools.Fd" - fd (fast file finder)

=== File Display
  * "Straylight.Script.Tools.Bat" - bat (cat with syntax highlighting)
  * "Straylight.Script.Tools.Delta" - delta (git diff viewer)

=== Code Quality
  * "Straylight.Script.Tools.Deadnix" - deadnix (find dead Nix code)
  * "Straylight.Script.Tools.Statix" - statix (Nix linter)
  * "Straylight.Script.Tools.Stylua" - stylua (Lua formatter)
  * "Straylight.Script.Tools.Taplo" - taplo (TOML toolkit)

=== Benchmarking & Stats
  * "Straylight.Script.Tools.Hyperfine" - hyperfine (command benchmarking)
  * "Straylight.Script.Tools.Tokei" - tokei (code statistics)
  * "Straylight.Script.Tools.Dust" - dust (disk usage)

=== Navigation
  * "Straylight.Script.Tools.Zoxide" - zoxide (smart cd)

=== Containers & JSON
  * "Straylight.Script.Tools.Jq" - jq (JSON processor)
  * "Straylight.Script.Tools.Crane" - crane (OCI image tool)
  * "Straylight.Script.Tools.Bwrap" - bwrap (bubblewrap sandbox)

=== GNU Coreutils & Classic Unix
  * "Straylight.Script.Tools.Ls" - ls (list directory contents)
  * "Straylight.Script.Tools.Grep" - grep (pattern matching)
  * "Straylight.Script.Tools.Sed" - sed (stream editor)
  * "Straylight.Script.Tools.Find" - find (file finder)
  * "Straylight.Script.Tools.Xargs" - xargs (build command lines)
  * "Straylight.Script.Tools.Tar" - tar (archive utility)
  * "Straylight.Script.Tools.Gzip" - gzip (compression)
  * "Straylight.Script.Tools.Wget" - wget (web downloader)
  * "Straylight.Script.Tools.Rsync" - rsync (remote sync)

== Adding new tools

New tool wrappers can be generated using the clap parser:

@
.\/gen-tool-wrapper.hs \<command\> > Weyl\/Script\/Tools\/\<Name\>.hs
@

Then review and adjust the generated code as needed.
-}
module Straylight.Script.Tools (
    -- * Re-exports for convenience

    -- | Note: Import qualified to avoid name conflicts between tools.

    -- ** Clap-based tools (Rust)
    module Rg,
    module Fd,
    module Bat,
    module Deadnix,
    module Delta,
    module Dust,
    module Hyperfine,
    module Statix,
    module Stylua,
    module Taplo,
    module Tokei,
    module Zoxide,

    -- ** GNU/Classic Unix tools
    module Ls,
    module Grep,
    module Sed,
    module Find,
    module Xargs,
    module Tar,
    module Gzip,
    module Wget,
    module Rsync,

    -- ** Container & JSON tools
    module Jq,
    module Crane,
    module Bwrap,
) where

-- Clap-based tools (Rust)

import qualified Straylight.Script.Tools.Bat as Bat
import qualified Straylight.Script.Tools.Deadnix as Deadnix
import qualified Straylight.Script.Tools.Delta as Delta
import qualified Straylight.Script.Tools.Dust as Dust
import qualified Straylight.Script.Tools.Fd as Fd
import qualified Straylight.Script.Tools.Hyperfine as Hyperfine
import qualified Straylight.Script.Tools.Rg as Rg
import qualified Straylight.Script.Tools.Statix as Statix
import qualified Straylight.Script.Tools.Stylua as Stylua
import qualified Straylight.Script.Tools.Taplo as Taplo
import qualified Straylight.Script.Tools.Tokei as Tokei
import qualified Straylight.Script.Tools.Zoxide as Zoxide

--                                                                       // gnu

import qualified Straylight.Script.Tools.Find as Find
import qualified Straylight.Script.Tools.Grep as Grep
import qualified Straylight.Script.Tools.Gzip as Gzip
import qualified Straylight.Script.Tools.Ls as Ls
import qualified Straylight.Script.Tools.Rsync as Rsync
import qualified Straylight.Script.Tools.Sed as Sed
import qualified Straylight.Script.Tools.Tar as Tar
import qualified Straylight.Script.Tools.Wget as Wget
import qualified Straylight.Script.Tools.Xargs as Xargs

-- Container & JSON tools

import qualified Straylight.Script.Tools.Bwrap as Bwrap
import qualified Straylight.Script.Tools.Crane as Crane
import qualified Straylight.Script.Tools.Jq as Jq
