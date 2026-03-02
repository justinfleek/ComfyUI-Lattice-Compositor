module Straylight.Nix.Syntax where

import Prelude

import Data.Array (filter)
import Data.Maybe (Maybe(..))
import Data.String (stripPrefix)
import Data.String.Pattern (Pattern(..))
import Straylight.Nix.Derivation (Action(..), Builder(..), Deps, Drv, Meta, Phases, Src(..), WrapAction(..), defaultDrv)
import Straylight.Nix.Types (PkgRef(..), SriHash, StorePath, sha256Hash)

-- | Attribute combinator type
type Attr = Drv -> Drv

-- | Build a derivation from a list of attributes
mkDerivation :: Array Attr -> Drv
mkDerivation attrs = foldr apply defaultDrv attrs
  where
  apply :: Attr -> Drv -> Drv
  apply f drv = f drv

-- | Basic attributes
pname :: String -> Attr
pname n drv = drv { name = n }

version :: String -> Attr
version v drv = drv { version = v }

src :: Src -> Attr
src s drv = drv { src = s }

strictDeps :: Boolean -> Attr
strictDeps b drv = drv { strictDeps = b }

doCheck :: Boolean -> Attr
doCheck b drv = drv { doCheck = b }

dontUnpack :: Boolean -> Attr
dontUnpack b drv = drv { dontUnpack = b }

-- | Source fetching
type SrcAttr
  = { tag :: String, value :: String }

owner :: String -> SrcAttr
owner o = { tag: "owner", value: o }

repo :: String -> SrcAttr
repo r = { tag: "repo", value: r }

rev :: String -> SrcAttr
rev r = { tag: "rev", value: r }

hash :: String -> SrcAttr
hash h = { tag: "hash", value: h }

url :: String -> SrcAttr
url u = { tag: "url", value: u }

fetchFromGitHub :: Array SrcAttr -> Src
fetchFromGitHub attrs =
  let
    find tag def = case filter (\a -> a.tag == tag) attrs of
      [ a ] -> a.value
      _ -> def
    stripSha t = case stripPrefix (Pattern "sha256-") t of
      Just rest -> rest
      Nothing -> t
  in
    SrcGitHub
      { owner: find "owner" ""
      , repo: find "repo" ""
      , rev: find "rev" ""
      , hash: sha256Hash (stripSha (find "hash" ""))
      }

fetchurl :: Array SrcAttr -> Src
fetchurl attrs =
  let
    find tag def = case filter (\a -> a.tag == tag) attrs of
      [ a ] -> a.value
      _ -> def
    stripSha t = case stripPrefix (Pattern "sha256-") t of
      Just rest -> rest
      Nothing -> t
  in
    SrcUrl
      { url: find "url" ""
      , hash: sha256Hash (stripSha (find "hash" ""))
      }

-- | Dependencies
nativeBuildInputs :: Array String -> Attr
nativeBuildInputs xs drv = drv { deps = (drv.deps) { nativeBuildInputs = xs } }

buildInputs :: Array String -> Attr
buildInputs xs drv = drv { deps = (drv.deps) { buildInputs = xs } }

propagatedBuildInputs :: Array String -> Attr
propagatedBuildInputs xs drv = drv { deps = (drv.deps) { propagatedBuildInputs = xs } }

checkInputs :: Array String -> Attr
checkInputs xs drv = drv { deps = (drv.deps) { checkInputs = xs } }

patches :: Array StorePath -> Attr
patches ps drv = drv { patches = ps }

-- | Build systems
cmake :: Array String -> Attr
cmake flags drv = drv { builder = CMake { flags, buildType: Nothing } }

cmakeFlags :: Array String -> Attr
cmakeFlags = cmake

configureFlags :: Array String -> Attr
configureFlags flags drv = drv { builder = Autotools { configureFlags: flags, makeFlags: [] } }

makeFlags :: Array String -> Attr
makeFlags flags drv = case drv.builder of
  Autotools cfg -> drv { builder = Autotools (cfg { makeFlags = flags }) }
  _ -> drv { builder = Autotools { configureFlags: [], makeFlags: flags } }

mesonFlags :: Array String -> Attr
mesonFlags flags drv = drv { builder = Meson { flags } }

-- | Phases
postPatch :: Array Action -> Attr
postPatch as drv = drv { phases = (drv.phases) { postPatch = as } }

preConfigure :: Array Action -> Attr
preConfigure as drv = drv { phases = (drv.phases) { preConfigure = as } }

installPhase :: Array Action -> Attr
installPhase as drv = drv { phases = (drv.phases) { install = as } }

postInstall :: Array Action -> Attr
postInstall as drv = drv { phases = (drv.phases) { postInstall = as } }

postFixup :: Array Action -> Attr
postFixup as drv = drv { phases = (drv.phases) { postFixup = as } }

-- | Phase actions
writeFile :: String -> String -> Action
writeFile = WriteFile

substitute :: String -> Array { from :: String, to :: String } -> Action
substitute = Substitute

mkdir :: String -> Action
mkdir = Mkdir

copy :: String -> String -> Action
copy = Copy

symlink :: String -> String -> Action
symlink = Symlink

remove :: String -> Action
remove = Remove

unzip :: String -> Action
unzip = Unzip

patchElfRpath :: String -> Array String -> Action
patchElfRpath = PatchElfRpath

patchElfAddRpath :: String -> Array String -> Action
patchElfAddRpath = PatchElfAddRpath

wrap :: String -> Array WrapAction -> Action
wrap = Wrap

run :: String -> Array String -> Action
run = Run

tool :: String -> Array String -> Action
tool pkg args = ToolRun (PkgName pkg) args

buildTool :: String -> Array String -> Action
buildTool pkg args = ToolRun (BuildPkgRef pkg) args

chmod :: String -> Int -> Action
chmod = Chmod

-- Wrap actions (import from Derivation)
import Straylight.Nix.Derivation (WrapAction(..))

wrapPrefix :: String -> String -> WrapAction
wrapPrefix = WrapPrefix

wrapSuffix :: String -> String -> WrapAction
wrapSuffix = WrapSuffix

wrapSet :: String -> String -> WrapAction
wrapSet = WrapSet

wrapSetDefault :: String -> String -> WrapAction
wrapSetDefault = WrapSetDefault

wrapUnset :: String -> WrapAction
wrapUnset = WrapUnset

wrapAddFlags :: String -> WrapAction
wrapAddFlags = WrapAddFlags

-- | Outputs
outputs :: Array String -> Attr
outputs outNames drv = drv { outputs = outNames }

-- | Metadata
description :: String -> Attr
description t drv = drv { meta = (drv.meta) { description = t } }

homepage :: String -> Attr
homepage t drv = drv { meta = (drv.meta) { homepage = Just t } }

license :: String -> Attr
license t drv = drv { meta = (drv.meta) { license = t } }

mainProgram :: String -> Attr
mainProgram t drv = drv { meta = (drv.meta) { mainProgram = Just t } }
