-- | Typed derivation construction for Nix WASM plugins (PureScript)
--
-- PureScript equivalents of the Haskell Straylight.Nix.Derivation module.
module Straylight.Nix.Derivation where

import Prelude

import Data.Int64 (Int64, fromInt)
import Data.Maybe (Maybe)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Straylight.Nix.Types (PkgRef(..), SriHash, StorePath, System, sha256Hash)
import Straylight.Nix.Value (Value, mkAttrs, mkBool, mkInt, mkList, mkNull, mkString)

-- | Source specification
data Src
  = SrcGitHub FetchGitHub
  | SrcUrl FetchUrl
  | SrcStore StorePath
  | SrcNull

derive instance Eq Src
derive instance Show Src

type FetchGitHub =
  { owner :: String
  , repo :: String
  , rev :: String
  , hash :: SriHash
  }

type FetchUrl =
  { url :: String
  , hash :: SriHash
  }

-- | Build system
data Builder
  = CMake { flags :: Array String, buildType :: Maybe String }
  | Autotools { configureFlags :: Array String, makeFlags :: Array String }
  | Meson { flags :: Array String }
  | CustomBuilder String
  | NoBuilder

derive instance Eq Builder
derive instance Show Builder

-- | Typed build action
data Action
  = WriteFile String String
  | Install Int String String  -- mode, src, dst
  | Mkdir String
  | Symlink String String  -- target, linkName
  | Copy String String  -- src, dst
  | Remove String
  | Unzip String  -- destDir
  | PatchElfRpath String (Array String)
  | PatchElfAddRpath String (Array String)
  | Substitute String (Array { from :: String, to :: String })
  | Wrap String (Array WrapAction)
  | Run String (Array String)
  | ToolRun PkgRef (Array String)
  | Chmod String Int

derive instance Eq Action
derive instance Show Action

-- | Wrap action
data WrapAction
  = WrapPrefix String String
  | WrapSuffix String String
  | WrapSet String String
  | WrapSetDefault String String
  | WrapUnset String
  | WrapAddFlags String

derive instance Eq WrapAction
derive instance Show WrapAction

-- | Build phases
type Phases =
  { postPatch :: Array Action
  , preConfigure :: Array Action
  , install :: Array Action
  , postInstall :: Array Action
  , postFixup :: Array Action
  }

emptyPhases :: Phases
emptyPhases =
  { postPatch: []
  , preConfigure: []
  , install: []
  , postInstall: []
  , postFixup: []
  }

-- | Dependencies
type Deps =
  { nativeBuildInputs :: Array String
  , buildInputs :: Array String
  , propagatedBuildInputs :: Array String
  , checkInputs :: Array String
  }

emptyDeps :: Deps
emptyDeps =
  { nativeBuildInputs: []
  , buildInputs: []
  , propagatedBuildInputs: []
  , checkInputs: []
  }

-- | Metadata
type Meta =
  { description :: String
  , homepage :: Maybe String
  , license :: String
  , platforms :: Array String
  , mainProgram :: Maybe String
  }

emptyMeta :: Meta
emptyMeta =
  { description: ""
  , homepage: Nothing
  , license: ""
  , platforms: []
  , mainProgram: Nothing
  }

-- | Environment variable
type EnvVar =
  { name :: String
  , value :: String
  }

-- | Derivation specification
type Drv =
  { name :: String
  , version :: String
  , src :: Src
  , builder :: Builder
  , deps :: Deps
  , meta :: Meta
  , env :: Array EnvVar
  , patches :: Array StorePath
  , phases :: Phases
  , strictDeps :: Boolean
  , doCheck :: Boolean
  , dontUnpack :: Boolean
  , system :: Maybe System
  , outputs :: Array String
  }

defaultDrv :: Drv
defaultDrv =
  { name: ""
  , version: ""
  , src: SrcNull
  , builder: NoBuilder
  , deps: emptyDeps
  , meta: emptyMeta
  , env: []
  , patches: []
  , phases: emptyPhases
  , strictDeps: true
  , doCheck: false
  , dontUnpack: false
  , system: Nothing
  , outputs: [ "out" ]
  }

-- | Convert Drv to Nix attrset
drvToNixAttrs :: Drv -> Effect Value
drvToNixAttrs drv = do
  pnameVal <- mkString drv.name
  versionVal <- mkString drv.version
  srcVal <- srcToNix drv.src
  builderVal <- builderToNix drv.builder
  depsVal <- depsToNix drv.deps
  metaVal <- metaToNix drv.meta
  envVal <- envToNix drv.env
  patchesVal <- traverse (\p -> mkString (case p of StorePath path -> path)) drv.patches >>= mkList
  phasesVal <- phasesToNix drv.phases
  strictDepsVal <- mkBool drv.strictDeps
  doCheckVal <- mkBool drv.doCheck
  dontUnpackVal <- mkBool drv.dontUnpack
  systemVal <- case drv.system of
    Nothing -> mkNull
    Just (System sysStr) -> mkString sysStr
  outputsVal <- traverse mkString drv.outputs >>= mkList
  
  mkAttrs
    [ { key: "pname", value: pnameVal }
    , { key: "version", value: versionVal }
    , { key: "src", value: srcVal }
    , { key: "builder", value: builderVal }
    , { key: "deps", value: depsVal }
    , { key: "meta", value: metaVal }
    , { key: "env", value: envVal }
    , { key: "patches", value: patchesVal }
    , { key: "phases", value: phasesVal }
    , { key: "strictDeps", value: strictDepsVal }
    , { key: "doCheck", value: doCheckVal }
    , { key: "dontUnpack", value: dontUnpackVal }
    , { key: "system", value: systemVal }
    , { key: "outputs", value: outputsVal }
    ]

srcToNix :: Src -> Effect Value
srcToNix (SrcGitHub fgh) = do
  typeVal <- mkString "github"
  ownerVal <- mkString fgh.owner
  repoVal <- mkString fgh.repo
  revVal <- mkString fgh.rev
  hashVal <- mkString (case fgh.hash of SriHash h -> h)
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "owner", value: ownerVal }
    , { key: "repo", value: repoVal }
    , { key: "rev", value: revVal }
    , { key: "hash", value: hashVal }
    ]
srcToNix (SrcUrl fu) = do
  typeVal <- mkString "url"
  urlVal <- mkString fu.url
  hashVal <- mkString (case fu.hash of SriHash h -> h)
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "url", value: urlVal }
    , { key: "hash", value: hashVal }
    ]
srcToNix (SrcStore sp) = do
  typeVal <- mkString "store"
  pathVal <- mkString (case sp of StorePath p -> p)
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "path", value: pathVal }
    ]
srcToNix SrcNull = mkNull

builderToNix :: Builder -> Effect Value
builderToNix (CMake { flags, buildType }) = do
  typeVal <- mkString "cmake"
  flagsVal <- traverse mkString flags >>= mkList
  buildTypeVal <- case buildType of
    Nothing -> mkNull
    Just bt -> mkString bt
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "flags", value: flagsVal }
    , { key: "buildType", value: buildTypeVal }
    ]
builderToNix (Autotools { configureFlags, makeFlags }) = do
  typeVal <- mkString "autotools"
  confFlagsVal <- traverse mkString configureFlags >>= mkList
  makeFlagsVal <- traverse mkString makeFlags >>= mkList
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "configureFlags", value: confFlagsVal }
    , { key: "makeFlags", value: makeFlagsVal }
    ]
builderToNix (Meson { flags }) = do
  typeVal <- mkString "meson"
  flagsVal <- traverse mkString flags >>= mkList
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "flags", value: flagsVal }
    ]
builderToNix (CustomBuilder name) = do
  typeVal <- mkString "custom"
  nameVal <- mkString name
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "name", value: nameVal }
    ]
builderToNix NoBuilder = do
  typeVal <- mkString "none"
  mkAttrs [ { key: "type", value: typeVal } ]

depsToNix :: Deps -> Effect Value
depsToNix deps = do
  nativeVal <- traverse mkString deps.nativeBuildInputs >>= mkList
  buildVal <- traverse mkString deps.buildInputs >>= mkList
  propagatedVal <- traverse mkString deps.propagatedBuildInputs >>= mkList
  checkVal <- traverse mkString deps.checkInputs >>= mkList
  mkAttrs
    [ { key: "nativeBuildInputs", value: nativeVal }
    , { key: "buildInputs", value: buildVal }
    , { key: "propagatedBuildInputs", value: propagatedVal }
    , { key: "checkInputs", value: checkVal }
    ]

metaToNix :: Meta -> Effect Value
metaToNix meta = do
  descVal <- mkString meta.description
  homepageVal <- case meta.homepage of
    Nothing -> mkNull
    Just h -> mkString h
  licenseVal <- mkString meta.license
  platformsVal <- traverse mkString meta.platforms >>= mkList
  mainProgramVal <- case meta.mainProgram of
    Nothing -> mkNull
    Just mp -> mkString mp
  mkAttrs
    [ { key: "description", value: descVal }
    , { key: "homepage", value: homepageVal }
    , { key: "license", value: licenseVal }
    , { key: "platforms", value: platformsVal }
    , { key: "mainProgram", value: mainProgramVal }
    ]

envToNix :: Array EnvVar -> Effect Value
envToNix vars = do
  -- Convert array of {name, value} to attrset
  attrs <- traverse (\v -> mkString v.value >>= \val -> pure { key: v.name, value: val }) vars
  mkAttrs attrs

phasesToNix :: Phases -> Effect Value
phasesToNix phases = do
  postPatchVal <- actionsToNix phases.postPatch
  preConfigureVal <- actionsToNix phases.preConfigure
  installVal <- actionsToNix phases.install
  postInstallVal <- actionsToNix phases.postInstall
  postFixupVal <- actionsToNix phases.postFixup
  mkAttrs
    [ { key: "postPatch", value: postPatchVal }
    , { key: "preConfigure", value: preConfigureVal }
    , { key: "installPhase", value: installVal }
    , { key: "postInstall", value: postInstallVal }
    , { key: "postFixup", value: postFixupVal }
    ]

actionsToNix :: Array Action -> Effect Value
actionsToNix actions = do
  vals <- traverse actionToNix actions
  mkList vals

actionToNix :: Action -> Effect Value
actionToNix (WriteFile path content) = do
  actionVal <- mkString "writeFile"
  pathVal <- mkString path
  contentVal <- mkString content
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "path", value: pathVal }
    , { key: "content", value: contentVal }
    ]
actionToNix (Install mode src dst) = do
  actionVal <- mkString "install"
  modeVal <- mkInt (fromInt mode)
  srcVal <- mkString src
  dstVal <- mkString dst
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "mode", value: modeVal }
    , { key: "src", value: srcVal }
    , { key: "dst", value: dstVal }
    ]
actionToNix (Mkdir path) = do
  actionVal <- mkString "mkdir"
  pathVal <- mkString path
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "path", value: pathVal }
    ]
actionToNix (Symlink target linkName) = do
  actionVal <- mkString "symlink"
  targetVal <- mkString target
  linkVal <- mkString linkName
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "target", value: targetVal }
    , { key: "link", value: linkVal }
    ]
actionToNix (Copy src dst) = do
  actionVal <- mkString "copy"
  srcVal <- mkString src
  dstVal <- mkString dst
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "src", value: srcVal }
    , { key: "dst", value: dstVal }
    ]
actionToNix (Remove path) = do
  actionVal <- mkString "remove"
  pathVal <- mkString path
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "path", value: pathVal }
    ]
actionToNix (Unzip destDir) = do
  actionVal <- mkString "unzip"
  destVal <- mkString destDir
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "dest", value: destVal }
    ]
actionToNix (PatchElfRpath path rpaths) = do
  actionVal <- mkString "patchelfRpath"
  pathVal <- mkString path
  rpathsVal <- traverse mkString rpaths >>= mkList
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "path", value: pathVal }
    , { key: "rpaths", value: rpathsVal }
    ]
actionToNix (PatchElfAddRpath path rpaths) = do
  actionVal <- mkString "patchelfAddRpath"
  pathVal <- mkString path
  rpathsVal <- traverse mkString rpaths >>= mkList
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "path", value: pathVal }
    , { key: "rpaths", value: rpathsVal }
    ]
actionToNix (Substitute file replacements) = do
  actionVal <- mkString "substitute"
  fileVal <- mkString file
  repsVal <- traverse (\r -> do
    fromVal <- mkString r.from
    toVal <- mkString r.to
    mkAttrs [ { key: "from", value: fromVal }, { key: "to", value: toVal } ]
  ) replacements >>= mkList
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "file", value: fileVal }
    , { key: "replacements", value: repsVal }
    ]
actionToNix (Wrap program wrapActions) = do
  actionVal <- mkString "wrap"
  programVal <- mkString program
  actionsVal <- traverse wrapActionToNix wrapActions >>= mkList
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "program", value: programVal }
    , { key: "wrapActions", value: actionsVal }
    ]
actionToNix (Run cmd args) = do
  actionVal <- mkString "run"
  cmdVal <- mkString cmd
  argsVal <- traverse mkString args >>= mkList
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "cmd", value: cmdVal }
    , { key: "args", value: argsVal }
    ]
actionToNix (ToolRun pkgRef args) = do
  actionVal <- mkString "toolRun"
  (pkgName /\ isBuildPkg) <- case pkgRef of
    PkgName name -> pure (name /\ false)
    BuildPkgRef name -> pure (name /\ true)
  pkgVal <- mkString pkgName
  buildPkgVal <- mkBool isBuildPkg
  argsVal <- traverse mkString args >>= mkList
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "pkg", value: pkgVal }
    , { key: "buildPackage", value: buildPkgVal }
    , { key: "args", value: argsVal }
    ]
actionToNix (Chmod path mode) = do
  actionVal <- mkString "chmod"
  pathVal <- mkString path
  modeVal <- mkInt (fromInt mode)
  mkAttrs
    [ { key: "action", value: actionVal }
    , { key: "path", value: pathVal }
    , { key: "mode", value: modeVal }
    ]

wrapActionToNix :: WrapAction -> Effect Value
wrapActionToNix (WrapPrefix var val) = do
  typeVal <- mkString "prefix"
  varVal <- mkString var
  valVal <- mkString val
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "var", value: varVal }
    , { key: "value", value: valVal }
    ]
wrapActionToNix (WrapSuffix var val) = do
  typeVal <- mkString "suffix"
  varVal <- mkString var
  valVal <- mkString val
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "var", value: varVal }
    , { key: "value", value: valVal }
    ]
wrapActionToNix (WrapSet var val) = do
  typeVal <- mkString "set"
  varVal <- mkString var
  valVal <- mkString val
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "var", value: varVal }
    , { key: "value", value: valVal }
    ]
wrapActionToNix (WrapSetDefault var val) = do
  typeVal <- mkString "setDefault"
  varVal <- mkString var
  valVal <- mkString val
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "var", value: varVal }
    , { key: "value", value: valVal }
    ]
wrapActionToNix (WrapUnset var) = do
  typeVal <- mkString "unset"
  varVal <- mkString var
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "var", value: varVal }
    ]
wrapActionToNix (WrapAddFlags flags) = do
  typeVal <- mkString "addFlags"
  flagsVal <- mkString flags
  mkAttrs
    [ { key: "type", value: typeVal }
    , { key: "flags", value: flagsVal }
    ]
