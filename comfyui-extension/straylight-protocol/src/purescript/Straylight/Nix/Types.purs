-- | Nix value types as seen from WASM modules (PureScript)
--
-- PureScript equivalents of the Haskell Straylight.Nix.Types module.
module Straylight.Nix.Types where

import Data.Maybe (Maybe)

-- | Store path (e.g., "/nix/store/abc123-foo-1.0")
newtype StorePath = StorePath String

derive newtype instance Eq StorePath
derive newtype instance Ord StorePath
derive newtype instance Show StorePath

-- | System identifier (e.g., "x86_64-linux")
newtype System = System String

derive newtype instance Eq System
derive newtype instance Ord System
derive newtype instance Show System

system_x86_64_linux :: System
system_x86_64_linux = System "x86_64-linux"

system_aarch64_linux :: System
system_aarch64_linux = System "aarch64-linux"

system_x86_64_darwin :: System
system_x86_64_darwin = System "x86_64-darwin"

system_aarch64_darwin :: System
system_aarch64_darwin = System "aarch64-darwin"

-- | SRI hash (e.g., "sha256-Khmrhp5qy4vvoQe4WgoogpjWrgcUB...")
newtype SriHash = SriHash String

derive newtype instance Eq SriHash
derive newtype instance Ord SriHash
derive newtype instance Show SriHash

sha256Hash :: String -> SriHash
sha256Hash b64 = SriHash ("sha256-" <> b64)

-- | Output path (relative path within an output)
data OutPath
  = OutPathDefault String  -- Path in $out
  | OutPathNamed String String  -- Path in named output ($dev/include)

derive instance Eq OutPath
derive instance Ord OutPath
derive instance Show OutPath

outPath :: String -> OutPath
outPath = OutPathDefault

outPathNamed :: String -> String -> OutPath
outPathNamed = OutPathNamed

-- | Source path (relative path within $src)
newtype SrcPath = SrcPath String

derive newtype instance Eq SrcPath
derive newtype instance Ord SrcPath
derive newtype instance Show SrcPath

srcPath :: String -> SrcPath
srcPath = SrcPath

-- | Package reference
data PkgRef
  = PkgName String  -- Regular package: "openssl" → ${pkgs.openssl}
  | BuildPkgRef String  -- Build package: "cmake" → ${pkgs.buildPackages.cmake}

derive instance Eq PkgRef
derive instance Ord PkgRef
derive instance Show PkgRef

pkgRef :: String -> PkgRef
pkgRef = PkgName

buildPkgRef :: String -> PkgRef
buildPkgRef = BuildPkgRef

-- | Rpath entry
data RpathEntry
  = RpathOut String  -- Relative to $out
  | RpathPkg String String  -- Package name, subpath
  | RpathLit String  -- Literal string (e.g., $ORIGIN)

derive instance Eq RpathEntry
derive instance Ord RpathEntry
derive instance Show RpathEntry

rpathOut :: String -> RpathEntry
rpathOut = RpathOut

rpathPkg :: String -> String -> RpathEntry
rpathPkg = RpathPkg

rpathLit :: String -> RpathEntry
rpathLit = RpathLit
