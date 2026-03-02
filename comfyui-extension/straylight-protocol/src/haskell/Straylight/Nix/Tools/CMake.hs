{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

{- | Typed CMake actions for build phases.

Pure data structures describing CMake invocations. No runtime dependencies.

@
import qualified Straylight.Nix.Tools.CMake as CMake

preConfigure
    [ CMake.configure CMake.defaultConfig
        { CMake.sourceDir = "."
        , CMake.buildDir = "build"
        , CMake.flags =
            [ CMake.flag "BUILD_STATIC_LIBS" "ON"
            , CMake.flag "BUILD_SHARED_LIBS" "OFF"
            , CMake.option "BUILD_TESTING" False
            ]
        }
    ]

installPhase
    [ CMake.build CMake.defaultConfig { CMake.buildDir = "build" }
    , CMake.install CMake.defaultConfig { CMake.buildDir = "build" }
    ]
@

The cmake package is automatically added to nativeBuildInputs.
-}
module Straylight.Nix.Tools.CMake (
    -- * Configuration
    Config (..),
    defaultConfig,

    -- * Build phase actions
    configure,
    build,
    install,

    -- * Flag construction
    Flag (..),
    flag,
    option,
) where

import Straylight.Nix.Derivation (Action (..))
import Straylight.Nix.Types (PkgRef (..))
import Data.Text (Text)
import qualified Data.Text as T

-- | CMake configuration flag
data Flag = Flag
    { flagName :: Text
    , flagValue :: Text
    }
    deriving (Show, Eq)

-- | Create a CMake flag: -DNAME=VALUE
--
-- Example:
--   flag "BUILD_STATIC_LIBS" "ON"
flag :: Text -> Text -> Flag
flag name value = Flag name value

-- | Create a CMake option (ON/OFF): -DNAME=ON or -DNAME=OFF
--
-- Example:
--   option "BUILD_TESTING" True  -- → -DBUILD_TESTING=ON
--   option "BUILD_TESTING" False -- → -DBUILD_TESTING=OFF
option :: Text -> Bool -> Flag
option name True = Flag name "ON"
option name False = Flag name "OFF"

-- | CMake configuration
data Config = Config
    { cmakeBinary :: Text
    -- ^ Path to cmake binary (default: "cmake")
    , sourceDir :: Text
    -- ^ Source directory (default: ".")
    , buildDir :: Text
    -- ^ Build directory (default: "build")
    , flags :: [Flag]
    -- ^ CMake flags (-DNAME=VALUE)
    }
    deriving (Show, Eq)

-- | Default CMake configuration
defaultConfig :: Config
defaultConfig = Config
    { cmakeBinary = "cmake"
    , sourceDir = "."
    , buildDir = "build"
    , flags = []
    }

-- | Run cmake configure: cmake -S <sourceDir> -B <buildDir> [flags...]
--
-- Example:
--   configure defaultConfig
--     { flags = [ flag "BUILD_STATIC_LIBS" "ON" ]
--     }
configure :: Config -> Action
configure Config{..} =
    ToolRun
        (PkgName cmakeBinary)
        ( [ "-S", sourceDir
          , "-B", buildDir
          ]
            ++ map (\f -> "-D" <> flagName f <> "=" <> flagValue f) flags
        )

-- | Run cmake build: cmake --build <buildDir>
--
-- Example:
--   build defaultConfig { buildDir = "build" }
build :: Config -> Action
build Config{..} =
    ToolRun (PkgName cmakeBinary) ["--build", buildDir]

-- | Run cmake install: cmake --install <buildDir> --prefix $out
--
-- Example:
--   install defaultConfig { buildDir = "build" }
install :: Config -> Action
install Config{..} =
    ToolRun (PkgName cmakeBinary) ["--install", buildDir, "--prefix", "$out"]
