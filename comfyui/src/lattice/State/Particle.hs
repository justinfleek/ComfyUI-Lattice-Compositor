-- |
-- Module      : Lattice.State.Particle
-- Description : Pure state management functions for particle store
-- 
-- Migrated from ui/src/stores/particleStore.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Particle
  ( -- Export functions
    exportTrajectoriesToJSON
  -- Types
  , BakedParticleTrajectory(..)
  , ParticleBakeResult(..)
  , ParticleKeyframe(..)
  , ExportFormat(..)
  , TrajectoryExport(..)
  , TrajectoryKeyframeExport(..)
  , ParticleTrajectoryJSON(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , withText
  , object
  , (.=)
  , (.:)
  , (.:?)
  , encode
  )
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString.Lazy as BSL
import GHC.Generics (Generic)

-- ============================================================================
-- PARTICLE KEYFRAME
-- ============================================================================

-- | Keyframe data for a particle trajectory
data ParticleKeyframe = ParticleKeyframe
  { particleKeyframeFrame :: Int
  , particleKeyframeX :: Double
  , particleKeyframeY :: Double
  , particleKeyframeZ :: Double
  , particleKeyframeSize :: Double
  , particleKeyframeOpacity :: Double
  , particleKeyframeRotation :: Double
  , particleKeyframeR :: Double
  , particleKeyframeG :: Double
  , particleKeyframeB :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticleKeyframe where
  toJSON (ParticleKeyframe frame x y z size opacity rotation r g b) =
    object
      [ "frame" .= frame
      , "x" .= x
      , "y" .= y
      , "z" .= z
      , "size" .= size
      , "opacity" .= opacity
      , "rotation" .= rotation
      , "r" .= r
      , "g" .= g
      , "b" .= b
      ]

instance FromJSON ParticleKeyframe where
  parseJSON = withObject "ParticleKeyframe" $ \o -> do
    frame <- o .: "frame"
    x <- o .: "x"
    y <- o .: "y"
    z <- o .: "z"
    size <- o .: "size"
    opacity <- o .: "opacity"
    rotation <- o .: "rotation"
    r <- o .: "r"
    g <- o .: "g"
    b <- o .: "b"
    return (ParticleKeyframe frame x y z size opacity rotation r g b)

-- ============================================================================
-- BAKED PARTICLE TRAJECTORY
-- ============================================================================

-- | Baked particle trajectory for export
data BakedParticleTrajectory = BakedParticleTrajectory
  { bakedTrajectoryParticleId :: Int
  , bakedTrajectoryEmitterId :: Text
  , bakedTrajectoryBirthFrame :: Int
  , bakedTrajectoryDeathFrame :: Int
  , bakedTrajectoryKeyframes :: [ParticleKeyframe]
  }
  deriving (Eq, Show, Generic)

instance ToJSON BakedParticleTrajectory where
  toJSON (BakedParticleTrajectory particleId emitterId birthFrame deathFrame keyframes) =
    object
      [ "particleId" .= particleId
      , "emitterId" .= emitterId
      , "birthFrame" .= birthFrame
      , "deathFrame" .= deathFrame
      , "keyframes" .= keyframes
      ]

instance FromJSON BakedParticleTrajectory where
  parseJSON = withObject "BakedParticleTrajectory" $ \o -> do
    particleId <- o .: "particleId"
    emitterId <- o .: "emitterId"
    birthFrame <- o .: "birthFrame"
    deathFrame <- o .: "deathFrame"
    keyframes <- o .: "keyframes"
    return (BakedParticleTrajectory particleId emitterId birthFrame deathFrame keyframes)

-- ============================================================================
-- EXPORT FORMAT
-- ============================================================================

-- | Export format type
data ExportFormat
  = ExportFormatTrajectories
  | ExportFormatShapeLayers
  deriving (Eq, Show, Generic)

instance ToJSON ExportFormat where
  toJSON ExportFormatTrajectories = "trajectories"
  toJSON ExportFormatShapeLayers = "shapeLayers"

instance FromJSON ExportFormat where
  parseJSON = withText "ExportFormat" $ \s ->
    case s of
      "trajectories" -> return ExportFormatTrajectories
      "shapeLayers" -> return ExportFormatShapeLayers
      _ -> fail "Invalid ExportFormat"

-- ============================================================================
-- PARTICLE BAKE RESULT
-- ============================================================================

-- | Result of particle baking
data ParticleBakeResult = ParticleBakeResult
  { bakeResultLayerId :: Text
  , bakeResultTrajectories :: [BakedParticleTrajectory]
  , bakeResultTotalFrames :: Int
  , bakeResultTotalParticles :: Int
  , bakeResultExportFormat :: ExportFormat
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticleBakeResult where
  toJSON (ParticleBakeResult layerId trajectories totalFrames totalParticles exportFormat) =
    object
      [ "layerId" .= layerId
      , "trajectories" .= trajectories
      , "totalFrames" .= totalFrames
      , "totalParticles" .= totalParticles
      , "exportFormat" .= exportFormat
      ]

instance FromJSON ParticleBakeResult where
  parseJSON = withObject "ParticleBakeResult" $ \o -> do
    layerId <- o .: "layerId"
    trajectories <- o .: "trajectories"
    totalFrames <- o .: "totalFrames"
    totalParticles <- o .: "totalParticles"
    exportFormat <- o .: "exportFormat"
    return (ParticleBakeResult layerId trajectories totalFrames totalParticles exportFormat)

-- ============================================================================
-- EXPORT JSON STRUCTURE (Abbreviated format)
-- ============================================================================

-- | Abbreviated keyframe format for export
data TrajectoryKeyframeExport = TrajectoryKeyframeExport
  { exportKeyframeF :: Int
  , exportKeyframeP :: [Double]
  , exportKeyframeS :: Double
  , exportKeyframeO :: Double
  , exportKeyframeR :: Double
  , exportKeyframeC :: [Double]
  }
  deriving (Eq, Show, Generic)

instance ToJSON TrajectoryKeyframeExport where
  toJSON (TrajectoryKeyframeExport f p s o r c) =
    object
      [ "f" .= f
      , "p" .= p
      , "s" .= s
      , "o" .= o
      , "r" .= r
      , "c" .= c
      ]

instance FromJSON TrajectoryKeyframeExport where
  parseJSON = withObject "TrajectoryKeyframeExport" $ \o -> do
    f <- o .: "f"
    p <- o .: "p"
    s <- o .: "s"
    o_ <- o .: "o"
    r <- o .: "r"
    c <- o .: "c"
    return (TrajectoryKeyframeExport f p s o_ r c)

-- | Abbreviated trajectory format for export
data TrajectoryExport = TrajectoryExport
  { exportTrajectoryId :: Int
  , exportTrajectoryEmitter :: Text
  , exportTrajectoryBirth :: Int
  , exportTrajectoryDeath :: Int
  , exportTrajectoryPath :: [TrajectoryKeyframeExport]
  }
  deriving (Eq, Show, Generic)

instance ToJSON TrajectoryExport where
  toJSON (TrajectoryExport id_ emitter birth death path) =
    object
      [ "id" .= id_
      , "emitter" .= emitter
      , "birth" .= birth
      , "death" .= death
      , "path" .= path
      ]

instance FromJSON TrajectoryExport where
  parseJSON = withObject "TrajectoryExport" $ \o -> do
    id_ <- o .: "id"
    emitter <- o .: "emitter"
    birth <- o .: "birth"
    death <- o .: "death"
    path <- o .: "path"
    return (TrajectoryExport id_ emitter birth death path)

-- | Final JSON export structure
data ParticleTrajectoryJSON = ParticleTrajectoryJSON
  { exportJSONVersion :: Text
  , exportJSONLayerId :: Text
  , exportJSONTotalFrames :: Int
  , exportJSONTotalParticles :: Int
  , exportJSONTrajectories :: [TrajectoryExport]
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticleTrajectoryJSON where
  toJSON (ParticleTrajectoryJSON version layerId totalFrames totalParticles trajectories) =
    object
      [ "version" .= version
      , "layerId" .= layerId
      , "totalFrames" .= totalFrames
      , "totalParticles" .= totalParticles
      , "trajectories" .= trajectories
      ]

instance FromJSON ParticleTrajectoryJSON where
  parseJSON = withObject "ParticleTrajectoryJSON" $ \o -> do
    version <- o .: "version"
    layerId <- o .: "layerId"
    totalFrames <- o .: "totalFrames"
    totalParticles <- o .: "totalParticles"
    trajectories <- o .: "trajectories"
    return (ParticleTrajectoryJSON version layerId totalFrames totalParticles trajectories)

-- ============================================================================
-- EXPORT FUNCTIONS
-- ============================================================================

-- | Convert trajectory keyframe to export format
keyframeToExport :: ParticleKeyframe -> TrajectoryKeyframeExport
keyframeToExport (ParticleKeyframe frame x y z size opacity rotation r g b) =
  TrajectoryKeyframeExport
    { exportKeyframeF = frame
    , exportKeyframeP = [x, y, z]
    , exportKeyframeS = size
    , exportKeyframeO = opacity
    , exportKeyframeR = rotation
    , exportKeyframeC = [r, g, b]
    }

-- | Convert trajectory to export format
trajectoryToExport :: BakedParticleTrajectory -> TrajectoryExport
trajectoryToExport (BakedParticleTrajectory particleId emitterId birthFrame deathFrame keyframes) =
  TrajectoryExport
    { exportTrajectoryId = particleId
    , exportTrajectoryEmitter = emitterId
    , exportTrajectoryBirth = birthFrame
    , exportTrajectoryDeath = deathFrame
    , exportTrajectoryPath = map keyframeToExport keyframes
    }

-- | Export particle trajectories to JSON format for external tools
-- Pure function: takes ParticleBakeResult, returns JSON string
exportTrajectoriesToJSON :: ParticleBakeResult -> Text
exportTrajectoriesToJSON result =
  let
    exportJSON = ParticleTrajectoryJSON
      { exportJSONVersion = "1.0"
      , exportJSONLayerId = bakeResultLayerId result
      , exportJSONTotalFrames = bakeResultTotalFrames result
      , exportJSONTotalParticles = bakeResultTotalParticles result
      , exportJSONTrajectories = map trajectoryToExport (bakeResultTrajectories result)
      }
    jsonBytes = encode exportJSON
  in
    TE.decodeUtf8 (BSL.toStrict jsonBytes)
