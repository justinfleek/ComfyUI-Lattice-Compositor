-- |
-- Module      : Lattice.State.Expression
-- Description : Pure state management functions for expression store
-- 
-- Migrated from ui/src/stores/expressionStore/index.ts, types.ts, drivers.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--
--                                                                      // note
-- This module re-exports them for convenience and adds expression store-specific
-- functionality (property drivers).
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Expression
  ( -- Re-export expression CRUD from keyframeStore
    module Lattice.State.Keyframe.Expression
  -- Query functions
  , getDriversForLayer
  , getDriversForProperty
  , checkCircularDependency
  -- Types
  , PropertyDriver(..)
  , AudioFeatureType(..)
  ) where

import Data.Aeson.Types ((.!=))
import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  , (.:?)
  )
import Data.List (filter, find)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Utils.Defaults (defaultText, defaultDouble, defaultBool)
import Lattice.Services.PropertyDriver
  ( DriverSourceType(..)
  , DriverTransform(..)
  , BlendMode(..)
  )
-- Re-export expression CRUD operations from keyframeStore
import Lattice.State.Keyframe.Expression

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Audio feature type for audio-driven property drivers
data AudioFeatureType
  = AudioAmplitude
  | AudioRMS
  | AudioSpectralCentroid
  | AudioSub
  | AudioBass
  | AudioLowMid
  | AudioMid
  | AudioHighMid
  | AudioHigh
  | AudioOnsets
  | AudioPeaks
  deriving (Eq, Show, Generic)

instance ToJSON AudioFeatureType where
  toJSON AudioAmplitude = "amplitude"
  toJSON AudioRMS = "rms"
  toJSON AudioSpectralCentroid = "spectralCentroid"
  toJSON AudioSub = "sub"
  toJSON AudioBass = "bass"
  toJSON AudioLowMid = "lowMid"
  toJSON AudioMid = "mid"
  toJSON AudioHighMid = "highMid"
  toJSON AudioHigh = "high"
  toJSON AudioOnsets = "onsets"
  toJSON AudioPeaks = "peaks"

instance FromJSON AudioFeatureType where
  parseJSON = withObject "AudioFeatureType" $ \v -> do
    s <- parseJSON v
    case s of
      "amplitude" -> return AudioAmplitude
      "rms" -> return AudioRMS
      "spectralCentroid" -> return AudioSpectralCentroid
      "sub" -> return AudioSub
      "bass" -> return AudioBass
      "lowMid" -> return AudioLowMid
      "mid" -> return AudioMid
      "highMid" -> return AudioHighMid
      "high" -> return AudioHigh
      "onsets" -> return AudioOnsets
      "peaks" -> return AudioPeaks
      _ -> fail "Invalid AudioFeatureType"

-- | Property driver - full type definition
-- Migrated from ui/src/services/propertyDriver.ts PropertyDriver interface
--                             // every // value // has // explicit // defaults
data PropertyDriver = PropertyDriver
  { propertyDriverId :: Text
  , propertyDriverName :: Text
  , propertyDriverEnabled :: Bool  -- Default: True
  , propertyDriverTargetLayerId :: Text
  , propertyDriverTargetProperty :: Text
  , propertyDriverSourceType :: DriverSourceType
  -- For property source (explicit defaults)
  , propertyDriverSourceLayerId :: Text  -- Default: "" (empty = not set)
  , propertyDriverSourceLayerIdSet :: Bool  -- Explicit flag: set (default: False)
  , propertyDriverSourceProperty :: Text  -- Default: "" (empty = not set)
  , propertyDriverSourcePropertySet :: Bool  -- Explicit flag: set (default: False)
  -- For audio source (explicit defaults)
  , propertyDriverAudioFeature :: AudioFeatureType  -- Default: AudioAmplitude
  , propertyDriverAudioFeatureSet :: Bool  -- Explicit flag: set (default: False)
  , propertyDriverAudioThreshold :: Double  -- Default: 0.0 (min: 0.0, max: 1.0)
  , propertyDriverAudioThresholdSet :: Bool  -- Explicit flag: set (default: False)
  , propertyDriverAudioAboveThreshold :: Bool  -- Default: True
  , propertyDriverAudioAboveThresholdSet :: Bool  -- Explicit flag: set (default: False)
  -- Transform chain
  , propertyDriverTransforms :: [DriverTransform]  -- Default: []
  -- Blend configuration
  , propertyDriverBlendMode :: BlendMode  -- Default: BlendAdd
  , propertyDriverBlendAmount :: Double  -- Default: 1.0 (min: 0.0, max: 1.0)
  }
  deriving (Eq, Show, Generic)

instance ToJSON PropertyDriver where
  toJSON (PropertyDriver id_ name enabled targetLayerId targetProperty sourceType sourceLayerId sourceLayerIdSet sourceProperty sourcePropertySet audioFeature audioFeatureSet audioThreshold audioThresholdSet audioAboveThreshold audioAboveThresholdSet transforms blendMode blendAmount) =
    let
      baseFields = ["id" .= id_, "name" .= name, "enabled" .= enabled, "targetLayerId" .= targetLayerId, "targetProperty" .= targetProperty, "sourceType" .= sourceType, "sourceLayerIdSet" .= sourceLayerIdSet, "sourcePropertySet" .= sourcePropertySet, "audioFeatureSet" .= audioFeatureSet, "audioThresholdSet" .= audioThresholdSet, "audioAboveThresholdSet" .= audioAboveThresholdSet, "transforms" .= transforms, "blendMode" .= blendMode, "blendAmount" .= blendAmount]
      withSourceLayerId = if sourceLayerIdSet && not (T.null sourceLayerId) then ("sourceLayerId" .= sourceLayerId) : baseFields else baseFields
      withSourceProperty = if sourcePropertySet && not (T.null sourceProperty) then ("sourceProperty" .= sourceProperty) : withSourceLayerId else withSourceLayerId
      withAudioFeature = if audioFeatureSet then ("audioFeature" .= audioFeature) : withSourceProperty else withSourceProperty
      withAudioThreshold = if audioThresholdSet then ("audioThreshold" .= audioThreshold) : withAudioFeature else withAudioFeature
      withAudioAboveThreshold = if audioAboveThresholdSet then ("audioAboveThreshold" .= audioAboveThreshold) : withAudioThreshold else withAudioThreshold
    in object withAudioAboveThreshold

instance FromJSON PropertyDriver where
  parseJSON = withObject "PropertyDriver" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    enabled <- o .:? "enabled" .!= True
    targetLayerId <- o .: "targetLayerId"
    targetProperty <- o .: "targetProperty"
    sourceType <- o .: "sourceType"
    sourceLayerId <- o .:? "sourceLayerId" .!= defaultText
    sourceLayerIdSet <- o .:? "sourceLayerIdSet" .!= False
    sourceProperty <- o .:? "sourceProperty" .!= defaultText
    sourcePropertySet <- o .:? "sourcePropertySet" .!= False
    audioFeature <- o .:? "audioFeature" .!= AudioAmplitude
    audioFeatureSet <- o .:? "audioFeatureSet" .!= False
    audioThreshold <- o .:? "audioThreshold" .!= defaultDouble
    audioThresholdSet <- o .:? "audioThresholdSet" .!= False
    audioAboveThreshold <- o .:? "audioAboveThreshold" .!= defaultBool
    audioAboveThresholdSet <- o .:? "audioAboveThresholdSet" .!= False
    transforms <- o .:? "transforms" .!= []
    blendMode <- o .:? "blendMode" .!= BlendAdd
    blendAmount <- o .:? "blendAmount" .!= 1.0
    return (PropertyDriver id_ name enabled targetLayerId targetProperty sourceType sourceLayerId sourceLayerIdSet sourceProperty sourcePropertySet audioFeature audioFeatureSet audioThreshold audioThresholdSet audioAboveThreshold audioAboveThresholdSet transforms blendMode blendAmount)

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // query // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Get all drivers for a specific layer
-- Pure function: takes layer ID and drivers list, returns filtered drivers
getDriversForLayer :: Text -> [PropertyDriver] -> [PropertyDriver]
getDriversForLayer layerId drivers =
  filter (\d -> propertyDriverTargetLayerId d == layerId) drivers

-- | Get all enabled drivers for a specific property
-- Pure function: takes layer ID, property path, and drivers list, returns filtered drivers
getDriversForProperty :: Text -> Text -> [PropertyDriver] -> [PropertyDriver]
getDriversForProperty layerId propertyPath drivers =
  filter (\d ->
    propertyDriverTargetLayerId d == layerId &&
    propertyDriverTargetProperty d == propertyPath &&
    propertyDriverEnabled d
  ) drivers

-- ════════════════════════════════════════════════════════════════════════════
--                                        // circular // dependency // checking
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if adding a driver would create a circular dependency
-- Pure function: takes new driver and existing drivers list, returns True if cycle detected
-- Migrated from PropertyDriverSystem.checkCircularDependency
-- Uses explicit flags - no Maybe/Nothing
checkCircularDependency :: PropertyDriver -> [PropertyDriver] -> Bool
checkCircularDependency newDriver existingDrivers =
  case propertyDriverSourceType newDriver of
    SourceProperty ->
      if propertyDriverSourceLayerIdSet newDriver && propertyDriverSourcePropertySet newDriver &&
         not (T.null (propertyDriverSourceLayerId newDriver)) &&
         not (T.null (propertyDriverSourceProperty newDriver))
      then
        let sourceLayerId = propertyDriverSourceLayerId newDriver
            sourceProperty = propertyDriverSourceProperty newDriver
            targetKey = propertyDriverTargetLayerId newDriver <> ":" <> propertyDriverTargetProperty newDriver
            visited = Set.empty
        in hasCycle sourceLayerId sourceProperty targetKey existingDrivers visited
      else False  -- Incomplete source configuration - no cycle possible
    _ -> False  -- Non-property sources cannot create cycles

-- | Internal helper: check for cycle in dependency graph
-- Pure function: DFS traversal of driver dependency graph
-- Uses explicit flags - no Maybe/Nothing
hasCycle ::
  Text ->  -- Current layer ID
  Text ->  -- Current property path
  Text ->  -- Target key (layerId:propertyPath)
  [PropertyDriver] ->  -- All existing drivers
  Set Text ->  -- Visited nodes (layerId:propertyPath keys)
  Bool  -- True if cycle detected
hasCycle currentLayerId currentProperty targetKey drivers visited =
  let currentKey = currentLayerId <> ":" <> currentProperty
  in
    -- If we've reached the target, we have a cycle
    if currentKey == targetKey
    then True
    -- If already visited this node, no cycle through this path
    else if Set.member currentKey visited
    then False
    else
      let newVisited = Set.insert currentKey visited
          -- Find all drivers that target this property
          targetingDrivers = filter (\d ->
            propertyDriverSourceType d == SourceProperty &&
            propertyDriverTargetLayerId d == currentLayerId &&
            propertyDriverTargetProperty d == currentProperty &&
            propertyDriverEnabled d
          ) drivers
          -- Check if any of their sources lead back to our target
          checkDriver driver =
            if propertyDriverSourceLayerIdSet driver && propertyDriverSourcePropertySet driver &&
               not (T.null (propertyDriverSourceLayerId driver)) &&
               not (T.null (propertyDriverSourceProperty driver))
            then
              let sourceLayerId = propertyDriverSourceLayerId driver
                  sourceProperty = propertyDriverSourceProperty driver
              in hasCycle sourceLayerId sourceProperty targetKey drivers newVisited
            else False
      in any checkDriver targetingDrivers
