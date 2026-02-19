-- |
-- Module      : Lattice.Types.LayerDataParticles
-- Description : Particle system layer data types
-- 
-- Migrated from ui/src/types/particles.ts
-- These types depend heavily on AnimatableProperty and Vec3
-- This is a large cohesive module for the entire particle system
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.LayerDataParticles
  ( -- Main type
    ParticleLayerData(..)
  -- System config
  , ParticleSystemLayerConfig(..)
  , ParticleBoundaryBehavior(..)
  -- Emitter config
  , ParticleEmitterConfig(..)
  , EmitterShape(..)
  , SpriteConfig(..)
  , SpritePlayMode(..)
  , DepthMapEmission(..)
  , DepthMapEmissionDepthMode(..)
  , MaskEmission(..)
  , MaskEmissionChannel(..)
  , SplinePathEmission(..)
  , SplinePathEmissionMode(..)
  -- Force fields
  , GravityWellConfig(..)
  , GravityWellFalloff(..)
  , VortexConfig(..)
  -- Physics
  , TurbulenceFieldConfig(..)
  , FlockingConfig(..)
  , CollisionConfig(..)
  , CollisionBoundaryBehavior(..)
  , CollisionPlaneConfig(..)
  -- Rendering
  , ParticleRenderOptions(..)
  , ParticleBlendMode(..)
  , ParticleShape(..)
  , ConnectionRenderConfig(..)
  , ParticleMeshMode(..)
  , ParticleMeshGeometry(..)
  -- Advanced features
  , SpringSystemConfig(..)
  , SpringStructure(..)
  , SpringStructureType(..)
  , SPHFluidConfig(..)
  , SPHFluidPreset(..)
  -- Audio
  , AudioBindingConfig(..)
  , AudioFeatureName(..)
  , AudioTargetType(..)
  , AudioCurveType(..)
  , AudioTriggerMode(..)
  , AudioParticleMapping(..)
  -- Sub-emitters
  , SubEmitterConfig(..)
  , SubEmitterTrigger(..)
  -- Modulation
  , ParticleModulationConfig(..)
  , ParticleModulationProperty(..)
  -- Configs
  , ParticleLODConfig(..)
  , ParticleDOFConfig(..)
  , ParticleGroupConfig(..)
  , ParticleVisualizationConfig(..)
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
  , Value(..)
  )
import Data.Text (Text)
import GHC.Generics (Generic)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  )
import Lattice.Types.Primitives
  ( Vec2(..)
  , Vec3(..)
  , BlendMode(..)
  , validateFinite
  , validateNonNegative
  , validateNormalized01
  )

-- ============================================================================
-- BASIC ENUMS AND TYPES
-- ============================================================================

-- | Emitter shape
data EmitterShape
  = EmitterShapePoint
  | EmitterShapeLine
  | EmitterShapeCircle
  | EmitterShapeBox
  | EmitterShapeSphere
  | EmitterShapeRing
  | EmitterShapeSpline
  | EmitterShapeDepthMap
  | EmitterShapeMask
  | EmitterShapeCone
  | EmitterShapeImage
  | EmitterShapeDepthEdge
  | EmitterShapeMesh
  deriving (Eq, Show, Generic)

instance ToJSON EmitterShape where
  toJSON EmitterShapePoint = "point"
  toJSON EmitterShapeLine = "line"
  toJSON EmitterShapeCircle = "circle"
  toJSON EmitterShapeBox = "box"
  toJSON EmitterShapeSphere = "sphere"
  toJSON EmitterShapeRing = "ring"
  toJSON EmitterShapeSpline = "spline"
  toJSON EmitterShapeDepthMap = "depth-map"
  toJSON EmitterShapeMask = "mask"
  toJSON EmitterShapeCone = "cone"
  toJSON EmitterShapeImage = "image"
  toJSON EmitterShapeDepthEdge = "depthEdge"
  toJSON EmitterShapeMesh = "mesh"

instance FromJSON EmitterShape where
  parseJSON = withText "EmitterShape" $ \s ->
    case s of
      "point" -> return EmitterShapePoint
      "line" -> return EmitterShapeLine
      "circle" -> return EmitterShapeCircle
      "box" -> return EmitterShapeBox
      "sphere" -> return EmitterShapeSphere
      "ring" -> return EmitterShapeRing
      "spline" -> return EmitterShapeSpline
      "depth-map" -> return EmitterShapeDepthMap
      "mask" -> return EmitterShapeMask
      "cone" -> return EmitterShapeCone
      "image" -> return EmitterShapeImage
      "depthEdge" -> return EmitterShapeDepthEdge
      "mesh" -> return EmitterShapeMesh
      _ -> fail "Invalid EmitterShape"

-- | Boundary behavior
data ParticleBoundaryBehavior
  = ParticleBoundaryBehaviorBounce
  | ParticleBoundaryBehaviorKill
  | ParticleBoundaryBehaviorWrap
  deriving (Eq, Show, Generic)

instance ToJSON ParticleBoundaryBehavior where
  toJSON ParticleBoundaryBehaviorBounce = "bounce"
  toJSON ParticleBoundaryBehaviorKill = "kill"
  toJSON ParticleBoundaryBehaviorWrap = "wrap"

instance FromJSON ParticleBoundaryBehavior where
  parseJSON = withText "ParticleBoundaryBehavior" $ \s ->
    case s of
      "bounce" -> return ParticleBoundaryBehaviorBounce
      "kill" -> return ParticleBoundaryBehaviorKill
      "wrap" -> return ParticleBoundaryBehaviorWrap
      _ -> fail "Invalid ParticleBoundaryBehavior"

-- | Sprite play mode
data SpritePlayMode
  = SpritePlayModeLoop
  | SpritePlayModeOnce
  | SpritePlayModePingpong
  | SpritePlayModeRandom
  deriving (Eq, Show, Generic)

instance ToJSON SpritePlayMode where
  toJSON SpritePlayModeLoop = "loop"
  toJSON SpritePlayModeOnce = "once"
  toJSON SpritePlayModePingpong = "pingpong"
  toJSON SpritePlayModeRandom = "random"

instance FromJSON SpritePlayMode where
  parseJSON = withText "SpritePlayMode" $ \s ->
    case s of
      "loop" -> return SpritePlayModeLoop
      "once" -> return SpritePlayModeOnce
      "pingpong" -> return SpritePlayModePingpong
      "random" -> return SpritePlayModeRandom
      _ -> fail "Invalid SpritePlayMode"

-- | Depth map emission depth mode
data DepthMapEmissionDepthMode
  = DepthMapEmissionDepthModeNearWhite
  | DepthMapEmissionDepthModeNearBlack
  deriving (Eq, Show, Generic)

instance ToJSON DepthMapEmissionDepthMode where
  toJSON DepthMapEmissionDepthModeNearWhite = "near-white"
  toJSON DepthMapEmissionDepthModeNearBlack = "near-black"

instance FromJSON DepthMapEmissionDepthMode where
  parseJSON = withText "DepthMapEmissionDepthMode" $ \s ->
    case s of
      "near-white" -> return DepthMapEmissionDepthModeNearWhite
      "near-black" -> return DepthMapEmissionDepthModeNearBlack
      _ -> fail "Invalid DepthMapEmissionDepthMode"

-- | Mask emission channel
data MaskEmissionChannel
  = MaskEmissionChannelLuminance
  | MaskEmissionChannelAlpha
  | MaskEmissionChannelRed
  | MaskEmissionChannelGreen
  | MaskEmissionChannelBlue
  deriving (Eq, Show, Generic)

instance ToJSON MaskEmissionChannel where
  toJSON MaskEmissionChannelLuminance = "luminance"
  toJSON MaskEmissionChannelAlpha = "alpha"
  toJSON MaskEmissionChannelRed = "red"
  toJSON MaskEmissionChannelGreen = "green"
  toJSON MaskEmissionChannelBlue = "blue"

instance FromJSON MaskEmissionChannel where
  parseJSON = withText "MaskEmissionChannel" $ \s ->
    case s of
      "luminance" -> return MaskEmissionChannelLuminance
      "alpha" -> return MaskEmissionChannelAlpha
      "red" -> return MaskEmissionChannelRed
      "green" -> return MaskEmissionChannelGreen
      "blue" -> return MaskEmissionChannelBlue
      _ -> fail "Invalid MaskEmissionChannel"

-- | Spline path emission mode
data SplinePathEmissionMode
  = SplinePathEmissionModeUniform
  | SplinePathEmissionModeRandom
  | SplinePathEmissionModeStart
  | SplinePathEmissionModeEnd
  | SplinePathEmissionModeSequential
  deriving (Eq, Show, Generic)

instance ToJSON SplinePathEmissionMode where
  toJSON SplinePathEmissionModeUniform = "uniform"
  toJSON SplinePathEmissionModeRandom = "random"
  toJSON SplinePathEmissionModeStart = "start"
  toJSON SplinePathEmissionModeEnd = "end"
  toJSON SplinePathEmissionModeSequential = "sequential"

instance FromJSON SplinePathEmissionMode where
  parseJSON = withText "SplinePathEmissionMode" $ \s ->
    case s of
      "uniform" -> return SplinePathEmissionModeUniform
      "random" -> return SplinePathEmissionModeRandom
      "start" -> return SplinePathEmissionModeStart
      "end" -> return SplinePathEmissionModeEnd
      "sequential" -> return SplinePathEmissionModeSequential
      _ -> fail "Invalid SplinePathEmissionMode"

-- | Gravity well falloff
data GravityWellFalloff
  = GravityWellFalloffLinear
  | GravityWellFalloffQuadratic
  | GravityWellFalloffConstant
  deriving (Eq, Show, Generic)

instance ToJSON GravityWellFalloff where
  toJSON GravityWellFalloffLinear = "linear"
  toJSON GravityWellFalloffQuadratic = "quadratic"
  toJSON GravityWellFalloffConstant = "constant"

instance FromJSON GravityWellFalloff where
  parseJSON = withText "GravityWellFalloff" $ \s ->
    case s of
      "linear" -> return GravityWellFalloffLinear
      "quadratic" -> return GravityWellFalloffQuadratic
      "constant" -> return GravityWellFalloffConstant
      _ -> fail "Invalid GravityWellFalloff"

-- | Collision boundary behavior
data CollisionBoundaryBehavior
  = CollisionBoundaryBehaviorNone
  | CollisionBoundaryBehaviorKill
  | CollisionBoundaryBehaviorBounce
  | CollisionBoundaryBehaviorWrap
  | CollisionBoundaryBehaviorStick
  deriving (Eq, Show, Generic)

instance ToJSON CollisionBoundaryBehavior where
  toJSON CollisionBoundaryBehaviorNone = "none"
  toJSON CollisionBoundaryBehaviorKill = "kill"
  toJSON CollisionBoundaryBehaviorBounce = "bounce"
  toJSON CollisionBoundaryBehaviorWrap = "wrap"
  toJSON CollisionBoundaryBehaviorStick = "stick"

instance FromJSON CollisionBoundaryBehavior where
  parseJSON = withText "CollisionBoundaryBehavior" $ \s ->
    case s of
      "none" -> return CollisionBoundaryBehaviorNone
      "kill" -> return CollisionBoundaryBehaviorKill
      "bounce" -> return CollisionBoundaryBehaviorBounce
      "wrap" -> return CollisionBoundaryBehaviorWrap
      "stick" -> return CollisionBoundaryBehaviorStick
      _ -> fail "Invalid CollisionBoundaryBehavior"

-- | Particle blend mode (simplified subset)
data ParticleBlendMode
  = ParticleBlendModeNormal
  | ParticleBlendModeAdditive
  | ParticleBlendModeMultiply
  | ParticleBlendModeScreen
  deriving (Eq, Show, Generic)

instance ToJSON ParticleBlendMode where
  toJSON ParticleBlendModeNormal = "normal"
  toJSON ParticleBlendModeAdditive = "additive"
  toJSON ParticleBlendModeMultiply = "multiply"
  toJSON ParticleBlendModeScreen = "screen"

instance FromJSON ParticleBlendMode where
  parseJSON = withText "ParticleBlendMode" $ \s ->
    case s of
      "normal" -> return ParticleBlendModeNormal
      "additive" -> return ParticleBlendModeAdditive
      "multiply" -> return ParticleBlendModeMultiply
      "screen" -> return ParticleBlendModeScreen
      _ -> fail "Invalid ParticleBlendMode"

-- | Particle shape
data ParticleShape
  = ParticleShapeCircle
  | ParticleShapeSquare
  | ParticleShapeTriangle
  | ParticleShapeStar
  deriving (Eq, Show, Generic)

instance ToJSON ParticleShape where
  toJSON ParticleShapeCircle = "circle"
  toJSON ParticleShapeSquare = "square"
  toJSON ParticleShapeTriangle = "triangle"
  toJSON ParticleShapeStar = "star"

instance FromJSON ParticleShape where
  parseJSON = withText "ParticleShape" $ \s ->
    case s of
      "circle" -> return ParticleShapeCircle
      "square" -> return ParticleShapeSquare
      "triangle" -> return ParticleShapeTriangle
      "star" -> return ParticleShapeStar
      _ -> fail "Invalid ParticleShape"

-- | Particle mesh mode
data ParticleMeshMode
  = ParticleMeshModeBillboard
  | ParticleMeshModeMesh
  deriving (Eq, Show, Generic)

instance ToJSON ParticleMeshMode where
  toJSON ParticleMeshModeBillboard = "billboard"
  toJSON ParticleMeshModeMesh = "mesh"

instance FromJSON ParticleMeshMode where
  parseJSON = withText "ParticleMeshMode" $ \s ->
    case s of
      "billboard" -> return ParticleMeshModeBillboard
      "mesh" -> return ParticleMeshModeMesh
      _ -> fail "Invalid ParticleMeshMode"

-- | Particle mesh geometry
data ParticleMeshGeometry
  = ParticleMeshGeometryCube
  | ParticleMeshGeometrySphere
  | ParticleMeshGeometryCylinder
  | ParticleMeshGeometryCone
  | ParticleMeshGeometryTorus
  | ParticleMeshGeometryCustom
  deriving (Eq, Show, Generic)

instance ToJSON ParticleMeshGeometry where
  toJSON ParticleMeshGeometryCube = "cube"
  toJSON ParticleMeshGeometrySphere = "sphere"
  toJSON ParticleMeshGeometryCylinder = "cylinder"
  toJSON ParticleMeshGeometryCone = "cone"
  toJSON ParticleMeshGeometryTorus = "torus"
  toJSON ParticleMeshGeometryCustom = "custom"

instance FromJSON ParticleMeshGeometry where
  parseJSON = withText "ParticleMeshGeometry" $ \s ->
    case s of
      "cube" -> return ParticleMeshGeometryCube
      "sphere" -> return ParticleMeshGeometrySphere
      "cylinder" -> return ParticleMeshGeometryCylinder
      "cone" -> return ParticleMeshGeometryCone
      "torus" -> return ParticleMeshGeometryTorus
      "custom" -> return ParticleMeshGeometryCustom
      _ -> fail "Invalid ParticleMeshGeometry"

-- | Spring structure type
data SpringStructureType
  = SpringStructureTypeCloth
  | SpringStructureTypeRope
  | SpringStructureTypeSoftbody
  | SpringStructureTypeCustom
  deriving (Eq, Show, Generic)

instance ToJSON SpringStructureType where
  toJSON SpringStructureTypeCloth = "cloth"
  toJSON SpringStructureTypeRope = "rope"
  toJSON SpringStructureTypeSoftbody = "softbody"
  toJSON SpringStructureTypeCustom = "custom"

instance FromJSON SpringStructureType where
  parseJSON = withText "SpringStructureType" $ \s ->
    case s of
      "cloth" -> return SpringStructureTypeCloth
      "rope" -> return SpringStructureTypeRope
      "softbody" -> return SpringStructureTypeSoftbody
      "custom" -> return SpringStructureTypeCustom
      _ -> fail "Invalid SpringStructureType"

-- | SPH fluid preset
data SPHFluidPreset
  = SPHFluidPresetWater
  | SPHFluidPresetHoney
  | SPHFluidPresetLava
  | SPHFluidPresetGas
  | SPHFluidPresetCustom
  deriving (Eq, Show, Generic)

instance ToJSON SPHFluidPreset where
  toJSON SPHFluidPresetWater = "water"
  toJSON SPHFluidPresetHoney = "honey"
  toJSON SPHFluidPresetLava = "lava"
  toJSON SPHFluidPresetGas = "gas"
  toJSON SPHFluidPresetCustom = "custom"

instance FromJSON SPHFluidPreset where
  parseJSON = withText "SPHFluidPreset" $ \s ->
    case s of
      "water" -> return SPHFluidPresetWater
      "honey" -> return SPHFluidPresetHoney
      "lava" -> return SPHFluidPresetLava
      "gas" -> return SPHFluidPresetGas
      "custom" -> return SPHFluidPresetCustom
      _ -> fail "Invalid SPHFluidPreset"

-- | Audio feature name
data AudioFeatureName
  = AudioFeatureNameAmplitude
  | AudioFeatureNameBass
  | AudioFeatureNameMid
  | AudioFeatureNameHigh
  | AudioFeatureNameBeat
  | AudioFeatureNameSpectralCentroid
  deriving (Eq, Show, Generic)

instance ToJSON AudioFeatureName where
  toJSON AudioFeatureNameAmplitude = "amplitude"
  toJSON AudioFeatureNameBass = "bass"
  toJSON AudioFeatureNameMid = "mid"
  toJSON AudioFeatureNameHigh = "high"
  toJSON AudioFeatureNameBeat = "beat"
  toJSON AudioFeatureNameSpectralCentroid = "spectralCentroid"

instance FromJSON AudioFeatureName where
  parseJSON = withText "AudioFeatureName" $ \s ->
    case s of
      "amplitude" -> return AudioFeatureNameAmplitude
      "bass" -> return AudioFeatureNameBass
      "mid" -> return AudioFeatureNameMid
      "high" -> return AudioFeatureNameHigh
      "beat" -> return AudioFeatureNameBeat
      "spectralCentroid" -> return AudioFeatureNameSpectralCentroid
      _ -> fail "Invalid AudioFeatureName"

-- | Audio target type
data AudioTargetType
  = AudioTargetTypeEmitter
  | AudioTargetTypeSystem
  | AudioTargetTypeForceField
  deriving (Eq, Show, Generic)

instance ToJSON AudioTargetType where
  toJSON AudioTargetTypeEmitter = "emitter"
  toJSON AudioTargetTypeSystem = "system"
  toJSON AudioTargetTypeForceField = "forceField"

instance FromJSON AudioTargetType where
  parseJSON = withText "AudioTargetType" $ \s ->
    case s of
      "emitter" -> return AudioTargetTypeEmitter
      "system" -> return AudioTargetTypeSystem
      "forceField" -> return AudioTargetTypeForceField
      _ -> fail "Invalid AudioTargetType"

-- | Audio curve type
data AudioCurveType
  = AudioCurveTypeLinear
  | AudioCurveTypeExponential
  | AudioCurveTypeLogarithmic
  | AudioCurveTypeStep
  deriving (Eq, Show, Generic)

instance ToJSON AudioCurveType where
  toJSON AudioCurveTypeLinear = "linear"
  toJSON AudioCurveTypeExponential = "exponential"
  toJSON AudioCurveTypeLogarithmic = "logarithmic"
  toJSON AudioCurveTypeStep = "step"

instance FromJSON AudioCurveType where
  parseJSON = withText "AudioCurveType" $ \s ->
    case s of
      "linear" -> return AudioCurveTypeLinear
      "exponential" -> return AudioCurveTypeExponential
      "logarithmic" -> return AudioCurveTypeLogarithmic
      "step" -> return AudioCurveTypeStep
      _ -> fail "Invalid AudioCurveType"

-- | Audio trigger mode
data AudioTriggerMode
  = AudioTriggerModeContinuous
  | AudioTriggerModeOnThreshold
  | AudioTriggerModeOnBeat
  deriving (Eq, Show, Generic)

instance ToJSON AudioTriggerMode where
  toJSON AudioTriggerModeContinuous = "continuous"
  toJSON AudioTriggerModeOnThreshold = "onThreshold"
  toJSON AudioTriggerModeOnBeat = "onBeat"

instance FromJSON AudioTriggerMode where
  parseJSON = withText "AudioTriggerMode" $ \s ->
    case s of
      "continuous" -> return AudioTriggerModeContinuous
      "onThreshold" -> return AudioTriggerModeOnThreshold
      "onBeat" -> return AudioTriggerModeOnBeat
      _ -> fail "Invalid AudioTriggerMode"

-- | Sub-emitter trigger
data SubEmitterTrigger
  = SubEmitterTriggerDeath
  deriving (Eq, Show, Generic)

instance ToJSON SubEmitterTrigger where
  toJSON SubEmitterTriggerDeath = "death"

instance FromJSON SubEmitterTrigger where
  parseJSON = withText "SubEmitterTrigger" $ \s ->
    case s of
      "death" -> return SubEmitterTriggerDeath
      _ -> fail "Invalid SubEmitterTrigger"

-- | Particle modulation property
data ParticleModulationProperty
  = ParticleModulationPropertySize
  | ParticleModulationPropertySpeed
  | ParticleModulationPropertyOpacity
  | ParticleModulationPropertyColorR
  | ParticleModulationPropertyColorG
  | ParticleModulationPropertyColorB
  deriving (Eq, Show, Generic)

instance ToJSON ParticleModulationProperty where
  toJSON ParticleModulationPropertySize = "size"
  toJSON ParticleModulationPropertySpeed = "speed"
  toJSON ParticleModulationPropertyOpacity = "opacity"
  toJSON ParticleModulationPropertyColorR = "colorR"
  toJSON ParticleModulationPropertyColorG = "colorG"
  toJSON ParticleModulationPropertyColorB = "colorB"

instance FromJSON ParticleModulationProperty where
  parseJSON = withText "ParticleModulationProperty" $ \s ->
    case s of
      "size" -> return ParticleModulationPropertySize
      "speed" -> return ParticleModulationPropertySpeed
      "opacity" -> return ParticleModulationPropertyOpacity
      "colorR" -> return ParticleModulationPropertyColorR
      "colorG" -> return ParticleModulationPropertyColorG
      "colorB" -> return ParticleModulationPropertyColorB
      _ -> fail "Invalid ParticleModulationProperty"

-- ============================================================================
-- CONFIGURATION TYPES
-- ============================================================================

-- | Particle LOD config
data ParticleLODConfig = ParticleLODConfig
  { particleLODConfigEnabled :: Bool
  , particleLODConfigDistances :: [Double]  -- [near, mid, far]
  , particleLODConfigSizeMultipliers :: [Double]  -- [near, mid, far]
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticleLODConfig where
  toJSON (ParticleLODConfig enabled distances multipliers) =
    object
      [ "enabled" .= enabled
      , "distances" .= distances
      , "sizeMultipliers" .= multipliers
      ]

instance FromJSON ParticleLODConfig where
  parseJSON = withObject "ParticleLODConfig" $ \o -> do
    enabled <- o .: "enabled"
    distances <- o .: "distances"
    multipliers <- o .: "sizeMultipliers"
    if all (\d -> validateFinite d && validateNonNegative d) distances &&
       all (\m -> validateFinite m && validateNonNegative m) multipliers
      then return (ParticleLODConfig enabled distances multipliers)
      else fail "ParticleLODConfig: distances and multipliers must be finite and non-negative"

-- | Particle DOF config
data ParticleDOFConfig = ParticleDOFConfig
  { particleDOFConfigEnabled :: Bool
  , particleDOFConfigFocusDistance :: Double
  , particleDOFConfigFocusRange :: Double
  , particleDOFConfigBlurAmount :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticleDOFConfig where
  toJSON (ParticleDOFConfig enabled focusDist focusRange blurAmount) =
    object
      [ "enabled" .= enabled
      , "focusDistance" .= focusDist
      , "focusRange" .= focusRange
      , "blurAmount" .= blurAmount
      ]

instance FromJSON ParticleDOFConfig where
  parseJSON = withObject "ParticleDOFConfig" $ \o -> do
    enabled <- o .: "enabled"
    focusDist <- o .: "focusDistance"
    focusRange <- o .: "focusRange"
    blurAmount <- o .: "blurAmount"
    if validateFinite focusDist && validateFinite focusRange && validateFinite blurAmount &&
       validateNonNegative focusDist && validateNonNegative focusRange && validateNormalized01 blurAmount
      then return (ParticleDOFConfig enabled focusDist focusRange blurAmount)
      else fail "ParticleDOFConfig: numeric values must be finite and within valid ranges"

-- | Particle group config
data ParticleGroupConfig = ParticleGroupConfig
  { particleGroupConfigId :: Text
  , particleGroupConfigName :: Text
  , particleGroupConfigEnabled :: Bool
  , particleGroupConfigColor :: (Double, Double, Double, Double)  -- RGBA tint
  , particleGroupConfigCollisionMask :: Double  -- Bitmask
  , particleGroupConfigConnectionMask :: Double  -- Bitmask
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticleGroupConfig where
  toJSON (ParticleGroupConfig id_ name enabled (r, g, b, a) collisionMask connectionMask) =
    object
      [ "id" .= id_
      , "name" .= name
      , "enabled" .= enabled
      , "color" .= [r, g, b, a]
      , "collisionMask" .= collisionMask
      , "connectionMask" .= connectionMask
      ]

instance FromJSON ParticleGroupConfig where
  parseJSON = withObject "ParticleGroupConfig" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    enabled <- o .: "enabled"
    colorArr <- o .: "color"
    (r, g, b, a) <- case colorArr of
      [r', g', b', a'] -> return (r', g', b', a')
      _ -> fail "ParticleGroupConfig: color must be [r, g, b, a]"
    collisionMask <- o .: "collisionMask"
    connectionMask <- o .: "connectionMask"
    if validateFinite r && validateFinite g && validateFinite b && validateFinite a &&
       validateNormalized01 r && validateNormalized01 g && validateNormalized01 b && validateNormalized01 a &&
       validateFinite collisionMask && validateFinite connectionMask &&
       validateNonNegative collisionMask && validateNonNegative connectionMask
      then return (ParticleGroupConfig id_ name enabled (r, g, b, a) collisionMask connectionMask)
      else fail "ParticleGroupConfig: numeric values must be finite and within valid ranges"

-- | Particle visualization config
data ParticleVisualizationConfig = ParticleVisualizationConfig
  { particleVisualizationConfigShowHorizon :: Bool
  , particleVisualizationConfigShowGrid :: Bool
  , particleVisualizationConfigShowAxis :: Bool
  , particleVisualizationConfigGridSize :: Double
  , particleVisualizationConfigGridDepth :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticleVisualizationConfig where
  toJSON (ParticleVisualizationConfig showHorizon showGrid showAxis gridSize gridDepth) =
    object
      [ "showHorizon" .= showHorizon
      , "showGrid" .= showGrid
      , "showAxis" .= showAxis
      , "gridSize" .= gridSize
      , "gridDepth" .= gridDepth
      ]

instance FromJSON ParticleVisualizationConfig where
  parseJSON = withObject "ParticleVisualizationConfig" $ \o -> do
    showHorizon <- o .: "showHorizon"
    showGrid <- o .: "showGrid"
    showAxis <- o .: "showAxis"
    gridSize <- o .: "gridSize"
    gridDepth <- o .: "gridDepth"
    if validateFinite gridSize && validateFinite gridDepth &&
       validateNonNegative gridSize && validateNonNegative gridDepth
      then return (ParticleVisualizationConfig showHorizon showGrid showAxis gridSize gridDepth)
      else fail "ParticleVisualizationConfig: gridSize and gridDepth must be finite and non-negative"

-- ============================================================================
-- EMISSION TYPES
-- ============================================================================

-- | Depth map emission
data DepthMapEmission = DepthMapEmission
  { depthMapEmissionSourceLayerId :: Text
  , depthMapEmissionDepthMin :: Double  -- 0-1
  , depthMapEmissionDepthMax :: Double  -- 0-1
  , depthMapEmissionDensity :: Double
  , depthMapEmissionVelocityByDepth :: Bool
  , depthMapEmissionSizeByDepth :: Bool
  , depthMapEmissionDepthMode :: DepthMapEmissionDepthMode
  }
  deriving (Eq, Show, Generic)

instance ToJSON DepthMapEmission where
  toJSON (DepthMapEmission sourceLayerId depthMin depthMax density velocityByDepth sizeByDepth depthMode) =
    object
      [ "sourceLayerId" .= sourceLayerId
      , "depthMin" .= depthMin
      , "depthMax" .= depthMax
      , "density" .= density
      , "velocityByDepth" .= velocityByDepth
      , "sizeByDepth" .= sizeByDepth
      , "depthMode" .= depthMode
      ]

instance FromJSON DepthMapEmission where
  parseJSON = withObject "DepthMapEmission" $ \o -> do
    sourceLayerId <- o .: "sourceLayerId"
    depthMin <- o .: "depthMin"
    depthMax <- o .: "depthMax"
    density <- o .: "density"
    velocityByDepth <- o .: "velocityByDepth"
    sizeByDepth <- o .: "sizeByDepth"
    depthMode <- o .: "depthMode"
    if validateNormalized01 depthMin && validateNormalized01 depthMax &&
       validateFinite density && validateNonNegative density &&
       depthMin <= depthMax
      then return (DepthMapEmission sourceLayerId depthMin depthMax density velocityByDepth sizeByDepth depthMode)
      else fail "DepthMapEmission: depthMin/depthMax must be in [0,1], density must be finite and non-negative"

-- | Mask emission
data MaskEmission = MaskEmission
  { maskEmissionSourceLayerId :: Text
  , maskEmissionThreshold :: Double  -- 0-1
  , maskEmissionDensity :: Double
  , maskEmissionChannel :: MaskEmissionChannel
  , maskEmissionInvert :: Bool
  , maskEmissionSampleRate :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON MaskEmission where
  toJSON (MaskEmission sourceLayerId threshold density channel invert sampleRate) =
    object
      [ "sourceLayerId" .= sourceLayerId
      , "threshold" .= threshold
      , "density" .= density
      , "channel" .= channel
      , "invert" .= invert
      , "sampleRate" .= sampleRate
      ]

instance FromJSON MaskEmission where
  parseJSON = withObject "MaskEmission" $ \o -> do
    sourceLayerId <- o .: "sourceLayerId"
    threshold <- o .: "threshold"
    density <- o .: "density"
    channel <- o .: "channel"
    invert <- o .: "invert"
    sampleRate <- o .: "sampleRate"
    if validateNormalized01 threshold && validateFinite density && validateFinite sampleRate &&
       validateNonNegative density && validateNonNegative sampleRate && sampleRate >= 1
      then return (MaskEmission sourceLayerId threshold density channel invert sampleRate)
      else fail "MaskEmission: threshold must be in [0,1], density and sampleRate must be finite and non-negative, sampleRate >= 1"

-- | Spline path emission
data SplinePathEmission = SplinePathEmission
  { splinePathEmissionLayerId :: Text
  , splinePathEmissionEmitMode :: SplinePathEmissionMode
  , splinePathEmissionParameter :: Double
  , splinePathEmissionAlignToPath :: Bool
  , splinePathEmissionOffset :: Double  -- Normalized
  , splinePathEmissionBidirectional :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON SplinePathEmission where
  toJSON (SplinePathEmission layerId emitMode parameter alignToPath offset bidirectional) =
    object
      [ "layerId" .= layerId
      , "emitMode" .= emitMode
      , "parameter" .= parameter
      , "alignToPath" .= alignToPath
      , "offset" .= offset
      , "bidirectional" .= bidirectional
      ]

instance FromJSON SplinePathEmission where
  parseJSON = withObject "SplinePathEmission" $ \o -> do
    layerId <- o .: "layerId"
    emitMode <- o .: "emitMode"
    parameter <- o .: "parameter"
    alignToPath <- o .: "alignToPath"
    offset <- o .: "offset"
    bidirectional <- o .: "bidirectional"
    if validateFinite parameter && validateFinite offset && validateNormalized01 offset
      then return (SplinePathEmission layerId emitMode parameter alignToPath offset bidirectional)
      else fail "SplinePathEmission: parameter and offset must be finite, offset must be in [0,1]"

-- | Sprite config
data SpriteConfig = SpriteConfig
  { spriteConfigEnabled :: Bool
  , spriteConfigImageUrl :: Maybe Text  -- null in TypeScript
  , spriteConfigIsSheet :: Bool
  , spriteConfigColumns :: Double
  , spriteConfigRows :: Double
  , spriteConfigTotalFrames :: Double
  , spriteConfigFrameRate :: Double
  , spriteConfigPlayMode :: SpritePlayMode
  , spriteConfigBillboard :: Bool
  , spriteConfigRotationEnabled :: Bool
  , spriteConfigRotationSpeed :: Double
  , spriteConfigRotationSpeedVariance :: Double
  , spriteConfigAlignToVelocity :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON SpriteConfig where
  toJSON (SpriteConfig enabled mImageUrl isSheet columns rows totalFrames frameRate playMode billboard rotationEnabled rotationSpeed rotationSpeedVariance alignToVelocity) =
    let
      baseFields = ["enabled" .= enabled, "isSheet" .= isSheet, "columns" .= columns, "rows" .= rows, "totalFrames" .= totalFrames, "frameRate" .= frameRate, "playMode" .= playMode, "billboard" .= billboard, "rotationEnabled" .= rotationEnabled, "rotationSpeed" .= rotationSpeed, "rotationSpeedVariance" .= rotationSpeedVariance, "alignToVelocity" .= alignToVelocity]
      withImageUrl = case mImageUrl of Just url -> ("imageUrl" .= url) : baseFields; Nothing -> baseFields
    in object withImageUrl

instance FromJSON SpriteConfig where
  parseJSON = withObject "SpriteConfig" $ \o -> do
    enabled <- o .: "enabled"
    mImageUrl <- o .:? "imageUrl"
    isSheet <- o .: "isSheet"
    columns <- o .: "columns"
    rows <- o .: "rows"
    totalFrames <- o .: "totalFrames"
    frameRate <- o .: "frameRate"
    playMode <- o .: "playMode"
    billboard <- o .: "billboard"
    rotationEnabled <- o .: "rotationEnabled"
    rotationSpeed <- o .: "rotationSpeed"
    rotationSpeedVariance <- o .: "rotationSpeedVariance"
    alignToVelocity <- o .: "alignToVelocity"
    if validateFinite columns && validateFinite rows && validateFinite totalFrames &&
       validateFinite frameRate && validateFinite rotationSpeed && validateFinite rotationSpeedVariance &&
       validateNonNegative columns && validateNonNegative rows && validateNonNegative totalFrames &&
       validateNonNegative frameRate && validateNonNegative rotationSpeed && validateNonNegative rotationSpeedVariance &&
       columns >= 1 && rows >= 1 && totalFrames >= 1 && frameRate > 0
      then return (SpriteConfig enabled mImageUrl isSheet columns rows totalFrames frameRate playMode billboard rotationEnabled rotationSpeed rotationSpeedVariance alignToVelocity)
      else fail "SpriteConfig: numeric values must be finite, non-negative, and within valid ranges"

-- ============================================================================
-- PARTICLE EMITTER CONFIG
-- ============================================================================

-- | Particle emitter config (very complex with many optional fields)
data ParticleEmitterConfig = ParticleEmitterConfig
  { particleEmitterConfigId :: Text
  , particleEmitterConfigName :: Text
  , particleEmitterConfigX :: Double
  , particleEmitterConfigY :: Double
  , particleEmitterConfigZ :: Maybe Double  -- Depth position
  , particleEmitterConfigDirection :: Double
  , particleEmitterConfigSpread :: Double
  , particleEmitterConfigSpeed :: Double
  , particleEmitterConfigSpeedVariance :: Double
  , particleEmitterConfigSize :: Double
  , particleEmitterConfigSizeVariance :: Double
  , particleEmitterConfigColor :: (Double, Double, Double)  -- RGB
  , particleEmitterConfigEmissionRate :: Double
  , particleEmitterConfigInitialBurst :: Double
  , particleEmitterConfigParticleLifetime :: Double
  , particleEmitterConfigLifetimeVariance :: Double
  , particleEmitterConfigEnabled :: Bool
  , particleEmitterConfigBurstOnBeat :: Bool
  , particleEmitterConfigBurstCount :: Double
  , particleEmitterConfigShape :: EmitterShape
  , particleEmitterConfigShapeRadius :: Double
  , particleEmitterConfigShapeWidth :: Double
  , particleEmitterConfigShapeHeight :: Double
  , particleEmitterConfigShapeDepth :: Double
  , particleEmitterConfigShapeInnerRadius :: Double
  , particleEmitterConfigEmitFromEdge :: Bool
  , particleEmitterConfigEmitFromVolume :: Bool
  , particleEmitterConfigSplinePath :: Maybe SplinePathEmission
  , particleEmitterConfigDepthMapEmission :: Maybe DepthMapEmission
  , particleEmitterConfigMaskEmission :: Maybe MaskEmission
  , particleEmitterConfigSprite :: SpriteConfig
  , particleEmitterConfigConeAngle :: Maybe Double
  , particleEmitterConfigConeRadius :: Maybe Double
  , particleEmitterConfigConeLength :: Maybe Double
  , particleEmitterConfigImageSourceLayerId :: Maybe Text
  , particleEmitterConfigEmissionThreshold :: Maybe Double
  , particleEmitterConfigEmitFromMaskEdge :: Maybe Bool
  , particleEmitterConfigDepthSourceLayerId :: Maybe Text
  , particleEmitterConfigDepthEdgeThreshold :: Maybe Double
  , particleEmitterConfigDepthScale :: Maybe Double
  , particleEmitterConfigLifespan :: Maybe Double
  , particleEmitterConfigStartSize :: Maybe Double
  , particleEmitterConfigEndSize :: Maybe Double
  , particleEmitterConfigStartColor :: Maybe Text
  , particleEmitterConfigEndColor :: Maybe Text
  , particleEmitterConfigStartOpacity :: Maybe Double
  , particleEmitterConfigEndOpacity :: Maybe Double
  , particleEmitterConfigVelocitySpread :: Maybe Double
  , particleEmitterConfigMeshVertices :: Maybe Value  -- Float32Array - stored as Value
  , particleEmitterConfigMeshNormals :: Maybe Value  -- Float32Array - stored as Value
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticleEmitterConfig where
  toJSON (ParticleEmitterConfig id_ name x y mZ direction spread speed speedVar size sizeVar (r, g, b) emissionRate initialBurst lifetime lifetimeVar enabled burstOnBeat burstCount shape shapeRadius shapeWidth shapeHeight shapeDepth shapeInnerRadius emitFromEdge emitFromVolume mSplinePath mDepthMap mMask sprite mConeAngle mConeRadius mConeLength mImageSource mEmissionThreshold mEmitFromMaskEdge mDepthSource mDepthEdgeThreshold mDepthScale mLifespan mStartSize mEndSize mStartColor mEndColor mStartOpacity mEndOpacity mVelocitySpread mMeshVertices mMeshNormals) =
    let
      baseFields = ["id" .= id_, "name" .= name, "x" .= x, "y" .= y, "direction" .= direction, "spread" .= spread, "speed" .= speed, "speedVariance" .= speedVar, "size" .= size, "sizeVariance" .= sizeVar, "color" .= [r, g, b], "emissionRate" .= emissionRate, "initialBurst" .= initialBurst, "particleLifetime" .= lifetime, "lifetimeVariance" .= lifetimeVar, "enabled" .= enabled, "burstOnBeat" .= burstOnBeat, "burstCount" .= burstCount, "shape" .= shape, "shapeRadius" .= shapeRadius, "shapeWidth" .= shapeWidth, "shapeHeight" .= shapeHeight, "shapeDepth" .= shapeDepth, "shapeInnerRadius" .= shapeInnerRadius, "emitFromEdge" .= emitFromEdge, "emitFromVolume" .= emitFromVolume, "sprite" .= sprite]
      f1 = case mZ of Just z -> ("z" .= z) : baseFields; Nothing -> baseFields
      f2 = case mSplinePath of Just p -> ("splinePath" .= p) : f1; Nothing -> f1
      f3 = case mDepthMap of Just d -> ("depthMapEmission" .= d) : f2; Nothing -> f2
      f4 = case mMask of Just m -> ("maskEmission" .= m) : f3; Nothing -> f3
      f5 = case mConeAngle of Just a -> ("coneAngle" .= a) : f4; Nothing -> f4
      f6 = case mConeRadius of Just r -> ("coneRadius" .= r) : f5; Nothing -> f5
      f7 = case mConeLength of Just l -> ("coneLength" .= l) : f6; Nothing -> f6
      f8 = case mImageSource of Just i -> ("imageSourceLayerId" .= i) : f7; Nothing -> f7
      f9 = case mEmissionThreshold of Just t -> ("emissionThreshold" .= t) : f8; Nothing -> f8
      f10 = case mEmitFromMaskEdge of Just e -> ("emitFromMaskEdge" .= e) : f9; Nothing -> f9
      f11 = case mDepthSource of Just d -> ("depthSourceLayerId" .= d) : f10; Nothing -> f10
      f12 = case mDepthEdgeThreshold of Just t -> ("depthEdgeThreshold" .= t) : f11; Nothing -> f11
      f13 = case mDepthScale of Just s -> ("depthScale" .= s) : f12; Nothing -> f12
      f14 = case mLifespan of Just l -> ("lifespan" .= l) : f13; Nothing -> f13
      f15 = case mStartSize of Just s -> ("startSize" .= s) : f14; Nothing -> f14
      f16 = case mEndSize of Just e -> ("endSize" .= e) : f15; Nothing -> f15
      f17 = case mStartColor of Just c -> ("startColor" .= c) : f16; Nothing -> f16
      f18 = case mEndColor of Just c -> ("endColor" .= c) : f17; Nothing -> f17
      f19 = case mStartOpacity of Just o -> ("startOpacity" .= o) : f18; Nothing -> f18
      f20 = case mEndOpacity of Just o -> ("endOpacity" .= o) : f19; Nothing -> f19
      f21 = case mVelocitySpread of Just v -> ("velocitySpread" .= v) : f20; Nothing -> f20
      f22 = case mMeshVertices of Just v -> ("meshVertices" .= v) : f21; Nothing -> f21
      f23 = case mMeshNormals of Just n -> ("meshNormals" .= n) : f22; Nothing -> f22
    in object f23

instance FromJSON ParticleEmitterConfig where
  parseJSON = withObject "ParticleEmitterConfig" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    x <- o .: "x"
    y <- o .: "y"
    mZ <- o .:? "z"
    direction <- o .: "direction"
    spread <- o .: "spread"
    speed <- o .: "speed"
    speedVar <- o .: "speedVariance"
    size <- o .: "size"
    sizeVar <- o .: "sizeVariance"
    colorArr <- o .: "color"
    (r, g, b) <- case colorArr of
      [r', g', b'] -> return (r', g', b')
      _ -> fail "ParticleEmitterConfig: color must be [r, g, b]"
    emissionRate <- o .: "emissionRate"
    initialBurst <- o .: "initialBurst"
    lifetime <- o .: "particleLifetime"
    lifetimeVar <- o .: "lifetimeVariance"
    enabled <- o .: "enabled"
    burstOnBeat <- o .: "burstOnBeat"
    burstCount <- o .: "burstCount"
    shape <- o .: "shape"
    shapeRadius <- o .: "shapeRadius"
    shapeWidth <- o .: "shapeWidth"
    shapeHeight <- o .: "shapeHeight"
    shapeDepth <- o .: "shapeDepth"
    shapeInnerRadius <- o .: "shapeInnerRadius"
    emitFromEdge <- o .: "emitFromEdge"
    emitFromVolume <- o .: "emitFromVolume"
    mSplinePath <- o .:? "splinePath"
    mDepthMap <- o .:? "depthMapEmission"
    mMask <- o .:? "maskEmission"
    sprite <- o .: "sprite"
    mConeAngle <- o .:? "coneAngle"
    mConeRadius <- o .:? "coneRadius"
    mConeLength <- o .:? "coneLength"
    mImageSource <- o .:? "imageSourceLayerId"
    mEmissionThreshold <- o .:? "emissionThreshold"
    mEmitFromMaskEdge <- o .:? "emitFromMaskEdge"
    mDepthSource <- o .:? "depthSourceLayerId"
    mDepthEdgeThreshold <- o .:? "depthEdgeThreshold"
    mDepthScale <- o .:? "depthScale"
    mLifespan <- o .:? "lifespan"
    mStartSize <- o .:? "startSize"
    mEndSize <- o .:? "endSize"
    mStartColor <- o .:? "startColor"
    mEndColor <- o .:? "endColor"
    mStartOpacity <- o .:? "startOpacity"
    mEndOpacity <- o .:? "endOpacity"
    mVelocitySpread <- o .:? "velocitySpread"
    mMeshVertices <- o .:? "meshVertices"
    mMeshNormals <- o .:? "meshNormals"
    -- Validate numeric values
    if validateFinite x && validateFinite y && validateFinite direction &&
       validateFinite spread && validateFinite speed && validateFinite speedVar &&
       validateFinite size && validateFinite sizeVar && validateFinite emissionRate &&
       validateFinite initialBurst && validateFinite lifetime && validateFinite lifetimeVar &&
       validateFinite burstCount && validateFinite shapeRadius && validateFinite shapeWidth &&
       validateFinite shapeHeight && validateFinite shapeDepth && validateFinite shapeInnerRadius &&
       validateNormalized01 r && validateNormalized01 g && validateNormalized01 b &&
       validateNonNegative speed && validateNonNegative size && validateNonNegative emissionRate &&
       validateNonNegative initialBurst && validateNonNegative lifetime && validateNonNegative burstCount &&
       validateNonNegative shapeRadius && validateNonNegative shapeWidth && validateNonNegative shapeHeight &&
       validateNonNegative shapeDepth && validateNonNegative shapeInnerRadius &&
       maybe True (\z -> validateFinite z) mZ &&
       maybe True (\a -> validateFinite a && validateNormalized01 a && a >= 0 && a <= 180) mConeAngle &&
       maybe True (\r -> validateFinite r && validateNonNegative r) mConeRadius &&
       maybe True (\l -> validateFinite l && validateNonNegative l) mConeLength &&
       maybe True (\t -> validateFinite t && validateNormalized01 t) mEmissionThreshold &&
       maybe True (\t -> validateFinite t && validateNonNegative t) mDepthEdgeThreshold &&
       maybe True (\s -> validateFinite s && validateNonNegative s) mDepthScale &&
       maybe True (\l -> validateFinite l && validateNonNegative l) mLifespan &&
       maybe True (\s -> validateFinite s && validateNonNegative s) mStartSize &&
       maybe True (\e -> validateFinite e && validateNonNegative e) mEndSize &&
       maybe True (\o -> validateFinite o && validateNormalized01 o) mStartOpacity &&
       maybe True (\o -> validateFinite o && validateNormalized01 o) mEndOpacity &&
       maybe True (\v -> validateFinite v && validateNonNegative v) mVelocitySpread
      then return (ParticleEmitterConfig id_ name x y mZ direction spread speed speedVar size sizeVar (r, g, b) emissionRate initialBurst lifetime lifetimeVar enabled burstOnBeat burstCount shape shapeRadius shapeWidth shapeHeight shapeDepth shapeInnerRadius emitFromEdge emitFromVolume mSplinePath mDepthMap mMask sprite mConeAngle mConeRadius mConeLength mImageSource mEmissionThreshold mEmitFromMaskEdge mDepthSource mDepthEdgeThreshold mDepthScale mLifespan mStartSize mEndSize mStartColor mEndColor mStartOpacity mEndOpacity mVelocitySpread mMeshVertices mMeshNormals)
      else fail "ParticleEmitterConfig: numeric values must be finite and within valid ranges"

-- ============================================================================
-- SYSTEM CONFIG
-- ============================================================================

-- | Particle system layer config
data ParticleSystemLayerConfig = ParticleSystemLayerConfig
  { particleSystemLayerConfigMaxParticles :: Double
  , particleSystemLayerConfigGravity :: Double
  , particleSystemLayerConfigWindStrength :: Double
  , particleSystemLayerConfigWindDirection :: Double
  , particleSystemLayerConfigWarmupPeriod :: Double
  , particleSystemLayerConfigRespectMaskBoundary :: Bool
  , particleSystemLayerConfigBoundaryBehavior :: ParticleBoundaryBehavior
  , particleSystemLayerConfigFriction :: Double
  , particleSystemLayerConfigTurbulenceFields :: Maybe [TurbulenceFieldConfig]
  , particleSystemLayerConfigSubEmitters :: Maybe [SubEmitterConfig]
  , particleSystemLayerConfigUseGPU :: Maybe Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticleSystemLayerConfig where
  toJSON (ParticleSystemLayerConfig maxParticles gravity windStrength windDirection warmupPeriod respectMask boundaryBehavior friction mTurbulenceFields mSubEmitters mUseGPU) =
    let
      baseFields = ["maxParticles" .= maxParticles, "gravity" .= gravity, "windStrength" .= windStrength, "windDirection" .= windDirection, "warmupPeriod" .= warmupPeriod, "respectMaskBoundary" .= respectMask, "boundaryBehavior" .= boundaryBehavior, "friction" .= friction]
      f1 = case mTurbulenceFields of Just t -> ("turbulenceFields" .= t) : baseFields; Nothing -> baseFields
      f2 = case mSubEmitters of Just s -> ("subEmitters" .= s) : f1; Nothing -> f1
      f3 = case mUseGPU of Just g -> ("useGPU" .= g) : f2; Nothing -> f2
    in object f3

instance FromJSON ParticleSystemLayerConfig where
  parseJSON = withObject "ParticleSystemLayerConfig" $ \o -> do
    maxParticles <- o .: "maxParticles"
    gravity <- o .: "gravity"
    windStrength <- o .: "windStrength"
    windDirection <- o .: "windDirection"
    warmupPeriod <- o .: "warmupPeriod"
    respectMask <- o .: "respectMaskBoundary"
    boundaryBehavior <- o .: "boundaryBehavior"
    friction <- o .: "friction"
    mTurbulenceFields <- o .:? "turbulenceFields"
    mSubEmitters <- o .:? "subEmitters"
    mUseGPU <- o .:? "useGPU"
    if validateFinite maxParticles && validateFinite gravity && validateFinite windStrength &&
       validateFinite windDirection && validateFinite warmupPeriod && validateFinite friction &&
       validateNonNegative maxParticles && validateNonNegative warmupPeriod && validateNormalized01 friction
      then return (ParticleSystemLayerConfig maxParticles gravity windStrength windDirection warmupPeriod respectMask boundaryBehavior friction mTurbulenceFields mSubEmitters mUseGPU)
      else fail "ParticleSystemLayerConfig: numeric values must be finite and within valid ranges"

-- ============================================================================
-- FORCE FIELDS
-- ============================================================================

-- | Gravity well config
data GravityWellConfig = GravityWellConfig
  { gravityWellConfigId :: Text
  , gravityWellConfigName :: Text
  , gravityWellConfigX :: Double
  , gravityWellConfigY :: Double
  , gravityWellConfigStrength :: Double
  , gravityWellConfigRadius :: Double
  , gravityWellConfigFalloff :: GravityWellFalloff
  , gravityWellConfigEnabled :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON GravityWellConfig where
  toJSON (GravityWellConfig id_ name x y strength radius falloff enabled) =
    object
      [ "id" .= id_
      , "name" .= name
      , "x" .= x
      , "y" .= y
      , "strength" .= strength
      , "radius" .= radius
      , "falloff" .= falloff
      , "enabled" .= enabled
      ]

instance FromJSON GravityWellConfig where
  parseJSON = withObject "GravityWellConfig" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    x <- o .: "x"
    y <- o .: "y"
    strength <- o .: "strength"
    radius <- o .: "radius"
    falloff <- o .: "falloff"
    enabled <- o .: "enabled"
    if validateFinite x && validateFinite y && validateFinite strength && validateFinite radius &&
       validateNonNegative radius && validateNonNegative strength
      then return (GravityWellConfig id_ name x y strength radius falloff enabled)
      else fail "GravityWellConfig: numeric values must be finite, radius and strength must be non-negative"

-- | Vortex config
data VortexConfig = VortexConfig
  { vortexConfigId :: Text
  , vortexConfigName :: Text
  , vortexConfigX :: Double
  , vortexConfigY :: Double
  , vortexConfigStrength :: Double
  , vortexConfigRadius :: Double
  , vortexConfigRotationSpeed :: Double
  , vortexConfigInwardPull :: Double
  , vortexConfigEnabled :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON VortexConfig where
  toJSON (VortexConfig id_ name x y strength radius rotationSpeed inwardPull enabled) =
    object
      [ "id" .= id_
      , "name" .= name
      , "x" .= x
      , "y" .= y
      , "strength" .= strength
      , "radius" .= radius
      , "rotationSpeed" .= rotationSpeed
      , "inwardPull" .= inwardPull
      , "enabled" .= enabled
      ]

instance FromJSON VortexConfig where
  parseJSON = withObject "VortexConfig" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    x <- o .: "x"
    y <- o .: "y"
    strength <- o .: "strength"
    radius <- o .: "radius"
    rotationSpeed <- o .: "rotationSpeed"
    inwardPull <- o .: "inwardPull"
    enabled <- o .: "enabled"
    if validateFinite x && validateFinite y && validateFinite strength && validateFinite radius &&
       validateFinite rotationSpeed && validateFinite inwardPull &&
       validateNonNegative radius && validateNonNegative strength
      then return (VortexConfig id_ name x y strength radius rotationSpeed inwardPull enabled)
      else fail "VortexConfig: numeric values must be finite, radius and strength must be non-negative"

-- ============================================================================
-- PHYSICS TYPES
-- ============================================================================

-- | Turbulence field config
data TurbulenceFieldConfig = TurbulenceFieldConfig
  { turbulenceFieldConfigId :: Text
  , turbulenceFieldConfigEnabled :: Bool
  , turbulenceFieldConfigScale :: Double  -- Noise frequency, 0.001-0.01
  , turbulenceFieldConfigStrength :: Double  -- Force magnitude, 0-500
  , turbulenceFieldConfigEvolutionSpeed :: Double  -- How fast noise changes over time, 0-1
  , turbulenceFieldConfigOctaves :: Maybe Double  -- Number of noise octaves (default: 1)
  , turbulenceFieldConfigPersistence :: Maybe Double  -- Amplitude multiplier per octave (default: 0.5)
  , turbulenceFieldConfigAnimationSpeed :: Maybe Double  -- Speed of noise evolution animation
  }
  deriving (Eq, Show, Generic)

instance ToJSON TurbulenceFieldConfig where
  toJSON (TurbulenceFieldConfig id_ enabled scale strength evolutionSpeed mOctaves mPersistence mAnimationSpeed) =
    let
      baseFields = ["id" .= id_, "enabled" .= enabled, "scale" .= scale, "strength" .= strength, "evolutionSpeed" .= evolutionSpeed]
      f1 = case mOctaves of Just o -> ("octaves" .= o) : baseFields; Nothing -> baseFields
      f2 = case mPersistence of Just p -> ("persistence" .= p) : f1; Nothing -> f1
      f3 = case mAnimationSpeed of Just a -> ("animationSpeed" .= a) : f2; Nothing -> f2
    in object f3

instance FromJSON TurbulenceFieldConfig where
  parseJSON = withObject "TurbulenceFieldConfig" $ \o -> do
    id_ <- o .: "id"
    enabled <- o .: "enabled"
    scale <- o .: "scale"
    strength <- o .: "strength"
    evolutionSpeed <- o .: "evolutionSpeed"
    mOctaves <- o .:? "octaves"
    mPersistence <- o .:? "persistence"
    mAnimationSpeed <- o .:? "animationSpeed"
    if validateFinite scale && validateFinite strength && validateFinite evolutionSpeed &&
       validateNonNegative scale && validateNonNegative strength && validateNormalized01 evolutionSpeed &&
       scale >= 0.001 && scale <= 0.01 && strength >= 0 && strength <= 500 &&
       maybe True (\o -> validateFinite o && validateNonNegative o && o >= 1) mOctaves &&
       maybe True (\p -> validateFinite p && validateNormalized01 p) mPersistence &&
       maybe True (\a -> validateFinite a && validateNonNegative a) mAnimationSpeed
      then return (TurbulenceFieldConfig id_ enabled scale strength evolutionSpeed mOctaves mPersistence mAnimationSpeed)
      else fail "TurbulenceFieldConfig: numeric values must be finite and within valid ranges"

-- | Flocking (boids) behavior configuration
data FlockingConfig = FlockingConfig
  { flockingConfigEnabled :: Bool
  , flockingConfigSeparationWeight :: Double  -- 0-100
  , flockingConfigSeparationRadius :: Double  -- Pixels
  , flockingConfigAlignmentWeight :: Double  -- 0-100
  , flockingConfigAlignmentRadius :: Double  -- Pixels
  , flockingConfigCohesionWeight :: Double  -- 0-100
  , flockingConfigCohesionRadius :: Double  -- Pixels
  , flockingConfigMaxSpeed :: Double  -- Maximum particle speed
  , flockingConfigMaxForce :: Double  -- Maximum steering force
  , flockingConfigPerceptionAngle :: Double  -- Field of view in degrees (180 = hemisphere)
  }
  deriving (Eq, Show, Generic)

instance ToJSON FlockingConfig where
  toJSON (FlockingConfig enabled sepWeight sepRadius alignWeight alignRadius cohesionWeight cohesionRadius maxSpeed maxForce perceptionAngle) =
    object
      [ "enabled" .= enabled
      , "separationWeight" .= sepWeight
      , "separationRadius" .= sepRadius
      , "alignmentWeight" .= alignWeight
      , "alignmentRadius" .= alignRadius
      , "cohesionWeight" .= cohesionWeight
      , "cohesionRadius" .= cohesionRadius
      , "maxSpeed" .= maxSpeed
      , "maxForce" .= maxForce
      , "perceptionAngle" .= perceptionAngle
      ]

instance FromJSON FlockingConfig where
  parseJSON = withObject "FlockingConfig" $ \o -> do
    enabled <- o .: "enabled"
    sepWeight <- o .: "separationWeight"
    sepRadius <- o .: "separationRadius"
    alignWeight <- o .: "alignmentWeight"
    alignRadius <- o .: "alignmentRadius"
    cohesionWeight <- o .: "cohesionWeight"
    cohesionRadius <- o .: "cohesionRadius"
    maxSpeed <- o .: "maxSpeed"
    maxForce <- o .: "maxForce"
    perceptionAngle <- o .: "perceptionAngle"
    if validateFinite sepWeight && validateFinite sepRadius && validateFinite alignWeight &&
       validateFinite alignRadius && validateFinite cohesionWeight && validateFinite cohesionRadius &&
       validateFinite maxSpeed && validateFinite maxForce && validateFinite perceptionAngle &&
       validateNormalized01 (sepWeight / 100) && validateNormalized01 (alignWeight / 100) &&
       validateNormalized01 (cohesionWeight / 100) && validateNonNegative sepRadius &&
       validateNonNegative alignRadius && validateNonNegative cohesionRadius &&
       validateNonNegative maxSpeed && validateNonNegative maxForce &&
       perceptionAngle >= 0 && perceptionAngle <= 180
      then return (FlockingConfig enabled sepWeight sepRadius alignWeight alignRadius cohesionWeight cohesionRadius maxSpeed maxForce perceptionAngle)
      else fail "FlockingConfig: numeric values must be finite and within valid ranges"

-- | Collision plane config
data CollisionPlaneConfig = CollisionPlaneConfig
  { collisionPlaneConfigId :: Text
  , collisionPlaneConfigName :: Maybe Text
  , collisionPlaneConfigEnabled :: Bool
  , collisionPlaneConfigPoint :: Vec3  -- A point on the plane
  , collisionPlaneConfigNormal :: Vec3  -- Plane normal (outward direction)
  , collisionPlaneConfigBounciness :: Double  -- 0-1
  , collisionPlaneConfigFriction :: Double  -- 0-1
  }
  deriving (Eq, Show, Generic)

instance ToJSON CollisionPlaneConfig where
  toJSON (CollisionPlaneConfig id_ mName enabled point normal bounciness friction) =
    let
      baseFields = ["id" .= id_, "enabled" .= enabled, "point" .= point, "normal" .= normal, "bounciness" .= bounciness, "friction" .= friction]
      withName = case mName of Just n -> ("name" .= n) : baseFields; Nothing -> baseFields
    in object withName

instance FromJSON CollisionPlaneConfig where
  parseJSON = withObject "CollisionPlaneConfig" $ \o -> do
    id_ <- o .: "id"
    mName <- o .:? "name"
    enabled <- o .: "enabled"
    point <- o .: "point"
    normal <- o .: "normal"
    bounciness <- o .: "bounciness"
    friction <- o .: "friction"
    if validateNormalized01 bounciness && validateNormalized01 friction
      then return (CollisionPlaneConfig id_ mName enabled point normal bounciness friction)
      else fail "CollisionPlaneConfig: bounciness and friction must be in [0,1]"

-- | Collision detection configuration
data CollisionConfig = CollisionConfig
  { collisionConfigEnabled :: Bool
  , collisionConfigParticleCollision :: Bool
  , collisionConfigParticleRadius :: Double
  , collisionConfigBounciness :: Double  -- 0-1
  , collisionConfigFriction :: Double  -- 0-1
  , collisionConfigBoundaryEnabled :: Bool
  , collisionConfigBoundaryBehavior :: CollisionBoundaryBehavior
  , collisionConfigBoundaryPadding :: Double  -- Pixels from edge
  , collisionConfigFloorEnabled :: Maybe Bool
  , collisionConfigFloorY :: Maybe Double  -- Normalized Y position (0=top, 1=bottom)
  , collisionConfigFloorBehavior :: Maybe CollisionBoundaryBehavior
  , collisionConfigFloorFriction :: Maybe Double  -- 0-1
  , collisionConfigCeilingEnabled :: Maybe Bool
  , collisionConfigCeilingY :: Maybe Double  -- Normalized Y position (0=top)
  , collisionConfigPlanes :: Maybe [CollisionPlaneConfig]
  }
  deriving (Eq, Show, Generic)

instance ToJSON CollisionConfig where
  toJSON (CollisionConfig enabled particleCollision particleRadius bounciness friction boundaryEnabled boundaryBehavior boundaryPadding mFloorEnabled mFloorY mFloorBehavior mFloorFriction mCeilingEnabled mCeilingY mPlanes) =
    let
      baseFields = ["enabled" .= enabled, "particleCollision" .= particleCollision, "particleRadius" .= particleRadius, "bounciness" .= bounciness, "friction" .= friction, "boundaryEnabled" .= boundaryEnabled, "boundaryBehavior" .= boundaryBehavior, "boundaryPadding" .= boundaryPadding]
      f1 = case mFloorEnabled of Just e -> ("floorEnabled" .= e) : baseFields; Nothing -> baseFields
      f2 = case mFloorY of Just y -> ("floorY" .= y) : f1; Nothing -> f1
      f3 = case mFloorBehavior of Just b -> ("floorBehavior" .= b) : f2; Nothing -> f2
      f4 = case mFloorFriction of Just f -> ("floorFriction" .= f) : f3; Nothing -> f3
      f5 = case mCeilingEnabled of Just e -> ("ceilingEnabled" .= e) : f4; Nothing -> f4
      f6 = case mCeilingY of Just y -> ("ceilingY" .= y) : f5; Nothing -> f5
      f7 = case mPlanes of Just p -> ("planes" .= p) : f6; Nothing -> f6
    in object f7

instance FromJSON CollisionConfig where
  parseJSON = withObject "CollisionConfig" $ \o -> do
    enabled <- o .: "enabled"
    particleCollision <- o .: "particleCollision"
    particleRadius <- o .: "particleRadius"
    bounciness <- o .: "bounciness"
    friction <- o .: "friction"
    boundaryEnabled <- o .: "boundaryEnabled"
    boundaryBehavior <- o .: "boundaryBehavior"
    boundaryPadding <- o .: "boundaryPadding"
    mFloorEnabled <- o .:? "floorEnabled"
    mFloorY <- o .:? "floorY"
    mFloorBehavior <- o .:? "floorBehavior"
    mFloorFriction <- o .:? "floorFriction"
    mCeilingEnabled <- o .:? "ceilingEnabled"
    mCeilingY <- o .:? "ceilingY"
    mPlanes <- o .:? "planes"
    if validateFinite particleRadius && validateNormalized01 bounciness && validateNormalized01 friction &&
       validateFinite boundaryPadding && validateNonNegative particleRadius && validateNonNegative boundaryPadding &&
       maybe True (\y -> validateFinite y && validateNormalized01 y) mFloorY &&
       maybe True (\f -> validateFinite f && validateNormalized01 f) mFloorFriction &&
       maybe True (\y -> validateFinite y && validateNormalized01 y) mCeilingY
      then return (CollisionConfig enabled particleCollision particleRadius bounciness friction boundaryEnabled boundaryBehavior boundaryPadding mFloorEnabled mFloorY mFloorBehavior mFloorFriction mCeilingEnabled mCeilingY mPlanes)
      else fail "CollisionConfig: numeric values must be finite and within valid ranges"

-- ============================================================================
-- RENDERING TYPES
-- ============================================================================

-- | Connection render config
data ConnectionRenderConfig = ConnectionRenderConfig
  { connectionRenderConfigEnabled :: Bool
  , connectionRenderConfigMaxDistance :: Double  -- Pixels
  , connectionRenderConfigMaxConnections :: Double  -- Per particle, 1-5
  , connectionRenderConfigLineWidth :: Double  -- 0.5-3
  , connectionRenderConfigLineOpacity :: Double  -- 0-1
  , connectionRenderConfigFadeByDistance :: Bool
  , connectionRenderConfigColor :: Maybe (Double, Double, Double)  -- Optional RGB color override (0-1 range)
  }
  deriving (Eq, Show, Generic)

instance ToJSON ConnectionRenderConfig where
  toJSON (ConnectionRenderConfig enabled maxDistance maxConnections lineWidth lineOpacity fadeByDistance mColor) =
    let
      baseFields = ["enabled" .= enabled, "maxDistance" .= maxDistance, "maxConnections" .= maxConnections, "lineWidth" .= lineWidth, "lineOpacity" .= lineOpacity, "fadeByDistance" .= fadeByDistance]
      withColor = case mColor of Just (r, g, b) -> ("color" .= [r, g, b]) : baseFields; Nothing -> baseFields
    in object withColor

instance FromJSON ConnectionRenderConfig where
  parseJSON = withObject "ConnectionRenderConfig" $ \o -> do
    enabled <- o .: "enabled"
    maxDistance <- o .: "maxDistance"
    maxConnections <- o .: "maxConnections"
    lineWidth <- o .: "lineWidth"
    lineOpacity <- o .: "lineOpacity"
    fadeByDistance <- o .: "fadeByDistance"
    mColorArr <- o .:? "color"
    mColor <- case mColorArr of
      Nothing -> return Nothing
      Just [r, g, b] -> return (Just (r, g, b))
      _ -> fail "ConnectionRenderConfig: color must be [r, g, b]"
    if validateFinite maxDistance && validateFinite maxConnections && validateFinite lineWidth &&
       validateFinite lineOpacity && validateNonNegative maxDistance &&
       maxConnections >= 1 && maxConnections <= 5 && lineWidth >= 0.5 && lineWidth <= 3 &&
       validateNormalized01 lineOpacity &&
       maybe True (\(r, g, b) -> validateNormalized01 r && validateNormalized01 g && validateNormalized01 b) mColor
      then return (ConnectionRenderConfig enabled maxDistance maxConnections lineWidth lineOpacity fadeByDistance mColor)
      else fail "ConnectionRenderConfig: numeric values must be finite and within valid ranges"

-- | Particle render options
data ParticleRenderOptions = ParticleRenderOptions
  { particleRenderOptionsBlendMode :: ParticleBlendMode
  , particleRenderOptionsRenderTrails :: Bool
  , particleRenderOptionsTrailLength :: Double
  , particleRenderOptionsTrailOpacityFalloff :: Double
  , particleRenderOptionsParticleShape :: ParticleShape
  , particleRenderOptionsGlowEnabled :: Bool
  , particleRenderOptionsGlowRadius :: Double
  , particleRenderOptionsGlowIntensity :: Double
  , particleRenderOptionsMotionBlur :: Bool
  , particleRenderOptionsMotionBlurStrength :: Double  -- 0-1
  , particleRenderOptionsMotionBlurSamples :: Double  -- 1-16
  , particleRenderOptionsConnections :: ConnectionRenderConfig
  , particleRenderOptionsSpriteEnabled :: Maybe Bool
  , particleRenderOptionsSpriteImageUrl :: Maybe Text
  , particleRenderOptionsSpriteColumns :: Maybe Double
  , particleRenderOptionsSpriteRows :: Maybe Double
  , particleRenderOptionsSpriteAnimate :: Maybe Bool
  , particleRenderOptionsSpriteFrameRate :: Maybe Double
  , particleRenderOptionsSpriteRandomStart :: Maybe Bool
  , particleRenderOptionsLODEnabled :: Maybe Bool
  , particleRenderOptionsLODDistances :: Maybe [Double]
  , particleRenderOptionsLODSizeMultipliers :: Maybe [Double]
  , particleRenderOptionsDOFEnabled :: Maybe Bool
  , particleRenderOptionsDOFFocusDistance :: Maybe Double
  , particleRenderOptionsDOFFocusRange :: Maybe Double
  , particleRenderOptionsDOFMaxBlur :: Maybe Double  -- 0-1
  , particleRenderOptionsShadowsEnabled :: Maybe Bool
  , particleRenderOptionsCastShadows :: Maybe Bool
  , particleRenderOptionsReceiveShadows :: Maybe Bool
  , particleRenderOptionsShadowSoftness :: Maybe Double
  , particleRenderOptionsMeshMode :: Maybe ParticleMeshMode
  , particleRenderOptionsMeshGeometry :: Maybe ParticleMeshGeometry
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticleRenderOptions where
  toJSON (ParticleRenderOptions blendMode renderTrails trailLength trailOpacityFalloff particleShape glowEnabled glowRadius glowIntensity motionBlur motionBlurStrength motionBlurSamples connections mSpriteEnabled mSpriteImageUrl mSpriteColumns mSpriteRows mSpriteAnimate mSpriteFrameRate mSpriteRandomStart mLODEnabled mLODDistances mLODSizeMultipliers mDOFEnabled mDOFFocusDistance mDOFFocusRange mDOFMaxBlur mShadowsEnabled mCastShadows mReceiveShadows mShadowSoftness mMeshMode mMeshGeometry) =
    let
      baseFields = ["blendMode" .= blendMode, "renderTrails" .= renderTrails, "trailLength" .= trailLength, "trailOpacityFalloff" .= trailOpacityFalloff, "particleShape" .= particleShape, "glowEnabled" .= glowEnabled, "glowRadius" .= glowRadius, "glowIntensity" .= glowIntensity, "motionBlur" .= motionBlur, "motionBlurStrength" .= motionBlurStrength, "motionBlurSamples" .= motionBlurSamples, "connections" .= connections]
      f1 = case mSpriteEnabled of Just e -> ("spriteEnabled" .= e) : baseFields; Nothing -> baseFields
      f2 = case mSpriteImageUrl of Just u -> ("spriteImageUrl" .= u) : f1; Nothing -> f1
      f3 = case mSpriteColumns of Just c -> ("spriteColumns" .= c) : f2; Nothing -> f2
      f4 = case mSpriteRows of Just r -> ("spriteRows" .= r) : f3; Nothing -> f3
      f5 = case mSpriteAnimate of Just a -> ("spriteAnimate" .= a) : f4; Nothing -> f4
      f6 = case mSpriteFrameRate of Just f -> ("spriteFrameRate" .= f) : f5; Nothing -> f5
      f7 = case mSpriteRandomStart of Just r -> ("spriteRandomStart" .= r) : f6; Nothing -> f6
      f8 = case mLODEnabled of Just e -> ("lodEnabled" .= e) : f7; Nothing -> f7
      f9 = case mLODDistances of Just d -> ("lodDistances" .= d) : f8; Nothing -> f8
      f10 = case mLODSizeMultipliers of Just m -> ("lodSizeMultipliers" .= m) : f9; Nothing -> f9
      f11 = case mDOFEnabled of Just e -> ("dofEnabled" .= e) : f10; Nothing -> f10
      f12 = case mDOFFocusDistance of Just d -> ("dofFocusDistance" .= d) : f11; Nothing -> f11
      f13 = case mDOFFocusRange of Just r -> ("dofFocusRange" .= r) : f12; Nothing -> f12
      f14 = case mDOFMaxBlur of Just b -> ("dofMaxBlur" .= b) : f13; Nothing -> f13
      f15 = case mShadowsEnabled of Just e -> ("shadowsEnabled" .= e) : f14; Nothing -> f14
      f16 = case mCastShadows of Just c -> ("castShadows" .= c) : f15; Nothing -> f15
      f17 = case mReceiveShadows of Just r -> ("receiveShadows" .= r) : f16; Nothing -> f16
      f18 = case mShadowSoftness of Just s -> ("shadowSoftness" .= s) : f17; Nothing -> f17
      f19 = case mMeshMode of Just m -> ("meshMode" .= m) : f18; Nothing -> f18
      f20 = case mMeshGeometry of Just g -> ("meshGeometry" .= g) : f19; Nothing -> f19
    in object f20

instance FromJSON ParticleRenderOptions where
  parseJSON = withObject "ParticleRenderOptions" $ \o -> do
    blendMode <- o .: "blendMode"
    renderTrails <- o .: "renderTrails"
    trailLength <- o .: "trailLength"
    trailOpacityFalloff <- o .: "trailOpacityFalloff"
    particleShape <- o .: "particleShape"
    glowEnabled <- o .: "glowEnabled"
    glowRadius <- o .: "glowRadius"
    glowIntensity <- o .: "glowIntensity"
    motionBlur <- o .: "motionBlur"
    motionBlurStrength <- o .: "motionBlurStrength"
    motionBlurSamples <- o .: "motionBlurSamples"
    connections <- o .: "connections"
    mSpriteEnabled <- o .:? "spriteEnabled"
    mSpriteImageUrl <- o .:? "spriteImageUrl"
    mSpriteColumns <- o .:? "spriteColumns"
    mSpriteRows <- o .:? "spriteRows"
    mSpriteAnimate <- o .:? "spriteAnimate"
    mSpriteFrameRate <- o .:? "spriteFrameRate"
    mSpriteRandomStart <- o .:? "spriteRandomStart"
    mLODEnabled <- o .:? "lodEnabled"
    mLODDistances <- o .:? "lodDistances"
    mLODSizeMultipliers <- o .:? "lodSizeMultipliers"
    mDOFEnabled <- o .:? "dofEnabled"
    mDOFFocusDistance <- o .:? "dofFocusDistance"
    mDOFFocusRange <- o .:? "dofFocusRange"
    mDOFMaxBlur <- o .:? "dofMaxBlur"
    mShadowsEnabled <- o .:? "shadowsEnabled"
    mCastShadows <- o .:? "castShadows"
    mReceiveShadows <- o .:? "receiveShadows"
    mShadowSoftness <- o .:? "shadowSoftness"
    mMeshMode <- o .:? "meshMode"
    mMeshGeometry <- o .:? "meshGeometry"
    if validateFinite trailLength && validateFinite trailOpacityFalloff && validateFinite glowRadius &&
       validateFinite glowIntensity && validateFinite motionBlurStrength && validateFinite motionBlurSamples &&
       validateNonNegative trailLength && validateNormalized01 trailOpacityFalloff &&
       validateNonNegative glowRadius && validateNonNegative glowIntensity &&
       validateNormalized01 motionBlurStrength && motionBlurSamples >= 1 && motionBlurSamples <= 16 &&
       maybe True (\c -> validateFinite c && validateNonNegative c && c >= 1) mSpriteColumns &&
       maybe True (\r -> validateFinite r && validateNonNegative r && r >= 1) mSpriteRows &&
       maybe True (\f -> validateFinite f && validateNonNegative f && f > 0) mSpriteFrameRate &&
       maybe True (\d -> all (\dist -> validateFinite dist && validateNonNegative dist) d) mLODDistances &&
       maybe True (\m -> all (\mult -> validateFinite mult && validateNonNegative mult) m) mLODSizeMultipliers &&
       maybe True (\d -> validateFinite d && validateNonNegative d) mDOFFocusDistance &&
       maybe True (\r -> validateFinite r && validateNonNegative r) mDOFFocusRange &&
       maybe True (\b -> validateFinite b && validateNormalized01 b) mDOFMaxBlur &&
       maybe True (\s -> validateFinite s && validateNonNegative s) mShadowSoftness
      then return (ParticleRenderOptions blendMode renderTrails trailLength trailOpacityFalloff particleShape glowEnabled glowRadius glowIntensity motionBlur motionBlurStrength motionBlurSamples connections mSpriteEnabled mSpriteImageUrl mSpriteColumns mSpriteRows mSpriteAnimate mSpriteFrameRate mSpriteRandomStart mLODEnabled mLODDistances mLODSizeMultipliers mDOFEnabled mDOFFocusDistance mDOFFocusRange mDOFMaxBlur mShadowsEnabled mCastShadows mReceiveShadows mShadowSoftness mMeshMode mMeshGeometry)
      else fail "ParticleRenderOptions: numeric values must be finite and within valid ranges"

-- ============================================================================
-- ADVANCED FEATURES
-- ============================================================================

-- | Spring structure
data SpringStructure = SpringStructure
  { springStructureId :: Text
  , springStructureType :: SpringStructureType
  , springStructureWidth :: Maybe Double  -- Cloth-specific: Particles in X
  , springStructureHeight :: Maybe Double  -- Cloth-specific: Particles in Y
  , springStructureLength :: Maybe Double  -- Rope-specific: Number of particles
  , springStructureStartParticle :: Double
  , springStructurePinnedParticles :: [Double]  -- Indices of fixed particles
  , springStructureStiffness :: Double
  , springStructureDamping :: Double
  , springStructureBreakThreshold :: Double  -- 0 = unbreakable
  }
  deriving (Eq, Show, Generic)

instance ToJSON SpringStructure where
  toJSON (SpringStructure id_ sType mWidth mHeight mLength startParticle pinnedParticles stiffness damping breakThreshold) =
    let
      baseFields = ["id" .= id_, "type" .= sType, "startParticle" .= startParticle, "pinnedParticles" .= pinnedParticles, "stiffness" .= stiffness, "damping" .= damping, "breakThreshold" .= breakThreshold]
      f1 = case mWidth of Just w -> ("width" .= w) : baseFields; Nothing -> baseFields
      f2 = case mHeight of Just h -> ("height" .= h) : f1; Nothing -> f1
      f3 = case mLength of Just l -> ("length" .= l) : f2; Nothing -> f2
    in object f3

instance FromJSON SpringStructure where
  parseJSON = withObject "SpringStructure" $ \o -> do
    id_ <- o .: "id"
    sType <- o .: "type"
    mWidth <- o .:? "width"
    mHeight <- o .:? "height"
    mLength <- o .:? "length"
    startParticle <- o .: "startParticle"
    pinnedParticles <- o .: "pinnedParticles"
    stiffness <- o .: "stiffness"
    damping <- o .: "damping"
    breakThreshold <- o .: "breakThreshold"
    if validateFinite startParticle && validateFinite stiffness && validateFinite damping &&
       validateFinite breakThreshold && validateNonNegative startParticle &&
       validateNonNegative stiffness && validateNonNegative damping && validateNonNegative breakThreshold &&
       stiffness >= 0.001 && stiffness <= 10000 && damping >= 0 && damping <= 1000 &&
       maybe True (\w -> validateFinite w && validateNonNegative w && w >= 1) mWidth &&
       maybe True (\h -> validateFinite h && validateNonNegative h && h >= 1) mHeight &&
       maybe True (\l -> validateFinite l && validateNonNegative l && l >= 1) mLength &&
       all (\p -> validateFinite p && validateNonNegative p) pinnedParticles
      then return (SpringStructure id_ sType mWidth mHeight mLength startParticle pinnedParticles stiffness damping breakThreshold)
      else fail "SpringStructure: numeric values must be finite and within valid ranges"

-- | Spring system config
data SpringSystemConfig = SpringSystemConfig
  { springSystemConfigEnabled :: Bool
  , springSystemConfigUseVerlet :: Bool  -- Verlet integration (more stable) vs Euler
  , springSystemConfigSolverIterations :: Double  -- 1-16
  , springSystemConfigGlobalStiffness :: Double  -- 0.001-10000
  , springSystemConfigGlobalDamping :: Double  -- 0-1000
  , springSystemConfigEnableBreaking :: Bool
  , springSystemConfigGravity :: Vec3
  , springSystemConfigStructures :: Maybe [SpringStructure]
  }
  deriving (Eq, Show, Generic)

instance ToJSON SpringSystemConfig where
  toJSON (SpringSystemConfig enabled useVerlet solverIterations globalStiffness globalDamping enableBreaking gravity mStructures) =
    let
      baseFields = ["enabled" .= enabled, "useVerlet" .= useVerlet, "solverIterations" .= solverIterations, "globalStiffness" .= globalStiffness, "globalDamping" .= globalDamping, "enableBreaking" .= enableBreaking, "gravity" .= gravity]
      withStructures = case mStructures of Just s -> ("structures" .= s) : baseFields; Nothing -> baseFields
    in object withStructures

instance FromJSON SpringSystemConfig where
  parseJSON = withObject "SpringSystemConfig" $ \o -> do
    enabled <- o .: "enabled"
    useVerlet <- o .: "useVerlet"
    solverIterations <- o .: "solverIterations"
    globalStiffness <- o .: "globalStiffness"
    globalDamping <- o .: "globalDamping"
    enableBreaking <- o .: "enableBreaking"
    gravity <- o .: "gravity"
    mStructures <- o .:? "structures"
    if validateFinite solverIterations && validateFinite globalStiffness && validateFinite globalDamping &&
       solverIterations >= 1 && solverIterations <= 16 &&
       globalStiffness >= 0.001 && globalStiffness <= 10000 &&
       globalDamping >= 0 && globalDamping <= 1000
      then return (SpringSystemConfig enabled useVerlet solverIterations globalStiffness globalDamping enableBreaking gravity mStructures)
      else fail "SpringSystemConfig: numeric values must be finite and within valid ranges"

-- | SPH fluid config
data SPHFluidConfig = SPHFluidConfig
  { sphFluidConfigEnabled :: Bool
  , sphFluidConfigPreset :: SPHFluidPreset
  , sphFluidConfigSmoothingRadius :: Double  -- h, affects neighbor search
  , sphFluidConfigRestDensity :: Double  -- ρ₀, fluid rest density
  , sphFluidConfigGasConstant :: Double  -- k, pressure stiffness
  , sphFluidConfigViscosity :: Double  -- μ, how "thick" the fluid is
  , sphFluidConfigSurfaceTension :: Double  -- σ, surface cohesion
  , sphFluidConfigGravity :: Vec3
  , sphFluidConfigBoundaryDamping :: Double  -- Energy loss at boundaries
  }
  deriving (Eq, Show, Generic)

instance ToJSON SPHFluidConfig where
  toJSON (SPHFluidConfig enabled preset smoothingRadius restDensity gasConstant viscosity surfaceTension gravity boundaryDamping) =
    object
      [ "enabled" .= enabled
      , "preset" .= preset
      , "smoothingRadius" .= smoothingRadius
      , "restDensity" .= restDensity
      , "gasConstant" .= gasConstant
      , "viscosity" .= viscosity
      , "surfaceTension" .= surfaceTension
      , "gravity" .= gravity
      , "boundaryDamping" .= boundaryDamping
      ]

instance FromJSON SPHFluidConfig where
  parseJSON = withObject "SPHFluidConfig" $ \o -> do
    enabled <- o .: "enabled"
    preset <- o .: "preset"
    smoothingRadius <- o .: "smoothingRadius"
    restDensity <- o .: "restDensity"
    gasConstant <- o .: "gasConstant"
    viscosity <- o .: "viscosity"
    surfaceTension <- o .: "surfaceTension"
    gravity <- o .: "gravity"
    boundaryDamping <- o .: "boundaryDamping"
    if validateFinite smoothingRadius && validateFinite restDensity && validateFinite gasConstant &&
       validateFinite viscosity && validateFinite surfaceTension && validateFinite boundaryDamping &&
       validateNonNegative smoothingRadius && validateNonNegative restDensity &&
       validateNonNegative gasConstant && validateNonNegative viscosity &&
       validateNonNegative surfaceTension && validateNormalized01 boundaryDamping
      then return (SPHFluidConfig enabled preset smoothingRadius restDensity gasConstant viscosity surfaceTension gravity boundaryDamping)
      else fail "SPHFluidConfig: numeric values must be finite and within valid ranges"

-- ============================================================================
-- AUDIO TYPES
-- ============================================================================

-- | Audio binding config
data AudioBindingConfig = AudioBindingConfig
  { audioBindingConfigId :: Text
  , audioBindingConfigEnabled :: Bool
  , audioBindingConfigFeature :: AudioFeatureName
  , audioBindingConfigSmoothing :: Double  -- 0-1
  , audioBindingConfigMin :: Double  -- Feature value mapping input min
  , audioBindingConfigMax :: Double  -- Feature value mapping input max
  , audioBindingConfigTarget :: AudioTargetType
  , audioBindingConfigTargetId :: Text
  , audioBindingConfigParameter :: Text
  , audioBindingConfigOutputMin :: Double
  , audioBindingConfigOutputMax :: Double
  , audioBindingConfigCurve :: AudioCurveType
  , audioBindingConfigStepCount :: Maybe Double  -- Number of discrete steps for 'step' curve (default: 5)
  , audioBindingConfigTriggerMode :: Maybe AudioTriggerMode
  , audioBindingConfigThreshold :: Maybe Double  -- Threshold value for 'onThreshold' mode (0-1)
  }
  deriving (Eq, Show, Generic)

instance ToJSON AudioBindingConfig where
  toJSON (AudioBindingConfig id_ enabled feature smoothing min_ max_ target targetId parameter outputMin outputMax curve mStepCount mTriggerMode mThreshold) =
    let
      baseFields = ["id" .= id_, "enabled" .= enabled, "feature" .= feature, "smoothing" .= smoothing, "min" .= min_, "max" .= max_, "target" .= target, "targetId" .= targetId, "parameter" .= parameter, "outputMin" .= outputMin, "outputMax" .= outputMax, "curve" .= curve]
      f1 = case mStepCount of Just s -> ("stepCount" .= s) : baseFields; Nothing -> baseFields
      f2 = case mTriggerMode of Just t -> ("triggerMode" .= t) : f1; Nothing -> f1
      f3 = case mThreshold of Just th -> ("threshold" .= th) : f2; Nothing -> f2
    in object f3

instance FromJSON AudioBindingConfig where
  parseJSON = withObject "AudioBindingConfig" $ \o -> do
    id_ <- o .: "id"
    enabled <- o .: "enabled"
    feature <- o .: "feature"
    smoothing <- o .: "smoothing"
    min_ <- o .: "min"
    max_ <- o .: "max"
    target <- o .: "target"
    targetId <- o .: "targetId"
    parameter <- o .: "parameter"
    outputMin <- o .: "outputMin"
    outputMax <- o .: "outputMax"
    curve <- o .: "curve"
    mStepCount <- o .:? "stepCount"
    mTriggerMode <- o .:? "triggerMode"
    mThreshold <- o .:? "threshold"
    if validateNormalized01 smoothing && validateFinite min_ && validateFinite max_ &&
       validateFinite outputMin && validateFinite outputMax && min_ <= max_ &&
       outputMin <= outputMax &&
       maybe True (\s -> validateFinite s && validateNonNegative s && s >= 1) mStepCount &&
       maybe True (\t -> validateFinite t && validateNormalized01 t) mThreshold
      then return (AudioBindingConfig id_ enabled feature smoothing min_ max_ target targetId parameter outputMin outputMax curve mStepCount mTriggerMode mThreshold)
      else fail "AudioBindingConfig: numeric values must be finite and within valid ranges"

-- | Audio particle mapping
data AudioParticleMapping = AudioParticleMapping
  { audioParticleMappingFeature :: Text  -- "amplitude" | "rms" | "bass" | "mid" | "high" | "onsets"
  , audioParticleMappingParameter :: Text  -- "emissionRate" | "speed" | "size" | "gravity" | "windStrength"
  , audioParticleMappingEmitterId :: Maybe Text
  , audioParticleMappingSensitivity :: Double
  , audioParticleMappingSmoothing :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON AudioParticleMapping where
  toJSON (AudioParticleMapping feature parameter mEmitterId sensitivity smoothing) =
    let
      baseFields = ["feature" .= feature, "parameter" .= parameter, "sensitivity" .= sensitivity, "smoothing" .= smoothing]
      withEmitterId = case mEmitterId of Just id -> ("emitterId" .= id) : baseFields; Nothing -> baseFields
    in object withEmitterId

instance FromJSON AudioParticleMapping where
  parseJSON = withObject "AudioParticleMapping" $ \o -> do
    feature <- o .: "feature"
    parameter <- o .: "parameter"
    mEmitterId <- o .:? "emitterId"
    sensitivity <- o .: "sensitivity"
    smoothing <- o .: "smoothing"
    if validateFinite sensitivity && validateFinite smoothing &&
       validateNonNegative sensitivity && validateNormalized01 smoothing
      then return (AudioParticleMapping feature parameter mEmitterId sensitivity smoothing)
      else fail "AudioParticleMapping: sensitivity and smoothing must be finite and within valid ranges"

-- ============================================================================
-- SUB-EMITTERS AND MODULATION
-- ============================================================================

-- | Sub-emitter config
data SubEmitterConfig = SubEmitterConfig
  { subEmitterConfigId :: Text
  , subEmitterConfigParentEmitterId :: Text  -- Which emitter's particles trigger this, or '*' for all
  , subEmitterConfigTrigger :: SubEmitterTrigger
  , subEmitterConfigSpawnCount :: Double  -- 1-10 particles on trigger
  , subEmitterConfigInheritVelocity :: Double  -- 0-1
  , subEmitterConfigSize :: Double
  , subEmitterConfigSizeVariance :: Double
  , subEmitterConfigLifetime :: Double  -- Frames
  , subEmitterConfigSpeed :: Double
  , subEmitterConfigSpread :: Double  -- Degrees
  , subEmitterConfigColor :: (Double, Double, Double)  -- RGB
  , subEmitterConfigEnabled :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON SubEmitterConfig where
  toJSON (SubEmitterConfig id_ parentEmitterId trigger spawnCount inheritVelocity size sizeVariance lifetime speed spread (r, g, b) enabled) =
    object
      [ "id" .= id_
      , "parentEmitterId" .= parentEmitterId
      , "trigger" .= trigger
      , "spawnCount" .= spawnCount
      , "inheritVelocity" .= inheritVelocity
      , "size" .= size
      , "sizeVariance" .= sizeVariance
      , "lifetime" .= lifetime
      , "speed" .= speed
      , "spread" .= spread
      , "color" .= [r, g, b]
      , "enabled" .= enabled
      ]

instance FromJSON SubEmitterConfig where
  parseJSON = withObject "SubEmitterConfig" $ \o -> do
    id_ <- o .: "id"
    parentEmitterId <- o .: "parentEmitterId"
    trigger <- o .: "trigger"
    spawnCount <- o .: "spawnCount"
    inheritVelocity <- o .: "inheritVelocity"
    size <- o .: "size"
    sizeVariance <- o .: "sizeVariance"
    lifetime <- o .: "lifetime"
    speed <- o .: "speed"
    spread <- o .: "spread"
    colorArr <- o .: "color"
    (r, g, b) <- case colorArr of
      [r', g', b'] -> return (r', g', b')
      _ -> fail "SubEmitterConfig: color must be [r, g, b]"
    enabled <- o .: "enabled"
    if validateFinite spawnCount && validateFinite inheritVelocity && validateFinite size &&
       validateFinite sizeVariance && validateFinite lifetime && validateFinite speed &&
       validateFinite spread && validateNormalized01 r && validateNormalized01 g && validateNormalized01 b &&
       validateNormalized01 inheritVelocity && spawnCount >= 1 && spawnCount <= 10 &&
       validateNonNegative size && validateNormalized01 sizeVariance &&
       validateNonNegative lifetime && validateNonNegative speed && validateNonNegative spread
      then return (SubEmitterConfig id_ parentEmitterId trigger spawnCount inheritVelocity size sizeVariance lifetime speed spread (r, g, b) enabled)
      else fail "SubEmitterConfig: numeric values must be finite and within valid ranges"

-- | Particle modulation config
data ParticleModulationConfig = ParticleModulationConfig
  { particleModulationConfigId :: Text
  , particleModulationConfigEmitterId :: Text
  , particleModulationConfigProperty :: ParticleModulationProperty
  , particleModulationConfigStartValue :: Double
  , particleModulationConfigEndValue :: Double
  , particleModulationConfigEasing :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticleModulationConfig where
  toJSON (ParticleModulationConfig id_ emitterId property startValue endValue easing) =
    object
      [ "id" .= id_
      , "emitterId" .= emitterId
      , "property" .= property
      , "startValue" .= startValue
      , "endValue" .= endValue
      , "easing" .= easing
      ]

instance FromJSON ParticleModulationConfig where
  parseJSON = withObject "ParticleModulationConfig" $ \o -> do
    id_ <- o .: "id"
    emitterId <- o .: "emitterId"
    property <- o .: "property"
    startValue <- o .: "startValue"
    endValue <- o .: "endValue"
    easing <- o .: "easing"
    if validateFinite startValue && validateFinite endValue
      then return (ParticleModulationConfig id_ emitterId property startValue endValue easing)
      else fail "ParticleModulationConfig: startValue and endValue must be finite"

-- ============================================================================
-- MAIN PARTICLE LAYER DATA
-- ============================================================================

-- | Particle layer data
data ParticleLayerData = ParticleLayerData
  { particleLayerDataSystemConfig :: ParticleSystemLayerConfig
  , particleLayerDataEmitters :: [ParticleEmitterConfig]
  , particleLayerDataGravityWells :: [GravityWellConfig]
  , particleLayerDataVortices :: [VortexConfig]
  , particleLayerDataModulations :: Maybe [ParticleModulationConfig]
  , particleLayerDataRenderOptions :: ParticleRenderOptions
  , particleLayerDataTurbulenceFields :: Maybe [TurbulenceFieldConfig]
  , particleLayerDataSubEmitters :: Maybe [SubEmitterConfig]
  , particleLayerDataFlocking :: Maybe FlockingConfig
  , particleLayerDataCollision :: Maybe CollisionConfig
  , particleLayerDataAudioBindings :: Maybe [AudioBindingConfig]
  , particleLayerDataAudioMappings :: Maybe [AudioParticleMapping]
  , particleLayerDataExportEnabled :: Maybe Bool
  , particleLayerDataExportFormat :: Maybe Text
  , particleLayerDataSpeedMapEnabled :: Maybe Bool
  , particleLayerDataSpeedMap :: Maybe (AnimatableProperty Double)
  , particleLayerDataVisualization :: Maybe ParticleVisualizationConfig
  , particleLayerDataGroups :: Maybe [ParticleGroupConfig]
  , particleLayerDataSpringConfig :: Maybe SpringSystemConfig
  , particleLayerDataSPHConfig :: Maybe SPHFluidConfig
  , particleLayerDataLODConfig :: Maybe ParticleLODConfig
  , particleLayerDataDOFConfig :: Maybe ParticleDOFConfig
  , particleLayerDataCollisionPlanes :: Maybe [CollisionPlaneConfig]
  , particleLayerDataParticleGroups :: Maybe [ParticleGroupConfig]
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticleLayerData where
  toJSON (ParticleLayerData systemConfig emitters gravityWells vortices mModulations renderOptions mTurbulenceFields mSubEmitters mFlocking mCollision mAudioBindings mAudioMappings mExportEnabled mExportFormat mSpeedMapEnabled mSpeedMap mVisualization mGroups mSpringConfig mSPHConfig mLODConfig mDOFConfig mCollisionPlanes mParticleGroups) =
    let
      baseFields = ["systemConfig" .= systemConfig, "emitters" .= emitters, "gravityWells" .= gravityWells, "vortices" .= vortices, "renderOptions" .= renderOptions]
      f1 = case mModulations of Just m -> ("modulations" .= m) : baseFields; Nothing -> baseFields
      f2 = case mTurbulenceFields of Just t -> ("turbulenceFields" .= t) : f1; Nothing -> f1
      f3 = case mSubEmitters of Just s -> ("subEmitters" .= s) : f2; Nothing -> f2
      f4 = case mFlocking of Just f -> ("flocking" .= f) : f3; Nothing -> f3
      f5 = case mCollision of Just c -> ("collision" .= c) : f4; Nothing -> f4
      f6 = case mAudioBindings of Just a -> ("audioBindings" .= a) : f5; Nothing -> f5
      f7 = case mAudioMappings of Just a -> ("audioMappings" .= a) : f6; Nothing -> f6
      f8 = case mExportEnabled of Just e -> ("exportEnabled" .= e) : f7; Nothing -> f7
      f9 = case mExportFormat of Just f -> ("exportFormat" .= f) : f8; Nothing -> f8
      f10 = case mSpeedMapEnabled of Just e -> ("speedMapEnabled" .= e) : f9; Nothing -> f9
      f11 = case mSpeedMap of Just s -> ("speedMap" .= s) : f10; Nothing -> f10
      f12 = case mVisualization of Just v -> ("visualization" .= v) : f11; Nothing -> f11
      f13 = case mGroups of Just g -> ("groups" .= g) : f12; Nothing -> f12
      f14 = case mSpringConfig of Just s -> ("springConfig" .= s) : f13; Nothing -> f13
      f15 = case mSPHConfig of Just s -> ("sphConfig" .= s) : f14; Nothing -> f14
      f16 = case mLODConfig of Just l -> ("lodConfig" .= l) : f15; Nothing -> f15
      f17 = case mDOFConfig of Just d -> ("dofConfig" .= d) : f16; Nothing -> f16
      f18 = case mCollisionPlanes of Just c -> ("collisionPlanes" .= c) : f17; Nothing -> f17
      f19 = case mParticleGroups of Just p -> ("particleGroups" .= p) : f18; Nothing -> f18
    in object f19

instance FromJSON ParticleLayerData where
  parseJSON = withObject "ParticleLayerData" $ \o -> do
    systemConfig <- o .: "systemConfig"
    emitters <- o .: "emitters"
    gravityWells <- o .: "gravityWells"
    vortices <- o .: "vortices"
    mModulations <- o .:? "modulations"
    renderOptions <- o .: "renderOptions"
    mTurbulenceFields <- o .:? "turbulenceFields"
    mSubEmitters <- o .:? "subEmitters"
    mFlocking <- o .:? "flocking"
    mCollision <- o .:? "collision"
    mAudioBindings <- o .:? "audioBindings"
    mAudioMappings <- o .:? "audioMappings"
    mExportEnabled <- o .:? "exportEnabled"
    mExportFormat <- o .:? "exportFormat"
    mSpeedMapEnabled <- o .:? "speedMapEnabled"
    mSpeedMap <- o .:? "speedMap"
    mVisualization <- o .:? "visualization"
    mGroups <- o .:? "groups"
    mSpringConfig <- o .:? "springConfig"
    mSPHConfig <- o .:? "sphConfig"
    mLODConfig <- o .:? "lodConfig"
    mDOFConfig <- o .:? "dofConfig"
    mCollisionPlanes <- o .:? "collisionPlanes"
    mParticleGroups <- o .:? "particleGroups"
    return (ParticleLayerData systemConfig emitters gravityWells vortices mModulations renderOptions mTurbulenceFields mSubEmitters mFlocking mCollision mAudioBindings mAudioMappings mExportEnabled mExportFormat mSpeedMapEnabled mSpeedMap mVisualization mGroups mSpringConfig mSPHConfig mLODConfig mDOFConfig mCollisionPlanes mParticleGroups)

