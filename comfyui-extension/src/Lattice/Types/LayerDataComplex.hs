-- |
-- Module      : Lattice.Types.LayerDataComplex
-- Description : Complex layer data types with AnimatableProperty dependencies
-- 
-- Migrated from ui/src/types/project.ts
-- These types use AnimatableProperty extensively
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.LayerDataComplex
  ( -- Generated map
    GeneratedMapData(..)
  , GeneratedMapType(..)
  -- Procedural matte
  , ProceduralMatteData(..)
  , ProceduralMatteType(..)
  , ProceduralMatteParams(..)
  , ProceduralMatteAnimation(..)
  , ProceduralMatteLevels(..)
  -- Depthflow
  , DepthflowLayerData(..)
  , DepthflowPreset(..)
  , DepthflowConfig(..)
  , CameraToDepthflowConfig(..)
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
  ( validateFinite
  , validateNonNegative
  )

-- ============================================================================
-- GENERATED MAP DATA
-- ============================================================================

-- | Generated map type
data GeneratedMapType
  = GeneratedMapTypeDepth  -- DepthAnything V3
  | GeneratedMapTypeNormal  -- NormalCrafter
  | GeneratedMapTypeEdge  -- Canny/HED
  | GeneratedMapTypePose  -- DWPose/OpenPose
  | GeneratedMapTypeSegment  -- SAM2/MatSeg
  | GeneratedMapTypeLineart  -- Lineart extraction
  | GeneratedMapTypeSoftedge  -- Soft edge detection
  deriving (Eq, Show, Generic)

instance ToJSON GeneratedMapType where
  toJSON GeneratedMapTypeDepth = "depth"
  toJSON GeneratedMapTypeNormal = "normal"
  toJSON GeneratedMapTypeEdge = "edge"
  toJSON GeneratedMapTypePose = "pose"
  toJSON GeneratedMapTypeSegment = "segment"
  toJSON GeneratedMapTypeLineart = "lineart"
  toJSON GeneratedMapTypeSoftedge = "softedge"

instance FromJSON GeneratedMapType where
  parseJSON = withText "GeneratedMapType" $ \s ->
    case s of
      "depth" -> return GeneratedMapTypeDepth
      "normal" -> return GeneratedMapTypeNormal
      "edge" -> return GeneratedMapTypeEdge
      "pose" -> return GeneratedMapTypePose
      "segment" -> return GeneratedMapTypeSegment
      "lineart" -> return GeneratedMapTypeLineart
      "softedge" -> return GeneratedMapTypeSoftedge
      _ -> fail "Invalid GeneratedMapType"

-- | Generated map data - AI-powered layer generation
data GeneratedMapData = GeneratedMapData
  { generatedMapDataSourceLayerId :: Text  -- Which layer to generate from
  , generatedMapDataMapType :: GeneratedMapType
  , generatedMapDataModelId :: Text  -- Which model to use
  , generatedMapDataParameters :: Value  -- Generation parameters (model-specific) - JSON object
  , generatedMapDataCachedResult :: Maybe Text  -- Base64 cached output
  , generatedMapDataLastGenerated :: Maybe Text  -- ISO timestamp
  }
  deriving (Eq, Show, Generic)

instance ToJSON GeneratedMapData where
  toJSON (GeneratedMapData sourceLayerId mapType modelId params mCachedResult mLastGen) =
    let
      baseFields = ["sourceLayerId" .= sourceLayerId, "mapType" .= mapType, "modelId" .= modelId, "parameters" .= params]
      withCachedResult = case mCachedResult of Just c -> ("cachedResult" .= c) : baseFields; Nothing -> baseFields
      withLastGen = case mLastGen of Just l -> ("lastGenerated" .= l) : withCachedResult; Nothing -> withCachedResult
    in object withLastGen

instance FromJSON GeneratedMapData where
  parseJSON = withObject "GeneratedMapData" $ \o -> do
    sourceLayerId <- o .: "sourceLayerId"
    mapType <- o .: "mapType"
    modelId <- o .: "modelId"
    params <- o .: "parameters"
    mCachedResult <- o .:? "cachedResult"
    mLastGen <- o .:? "lastGenerated"
    return (GeneratedMapData sourceLayerId mapType modelId params mCachedResult mLastGen)

-- ============================================================================
-- PROCEDURAL MATTE DATA
-- ============================================================================

-- | Procedural matte type
data ProceduralMatteType
  = ProceduralMatteLinearGradient
  | ProceduralMatteRadialGradient
  | ProceduralMatteAngularGradient
  | ProceduralMatteRamp
  | ProceduralMatteNoise
  | ProceduralMatteCheckerboard
  | ProceduralMatteCircle
  | ProceduralMatteRectangle
  | ProceduralMatteGrid
  | ProceduralMatteWave
  | ProceduralMatteVenetianBlinds
  | ProceduralMatteIris
  | ProceduralMatteRadialWipe
  | ProceduralMatteDissolve
  deriving (Eq, Show, Generic)

instance ToJSON ProceduralMatteType where
  toJSON ProceduralMatteLinearGradient = "linear_gradient"
  toJSON ProceduralMatteRadialGradient = "radial_gradient"
  toJSON ProceduralMatteAngularGradient = "angular_gradient"
  toJSON ProceduralMatteRamp = "ramp"
  toJSON ProceduralMatteNoise = "noise"
  toJSON ProceduralMatteCheckerboard = "checkerboard"
  toJSON ProceduralMatteCircle = "circle"
  toJSON ProceduralMatteRectangle = "rectangle"
  toJSON ProceduralMatteGrid = "grid"
  toJSON ProceduralMatteWave = "wave"
  toJSON ProceduralMatteVenetianBlinds = "venetian_blinds"
  toJSON ProceduralMatteIris = "iris"
  toJSON ProceduralMatteRadialWipe = "radial_wipe"
  toJSON ProceduralMatteDissolve = "dissolve"

instance FromJSON ProceduralMatteType where
  parseJSON = withText "ProceduralMatteType" $ \s ->
    case s of
      "linear_gradient" -> return ProceduralMatteLinearGradient
      "radial_gradient" -> return ProceduralMatteRadialGradient
      "angular_gradient" -> return ProceduralMatteAngularGradient
      "ramp" -> return ProceduralMatteRamp
      "noise" -> return ProceduralMatteNoise
      "checkerboard" -> return ProceduralMatteCheckerboard
      "circle" -> return ProceduralMatteCircle
      "rectangle" -> return ProceduralMatteRectangle
      "grid" -> return ProceduralMatteGrid
      "wave" -> return ProceduralMatteWave
      "venetian_blinds" -> return ProceduralMatteVenetianBlinds
      "iris" -> return ProceduralMatteIris
      "radial_wipe" -> return ProceduralMatteRadialWipe
      "dissolve" -> return ProceduralMatteDissolve
      _ -> fail "Invalid ProceduralMatteType"

-- | Procedural matte animation settings
data ProceduralMatteAnimation = ProceduralMatteAnimation
  { proceduralMatteAnimationEnabled :: Bool  -- Enable animation
  , proceduralMatteAnimationSpeed :: AnimatableProperty Double  -- Animation speed multiplier
  , proceduralMatteAnimationPhase :: AnimatableProperty Double  -- Animation phase offset (0-1)
  , proceduralMatteAnimationDirection :: AnimatableProperty Double  -- Animation direction (for gradients/wipes) - Degrees
  }
  deriving (Eq, Show, Generic)

instance ToJSON ProceduralMatteAnimation where
  toJSON (ProceduralMatteAnimation enabled speed phase direction) =
    object
      [ "enabled" .= enabled
      , "speed" .= speed
      , "phase" .= phase
      , "direction" .= direction
      ]

instance FromJSON ProceduralMatteAnimation where
  parseJSON = withObject "ProceduralMatteAnimation" $ \o -> do
    enabled <- o .: "enabled"
    speed <- o .: "speed"
    phase <- o .: "phase"
    direction <- o .: "direction"
    return (ProceduralMatteAnimation enabled speed phase direction)

-- | Procedural matte levels (output levels)
data ProceduralMatteLevels = ProceduralMatteLevels
  { proceduralMatteLevelsInputBlack :: AnimatableProperty Double  -- 0-255
  , proceduralMatteLevelsInputWhite :: AnimatableProperty Double  -- 0-255
  , proceduralMatteLevelsGamma :: AnimatableProperty Double  -- 0.1-10
  , proceduralMatteLevelsOutputBlack :: AnimatableProperty Double  -- 0-255
  , proceduralMatteLevelsOutputWhite :: AnimatableProperty Double  -- 0-255
  }
  deriving (Eq, Show, Generic)

instance ToJSON ProceduralMatteLevels where
  toJSON (ProceduralMatteLevels inputBlack inputWhite gamma outputBlack outputWhite) =
    object
      [ "inputBlack" .= inputBlack
      , "inputWhite" .= inputWhite
      , "gamma" .= gamma
      , "outputBlack" .= outputBlack
      , "outputWhite" .= outputWhite
      ]

instance FromJSON ProceduralMatteLevels where
  parseJSON = withObject "ProceduralMatteLevels" $ \o -> do
    inputBlack <- o .: "inputBlack"
    inputWhite <- o .: "inputWhite"
    gamma <- o .: "gamma"
    outputBlack <- o .: "outputBlack"
    outputWhite <- o .: "outputWhite"
    return (ProceduralMatteLevels inputBlack inputWhite gamma outputBlack outputWhite)

-- | Procedural matte parameters (varies by pattern type)
-- Note: Many fields are optional depending on pattern type
data ProceduralMatteParams = ProceduralMatteParams
  { proceduralMatteParamsAngle :: Maybe (AnimatableProperty Double)  -- Direction in degrees (Linear/Angular gradient)
  , proceduralMatteParamsBlend :: Maybe (AnimatableProperty Double)  -- Blend width (0-1)
  , proceduralMatteParamsCenterX :: Maybe (AnimatableProperty Double)  -- Center X (0-1) (Radial gradient)
  , proceduralMatteParamsCenterY :: Maybe (AnimatableProperty Double)  -- Center Y (0-1)
  , proceduralMatteParamsRadius :: Maybe (AnimatableProperty Double)  -- Radius (0-2)
  , proceduralMatteParamsProgress :: Maybe (AnimatableProperty Double)  -- Wipe progress (0-1) (Ramp/Wipe)
  , proceduralMatteParamsSoftness :: Maybe (AnimatableProperty Double)  -- Edge softness
  , proceduralMatteParamsScale :: Maybe (AnimatableProperty Double)  -- Noise scale
  , proceduralMatteParamsOctaves :: Maybe Double  -- Fractal octaves (1-8)
  , proceduralMatteParamsPersistence :: Maybe Double  -- Fractal persistence
  , proceduralMatteParamsLacunarity :: Maybe Double  -- Fractal lacunarity
  , proceduralMatteParamsSeed :: Maybe Double  -- Random seed
  , proceduralMatteParamsTilesX :: Maybe (AnimatableProperty Double)  -- Horizontal tiles (Checkerboard/Grid)
  , proceduralMatteParamsTilesY :: Maybe (AnimatableProperty Double)  -- Vertical tiles
  , proceduralMatteParamsRotation :: Maybe (AnimatableProperty Double)  -- Pattern rotation
  , proceduralMatteParamsWidth :: Maybe (AnimatableProperty Double)  -- Shape width (Circle/Rectangle)
  , proceduralMatteParamsHeight :: Maybe (AnimatableProperty Double)  -- Shape height
  , proceduralMatteParamsCornerRadius :: Maybe (AnimatableProperty Double)  -- Corner radius
  , proceduralMatteParamsFrequency :: Maybe (AnimatableProperty Double)  -- Wave frequency
  , proceduralMatteParamsAmplitude :: Maybe (AnimatableProperty Double)  -- Wave amplitude
  , proceduralMatteParamsWaveType :: Maybe Text  -- "sine" | "triangle" | "square" | "sawtooth"
  , proceduralMatteParamsSlats :: Maybe (AnimatableProperty Double)  -- Number of slats (Venetian blinds)
  , proceduralMatteParamsFeather :: Maybe (AnimatableProperty Double)  -- Edge feather (Iris)
  , proceduralMatteParamsRandomness :: Maybe (AnimatableProperty Double)  -- Dissolve randomness
  , proceduralMatteParamsBlockSize :: Maybe (AnimatableProperty Double)  -- Dissolve block size
  }
  deriving (Eq, Show, Generic)

instance ToJSON ProceduralMatteParams where
  toJSON (ProceduralMatteParams angle blend centerX centerY radius progress softness scale octaves persistence lacunarity seed tilesX tilesY rotation width height cornerRadius frequency amplitude waveType slats feather randomness blockSize) =
    let
      baseFields = []
      f1 = case angle of Just a -> ("angle" .= a) : baseFields; Nothing -> baseFields
      f2 = case blend of Just b -> ("blend" .= b) : f1; Nothing -> f1
      f3 = case centerX of Just x -> ("centerX" .= x) : f2; Nothing -> f2
      f4 = case centerY of Just y -> ("centerY" .= y) : f3; Nothing -> f3
      f5 = case radius of Just r -> ("radius" .= r) : f4; Nothing -> f4
      f6 = case progress of Just p -> ("progress" .= p) : f5; Nothing -> f5
      f7 = case softness of Just s -> ("softness" .= s) : f6; Nothing -> f6
      f8 = case scale of Just sc -> ("scale" .= sc) : f7; Nothing -> f7
      f9 = case octaves of Just o -> ("octaves" .= o) : f8; Nothing -> f8
      f10 = case persistence of Just p -> ("persistence" .= p) : f9; Nothing -> f9
      f11 = case lacunarity of Just l -> ("lacunarity" .= l) : f10; Nothing -> f10
      f12 = case seed of Just se -> ("seed" .= se) : f11; Nothing -> f11
      f13 = case tilesX of Just tx -> ("tilesX" .= tx) : f12; Nothing -> f12
      f14 = case tilesY of Just ty -> ("tilesY" .= ty) : f13; Nothing -> f13
      f15 = case rotation of Just rot -> ("rotation" .= rot) : f14; Nothing -> f14
      f16 = case width of Just w -> ("width" .= w) : f15; Nothing -> f15
      f17 = case height of Just h -> ("height" .= h) : f16; Nothing -> f16
      f18 = case cornerRadius of Just cr -> ("cornerRadius" .= cr) : f17; Nothing -> f17
      f19 = case frequency of Just f -> ("frequency" .= f) : f18; Nothing -> f18
      f20 = case amplitude of Just a -> ("amplitude" .= a) : f19; Nothing -> f19
      f21 = case waveType of Just wt -> ("waveType" .= wt) : f20; Nothing -> f20
      f22 = case slats of Just sl -> ("slats" .= sl) : f21; Nothing -> f21
      f23 = case feather of Just fe -> ("feather" .= fe) : f22; Nothing -> f22
      f24 = case randomness of Just r -> ("randomness" .= r) : f23; Nothing -> f23
      f25 = case blockSize of Just bs -> ("blockSize" .= bs) : f24; Nothing -> f24
    in object f25

instance FromJSON ProceduralMatteParams where
  parseJSON = withObject "ProceduralMatteParams" $ \o -> do
    angle <- o .:? "angle"
    blend <- o .:? "blend"
    centerX <- o .:? "centerX"
    centerY <- o .:? "centerY"
    radius <- o .:? "radius"
    progress <- o .:? "progress"
    softness <- o .:? "softness"
    scale <- o .:? "scale"
    octaves <- o .:? "octaves"
    persistence <- o .:? "persistence"
    lacunarity <- o .:? "lacunarity"
    seed <- o .:? "seed"
    tilesX <- o .:? "tilesX"
    tilesY <- o .:? "tilesY"
    rotation <- o .:? "rotation"
    width <- o .:? "width"
    height <- o .:? "height"
    cornerRadius <- o .:? "cornerRadius"
    frequency <- o .:? "frequency"
    amplitude <- o .:? "amplitude"
    waveType <- o .:? "waveType"
    slats <- o .:? "slats"
    feather <- o .:? "feather"
    randomness <- o .:? "randomness"
    blockSize <- o .:? "blockSize"
    -- Validate numeric values if present
    case octaves of
      Nothing -> return ()
      Just o -> if validateFinite o && o >= 1 && o <= 8
        then return ()
        else fail "ProceduralMatteParams: octaves must be 1-8"
    case persistence of
      Nothing -> return ()
      Just p -> if validateFinite p && validateNonNegative p
        then return ()
        else fail "ProceduralMatteParams: persistence must be finite and non-negative"
    case lacunarity of
      Nothing -> return ()
      Just l -> if validateFinite l && validateNonNegative l
        then return ()
        else fail "ProceduralMatteParams: lacunarity must be finite and non-negative"
    case seed of
      Nothing -> return ()
      Just s -> if validateFinite s && validateNonNegative s
        then return ()
        else fail "ProceduralMatteParams: seed must be finite and non-negative"
    return (ProceduralMatteParams angle blend centerX centerY radius progress softness scale octaves persistence lacunarity seed tilesX tilesY rotation width height cornerRadius frequency amplitude waveType slats feather randomness blockSize)

-- | Procedural matte data - generates animated patterns
-- Useful for creating track mattes without additional assets
data ProceduralMatteData = ProceduralMatteData
  { proceduralMatteDataPatternType :: ProceduralMatteType  -- Pattern type
  , proceduralMatteDataParameters :: ProceduralMatteParams  -- Pattern-specific parameters
  , proceduralMatteDataAnimation :: ProceduralMatteAnimation  -- Animation settings
  , proceduralMatteDataInverted :: Bool  -- Invert the output (swap black/white)
  , proceduralMatteDataLevels :: ProceduralMatteLevels  -- Output levels (min/max black/white)
  }
  deriving (Eq, Show, Generic)

instance ToJSON ProceduralMatteData where
  toJSON (ProceduralMatteData patternType params animation inverted levels) =
    object
      [ "patternType" .= patternType
      , "parameters" .= params
      , "animation" .= animation
      , "inverted" .= inverted
      , "levels" .= levels
      ]

instance FromJSON ProceduralMatteData where
  parseJSON = withObject "ProceduralMatteData" $ \o -> do
    patternType <- o .: "patternType"
    params <- o .: "parameters"
    animation <- o .: "animation"
    inverted <- o .: "inverted"
    levels <- o .: "levels"
    return (ProceduralMatteData patternType params animation inverted levels)

-- ============================================================================
-- DEPTHFLOW LAYER DATA
-- ============================================================================

-- | Depthflow preset
data DepthflowPreset
  = DepthflowPresetStatic
  | DepthflowPresetZoomIn
  | DepthflowPresetZoomOut
  | DepthflowPresetDollyZoomIn
  | DepthflowPresetDollyZoomOut
  | DepthflowPresetPanLeft
  | DepthflowPresetPanRight
  | DepthflowPresetPanUp
  | DepthflowPresetPanDown
  | DepthflowPresetCircleCW
  | DepthflowPresetCircleCCW
  | DepthflowPresetHorizontalSwing
  | DepthflowPresetVerticalSwing
  | DepthflowPresetCustom
  deriving (Eq, Show, Generic)

instance ToJSON DepthflowPreset where
  toJSON DepthflowPresetStatic = "static"
  toJSON DepthflowPresetZoomIn = "zoom_in"
  toJSON DepthflowPresetZoomOut = "zoom_out"
  toJSON DepthflowPresetDollyZoomIn = "dolly_zoom_in"
  toJSON DepthflowPresetDollyZoomOut = "dolly_zoom_out"
  toJSON DepthflowPresetPanLeft = "pan_left"
  toJSON DepthflowPresetPanRight = "pan_right"
  toJSON DepthflowPresetPanUp = "pan_up"
  toJSON DepthflowPresetPanDown = "pan_down"
  toJSON DepthflowPresetCircleCW = "circle_cw"
  toJSON DepthflowPresetCircleCCW = "circle_ccw"
  toJSON DepthflowPresetHorizontalSwing = "horizontal_swing"
  toJSON DepthflowPresetVerticalSwing = "vertical_swing"
  toJSON DepthflowPresetCustom = "custom"

instance FromJSON DepthflowPreset where
  parseJSON = withText "DepthflowPreset" $ \s ->
    case s of
      "static" -> return DepthflowPresetStatic
      "zoom_in" -> return DepthflowPresetZoomIn
      "zoom_out" -> return DepthflowPresetZoomOut
      "dolly_zoom_in" -> return DepthflowPresetDollyZoomIn
      "dolly_zoom_out" -> return DepthflowPresetDollyZoomOut
      "pan_left" -> return DepthflowPresetPanLeft
      "pan_right" -> return DepthflowPresetPanRight
      "pan_up" -> return DepthflowPresetPanUp
      "pan_down" -> return DepthflowPresetPanDown
      "circle_cw" -> return DepthflowPresetCircleCW
      "circle_ccw" -> return DepthflowPresetCircleCCW
      "horizontal_swing" -> return DepthflowPresetHorizontalSwing
      "vertical_swing" -> return DepthflowPresetVerticalSwing
      "custom" -> return DepthflowPresetCustom
      _ -> fail "Invalid DepthflowPreset"

-- | Depthflow config
data DepthflowConfig = DepthflowConfig
  { depthflowConfigPreset :: DepthflowPreset
  , depthflowConfigZoom :: Double
  , depthflowConfigOffsetX :: Double
  , depthflowConfigOffsetY :: Double
  , depthflowConfigRotation :: Double
  , depthflowConfigDepthScale :: Double
  , depthflowConfigFocusDepth :: Double
  , depthflowConfigDollyZoom :: Double
  , depthflowConfigOrbitRadius :: Double
  , depthflowConfigOrbitSpeed :: Double
  , depthflowConfigSwingAmplitude :: Double
  , depthflowConfigSwingFrequency :: Double
  , depthflowConfigEdgeDilation :: Double
  , depthflowConfigInpaintEdges :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON DepthflowConfig where
  toJSON (DepthflowConfig preset zoom offsetX offsetY rotation depthScale focusDepth dollyZoom orbitRadius orbitSpeed swingAmp swingFreq edgeDilation inpaintEdges) =
    object
      [ "preset" .= preset
      , "zoom" .= zoom
      , "offsetX" .= offsetX
      , "offsetY" .= offsetY
      , "rotation" .= rotation
      , "depthScale" .= depthScale
      , "focusDepth" .= focusDepth
      , "dollyZoom" .= dollyZoom
      , "orbitRadius" .= orbitRadius
      , "orbitSpeed" .= orbitSpeed
      , "swingAmplitude" .= swingAmp
      , "swingFrequency" .= swingFreq
      , "edgeDilation" .= edgeDilation
      , "inpaintEdges" .= inpaintEdges
      ]

instance FromJSON DepthflowConfig where
  parseJSON = withObject "DepthflowConfig" $ \o -> do
    preset <- o .: "preset"
    zoom <- o .: "zoom"
    offsetX <- o .: "offsetX"
    offsetY <- o .: "offsetY"
    rotation <- o .: "rotation"
    depthScale <- o .: "depthScale"
    focusDepth <- o .: "focusDepth"
    dollyZoom <- o .: "dollyZoom"
    orbitRadius <- o .: "orbitRadius"
    orbitSpeed <- o .: "orbitSpeed"
    swingAmp <- o .: "swingAmplitude"
    swingFreq <- o .: "swingFrequency"
    edgeDilation <- o .: "edgeDilation"
    inpaintEdges <- o .: "inpaintEdges"
    -- Validate numeric values
    if validateFinite zoom && validateFinite offsetX &&
       validateFinite offsetY && validateFinite rotation &&
       validateFinite depthScale && validateFinite focusDepth &&
       validateFinite dollyZoom && validateFinite orbitRadius &&
       validateFinite orbitSpeed && validateFinite swingAmp &&
       validateFinite swingFreq && validateFinite edgeDilation &&
       validateNonNegative focusDepth && validateNonNegative edgeDilation
      then return (DepthflowConfig preset zoom offsetX offsetY rotation depthScale focusDepth dollyZoom orbitRadius orbitSpeed swingAmp swingFreq edgeDilation inpaintEdges)
      else fail "DepthflowConfig: numeric values must be finite, focusDepth and edgeDilation must be non-negative"

-- | Camera → Depthflow sync configuration
data CameraToDepthflowConfig = CameraToDepthflowConfig
  { cameraToDepthflowConfigSensitivityX :: Double
  , cameraToDepthflowConfigSensitivityY :: Double
  , cameraToDepthflowConfigSensitivityZ :: Double
  , cameraToDepthflowConfigSensitivityRotation :: Double
  , cameraToDepthflowConfigBaseZoom :: Double
  , cameraToDepthflowConfigInvertX :: Bool
  , cameraToDepthflowConfigInvertY :: Bool
  , cameraToDepthflowConfigZoomClamp :: (Double, Double)  -- min, max
  , cameraToDepthflowConfigOffsetClamp :: (Double, Double)  -- min, max
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraToDepthflowConfig where
  toJSON (CameraToDepthflowConfig sensX sensY sensZ sensRot baseZoom invertX invertY zoomClamp offsetClamp) =
    object
      [ "sensitivityX" .= sensX
      , "sensitivityY" .= sensY
      , "sensitivityZ" .= sensZ
      , "sensitivityRotation" .= sensRot
      , "baseZoom" .= baseZoom
      , "invertX" .= invertX
      , "invertY" .= invertY
      , "zoomClamp" .= object ["min" .= fst zoomClamp, "max" .= snd zoomClamp]
      , "offsetClamp" .= object ["min" .= fst offsetClamp, "max" .= snd offsetClamp]
      ]

instance FromJSON CameraToDepthflowConfig where
  parseJSON = withObject "CameraToDepthflowConfig" $ \o -> do
    sensX <- o .: "sensitivityX"
    sensY <- o .: "sensitivityY"
    sensZ <- o .: "sensitivityZ"
    sensRot <- o .: "sensitivityRotation"
    baseZoom <- o .: "baseZoom"
    invertX <- o .: "invertX"
    invertY <- o .: "invertY"
    zoomClampObj <- o .: "zoomClamp"
    offsetClampObj <- o .: "offsetClamp"
    zoomMin <- zoomClampObj .: "min"
    zoomMax <- zoomClampObj .: "max"
    offsetMin <- offsetClampObj .: "min"
    offsetMax <- offsetClampObj .: "max"
    -- Validate numeric values
    if validateFinite sensX && validateFinite sensY &&
       validateFinite sensZ && validateFinite sensRot &&
       validateFinite baseZoom && validateFinite zoomMin &&
       validateFinite zoomMax && validateFinite offsetMin &&
       validateFinite offsetMax && zoomMin <= zoomMax &&
       offsetMin <= offsetMax
      then return (CameraToDepthflowConfig sensX sensY sensZ sensRot baseZoom invertX invertY (zoomMin, zoomMax) (offsetMin, offsetMax))
      else fail "CameraToDepthflowConfig: numeric values must be finite, clampD ranges must be valid"

-- | Depthflow layer data - parallax layer (matching akatz-ai)
data DepthflowLayerData = DepthflowLayerData
  { depthflowLayerDataSourceLayerId :: Maybe Text  -- CODE IS TRUTH - defaults create null
  , depthflowLayerDataDepthLayerId :: Maybe Text  -- CODE IS TRUTH - defaults create null
  , depthflowLayerDataConfig :: DepthflowConfig
  , depthflowLayerDataAnimatedZoom :: Maybe (AnimatableProperty Double)
  , depthflowLayerDataAnimatedOffsetX :: Maybe (AnimatableProperty Double)
  , depthflowLayerDataAnimatedOffsetY :: Maybe (AnimatableProperty Double)
  , depthflowLayerDataAnimatedRotation :: Maybe (AnimatableProperty Double)
  , depthflowLayerDataAnimatedDepthScale :: Maybe (AnimatableProperty Double)
  , depthflowLayerDataCameraSyncEnabled :: Maybe Bool  -- Camera sync - drives depthflow from 3D camera motion
  , depthflowLayerDataCameraSyncLayerId :: Maybe Text  -- ID of the camera layer to sync from
  , depthflowLayerDataCameraSyncConfig :: Maybe CameraToDepthflowConfig
  }
  deriving (Eq, Show, Generic)

instance ToJSON DepthflowLayerData where
  toJSON (DepthflowLayerData mSourceLayerId mDepthLayerId config mZoom mOffsetX mOffsetY mRotation mDepthScale mCameraSyncEnabled mCameraSyncLayerId mCameraSyncConfig) =
    let
      baseFields = ["config" .= config]
      f1 = case mSourceLayerId of Just s -> ("sourceLayerId" .= s) : baseFields; Nothing -> baseFields
      f2 = case mDepthLayerId of Just d -> ("depthLayerId" .= d) : f1; Nothing -> f1
      f3 = case mZoom of Just z -> ("animatedZoom" .= z) : f2; Nothing -> f2
      f4 = case mOffsetX of Just x -> ("animatedOffsetX" .= x) : f3; Nothing -> f3
      f5 = case mOffsetY of Just y -> ("animatedOffsetY" .= y) : f4; Nothing -> f4
      f6 = case mRotation of Just r -> ("animatedRotation" .= r) : f5; Nothing -> f5
      f7 = case mDepthScale of Just ds -> ("animatedDepthScale" .= ds) : f6; Nothing -> f6
      f8 = case mCameraSyncEnabled of Just c -> ("cameraSyncEnabled" .= c) : f7; Nothing -> f7
      f9 = case mCameraSyncLayerId of Just l -> ("cameraSyncLayerId" .= l) : f8; Nothing -> f8
      f10 = case mCameraSyncConfig of Just cfg -> ("cameraSyncConfig" .= cfg) : f9; Nothing -> f9
    in object f10

instance FromJSON DepthflowLayerData where
  parseJSON = withObject "DepthflowLayerData" $ \o -> do
    mSourceLayerId <- o .:? "sourceLayerId"
    mDepthLayerId <- o .:? "depthLayerId"
    config <- o .: "config"
    mZoom <- o .:? "animatedZoom"
    mOffsetX <- o .:? "animatedOffsetX"
    mOffsetY <- o .:? "animatedOffsetY"
    mRotation <- o .:? "animatedRotation"
    mDepthScale <- o .:? "animatedDepthScale"
    mCameraSyncEnabled <- o .:? "cameraSyncEnabled"
    mCameraSyncLayerId <- o .:? "cameraSyncLayerId"
    mCameraSyncConfig <- o .:? "cameraSyncConfig"
    return (DepthflowLayerData mSourceLayerId mDepthLayerId config mZoom mOffsetX mOffsetY mRotation mDepthScale mCameraSyncEnabled mCameraSyncLayerId mCameraSyncConfig)
