-- |
-- Module      : Lattice.Types.LayerDataAsset
-- Description : Asset-based layer data types (Image, Video, Audio)
-- 
-- Migrated from ui/src/types/project.ts
-- These types depend on AssetReference (assetId field)
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.LayerDataAsset
  ( -- Image layer
    ImageLayerData(..)
  , ImageFit(..)
  , ImageSourceType(..)
  , CropRect(..)
  -- Audio layer
  , AudioLayerData(..)
  , AudioMarker(..)
  -- Video layer
  , VideoData(..)
  , TimewarpMethod(..)
  , FrameBlending(..)
  -- Depth layer
  , DepthLayerData(..)
  , DepthVisualizationMode(..)
  , DepthColorMap(..)
  -- Normal layer
  , NormalLayerData(..)
  , NormalVisualizationMode(..)
  , NormalFormat(..)
  -- Nested comp layer
  , NestedCompData(..)
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
  ( Vec3(..)
  , validateFinite
  , validateNonNegative
  )

-- ============================================================================
-- IMAGE LAYER DATA
-- ============================================================================

-- | Image fit mode
data ImageFit
  = ImageFitNone
  | ImageFitContain
  | ImageFitCover
  | ImageFitFill
  deriving (Eq, Show, Generic)

instance ToJSON ImageFit where
  toJSON ImageFitNone = "none"
  toJSON ImageFitContain = "contain"
  toJSON ImageFitCover = "cover"
  toJSON ImageFitFill = "fill"

instance FromJSON ImageFit where
  parseJSON = withText "ImageFit" $ \s ->
    case s of
      "none" -> return ImageFitNone
      "contain" -> return ImageFitContain
      "cover" -> return ImageFitCover
      "fill" -> return ImageFitFill
      _ -> fail "Invalid ImageFit"

-- | Image source type
data ImageSourceType
  = ImageSourceFile
  | ImageSourceGenerated
  | ImageSourceSegmented
  | ImageSourceInline
  deriving (Eq, Show, Generic)

instance ToJSON ImageSourceType where
  toJSON ImageSourceFile = "file"
  toJSON ImageSourceGenerated = "generated"
  toJSON ImageSourceSegmented = "segmented"
  toJSON ImageSourceInline = "inline"

instance FromJSON ImageSourceType where
  parseJSON = withText "ImageSourceType" $ \s ->
    case s of
      "file" -> return ImageSourceFile
      "generated" -> return ImageSourceGenerated
      "segmented" -> return ImageSourceSegmented
      "inline" -> return ImageSourceInline
      _ -> fail "Invalid ImageSourceType"

-- | Crop rectangle
data CropRect = CropRect
  { cropRectX :: Double
  , cropRectY :: Double
  , cropRectWidth :: Double
  , cropRectHeight :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON CropRect where
  toJSON (CropRect x y w h) =
    object ["x" .= x, "y" .= y, "width" .= w, "height" .= h]

instance FromJSON CropRect where
  parseJSON = withObject "CropRect" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    w <- o .: "width"
    h <- o .: "height"
    if validateFinite x && validateFinite y &&
       validateFinite w && validateFinite h &&
       validateNonNegative w && validateNonNegative h
      then return (CropRect x y w h)
      else fail "CropRect: all values must be finite, width and height must be non-negative"

-- | Image layer data
data ImageLayerData = ImageLayerData
  { imageLayerDataAssetId :: Text  -- Asset reference - empty string if using inline source
  , imageLayerDataSource :: Text  -- Inline data URL - empty string if using assetId
  , imageLayerDataFit :: ImageFit  -- Display options
  , imageLayerDataCropEnabled :: Bool  -- Cropping (for segmented regions)
  , imageLayerDataCropRect :: CropRect
  , imageLayerDataSourceType :: ImageSourceType  -- Source info (for regeneration/editing)
  , imageLayerDataSegmentationMaskId :: Text  -- Empty string if not from segmentation
  }
  deriving (Eq, Show, Generic)

instance ToJSON ImageLayerData where
  toJSON (ImageLayerData assetId source fit cropEnabled cropRect sourceType segMaskId) =
    object
      [ "assetId" .= assetId
      , "source" .= source
      , "fit" .= fit
      , "cropEnabled" .= cropEnabled
      , "cropRect" .= cropRect
      , "sourceType" .= sourceType
      , "segmentationMaskId" .= segMaskId
      ]

instance FromJSON ImageLayerData where
  parseJSON = withObject "ImageLayerData" $ \o -> do
    assetId <- o .: "assetId"
    source <- o .: "source"
    fit <- o .: "fit"
    cropEnabled <- o .: "cropEnabled"
    cropRect <- o .: "cropRect"
    sourceType <- o .: "sourceType"
    segMaskId <- o .: "segmentationMaskId"
    return (ImageLayerData assetId source fit cropEnabled cropRect sourceType segMaskId)

-- ============================================================================
-- AUDIO LAYER DATA
-- ============================================================================

-- | Audio marker for cue points
data AudioMarker = AudioMarker
  { audioMarkerFrame :: Double
  , audioMarkerLabel :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON AudioMarker where
  toJSON (AudioMarker frame label) =
    object ["frame" .= frame, "label" .= label]

instance FromJSON AudioMarker where
  parseJSON = withObject "AudioMarker" $ \o -> do
    frame <- o .: "frame"
    label <- o .: "label"
    if validateFinite frame && validateNonNegative frame
      then return (AudioMarker frame label)
      else fail "AudioMarker: frame must be finite and non-negative"

-- | Audio layer data - audio-only layer (no visual)
data AudioLayerData = AudioLayerData
  { audioLayerDataAssetId :: Maybe Text  -- Source asset ID (audio file)
  , audioLayerDataLevel :: AnimatableProperty Double  -- Audio level (dB, 0 = unity)
  , audioLayerDataMuted :: Bool  -- Mute toggle
  , audioLayerDataSolo :: Bool  -- Solo this audio track
  , audioLayerDataPan :: AnimatableProperty Double  -- Panning (-1 = left, 0 = center, 1 = right)
  , audioLayerDataStartTime :: Double  -- Playback settings
  , audioLayerDataLoop :: Bool
  , audioLayerDataSpeed :: Double
  , audioLayerDataShowWaveform :: Bool  -- Waveform visualization in timeline
  , audioLayerDataWaveformColor :: Text
  , audioLayerDataExposeFeatures :: Bool  -- Audio reactivity - expose audio features for linking
  , audioLayerDataWaveform :: Maybe [Double]  -- Waveform data (sample amplitudes)
  , audioLayerDataBeats :: Maybe [Double]  -- Detected beat frames
  , audioLayerDataTempo :: Maybe Double  -- Detected tempo (BPM)
  , audioLayerDataAmplitudeData :: Maybe [Double]  -- Per-frame amplitude data
  , audioLayerDataMarkers :: Maybe [AudioMarker]  -- Layer-specific markers (for audio cue points)
  }
  deriving (Eq, Show, Generic)

instance ToJSON AudioLayerData where
  toJSON (AudioLayerData mAssetId level muted solo pan startTime loop speed showWaveform waveformColor exposeFeatures mWaveform mBeats mTempo mAmplitude mMarkers) =
    let
      baseFields = ["level" .= level, "muted" .= muted, "solo" .= solo, "pan" .= pan, "startTime" .= startTime, "loop" .= loop, "speed" .= speed, "showWaveform" .= showWaveform, "waveformColor" .= waveformColor, "exposeFeatures" .= exposeFeatures]
      f1 = case mAssetId of Just a -> ("assetId" .= a) : baseFields; Nothing -> baseFields
      f2 = case mWaveform of Just w -> ("waveform" .= w) : f1; Nothing -> f1
      f3 = case mBeats of Just b -> ("beats" .= b) : f2; Nothing -> f2
      f4 = case mTempo of Just t -> ("tempo" .= t) : f3; Nothing -> f3
      f5 = case mAmplitude of Just a -> ("amplitudeData" .= a) : f4; Nothing -> f4
      f6 = case mMarkers of Just m -> ("markers" .= m) : f5; Nothing -> f5
    in object f6

instance FromJSON AudioLayerData where
  parseJSON = withObject "AudioLayerData" $ \o -> do
    mAssetId <- o .:? "assetId"
    level <- o .: "level"
    muted <- o .: "muted"
    solo <- o .: "solo"
    pan <- o .: "pan"
    startTime <- o .: "startTime"
    loop <- o .: "loop"
    speed <- o .: "speed"
    showWaveform <- o .: "showWaveform"
    waveformColor <- o .: "waveformColor"
    exposeFeatures <- o .: "exposeFeatures"
    mWaveform <- o .:? "waveform"
    mBeats <- o .:? "beats"
    mTempo <- o .:? "tempo"
    mAmplitude <- o .:? "amplitudeData"
    mMarkers <- o .:? "markers"
    -- Validate numeric values
    if validateFinite startTime && validateFinite speed &&
       validateNonNegative startTime && validateNonNegative speed &&
       maybe True (\t -> validateFinite t && validateNonNegative t) mTempo
      then return (AudioLayerData mAssetId level muted solo pan startTime loop speed showWaveform waveformColor exposeFeatures mWaveform mBeats mTempo mAmplitude mMarkers)
      else fail "AudioLayerData: numeric values must be finite and non-negative"

-- ============================================================================
-- VIDEO DATA
-- ============================================================================

-- | Timewarp method
data TimewarpMethod
  = TimewarpWholeFrames
  | TimewarpFrameMix
  | TimewarpPixelMotion
  deriving (Eq, Show, Generic)

instance ToJSON TimewarpMethod where
  toJSON TimewarpWholeFrames = "whole-frames"
  toJSON TimewarpFrameMix = "frame-mix"
  toJSON TimewarpPixelMotion = "pixel-motion"

instance FromJSON TimewarpMethod where
  parseJSON = withText "TimewarpMethod" $ \s ->
    case s of
      "whole-frames" -> return TimewarpWholeFrames
      "frame-mix" -> return TimewarpFrameMix
      "pixel-motion" -> return TimewarpPixelMotion
      _ -> fail "Invalid TimewarpMethod"

-- | Frame blending mode
data FrameBlending
  = FrameBlendingNone
  | FrameBlendingFrameMix
  | FrameBlendingPixelMotion
  deriving (Eq, Show, Generic)

instance ToJSON FrameBlending where
  toJSON FrameBlendingNone = "none"
  toJSON FrameBlendingFrameMix = "frame-mix"
  toJSON FrameBlendingPixelMotion = "pixel-motion"

instance FromJSON FrameBlending where
  parseJSON = withText "FrameBlending" $ \s ->
    case s of
      "none" -> return FrameBlendingNone
      "frame-mix" -> return FrameBlendingFrameMix
      "pixel-motion" -> return FrameBlendingPixelMotion
      _ -> fail "Invalid FrameBlending"

-- | Video data - full video playback control
data VideoData = VideoData
  { videoDataAssetId :: Maybe Text  -- Asset ID
  , videoDataLoop :: Bool  -- Loop when reaching end
  , videoDataPingPong :: Maybe Bool  -- CODE IS TRUTH - not in defaults, code uses fallback
  , videoDataStartTime :: Double  -- Start offset in source video (seconds)
  , videoDataEndTime :: Maybe Double  -- End time in source (undefined = full duration)
  , videoDataSpeed :: Double  -- Playback speed (1 = normal, 2 = 2x, 0.5 = half)
  , videoDataSpeedMapEnabled :: Maybe Bool  -- CODE IS TRUTH - not in defaults
  , videoDataSpeedMap :: Maybe (AnimatableProperty Double)  -- Maps comp time to video time
  , videoDataTimeRemapEnabled :: Maybe Bool  -- @deprecated Use 'speedMapEnabled' instead
  , videoDataTimeRemap :: Maybe (AnimatableProperty Double)  -- @deprecated Use 'speedMap' instead
  , videoDataTimewarpEnabled :: Maybe Bool  -- Timewarp - animatable speed with integration
  , videoDataTimewarpSpeed :: Maybe (AnimatableProperty Double)  -- Speed % (100 = normal, 200 = 2x, 50 = 0.5x)
  , videoDataTimewarpMethod :: Maybe TimewarpMethod
  , videoDataFrameBlending :: Maybe FrameBlending  -- Frame blending for speed changes
  , videoDataAudioEnabled :: Maybe Bool  -- CODE IS TRUTH - not in defaults
  , videoDataAudioLevel :: Maybe Double  -- 0-100 - CODE IS TRUTH - not in defaults
  , videoDataPosterFrame :: Double  -- Frame to show when paused at start
  }
  deriving (Eq, Show, Generic)

instance ToJSON VideoData where
  toJSON (VideoData mAssetId loop mPingPong startTime mEndTime speed mSpeedMapEnabled mSpeedMap mTimeRemapEnabled mTimeRemap mTimewarpEnabled mTimewarpSpeed mTimewarpMethod mFrameBlending mAudioEnabled mAudioLevel posterFrame) =
    let
      baseFields = ["loop" .= loop, "startTime" .= startTime, "speed" .= speed, "posterFrame" .= posterFrame]
      f1 = case mAssetId of Just a -> ("assetId" .= a) : baseFields; Nothing -> baseFields
      f2 = case mPingPong of Just p -> ("pingPong" .= p) : f1; Nothing -> f1
      f3 = case mEndTime of Just e -> ("endTime" .= e) : f2; Nothing -> f2
      f4 = case mSpeedMapEnabled of Just s -> ("speedMapEnabled" .= s) : f3; Nothing -> f3
      f5 = case mSpeedMap of Just s -> ("speedMap" .= s) : f4; Nothing -> f4
      f6 = case mTimeRemapEnabled of Just t -> ("timeRemapEnabled" .= t) : f5; Nothing -> f5
      f7 = case mTimeRemap of Just t -> ("timeRemap" .= t) : f6; Nothing -> f6
      f8 = case mTimewarpEnabled of Just t -> ("timewarpEnabled" .= t) : f7; Nothing -> f7
      f9 = case mTimewarpSpeed of Just s -> ("timewarpSpeed" .= s) : f8; Nothing -> f8
      f10 = case mTimewarpMethod of Just m -> ("timewarpMethod" .= m) : f9; Nothing -> f9
      f11 = case mFrameBlending of Just f -> ("frameBlending" .= f) : f10; Nothing -> f10
      f12 = case mAudioEnabled of Just a -> ("audioEnabled" .= a) : f11; Nothing -> f11
      f13 = case mAudioLevel of Just l -> ("audioLevel" .= l) : f12; Nothing -> f12
    in object f13

instance FromJSON VideoData where
  parseJSON = withObject "VideoData" $ \o -> do
    mAssetId <- o .:? "assetId"
    loop <- o .: "loop"
    mPingPong <- o .:? "pingPong"
    startTime <- o .: "startTime"
    mEndTime <- o .:? "endTime"
    speed <- o .: "speed"
    mSpeedMapEnabled <- o .:? "speedMapEnabled"
    mSpeedMap <- o .:? "speedMap"
    mTimeRemapEnabled <- o .:? "timeRemapEnabled"
    mTimeRemap <- o .:? "timeRemap"
    mTimewarpEnabled <- o .:? "timewarpEnabled"
    mTimewarpSpeed <- o .:? "timewarpSpeed"
    mTimewarpMethod <- o .:? "timewarpMethod"
    mFrameBlending <- o .:? "frameBlending"
    mAudioEnabled <- o .:? "audioEnabled"
    mAudioLevel <- o .:? "audioLevel"
    posterFrame <- o .: "posterFrame"
    -- Validate numeric values
    if validateFinite startTime && validateFinite speed &&
       validateFinite posterFrame &&
       validateNonNegative startTime && validateNonNegative speed &&
       validateNonNegative posterFrame &&
       maybe True (\e -> validateFinite e && validateNonNegative e) mEndTime &&
       maybe True (\l -> validateFinite l && l >= 0 && l <= 100) mAudioLevel
      then
        -- Validate endTime >= startTime if both present (matches Zod schema refinement)
        case mEndTime of
          Nothing -> return (VideoData mAssetId loop mPingPong startTime mEndTime speed mSpeedMapEnabled mSpeedMap mTimeRemapEnabled mTimeRemap mTimewarpEnabled mTimewarpSpeed mTimewarpMethod mFrameBlending mAudioEnabled mAudioLevel posterFrame)
          Just endTime ->
            if endTime >= startTime
              then return (VideoData mAssetId loop mPingPong startTime mEndTime speed mSpeedMapEnabled mSpeedMap mTimeRemapEnabled mTimeRemap mTimewarpEnabled mTimewarpSpeed mTimewarpMethod mFrameBlending mAudioEnabled mAudioLevel posterFrame)
              else fail "VideoData: endTime must be >= startTime"
      else fail "VideoData: numeric values must be finite and within valid ranges"

-- ============================================================================
-- DEPTH LAYER DATA
-- ============================================================================

-- | Depth visualization mode
data DepthVisualizationMode
  = DepthVisualizationGrayscale
  | DepthVisualizationColormap
  | DepthVisualizationContour
  | DepthVisualization3DMesh
  deriving (Eq, Show, Generic)

instance ToJSON DepthVisualizationMode where
  toJSON DepthVisualizationGrayscale = "grayscale"
  toJSON DepthVisualizationColormap = "colormap"
  toJSON DepthVisualizationContour = "contour"
  toJSON DepthVisualization3DMesh = "3d-mesh"

instance FromJSON DepthVisualizationMode where
  parseJSON = withText "DepthVisualizationMode" $ \s ->
    case s of
      "grayscale" -> return DepthVisualizationGrayscale
      "colormap" -> return DepthVisualizationColormap
      "contour" -> return DepthVisualizationContour
      "3d-mesh" -> return DepthVisualization3DMesh
      _ -> fail "Invalid DepthVisualizationMode"

-- | Depth color map preset
data DepthColorMap
  = DepthColorMapTurbo
  | DepthColorMapViridis
  | DepthColorMapPlasma
  | DepthColorMapInferno
  | DepthColorMapMagma
  | DepthColorMapGrayscale
  deriving (Eq, Show, Generic)

instance ToJSON DepthColorMap where
  toJSON DepthColorMapTurbo = "turbo"
  toJSON DepthColorMapViridis = "viridis"
  toJSON DepthColorMapPlasma = "plasma"
  toJSON DepthColorMapInferno = "inferno"
  toJSON DepthColorMapMagma = "magma"
  toJSON DepthColorMapGrayscale = "grayscale"

instance FromJSON DepthColorMap where
  parseJSON = withText "DepthColorMap" $ \s ->
    case s of
      "turbo" -> return DepthColorMapTurbo
      "viridis" -> return DepthColorMapViridis
      "plasma" -> return DepthColorMapPlasma
      "inferno" -> return DepthColorMapInferno
      "magma" -> return DepthColorMapMagma
      "grayscale" -> return DepthColorMapGrayscale
      _ -> fail "Invalid DepthColorMap"

-- | Depth layer data - depth map visualization for AI workflows
data DepthLayerData = DepthLayerData
  { depthLayerDataAssetId :: Maybe Text  -- Source asset ID (depth map image)
  , depthLayerDataVisualizationMode :: DepthVisualizationMode  -- Visualization mode
  , depthLayerDataColorMap :: DepthColorMap  -- Color map preset for visualization
  , depthLayerDataInvert :: Bool  -- Invert depth values (near <-> far)
  , depthLayerDataMinDepth :: Double  -- Depth range normalization
  , depthLayerDataMaxDepth :: Double
  , depthLayerDataAutoNormalize :: Bool
  , depthLayerDataContourLevels :: Double  -- Contour settings (when visualizationMode = 'contour')
  , depthLayerDataContourColor :: Text
  , depthLayerDataContourWidth :: Double
  , depthLayerDataMeshDisplacement :: AnimatableProperty Double  -- 3D mesh settings (when visualizationMode = '3d-mesh')
  , depthLayerDataMeshResolution :: Double
  , depthLayerDataWireframe :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON DepthLayerData where
  toJSON (DepthLayerData mAssetId visMode colorMap invert minDepth maxDepth autoNorm contourLevels contourColor contourWidth meshDisp meshRes wireframe) =
    let
      baseFields = ["visualizationMode" .= visMode, "colorMap" .= colorMap, "invert" .= invert, "minDepth" .= minDepth, "maxDepth" .= maxDepth, "autoNormalize" .= autoNorm, "contourLevels" .= contourLevels, "contourColor" .= contourColor, "contourWidth" .= contourWidth, "meshDisplacement" .= meshDisp, "meshResolution" .= meshRes, "wireframe" .= wireframe]
      withAssetId = case mAssetId of Just a -> ("assetId" .= a) : baseFields; Nothing -> baseFields
    in object withAssetId

instance FromJSON DepthLayerData where
  parseJSON = withObject "DepthLayerData" $ \o -> do
    mAssetId <- o .:? "assetId"
    visMode <- o .: "visualizationMode"
    colorMap <- o .: "colorMap"
    invert <- o .: "invert"
    minDepth <- o .: "minDepth"
    maxDepth <- o .: "maxDepth"
    autoNorm <- o .: "autoNormalize"
    contourLevels <- o .: "contourLevels"
    contourColor <- o .: "contourColor"
    contourWidth <- o .: "contourWidth"
    meshDisp <- o .: "meshDisplacement"
    meshRes <- o .: "meshResolution"
    wireframe <- o .: "wireframe"
    -- Validate numeric values
    if validateFinite minDepth && validateFinite maxDepth &&
       validateFinite contourLevels && validateFinite contourWidth &&
       validateFinite meshRes &&
       validateNonNegative contourLevels && validateNonNegative contourWidth &&
       validateNonNegative meshRes &&
       maxDepth > minDepth  -- Matches Zod schema refinement: maxDepth must be greater than minDepth
      then return (DepthLayerData mAssetId visMode colorMap invert minDepth maxDepth autoNorm contourLevels contourColor contourWidth meshDisp meshRes wireframe)
      else fail "DepthLayerData: numeric values must be finite and within valid ranges, and maxDepth must be greater than minDepth"

-- ============================================================================
-- NORMAL LAYER DATA
-- ============================================================================

-- | Normal visualization mode
data NormalVisualizationMode
  = NormalVisualizationRGB
  | NormalVisualizationHemisphere
  | NormalVisualizationArrows
  | NormalVisualizationLit
  deriving (Eq, Show, Generic)

instance ToJSON NormalVisualizationMode where
  toJSON NormalVisualizationRGB = "rgb"
  toJSON NormalVisualizationHemisphere = "hemisphere"
  toJSON NormalVisualizationArrows = "arrows"
  toJSON NormalVisualizationLit = "lit"

instance FromJSON NormalVisualizationMode where
  parseJSON = withText "NormalVisualizationMode" $ \s ->
    case s of
      "rgb" -> return NormalVisualizationRGB
      "hemisphere" -> return NormalVisualizationHemisphere
      "arrows" -> return NormalVisualizationArrows
      "lit" -> return NormalVisualizationLit
      _ -> fail "Invalid NormalVisualizationMode"

-- | Normal map format
data NormalFormat
  = NormalFormatOpenGL
  | NormalFormatDirectX
  deriving (Eq, Show, Generic)

instance ToJSON NormalFormat where
  toJSON NormalFormatOpenGL = "opengl"
  toJSON NormalFormatDirectX = "directx"

instance FromJSON NormalFormat where
  parseJSON = withText "NormalFormat" $ \s ->
    case s of
      "opengl" -> return NormalFormatOpenGL
      "directx" -> return NormalFormatDirectX
      _ -> fail "Invalid NormalFormat"

-- | Normal layer data - normal map visualization for AI workflows
data NormalLayerData = NormalLayerData
  { normalLayerDataAssetId :: Maybe Text  -- Source asset ID (normal map image)
  , normalLayerDataVisualizationMode :: NormalVisualizationMode  -- Visualization mode
  , normalLayerDataFormat :: NormalFormat  -- Normal map format
  , normalLayerDataFlipX :: Bool  -- Flip channels
  , normalLayerDataFlipY :: Bool
  , normalLayerDataFlipZ :: Bool
  , normalLayerDataArrowDensity :: Double  -- Arrow visualization settings
  , normalLayerDataArrowScale :: Double
  , normalLayerDataArrowColor :: Text
  , normalLayerDataLightDirection :: Vec3  -- Lit visualization settings (fake lighting preview)
  , normalLayerDataLightIntensity :: Double
  , normalLayerDataAmbientIntensity :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON NormalLayerData where
  toJSON (NormalLayerData mAssetId visMode format flipX flipY flipZ arrowDensity arrowScale arrowColor lightDir lightIntensity ambientIntensity) =
    let
      baseFields = ["visualizationMode" .= visMode, "format" .= format, "flipX" .= flipX, "flipY" .= flipY, "flipZ" .= flipZ, "arrowDensity" .= arrowDensity, "arrowScale" .= arrowScale, "arrowColor" .= arrowColor, "lightDirection" .= lightDir, "lightIntensity" .= lightIntensity, "ambientIntensity" .= ambientIntensity]
      withAssetId = case mAssetId of Just a -> ("assetId" .= a) : baseFields; Nothing -> baseFields
    in object withAssetId

instance FromJSON NormalLayerData where
  parseJSON = withObject "NormalLayerData" $ \o -> do
    mAssetId <- o .:? "assetId"
    visMode <- o .: "visualizationMode"
    format <- o .: "format"
    flipX <- o .: "flipX"
    flipY <- o .: "flipY"
    flipZ <- o .: "flipZ"
    arrowDensity <- o .: "arrowDensity"
    arrowScale <- o .: "arrowScale"
    arrowColor <- o .: "arrowColor"
    lightDir <- o .: "lightDirection"
    lightIntensity <- o .: "lightIntensity"
    ambientIntensity <- o .: "ambientIntensity"
    -- Validate numeric values
    if validateFinite arrowDensity && validateFinite arrowScale &&
       validateFinite lightIntensity && validateFinite ambientIntensity &&
       validateNonNegative arrowDensity && validateNonNegative arrowScale &&
       validateNonNegative lightIntensity && validateNonNegative ambientIntensity
      then return (NormalLayerData mAssetId visMode format flipX flipY flipZ arrowDensity arrowScale arrowColor lightDir lightIntensity ambientIntensity)
      else fail "NormalLayerData: numeric values must be finite and non-negative"

-- ============================================================================
-- NESTED COMP DATA
-- ============================================================================

-- | Nested comp data - nested composition reference
data NestedCompData = NestedCompData
  { nestedCompDataCompositionId :: Maybe Text  -- Reference to composition in project.compositions
  , nestedCompDataSpeedMapEnabled :: Maybe Bool  -- CODE IS TRUTH - not in defaults
  , nestedCompDataSpeedMap :: Maybe (AnimatableProperty Double)  -- Maps parent time to nested comp time
  , nestedCompDataTimeRemapEnabled :: Maybe Bool  -- @deprecated Use 'speedMapEnabled' instead
  , nestedCompDataTimeRemap :: Maybe (AnimatableProperty Double)  -- @deprecated Use 'speedMap' instead
  , nestedCompDataTimewarpEnabled :: Maybe Bool  -- Timewarp - animatable speed with integration
  , nestedCompDataTimewarpSpeed :: Maybe (AnimatableProperty Double)  -- Speed % (100 = normal, 200 = 2x, 50 = 0.5x)
  , nestedCompDataTimewarpMethod :: Maybe TimewarpMethod
  , nestedCompDataFlattenTransform :: Maybe Bool  -- CODE IS TRUTH - not in defaults - Flatten transform (render nested layers in parent's 3D space)
  , nestedCompDataOverrideFrameRate :: Maybe Bool  -- CODE IS TRUTH - not in defaults
  , nestedCompDataFrameRate :: Maybe Double  -- Override nested comp settings
  }
  deriving (Eq, Show, Generic)

instance ToJSON NestedCompData where
  toJSON (NestedCompData mCompId mSpeedMapEnabled mSpeedMap mTimeRemapEnabled mTimeRemap mTimewarpEnabled mTimewarpSpeed mTimewarpMethod mFlatten mOverrideFps mFrameRate) =
    let
      baseFields = []
      f1 = case mCompId of Just c -> ("compositionId" .= c) : baseFields; Nothing -> baseFields
      f2 = case mSpeedMapEnabled of Just s -> ("speedMapEnabled" .= s) : f1; Nothing -> f1
      f3 = case mSpeedMap of Just s -> ("speedMap" .= s) : f2; Nothing -> f2
      f4 = case mTimeRemapEnabled of Just t -> ("timeRemapEnabled" .= t) : f3; Nothing -> f3
      f5 = case mTimeRemap of Just t -> ("timeRemap" .= t) : f4; Nothing -> f4
      f6 = case mTimewarpEnabled of Just t -> ("timewarpEnabled" .= t) : f5; Nothing -> f5
      f7 = case mTimewarpSpeed of Just s -> ("timewarpSpeed" .= s) : f6; Nothing -> f6
      f8 = case mTimewarpMethod of Just m -> ("timewarpMethod" .= m) : f7; Nothing -> f7
      f9 = case mFlatten of Just f -> ("flattenTransform" .= f) : f8; Nothing -> f8
      f10 = case mOverrideFps of Just o -> ("overrideFrameRate" .= o) : f9; Nothing -> f9
      f11 = case mFrameRate of Just f -> ("frameRate" .= f) : f10; Nothing -> f10
    in object f11

instance FromJSON NestedCompData where
  parseJSON = withObject "NestedCompData" $ \o -> do
    mCompId <- o .:? "compositionId"
    mSpeedMapEnabled <- o .:? "speedMapEnabled"
    mSpeedMap <- o .:? "speedMap"
    mTimeRemapEnabled <- o .:? "timeRemapEnabled"
    mTimeRemap <- o .:? "timeRemap"
    mTimewarpEnabled <- o .:? "timewarpEnabled"
    mTimewarpSpeed <- o .:? "timewarpSpeed"
    mTimewarpMethod <- o .:? "timewarpMethod"
    mFlatten <- o .:? "flattenTransform"
    mOverrideFps <- o .:? "overrideFrameRate"
    mFrameRate <- o .:? "frameRate"
    -- Validate frameRate if present
    case mFrameRate of
      Nothing -> return ()
      Just fps -> if validateFinite fps && validateNonNegative fps
        then return ()
        else fail "NestedCompData: frameRate must be finite and non-negative"
    return (NestedCompData mCompId mSpeedMapEnabled mSpeedMap mTimeRemapEnabled mTimeRemap mTimewarpEnabled mTimewarpSpeed mTimewarpMethod mFlatten mOverrideFps mFrameRate)
