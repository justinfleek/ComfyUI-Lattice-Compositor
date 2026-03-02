-- |
-- Module      : Lattice.State.Layer.Specialized
-- Description : Specialized layer creation operations
-- 
-- Extracted from Lattice.State.Layer
-- Pure functions for creating specialized layer types (text, spline, shape, camera, nested comp)
-- and replacing layer sources
--
{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Layer.Specialized
  ( createTextLayer
  , createSplineLayer
  , createShapeLayer
  , createCameraLayer
  , createNestedCompLayer
  , updateNestedCompLayerData
  , replaceLayerSource
  , CharacterVectorGroup(..)
  , bezierPathToControlPoints
  , convertTextLayerToSplines
  ) where

import Data.List (last, zipWith)
import Data.Maybe (Maybe(..), isJust, isNothing, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Layer.CRUD (createLayer, regenerateKeyframeIds)
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.State.Layer.Types (CreateLayerOptions(..), LayerSourceReplacement(..), LayerSourceReplacementType(..))
import Lattice.Types.Animation (AnimatableProperty(..), PropertyType(..), createAnimatableProperty)
import Lattice.Types.Layer
  ( Layer(..)
  , LayerType(..)
  , LayerData(..)
  )
import Lattice.Types.LayerData3D (CameraLayerData(..))
import Lattice.Types.LayerDataAsset
  ( NestedCompData(..)
  , ImageLayerData(..)
  , ImageFit(..)
  , ImageSourceType(..)
  , CropRect(..)
  , VideoData(..)
  )
import Lattice.Types.LayerDataShapes
  ( ShapeLayerData(..)
  , ShapeQuality(..)
  , BezierPath(..)
  , BezierVertex(..)
  , Point2D(..)
  )
import Lattice.Types.LayerDataSpline
  ( SplineData(..)
  , SplineStrokeType(..)
  , ControlPoint(..)
  , ControlPointHandle(..)
  , ControlPointType(..)
  )
import Lattice.Types.LayerDataText
  ( TextData(..)
  , TextFontStyle(..)
  , TextAlign(..)
  , TextPathAlign(..)
  , TextAnchorPointGrouping(..)
  , TextFillAndStroke(..)
  , TextInterCharacterBlending(..)
  )
import Lattice.Types.Primitives
  ( Vec2(..)
  , Vec3(..)
  , Position2DOr3D(..)
  )
import Lattice.Types.Transform (LayerTransform(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // specialized // layer // creation
-- ════════════════════════════════════════════════════════════════════════════

-- | Create a text layer with default text data
-- Pure function: takes text content, layer ID, composition settings, and ID generators
-- Returns new text layer with default text data
createTextLayer ::
  Text -> -- Text content
  Text -> -- Layer ID (generated at FFI boundary)
  CreateLayerOptions -> -- Creation options
  Double -> -- Composition width
  Double -> -- Composition height
  Int -> -- Composition frame count
  (Text -> Text) -> -- ID generator for transform properties
  (Text -> Text) -> -- ID generator for opacity property
  (Text -> Text) -> -- ID generator for audio properties (if needed)
  Layer
createTextLayer textContent layerId options compWidth compHeight frameCount genTransformId genOpacityId genAudioId =
  let
    -- Create default text data
    textData = TextData
      { textDataText = textContent
      , textDataFontFamily = "Arial"
      , textDataFontSize = 72.0
      , textDataFontWeight = "400"
      , textDataFontStyle = TextFontStyleNormal
      , textDataFill = "#ffffff"
      , textDataStroke = ""
      , textDataStrokeWidth = 0.0
      , textDataTracking = 0.0
      , textDataLineSpacing = 0.0
      , textDataLineAnchor = 0.0
      , textDataCharacterOffset = 0.0
      , textDataCharacterValue = 0.0
      , textDataBlur = Vec2 0.0 0.0
      , textDataLetterSpacing = 0.0
      , textDataLineHeight = 1.2
      , textDataTextAlign = TextAlignLeft
      , textDataPathLayerId = ""
      , textDataPathReversed = False
      , textDataPathPerpendicularToPath = True
      , textDataPathForceAlignment = False
      , textDataPathFirstMargin = 0.0
      , textDataPathLastMargin = 0.0
      , textDataPathOffset = 0.0
      , textDataPathAlign = TextPathAlignLeft
      , textDataAnchorPointGrouping = Just TextAnchorPointGroupingCharacter
      , textDataGroupingAlignment = Just (Vec2 0.0 0.0)
      , textDataFillAndStroke = Just TextFillAndStrokeFillOverStroke
      , textDataInterCharacterBlending = Just TextInterCharacterBlendingNormal
      , textDataPerCharacter3D = Just False
      , textDataBaselineShift = Nothing
      , textDataTextCase = Nothing
      , textDataVerticalAlign = Nothing
      , textDataKerning = Nothing
      , textDataLigatures = Nothing
      , textDataDiscretionaryLigatures = Nothing
      , textDataSmallCapsFeature = Nothing
      , textDataStylisticSet = Nothing
      , textDataFirstLineIndent = Nothing
      , textDataSpaceBefore = Nothing
      , textDataSpaceAfter = Nothing
      , textDataAnimators = Nothing
      }
    
    -- Use provided name or default to first 20 chars of text
    layerName_ = case createLayerOptionsName options of
      Just name -> name
      Nothing -> T.take 20 textContent
    
    -- Create layer with text data
    baseLayer = createLayer layerId LayerTypeText (options {createLayerOptionsName = Just layerName_}) compWidth compHeight frameCount (Just (LayerDataText textData)) genTransformId genOpacityId genAudioId
  in
    baseLayer

-- | Create a spline layer with default spline data
-- Pure function: takes layer ID, composition settings, and ID generators
-- Returns new spline layer with default spline data
createSplineLayer ::
  Text -> -- Layer ID (generated at FFI boundary)
  CreateLayerOptions -> -- Creation options
  Double -> -- Composition width
  Double -> -- Composition height
  Int -> -- Composition frame count
  (Text -> Text) -> -- ID generator for transform properties
  (Text -> Text) -> -- ID generator for opacity property
  (Text -> Text) -> -- ID generator for audio properties (if needed)
  Layer
createSplineLayer layerId options compWidth compHeight frameCount genTransformId genOpacityId genAudioId =
  let
    -- Create default spline data (matching TypeScript createSplineLayer)
    splineData = SplineData
      { splineDataPathData = ""
      , splineDataControlPoints = []
      , splineDataClosed = False
      , splineDataStrokeType = Just SplineStrokeTypeSolid
      , splineDataStroke = "#00ff00"
      , splineDataStrokeGradient = Nothing
      , splineDataStrokeWidth = 2.0
      , splineDataStrokeOpacity = Nothing  -- Default 100
      , splineDataLineCap = Nothing  -- Default based on renderer
      , splineDataLineJoin = Nothing  -- Default based on renderer
      , splineDataStrokeMiterLimit = Nothing  -- Default 4
      , splineDataDashArray = Nothing
      , splineDataDashOffset = Nothing
      , splineDataFill = Nothing  -- Empty = no fill
      , splineDataFillOpacity = Nothing  -- Default 100
      , splineDataTrimStart = Nothing
      , splineDataTrimEnd = Nothing
      , splineDataTrimOffset = Nothing
      , splineDataPathEffects = Nothing
      , splineDataAnimatedControlPoints = Nothing
      , splineDataAnimated = Nothing
      , splineDataLOD = Nothing
      , splineDataWarpPins = Nothing
      , splineDataPuppetPins = Nothing
      , splineDataAudioReactive = Nothing
      }
    
    -- Create layer with spline data
    baseLayer = createLayer layerId LayerTypeSpline options compWidth compHeight frameCount (Just (LayerDataSpline splineData)) genTransformId genOpacityId genAudioId
  in
    baseLayer

-- | Create a shape layer with default shape data
-- Pure function: takes layer ID, composition settings, and ID generators
-- Returns new shape layer with default shape data
createShapeLayer ::
  Text -> -- Layer ID (generated at FFI boundary)
  CreateLayerOptions -> -- Creation options
  Double -> -- Composition width
  Double -> -- Composition height
  Int -> -- Composition frame count
  (Text -> Text) -> -- ID generator for transform properties
  (Text -> Text) -> -- ID generator for opacity property
  (Text -> Text) -> -- ID generator for audio properties (if needed)
  Layer
createShapeLayer layerId options compWidth compHeight frameCount genTransformId genOpacityId genAudioId =
  let
    -- Create default shape layer data (empty contents - user adds shapes)
    -- Matching TypeScript createShapeLayer defaults
    shapeLayerData = ShapeLayerData
      { shapeLayerDataContents = []
      , shapeLayerDataBlendMode = "normal"
      , shapeLayerDataQuality = ShapeQualityNormal
      , shapeLayerDataGPUAccelerated = True
      }
    
    -- Create layer with shape data
    baseLayer = createLayer layerId LayerTypeShape options compWidth compHeight frameCount (Just (LayerDataShape shapeLayerData)) genTransformId genOpacityId genAudioId
  in
    baseLayer

-- | Create a camera layer with default camera data
-- Pure function: takes camera ID, layer ID, composition settings, and ID generators
-- Returns new camera layer with camera data
-- Note: Camera object creation is handled at FFI boundary (cameraStore)
-- This function only creates the layer with camera data reference
createCameraLayer ::
  Text -> -- Camera ID (generated at FFI boundary)
  Text -> -- Layer ID (generated at FFI boundary)
  CreateLayerOptions -> -- Creation options
  Double -> -- Composition width
  Double -> -- Composition height
  Int -> -- Composition frame count
  Bool -> -- Is active camera?
  (Text -> Text) -> -- ID generator for transform properties
  (Text -> Text) -> -- ID generator for opacity property
  (Text -> Text) -> -- ID generator for audio properties (if needed)
  Layer
createCameraLayer cameraId layerId options compWidth compHeight frameCount isActiveCamera genTransformId genOpacityId genAudioId =
  let
    -- Create camera layer data (matching TypeScript createCameraLayer)
    cameraLayerData = CameraLayerData
      { cameraLayerDataCameraId = Just cameraId
      , cameraLayerDataIsActiveCamera = isActiveCamera
      , cameraLayerDataCamera = Nothing  -- Camera object stored separately in cameraStore
      , cameraLayerDataAnimatedPosition = Nothing
      , cameraLayerDataAnimatedTarget = Nothing
      , cameraLayerDataAnimatedFov = Nothing
      , cameraLayerDataAnimatedFocalLength = Nothing
      , cameraLayerDataPathFollowing = Nothing
      , cameraLayerDataPathFollowingConfig = Nothing
      , cameraLayerDataDepthOfField = Nothing
      , cameraLayerDataAnimatedFocusDistance = Nothing
      , cameraLayerDataAnimatedAperture = Nothing
      , cameraLayerDataAnimatedBlurLevel = Nothing
      , cameraLayerDataShake = Nothing
      , cameraLayerDataRackFocus = Nothing
      , cameraLayerDataAutoFocus = Nothing
      , cameraLayerDataTrajectoryKeyframes = Nothing
      }
    
    -- Create layer with camera data
    -- Camera layers are always 3D
    baseLayer = createLayer layerId LayerTypeCamera options compWidth compHeight frameCount (Just (LayerDataCamera cameraLayerData)) genTransformId genOpacityId genAudioId
    
    -- Force 3D mode for camera layers (camera layers are always 3D)
    updatedLayer = baseLayer {layerThreeD = True}
  in
    updatedLayer

-- | Create a nested comp layer with default nested comp data
-- Pure function: takes composition ID, layer ID, composition settings, and ID generators
-- Returns new nested comp layer with nested comp data
createNestedCompLayer ::
  Text -> -- Composition ID (reference to composition in project)
  Text -> -- Layer ID (generated at FFI boundary)
  CreateLayerOptions -> -- Creation options
  Double -> -- Composition width
  Double -> -- Composition height
  Int -> -- Composition frame count
  (Text -> Text) -> -- ID generator for transform properties
  (Text -> Text) -> -- ID generator for opacity property
  (Text -> Text) -> -- ID generator for audio properties (if needed)
  Layer
createNestedCompLayer compositionId layerId options compWidth compHeight frameCount genTransformId genOpacityId genAudioId =
  let
    -- Create nested comp data (matching TypeScript createNestedCompLayer)
    nestedCompData = NestedCompData
      { nestedCompDataCompositionId = Just compositionId
      , nestedCompDataSpeedMapEnabled = Just False
      , nestedCompDataSpeedMap = Nothing
      , nestedCompDataTimeRemapEnabled = Just False
      , nestedCompDataTimeRemap = Nothing
      , nestedCompDataTimewarpEnabled = Nothing
      , nestedCompDataTimewarpSpeed = Nothing
      , nestedCompDataTimewarpMethod = Nothing
      , nestedCompDataFlattenTransform = Just False
      , nestedCompDataOverrideFrameRate = Just False
      , nestedCompDataFrameRate = Nothing
      }
    
    -- Use provided name or default to "Nested Comp"
    layerName_ = case createLayerOptionsName options of
      Just name -> name
      Nothing -> "Nested Comp"
    
    -- Create layer with nested comp data
    baseLayer = createLayer layerId LayerTypeNestedComp (options {createLayerOptionsName = Just layerName_}) compWidth compHeight frameCount (Just (LayerDataNestedComp nestedCompData)) genTransformId genOpacityId genAudioId
  in
    baseLayer

-- | Update nested comp layer data
-- Pure function: takes layer ID, data updates, and layers list
-- Returns new layers list with updated nested comp data, or error if layer not found or not a nested comp layer
updateNestedCompLayerData ::
  Text -> -- Layer ID
  Maybe Text -> -- Composition ID update
  Maybe Bool -> -- Speed map enabled update
  Maybe Bool -> -- Flatten transform update
  Maybe Bool -> -- Override frame rate update
  Maybe Double -> -- Frame rate update
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with updated nested comp data, or error
updateNestedCompLayerData targetLayerId mCompositionId mSpeedMapEnabled mFlattenTransform mOverrideFrameRate mFrameRate layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case layerData existingLayer of
        Just (LayerDataNestedComp existingNestedCompData) ->
          let
            -- Update nested comp data fields
            updatedNestedCompData = existingNestedCompData
              { nestedCompDataCompositionId = maybe (nestedCompDataCompositionId existingNestedCompData) Just mCompositionId
              , nestedCompDataSpeedMapEnabled = maybe (nestedCompDataSpeedMapEnabled existingNestedCompData) Just mSpeedMapEnabled
              , nestedCompDataFlattenTransform = maybe (nestedCompDataFlattenTransform existingNestedCompData) Just mFlattenTransform
              , nestedCompDataOverrideFrameRate = maybe (nestedCompDataOverrideFrameRate existingNestedCompData) Just mOverrideFrameRate
              , nestedCompDataFrameRate = maybe (nestedCompDataFrameRate existingNestedCompData) Just mFrameRate
              }
            
            updatedLayer = existingLayer
              { layerData = Just (LayerDataNestedComp updatedNestedCompData)
              }
          in
            Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
        _ -> Left ("Layer is not a nested comp layer: " <> targetLayerId)

-- | Replace a layer's source with a new asset or composition
-- Pure function: takes layer ID, source replacement data, and layers list
-- Returns new layers list with replaced source, or error if layer not found or invalid replacement
replaceLayerSource ::
  Text -> -- Layer ID
  LayerSourceReplacement -> -- New source data
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with replaced source, or error
replaceLayerSource targetLayerId newSource layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      let
        assetId = case (layerSourceReplacementAssetId newSource, layerSourceReplacementId newSource) of
          (Just aid, _) -> Just aid
          (Nothing, Just id_) -> Just id_
          (Nothing, Nothing) -> Nothing
        
        replacementType = layerSourceReplacementType newSource
        newName = layerSourceReplacementName newSource
      in
        case (layerType existingLayer, replacementType) of
          -- Image layer with asset replacement
          (LayerTypeImage, LayerSourceReplacementTypeAsset) ->
            case (assetId, layerData existingLayer) of
              (Just aid, Just (LayerDataImage imageData)) ->
                let
                  updatedImageData = imageData {imageLayerDataAssetId = aid}
                  updatedLayer = existingLayer
                    { layerData = Just (LayerDataImage updatedImageData)
                    , layerName = newName
                    }
                in
                  Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
              _ -> Left ("Cannot replace image source: invalid asset ID or image data")
          
          -- Video layer with asset replacement
          (LayerTypeVideo, LayerSourceReplacementTypeAsset) ->
            case (assetId, layerData existingLayer) of
              (Just aid, Just (LayerDataVideo videoData)) ->
                let
                  updatedVideoData = videoData {videoDataAssetId = Just aid}
                  updatedLayer = existingLayer
                    { layerData = Just (LayerDataVideo updatedVideoData)
                    , layerName = newName
                    }
                in
                  Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
              _ -> Left ("Cannot replace video source: invalid asset ID or video data")
          
          -- Solid layer converting to image
          (LayerTypeSolid, LayerSourceReplacementTypeAsset) ->
            case assetId of
              Just aid ->
                let
                  -- Create new image layer data
                  imageData = ImageLayerData
                    { imageLayerDataAssetId = aid
                    , imageLayerDataSource = ""
                    , imageLayerDataFit = ImageFitNone
                    , imageLayerDataCropEnabled = False
                    , imageLayerDataCropRect = CropRect 0.0 0.0 0.0 0.0
                    , imageLayerDataSourceType = ImageSourceFile
                    , imageLayerDataSegmentationMaskId = ""
                    }
                  
                  updatedLayer = existingLayer
                    { layerType = LayerTypeImage
                    , layerData = Just (LayerDataImage imageData)
                    , layerName = newName
                    }
                in
                  Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
              Nothing -> Left ("Cannot convert solid to image: invalid asset ID")
          
          -- Nested comp layer with composition replacement
          (LayerTypeNestedComp, LayerSourceReplacementTypeComposition) ->
            case (layerSourceReplacementId newSource, layerData existingLayer) of
              (Just compId, Just (LayerDataNestedComp nestedCompData)) ->
                let
                  updatedNestedCompData = nestedCompData {nestedCompDataCompositionId = Just compId}
                  updatedLayer = existingLayer
                    { layerData = Just (LayerDataNestedComp updatedNestedCompData)
                    , layerName = newName
                    }
                in
                  Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
              _ -> Left ("Cannot replace nested comp source: invalid composition ID or nested comp data")
          
          -- Any layer converting to nested comp
          (_, LayerSourceReplacementTypeComposition) ->
            case layerSourceReplacementId newSource of
              Just compId ->
                let
                  nestedCompData = NestedCompData
                    { nestedCompDataCompositionId = Just compId
                    , nestedCompDataSpeedMapEnabled = Just False
                    , nestedCompDataSpeedMap = Nothing
                    , nestedCompDataTimeRemapEnabled = Just False
                    , nestedCompDataTimeRemap = Nothing
                    , nestedCompDataTimewarpEnabled = Nothing
                    , nestedCompDataTimewarpSpeed = Nothing
                    , nestedCompDataTimewarpMethod = Nothing
                    , nestedCompDataFlattenTransform = Just False
                    , nestedCompDataOverrideFrameRate = Just False
                    , nestedCompDataFrameRate = Nothing
                    }
                  
                  updatedLayer = existingLayer
                    { layerType = LayerTypeNestedComp
                    , layerData = Just (LayerDataNestedComp nestedCompData)
                    , layerName = newName
                    }
                in
                  Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
              Nothing -> Left ("Cannot convert to nested comp: invalid composition ID")
          
          -- Generic asset replacement - determine type from file extension
          (_, LayerSourceReplacementTypeAsset) ->
            case (assetId, layerSourceReplacementPath newSource) of
              (Just aid, Just path) ->
                let
                  -- Extract file extension
                  pathParts = T.splitOn "." path
                  ext = if null pathParts
                    then ""
                    else T.toLower (last pathParts)
                  
                  imageExts = ["png", "jpg", "jpeg", "gif", "webp", "svg"]
                  videoExts = ["mp4", "webm", "mov", "avi"]
                  
                  (newLayerType, newLayerData) = if ext `elem` imageExts
                    then
                      let
                        imageData = ImageLayerData
                          { imageLayerDataAssetId = aid
                          , imageLayerDataSource = ""
                          , imageLayerDataFit = ImageFitNone
                          , imageLayerDataCropEnabled = False
                          , imageLayerDataCropRect = CropRect 0.0 0.0 0.0 0.0
                          , imageLayerDataSourceType = ImageSourceFile
                          , imageLayerDataSegmentationMaskId = ""
                          }
                      in
                        (LayerTypeImage, Just (LayerDataImage imageData))
                    else if ext `elem` videoExts
                      then
                        let
                          videoData = VideoData
                            { videoDataAssetId = Just aid
                            , videoDataLoop = True
                            , videoDataPingPong = Nothing
                            , videoDataStartTime = 0.0
                            , videoDataEndTime = Nothing
                            , videoDataSpeed = 1.0
                            , videoDataSpeedMapEnabled = Nothing
                            , videoDataSpeedMap = Nothing
                            , videoDataTimeRemapEnabled = Nothing
                            , videoDataTimeRemap = Nothing
                            , videoDataTimewarpEnabled = Nothing
                            , videoDataTimewarpSpeed = Nothing
                            , videoDataTimewarpMethod = Nothing
                            , videoDataFrameBlending = Nothing
                            , videoDataAudioEnabled = Nothing
                            , videoDataAudioLevel = Nothing
                            , videoDataPosterFrame = 0.0
                            }
                        in
                          (LayerTypeVideo, Just (LayerDataVideo videoData))
                      else
                        (layerType existingLayer, layerData existingLayer)  -- Unknown extension, keep current type
                  
                  updatedLayer = existingLayer
                    { layerType = newLayerType
                    , layerData = newLayerData
                    , layerName = newName
                    }
                in
                  Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
              _ -> Left ("Cannot replace layer source: invalid asset ID or path")
          
          _ -> Left ("Unsupported source replacement: layer type " <> T.pack (show (layerType existingLayer)) <> " with replacement type " <> T.pack (show replacementType))

-- ════════════════════════════════════════════════════════════════════════════
--                                        // text // to // spline // conversion
-- ════════════════════════════════════════════════════════════════════════════

-- | Character vector group (pre-converted from async text-to-vector operation)
-- This represents paths for a single character
data CharacterVectorGroup = CharacterVectorGroup
  { characterVectorGroupCharacter :: Text
  , characterVectorGroupCharIndex :: Int
  , characterVectorGroupPaths :: [BezierPath]
  , characterVectorGroupBoundsX :: Double
  , characterVectorGroupBoundsY :: Double
  }
  deriving (Eq, Show)

-- | Convert BezierPath vertices to ControlPoint format
-- Pure function: takes BezierPath, returns ControlPoints
-- BezierVertex handles are RELATIVE, ControlPoint handles are ABSOLUTE
bezierPathToControlPoints ::
  BezierPath ->
  (Text -> Text) -> -- ID generator
  [ControlPoint]
bezierPathToControlPoints (BezierPath vertices _) genId =
  zipWith (\i vertex ->
    let
      point = bezierVertexPoint vertex
      inHandleRel = bezierVertexInHandle vertex
      outHandleRel = bezierVertexOutHandle vertex
      
      -- Convert relative handles to absolute
      handleIn = if point2DX inHandleRel /= 0.0 || point2DY inHandleRel /= 0.0
        then Just (ControlPointHandle (point2DX point + point2DX inHandleRel) (point2DY point + point2DY inHandleRel))
        else Nothing
      
      handleOut = if point2DX outHandleRel /= 0.0 || point2DY outHandleRel /= 0.0
        then Just (ControlPointHandle (point2DX point + point2DX outHandleRel) (point2DY point + point2DY outHandleRel))
        else Nothing
      
      pointType = if isJust handleIn || isJust handleOut
        then ControlPointTypeSmooth
        else ControlPointTypeCorner
    in
      ControlPoint
        { controlPointId = genId ("cp_" <> T.pack (show i))
        , controlPointX = point2DX point
        , controlPointY = point2DY point
        , controlPointDepth = Just 0.0
        , controlPointHandleIn = handleIn
        , controlPointHandleOut = handleOut
        , controlPointType = pointType
        , controlPointGroup = Nothing
        }
  ) [0 ..] vertices

-- | Convert a text layer to one or more spline layers
-- Pure function: takes layer ID, pre-converted paths, options, ID generators, composition settings, and layers list
-- Returns list of created layer IDs and new layers list, or error
--                                                                      // note
-- This function takes the already-converted paths as input.
convertTextLayerToSplines ::
  Text -> -- Text layer ID
  [BezierPath] -> -- All paths (from text-to-vector conversion)
  [CharacterVectorGroup] -> -- Per-character paths (from text-to-vector conversion)
  Bool -> -- Per character flag
  Bool -> -- Keep original flag
  Bool -> -- Group characters flag
  Double -> -- Composition width
  Double -> -- Composition height
  Int -> -- Composition frame count
  (Text -> Text) -> -- ID generator for layers
  (Text -> Text) -> -- ID generator for control points
  (Text -> Text) -> -- ID generator for transform properties
  (Text -> Text) -> -- ID generator for opacity property
  (Text -> Text) -> -- ID generator for audio properties
  CreateLayerOptions -> -- Creation options
  [Layer] -> -- Current layers list
  Either Text ([Text], [Layer]) -- Returns (created layer IDs, new layers list), or error
convertTextLayerToSplines textLayerId allPaths characterGroups perCharacter keepOriginal groupCharacters compWidth compHeight frameCount genLayerId genControlPointId genTransformId genOpacityId genAudioId defaultOptions layers =
  case getLayerById layers textLayerId of
    Nothing -> Left ("Text layer not found: " <> textLayerId)
    Just textLayer ->
      case (layerType textLayer, layerData textLayer) of
        (LayerTypeText, Just (LayerDataText textData)) ->
          let
            textContent = textDataText textData
          in
            if T.null textContent
              then Left ("Text layer has no text content: " <> textLayerId)
              else
                if null allPaths && null characterGroups
                  then Left ("No paths generated for text layer: " <> textLayerId)
                  else
                    let
                      -- Get text layer properties for spline styling
                      fillColor = textDataFill textData
                      strokeColor = textDataStroke textData
                      strokeWidth = textDataStrokeWidth textData
                      
                      -- Get parent ID
                      parentId = layerParentId textLayer
                      
                      -- Create spline layers
                      result = if perCharacter && not (null characterGroups)
                        then
                          -- Create one spline layer per character
                          let
                            -- Create parent group layer if requested
                            (groupLayerId, layersAfterGroup) = if groupCharacters
                              then
                                let
                                  groupLayerId_ = genLayerId (textLayerId <> "_group")
                                  groupOptions = defaultOptions {createLayerOptionsName = Just (layerName textLayer <> " (Group)")}
                                  groupLayer = createLayer groupLayerId_ LayerTypeNull groupOptions compWidth compHeight frameCount Nothing genTransformId genOpacityId genAudioId
                                  groupLayerWithTransform = groupLayer {layerTransform = layerTransform textLayer}
                                  layersWithGroup = groupLayerWithTransform : layers
                                in
                                  (Just groupLayerId_, layersWithGroup)
                              else
                                (parentId, layers)
                            
                            -- Create character layers
                            createCharLayer i charGroup =
                              let
                                -- Skip whitespace characters
                                char = characterVectorGroupCharacter charGroup
                                charPaths = characterVectorGroupPaths charGroup
                              in
                                if T.null (T.strip char) || null charPaths
                                  then Nothing
                                  else
                                    let
                                      -- Combine all paths for this character into one
                                      allControlPoints = concatMap (\path -> bezierPathToControlPoints path genControlPointId) charPaths
                                    in
                                      if null allControlPoints
                                        then Nothing
                                        else
                                          let
                                            charLayerName = layerName textLayer <> " - \"" <> char <> "\" [" <> T.pack (show i) <> "]"
                                            charLayerId_ = genLayerId (textLayerId <> "_char_" <> T.pack (show i))
                                            charOptions = defaultOptions {createLayerOptionsName = Just charLayerName}
                                            
                                            -- Determine if paths are closed (check first path)
                                            closed = case charPaths of
                                              (BezierPath _ closedFlag):_ -> closedFlag
                                              _ -> False
                                            
                                            splineData = SplineData
                                              { splineDataPathData = ""
                                              , splineDataControlPoints = allControlPoints
                                              , splineDataClosed = closed
                                              , splineDataStrokeType = Just SplineStrokeTypeSolid
                                              , splineDataStroke = strokeColor
                                              , splineDataStrokeGradient = Nothing
                                              , splineDataStrokeWidth = strokeWidth
                                              , splineDataStrokeOpacity = Nothing
                                              , splineDataLineCap = Nothing
                                              , splineDataLineJoin = Nothing
                                              , splineDataStrokeMiterLimit = Nothing
                                              , splineDataDashArray = Nothing
                                              , splineDataDashOffset = Nothing
                                              , splineDataFill = Just fillColor
                                              , splineDataFillOpacity = Nothing
                                              , splineDataTrimStart = Nothing
                                              , splineDataTrimEnd = Nothing
                                              , splineDataTrimOffset = Nothing
                                              , splineDataPathEffects = Nothing
                                              , splineDataAnimatedControlPoints = Nothing
                                              , splineDataAnimated = Nothing
                                              , splineDataLOD = Nothing
                                              , splineDataWarpPins = Nothing
                                              , splineDataPuppetPins = Nothing
                                              , splineDataAudioReactive = Nothing
                                              }
                                            
                                            charLayer = createLayer charLayerId_ LayerTypeSpline charOptions compWidth compHeight frameCount (Just (LayerDataSpline splineData)) genTransformId genOpacityId genAudioId
                                            
                                            charLayerWithData = charLayer
                                              { layerParentId = groupLayerId
                                              , layerInPoint = layerInPoint textLayer
                                              , layerOutPoint = layerOutPoint textLayer
                                              }
                                            
                                            -- Position relative to character bounds (if not grouped)
                                            finalCharLayer = if isNothing groupLayerId
                                              then
                                                let
                                                  transform = layerTransform charLayerWithData
                                                  positionProp = transformPosition transform
                                                  currentPos = animatablePropertyValue positionProp
                                                  newPos = Position2DOr3D
                                                    (position2DOr3DX currentPos + characterVectorGroupBoundsX charGroup)
                                                    (position2DOr3DY currentPos)
                                                    (position2DOr3DZ currentPos)
                                                  updatedPositionProp = positionProp {animatablePropertyValue = newPos}
                                                  updatedTransform = transform {transformPosition = updatedPositionProp}
                                                in
                                                  charLayerWithData {layerTransform = updatedTransform}
                                              else
                                                charLayerWithData
                                          in
                                            Just (layerId finalCharLayer, finalCharLayer)
                            
                            charLayers = mapMaybe (uncurry createCharLayer) (zip [0..] characterGroups)
                            createdIds = map fst charLayers
                            newLayers = map snd charLayers ++ layersAfterGroup
                            
                            -- Remove original layer if not keeping
                            finalLayers = if keepOriginal
                              then newLayers
                              else filter (\l -> layerId l /= textLayerId) newLayers
                          in
                            Right (createdIds, finalLayers)
                        else
                          -- Create single spline layer with all paths
                          let
                            allControlPoints = concatMap (\path -> bezierPathToControlPoints path genControlPointId) allPaths
                          in
                            if null allControlPoints
                              then Left ("No control points generated for text layer: " <> textLayerId)
                              else
                                let
                                  splineLayerId_ = genLayerId (textLayerId <> "_spline")
                                  splineOptions = defaultOptions {createLayerOptionsName = Just (layerName textLayer <> " (Spline)")}
                                  
                                  -- Determine if paths are closed (check first path)
                                  closed = case allPaths of
                                    (BezierPath _ closedFlag):_ -> closedFlag
                                    _ -> False
                                  
                                  splineData = SplineData
                                    { splineDataPathData = ""
                                    , splineDataControlPoints = allControlPoints
                                    , splineDataClosed = closed
                                    , splineDataStrokeType = Just SplineStrokeTypeSolid
                                    , splineDataStroke = strokeColor
                                    , splineDataStrokeGradient = Nothing
                                    , splineDataStrokeWidth = strokeWidth
                                    , splineDataStrokeOpacity = Nothing
                                    , splineDataLineCap = Nothing
                                    , splineDataLineJoin = Nothing
                                    , splineDataStrokeMiterLimit = Nothing
                                    , splineDataDashArray = Nothing
                                    , splineDataDashOffset = Nothing
                                    , splineDataFill = Just fillColor
                                    , splineDataFillOpacity = Nothing
                                    , splineDataTrimStart = Nothing
                                    , splineDataTrimEnd = Nothing
                                    , splineDataTrimOffset = Nothing
                                    , splineDataPathEffects = Nothing
                                    , splineDataAnimatedControlPoints = Nothing
                                    , splineDataAnimated = Nothing
                                    , splineDataLOD = Nothing
                                    , splineDataWarpPins = Nothing
                                    , splineDataPuppetPins = Nothing
                                    , splineDataAudioReactive = Nothing
                                    }
                                  
                                  splineLayer = createLayer splineLayerId_ LayerTypeSpline splineOptions compWidth compHeight frameCount (Just (LayerDataSpline splineData)) genTransformId genOpacityId genAudioId
                                  
                                  splineLayerWithData = splineLayer
                                    { layerTransform = layerTransform textLayer
                                    , layerParentId = parentId
                                    , layerInPoint = layerInPoint textLayer
                                    , layerOutPoint = layerOutPoint textLayer
                                    }
                                  
                                  createdId = layerId splineLayerWithData
                                  
                                  -- Remove original layer if not keeping
                                  finalLayers = if keepOriginal
                                    then splineLayerWithData : layers
                                    else splineLayerWithData : filter (\l -> layerId l /= textLayerId) layers
                                in
                                  Right ([createdId], finalLayers)
                    in
                      result
        _ -> Left ("Layer is not a text layer: " <> textLayerId)
