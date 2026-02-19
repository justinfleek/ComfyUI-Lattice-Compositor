-- |
-- Module      : Lattice.Types.LayerData3D
-- Description : 3D layer data types (Model, PointCloud, Camera)
-- 
-- Migrated from ui/src/types/project.ts
-- These types depend on AnimatableProperty and Vec3
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.LayerData3D
  ( -- Model layer
    ModelLayerData(..)
  , ModelFormat(..)
  , ModelMaterialOverride(..)
  , ModelAnimationClip(..)
  , ModelAnimation(..)
  , ModelLOD(..)
  , ModelBoundingBox(..)
  , ModelScale(..)
  -- Point cloud layer
  , PointCloudLayerData(..)
  , PointCloudFormat(..)
  , PointCloudColorMode(..)
  , PointCloudRenderMode(..)
  , PointCloudColorGradient(..)
  , PointCloudGradientStop(..)
  , PointCloudLOD(..)
  , PointCloudOctree(..)
  , PointCloudEDL(..)
  , PointCloudClipPlane(..)
  -- Camera layer
  , CameraLayerData(..)
  , CameraType(..)
  , Camera3D(..)
  , CameraDepthOfField(..)
  , CameraPathFollowing(..)
  , CameraShakeData(..)
  , CameraShakeType(..)
  , CameraRackFocusData(..)
  , CameraRackFocusEasing(..)
  , CameraAutoFocusData(..)
  , CameraAutoFocusMode(..)
  , CameraPathFollowingData(..)
  , CameraLookMode(..)
  , CameraTrajectoryKeyframes(..)
  , CameraTrajectoryPositionKeyframe(..)
  , CameraTrajectoryPOIKeyframe(..)
  , CameraTrajectoryZoomKeyframe(..)
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
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  )
import Lattice.Types.Primitives
  ( Vec3(..)
  , validateFinite
  , validateNonNegative
  , validateNormalized01
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // model // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Model format
data ModelFormat
  = ModelFormatGLTF
  | ModelFormatGLB
  | ModelFormatOBJ
  | ModelFormatFBX
  | ModelFormatUSD
  | ModelFormatUSDA
  | ModelFormatUSDC
  | ModelFormatUSDZ
  | ModelFormatDAE
  deriving (Eq, Show, Generic)

instance ToJSON ModelFormat where
  toJSON ModelFormatGLTF = "gltf"
  toJSON ModelFormatGLB = "glb"
  toJSON ModelFormatOBJ = "obj"
  toJSON ModelFormatFBX = "fbx"
  toJSON ModelFormatUSD = "usd"
  toJSON ModelFormatUSDA = "usda"
  toJSON ModelFormatUSDC = "usdc"
  toJSON ModelFormatUSDZ = "usdz"
  toJSON ModelFormatDAE = "dae"

instance FromJSON ModelFormat where
  parseJSON = withText "ModelFormat" $ \s ->
    case s of
      t | t == T.pack "gltf" -> return ModelFormatGLTF
      t | t == T.pack "glb" -> return ModelFormatGLB
      t | t == T.pack "obj" -> return ModelFormatOBJ
      t | t == T.pack "fbx" -> return ModelFormatFBX
      t | t == T.pack "usd" -> return ModelFormatUSD
      t | t == T.pack "usda" -> return ModelFormatUSDA
      t | t == T.pack "usdc" -> return ModelFormatUSDC
      t | t == T.pack "usdz" -> return ModelFormatUSDZ
      t | t == T.pack "dae" -> return ModelFormatDAE
      _ -> fail "Invalid ModelFormat"

-- | Model material override options
data ModelMaterialOverride = ModelMaterialOverride
  { modelMaterialOverrideColorOverride :: Maybe Text  -- Override all materials with a single color
  , modelMaterialOverrideOpacityOverride :: Maybe Double  -- Override opacity (0-1)
  , modelMaterialOverrideWireframe :: Maybe Bool  -- Use wireframe rendering
  , modelMaterialOverrideWireframeColor :: Maybe Text  -- Wireframe color
  , modelMaterialOverrideFlatShading :: Maybe Bool  -- Use flat shading
  , modelMaterialOverrideMetalness :: Maybe Double  -- Override metalness (0-1)
  , modelMaterialOverrideRoughness :: Maybe Double  -- Override roughness (0-1)
  , modelMaterialOverrideEmissive :: Maybe Text  -- Emissive color
  , modelMaterialOverrideEmissiveIntensity :: Maybe Double  -- Emissive intensity
  , modelMaterialOverrideUseDepthMaterial :: Maybe Bool  -- Use depth material (for depth maps)
  , modelMaterialOverrideUseNormalMaterial :: Maybe Bool  -- Use normal material (for normal maps)
  }
  deriving (Eq, Show, Generic)

instance ToJSON ModelMaterialOverride where
  toJSON (ModelMaterialOverride mColor mOpacity mWireframe mWireframeColor mFlatShading mMetalness mRoughness mEmissive mEmissiveIntensity mUseDepth mUseNormal) =
    let
      baseFields = []
      f1 = case mColor of Just c -> ("colorOverride" .= c) : baseFields; Nothing -> baseFields
      f2 = case mOpacity of Just o -> ("opacityOverride" .= o) : f1; Nothing -> f1
      f3 = case mWireframe of Just w -> ("wireframe" .= w) : f2; Nothing -> f2
      f4 = case mWireframeColor of Just wc -> ("wireframeColor" .= wc) : f3; Nothing -> f3
      f5 = case mFlatShading of Just f -> ("flatShading" .= f) : f4; Nothing -> f4
      f6 = case mMetalness of Just m -> ("metalness" .= m) : f5; Nothing -> f5
      f7 = case mRoughness of Just r -> ("roughness" .= r) : f6; Nothing -> f6
      f8 = case mEmissive of Just e -> ("emissive" .= e) : f7; Nothing -> f7
      f9 = case mEmissiveIntensity of Just ei -> ("emissiveIntensity" .= ei) : f8; Nothing -> f8
      f10 = case mUseDepth of Just d -> ("useDepthMaterial" .= d) : f9; Nothing -> f9
      f11 = case mUseNormal of Just n -> ("useNormalMaterial" .= n) : f10; Nothing -> f10
    in object f11

instance FromJSON ModelMaterialOverride where
  parseJSON = withObject "ModelMaterialOverride" $ \o -> do
    mColor <- o .:? "colorOverride"
    mOpacity <- o .:? "opacityOverride"
    mWireframe <- o .:? "wireframe"
    mWireframeColor <- o .:? "wireframeColor"
    mFlatShading <- o .:? "flatShading"
    mMetalness <- o .:? "metalness"
    mRoughness <- o .:? "roughness"
    mEmissive <- o .:? "emissive"
    mEmissiveIntensity <- o .:? "emissiveIntensity"
    mUseDepth <- o .:? "useDepthMaterial"
    mUseNormal <- o .:? "useNormalMaterial"
    -- Validate numeric values if present
    case mOpacity of
      Nothing -> return ()
      Just op -> if validateNormalized01 op
        then return ()
        else fail "ModelMaterialOverride: opacityOverride must be in range [0, 1]"
    case mMetalness of
      Nothing -> return ()
      Just m -> if validateNormalized01 m
        then return ()
        else fail "ModelMaterialOverride: metalness must be in range [0, 1]"
    case mRoughness of
      Nothing -> return ()
      Just r -> if validateNormalized01 r
        then return ()
        else fail "ModelMaterialOverride: roughness must be in range [0, 1]"
    case mEmissiveIntensity of
      Nothing -> return ()
      Just ei -> if validateFinite ei && validateNonNegative ei
        then return ()
        else fail "ModelMaterialOverride: emissiveIntensity must be finite and non-negative"
    return (ModelMaterialOverride mColor mOpacity mWireframe mWireframeColor mFlatShading mMetalness mRoughness mEmissive mEmissiveIntensity mUseDepth mUseNormal)

-- | Model animation clip info
data ModelAnimationClip = ModelAnimationClip
  { modelAnimationClipName :: Text
  , modelAnimationClipDuration :: Double  -- In seconds
  , modelAnimationClipFrameCount :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON ModelAnimationClip where
  toJSON (ModelAnimationClip name duration frameCount) =
    object
      [ "name" .= name
      , "duration" .= duration
      , "frameCount" .= frameCount
      ]

instance FromJSON ModelAnimationClip where
  parseJSON = withObject "ModelAnimationClip" $ \o -> do
    name <- o .: "name"
    duration <- o .: "duration"
    frameCount <- o .: "frameCount"
    if validateFinite duration && validateFinite frameCount &&
       validateNonNegative duration && validateNonNegative frameCount
      then return (ModelAnimationClip name duration frameCount)
      else fail "ModelAnimationClip: duration and frameCount must be finite and non-negative"

-- | Model animation settings
data ModelAnimation = ModelAnimation
  { modelAnimationClips :: [ModelAnimationClip]  -- Available animation clips in the model
  , modelAnimationActiveClip :: Maybe Text  -- Currently active clip name
  , modelAnimationTime :: AnimatableProperty Double  -- Animation time (can be keyframed for scrubbing)
  , modelAnimationSpeed :: Double  -- Playback speed multiplier
  , modelAnimationLoop :: Bool  -- Loop animation
  , modelAnimationAutoPlay :: Bool  -- Auto-play animation
  }
  deriving (Eq, Show, Generic)

instance ToJSON ModelAnimation where
  toJSON (ModelAnimation clips mActiveClip time speed loop autoPlay) =
    let
      baseFields = ["clips" .= clips, "time" .= time, "speed" .= speed, "loop" .= loop, "autoPlay" .= autoPlay]
      withActiveClip = case mActiveClip of Just a -> ("activeClip" .= a) : baseFields; Nothing -> baseFields
    in object withActiveClip

instance FromJSON ModelAnimation where
  parseJSON = withObject "ModelAnimation" $ \o -> do
    clips <- o .: "clips"
    mActiveClip <- o .:? "activeClip"
    time <- o .: "time"
    speed <- o .: "speed"
    loop <- o .: "loop"
    autoPlay <- o .: "autoPlay"
    if validateFinite speed && validateNonNegative speed
      then return (ModelAnimation clips mActiveClip time speed loop autoPlay)
      else fail "ModelAnimation: speed must be finite and non-negative"

-- | Model bounding box info
data ModelBoundingBox = ModelBoundingBox
  { modelBoundingBoxMin :: Vec3
  , modelBoundingBoxMax :: Vec3
  , modelBoundingBoxCenter :: Vec3
  , modelBoundingBoxSize :: Vec3
  }
  deriving (Eq, Show, Generic)

instance ToJSON ModelBoundingBox where
  toJSON (ModelBoundingBox min_ max_ center size) =
    object
      [ "min" .= min_
      , "max" .= max_
      , "center" .= center
      , "size" .= size
      ]

instance FromJSON ModelBoundingBox where
  parseJSON = withObject "ModelBoundingBox" $ \o -> do
    min_ <- o .: "min"
    max_ <- o .: "max"
    center <- o .: "center"
    size <- o .: "size"
    return (ModelBoundingBox min_ max_ center size)

-- | Model scale (uniform or per-axis)
data ModelScale
  = ModelScaleUniform (AnimatableProperty Double)
  | ModelScalePerAxis
    { modelScaleX :: AnimatableProperty Double
    , modelScaleY :: AnimatableProperty Double
    , modelScaleZ :: AnimatableProperty Double
    }
  deriving (Eq, Show, Generic)

instance ToJSON ModelScale where
  toJSON (ModelScaleUniform scale) = toJSON scale
  toJSON (ModelScalePerAxis x y z) =
    object ["x" .= x, "y" .= y, "z" .= z]

instance FromJSON ModelScale where
  parseJSON v@(Object o) = do
    -- Try to parse as per-axis first (has x, y, z)
    x <- o .:? "x"
    y <- o .:? "y"
    z <- o .:? "z"
    case (x, y, z) of
      (Just x', Just y', Just z') ->
        return (ModelScalePerAxis x' y' z')
      _ -> do
        -- Otherwise parse as uniform scale (single number)
        scale <- parseJSON v
        return (ModelScaleUniform scale)
  parseJSON v = do
    -- Single number = uniform scale
    scale <- parseJSON v
    return (ModelScaleUniform scale)

-- | Model LOD settings
data ModelLOD = ModelLOD
  { modelLODEnabled :: Bool
  , modelLODDistances :: [Double]  -- Distance thresholds for LOD levels
  , modelLODAssetIds :: [Text]  -- Asset IDs for lower-detail versions
  }
  deriving (Eq, Show, Generic)

instance ToJSON ModelLOD where
  toJSON (ModelLOD enabled distances assetIds) =
    object
      [ "enabled" .= enabled
      , "distances" .= distances
      , "lodAssetIds" .= assetIds
      ]

instance FromJSON ModelLOD where
  parseJSON = withObject "ModelLOD" $ \o -> do
    enabled <- o .: "enabled"
    distances <- o .: "distances"
    assetIds <- o .: "lodAssetIds"
    -- Validate distances are finite and non-negative
    if all (\d -> validateFinite d && validateNonNegative d) distances
      then return (ModelLOD enabled distances assetIds)
      else fail "ModelLOD: all distances must be finite and non-negative"

-- | 3D Model layer data
data ModelLayerData = ModelLayerData
  { modelLayerDataAssetId :: Text  -- Asset ID reference to the model file
  , modelLayerDataFormat :: ModelFormat  -- Original format of the model
  , modelLayerDataScale :: ModelScale  -- Model scale (uniform or per-axis)
  , modelLayerDataUniformScale :: Bool  -- Use uniform scale
  , modelLayerDataMaterialOverride :: Maybe ModelMaterialOverride  -- Material overrides
  , modelLayerDataAnimation :: Maybe ModelAnimation  -- Animation settings
  , modelLayerDataBoundingBox :: Maybe ModelBoundingBox  -- Bounding box (calculated after load)
  , modelLayerDataCastShadow :: Bool  -- Cast shadows
  , modelLayerDataReceiveShadow :: Bool  -- Receive shadows
  , modelLayerDataFrustumCulled :: Bool  -- Frustum culling
  , modelLayerDataRenderOrder :: Double  -- Render order (for transparency sorting)
  , modelLayerDataShowBoundingBox :: Bool  -- Show bounding box wireframe in editor
  , modelLayerDataShowSkeleton :: Bool  -- Show skeleton/bones for skinned meshes
  , modelLayerDataEnvMapIntensity :: Double  -- Environment map intensity (0-1)
  , modelLayerDataLOD :: Maybe ModelLOD  -- LOD (Level of Detail) settings
  }
  deriving (Eq, Show, Generic)

instance ToJSON ModelLayerData where
  toJSON (ModelLayerData assetId format scale uniformScale mMaterialOverride mAnimation mBoundingBox castShadow receiveShadow frustumCulled renderOrder showBoundingBox showSkeleton envMapIntensity mLOD) =
    let
      baseFields = ["assetId" .= assetId, "format" .= format, "scale" .= scale, "uniformScale" .= uniformScale, "castShadow" .= castShadow, "receiveShadow" .= receiveShadow, "frustumCulled" .= frustumCulled, "renderOrder" .= renderOrder, "showBoundingBox" .= showBoundingBox, "showSkeleton" .= showSkeleton, "envMapIntensity" .= envMapIntensity]
      f1 = case mMaterialOverride of Just m -> ("materialOverride" .= m) : baseFields; Nothing -> baseFields
      f2 = case mAnimation of Just a -> ("animation" .= a) : f1; Nothing -> f1
      f3 = case mBoundingBox of Just b -> ("boundingBox" .= b) : f2; Nothing -> f2
      f4 = case mLOD of Just l -> ("lod" .= l) : f3; Nothing -> f3
    in object f4

instance FromJSON ModelLayerData where
  parseJSON = withObject "ModelLayerData" $ \o -> do
    assetId <- o .: "assetId"
    format <- o .: "format"
    scale <- o .: "scale"
    uniformScale <- o .: "uniformScale"
    mMaterialOverride <- o .:? "materialOverride"
    mAnimation <- o .:? "animation"
    mBoundingBox <- o .:? "boundingBox"
    castShadow <- o .: "castShadow"
    receiveShadow <- o .: "receiveShadow"
    frustumCulled <- o .: "frustumCulled"
    renderOrder <- o .: "renderOrder"
    showBoundingBox <- o .: "showBoundingBox"
    showSkeleton <- o .: "showSkeleton"
    envMapIntensity <- o .: "envMapIntensity"
    mLOD <- o .:? "lod"
    -- Validate numeric values
    if validateFinite renderOrder && validateNormalized01 envMapIntensity
      then return (ModelLayerData assetId format scale uniformScale mMaterialOverride mAnimation mBoundingBox castShadow receiveShadow frustumCulled renderOrder showBoundingBox showSkeleton envMapIntensity mLOD)
      else fail "ModelLayerData: renderOrder must be finite, envMapIntensity must be in range [0, 1]"

-- ════════════════════════════════════════════════════════════════════════════
--                                           // point // cloud // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Point cloud format
data PointCloudFormat
  = PointCloudFormatPLY
  | PointCloudFormatPCD
  | PointCloudFormatLAS
  | PointCloudFormatLAZ
  | PointCloudFormatXYZ
  | PointCloudFormatPTS
  deriving (Eq, Show, Generic)

instance ToJSON PointCloudFormat where
  toJSON PointCloudFormatPLY = "ply"
  toJSON PointCloudFormatPCD = "pcd"
  toJSON PointCloudFormatLAS = "las"
  toJSON PointCloudFormatLAZ = "laz"
  toJSON PointCloudFormatXYZ = "xyz"
  toJSON PointCloudFormatPTS = "pts"

instance FromJSON PointCloudFormat where
  parseJSON = withText "PointCloudFormat" $ \s ->
    case s of
      t | t == T.pack "ply" -> return PointCloudFormatPLY
      t | t == T.pack "pcd" -> return PointCloudFormatPCD
      t | t == T.pack "las" -> return PointCloudFormatLAS
      t | t == T.pack "laz" -> return PointCloudFormatLAZ
      t | t == T.pack "xyz" -> return PointCloudFormatXYZ
      t | t == T.pack "pts" -> return PointCloudFormatPTS
      _ -> fail "Invalid PointCloudFormat"

-- | Point cloud coloring mode
data PointCloudColorMode
  = PointCloudColorModeRGB  -- Use embedded RGB colors
  | PointCloudColorModeIntensity  -- Color by intensity value
  | PointCloudColorModeHeight  -- Color by Z position (height map)
  | PointCloudColorModeDepth  -- Color by distance from camera
  | PointCloudColorModeNormal  -- Color by surface normal
  | PointCloudColorModeClassification  -- Color by point classification (LAS)
  | PointCloudColorModeUniform  -- Single uniform color
  deriving (Eq, Show, Generic)

instance ToJSON PointCloudColorMode where
  toJSON PointCloudColorModeRGB = "rgb"
  toJSON PointCloudColorModeIntensity = "intensity"
  toJSON PointCloudColorModeHeight = "height"
  toJSON PointCloudColorModeDepth = "depth"
  toJSON PointCloudColorModeNormal = "normal"
  toJSON PointCloudColorModeClassification = "classification"
  toJSON PointCloudColorModeUniform = "uniform"

instance FromJSON PointCloudColorMode where
  parseJSON = withText "PointCloudColorMode" $ \s ->
    case s of
      t | t == T.pack "rgb" -> return PointCloudColorModeRGB
      t | t == T.pack "intensity" -> return PointCloudColorModeIntensity
      t | t == T.pack "height" -> return PointCloudColorModeHeight
      t | t == T.pack "depth" -> return PointCloudColorModeDepth
      t | t == T.pack "normal" -> return PointCloudColorModeNormal
      t | t == T.pack "classification" -> return PointCloudColorModeClassification
      t | t == T.pack "uniform" -> return PointCloudColorModeUniform
      _ -> fail "Invalid PointCloudColorMode"

-- | Point cloud rendering mode
data PointCloudRenderMode
  = PointCloudRenderModePoints  -- Standard GL_POINTS
  | PointCloudRenderModeCircles  -- Screen-space circles (anti-aliased)
  | PointCloudRenderModeSquares  -- Screen-space squares
  | PointCloudRenderModeSplats  -- Gaussian splats (3DGS-style)
  deriving (Eq, Show, Generic)

instance ToJSON PointCloudRenderMode where
  toJSON PointCloudRenderModePoints = "points"
  toJSON PointCloudRenderModeCircles = "circles"
  toJSON PointCloudRenderModeSquares = "squares"
  toJSON PointCloudRenderModeSplats = "splats"

instance FromJSON PointCloudRenderMode where
  parseJSON = withText "PointCloudRenderMode" $ \s ->
    case s of
      t | t == T.pack "points" -> return PointCloudRenderModePoints
      t | t == T.pack "circles" -> return PointCloudRenderModeCircles
      t | t == T.pack "squares" -> return PointCloudRenderModeSquares
      t | t == T.pack "splats" -> return PointCloudRenderModeSplats
      _ -> fail "Invalid PointCloudRenderMode"

-- | Color gradient stop
data PointCloudGradientStop = PointCloudGradientStop
  { pointCloudGradientStopPosition :: Double
  , pointCloudGradientStopColor :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON PointCloudGradientStop where
  toJSON (PointCloudGradientStop position color) =
    object ["position" .= position, "color" .= color]

instance FromJSON PointCloudGradientStop where
  parseJSON = withObject "PointCloudGradientStop" $ \o -> do
    position <- o .: "position"
    color <- o .: "color"
    if validateFinite position && validateNormalized01 position
      then return (PointCloudGradientStop position color)
      else fail "PointCloudGradientStop: position must be finite and in range [0, 1]"

-- | Color gradient for height/depth/intensity modes
data PointCloudColorGradient = PointCloudColorGradient
  { pointCloudColorGradientStops :: [PointCloudGradientStop]
  }
  deriving (Eq, Show, Generic)

instance ToJSON PointCloudColorGradient where
  toJSON (PointCloudColorGradient stops) =
    object ["stops" .= stops]

instance FromJSON PointCloudColorGradient where
  parseJSON = withObject "PointCloudColorGradient" $ \o -> do
    stops <- o .: "stops"
    return (PointCloudColorGradient stops)

-- | Point cloud LOD settings
data PointCloudLOD = PointCloudLOD
  { pointCloudLODEnabled :: Bool
  , pointCloudLODMaxPoints :: [Double]  -- Max points to render at each LOD level
  , pointCloudLODDistances :: [Double]  -- Distance thresholds
  }
  deriving (Eq, Show, Generic)

instance ToJSON PointCloudLOD where
  toJSON (PointCloudLOD enabled maxPoints distances) =
    object
      [ "enabled" .= enabled
      , "maxPoints" .= maxPoints
      , "distances" .= distances
      ]

instance FromJSON PointCloudLOD where
  parseJSON = withObject "PointCloudLOD" $ \o -> do
    enabled <- o .: "enabled"
    maxPoints <- o .: "maxPoints"
    distances <- o .: "distances"
    -- Validate numeric values
    if all (\p -> validateFinite p && validateNonNegative p) maxPoints &&
       all (\d -> validateFinite d && validateNonNegative d) distances
      then return (PointCloudLOD enabled maxPoints distances)
      else fail "PointCloudLOD: maxPoints and distances must be finite and non-negative"

-- | Point cloud octree acceleration
data PointCloudOctree = PointCloudOctree
  { pointCloudOctreeEnabled :: Bool
  , pointCloudOctreeMaxDepth :: Double  -- Max depth of octree
  , pointCloudOctreePointsPerNode :: Double  -- Points per node before splitting
  }
  deriving (Eq, Show, Generic)

instance ToJSON PointCloudOctree where
  toJSON (PointCloudOctree enabled maxDepth pointsPerNode) =
    object
      [ "enabled" .= enabled
      , "maxDepth" .= maxDepth
      , "pointsPerNode" .= pointsPerNode
      ]

instance FromJSON PointCloudOctree where
  parseJSON = withObject "PointCloudOctree" $ \o -> do
    enabled <- o .: "enabled"
    maxDepth <- o .: "maxDepth"
    pointsPerNode <- o .: "pointsPerNode"
    if validateFinite maxDepth && validateFinite pointsPerNode &&
       validateNonNegative maxDepth && validateNonNegative pointsPerNode
      then return (PointCloudOctree enabled maxDepth pointsPerNode)
      else fail "PointCloudOctree: maxDepth and pointsPerNode must be finite and non-negative"

-- | Point cloud EDL (Eye-Dome Lighting)
data PointCloudEDL = PointCloudEDL
  { pointCloudEDLEnabled :: Bool
  , pointCloudEDLStrength :: Double
  , pointCloudEDLRadius :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON PointCloudEDL where
  toJSON (PointCloudEDL enabled strength radius) =
    object
      [ "enabled" .= enabled
      , "strength" .= strength
      , "radius" .= radius
      ]

instance FromJSON PointCloudEDL where
  parseJSON = withObject "PointCloudEDL" $ \o -> do
    enabled <- o .: "enabled"
    strength <- o .: "strength"
    radius <- o .: "radius"
    if validateFinite strength && validateFinite radius &&
       validateNonNegative strength && validateNonNegative radius
      then return (PointCloudEDL enabled strength radius)
      else fail "PointCloudEDL: strength and radius must be finite and non-negative"

-- | Point cloud clipping plane
data PointCloudClipPlane = PointCloudClipPlane
  { pointCloudClipPlaneNormal :: Vec3
  , pointCloudClipPlaneConstant :: Double
  , pointCloudClipPlaneEnabled :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON PointCloudClipPlane where
  toJSON (PointCloudClipPlane normal constant enabled) =
    object
      [ "normal" .= normal
      , "constant" .= constant
      , "enabled" .= enabled
      ]

instance FromJSON PointCloudClipPlane where
  parseJSON = withObject "PointCloudClipPlane" $ \o -> do
    normal <- o .: "normal"
    constant <- o .: "constant"
    enabled <- o .: "enabled"
    if validateFinite constant
      then return (PointCloudClipPlane normal constant enabled)
      else fail "PointCloudClipPlane: constant must be finite"

-- | Point cloud layer data
data PointCloudLayerData = PointCloudLayerData
  { pointCloudLayerDataAssetId :: Text  -- Asset ID reference to the point cloud file
  , pointCloudLayerDataFormat :: PointCloudFormat  -- Original format
  , pointCloudLayerDataPointCount :: Double  -- Total point count (from file)
  , pointCloudLayerDataPointSize :: AnimatableProperty Double  -- Point size (in world units or pixels depending on sizeAttenuation)
  , pointCloudLayerDataSizeAttenuation :: Bool  -- Size attenuation (points get smaller with distance)
  , pointCloudLayerDataMinPointSize :: Double  -- Minimum point size (pixels)
  , pointCloudLayerDataMaxPointSize :: Double  -- Maximum point size (pixels)
  , pointCloudLayerDataColorMode :: PointCloudColorMode  -- Coloring mode
  , pointCloudLayerDataUniformColor :: Text  -- Uniform color (when colorMode = 'uniform')
  , pointCloudLayerDataColorGradient :: Maybe PointCloudColorGradient  -- Color gradient for height/depth/intensity modes
  , pointCloudLayerDataRenderMode :: PointCloudRenderMode  -- Render mode
  , pointCloudLayerDataOpacity :: AnimatableProperty Double  -- Point opacity (0-1)
  , pointCloudLayerDataDepthTest :: Bool  -- Enable depth testing
  , pointCloudLayerDataDepthWrite :: Bool  -- Write to depth buffer
  , pointCloudLayerDataBoundingBox :: Maybe ModelBoundingBox  -- Bounding box
  , pointCloudLayerDataShowBoundingBox :: Bool  -- Show bounding box wireframe
  , pointCloudLayerDataLOD :: Maybe PointCloudLOD  -- Level of detail settings
  , pointCloudLayerDataOctree :: Maybe PointCloudOctree  -- Octree acceleration (for large point clouds)
  , pointCloudLayerDataPointBudget :: Double  -- Point budget (max points to render per frame)
  , pointCloudLayerDataEDL :: Maybe PointCloudEDL  -- EDL (Eye-Dome Lighting) for better depth perception
  , pointCloudLayerDataClipPlanes :: Maybe [PointCloudClipPlane]  -- Clipping planes
  , pointCloudLayerDataClassificationFilter :: Maybe [Double]  -- Classification filter (for LAS files)
  , pointCloudLayerDataIntensityRange :: Maybe (Double, Double)  -- Intensity range filter (min, max)
  }
  deriving (Eq, Show, Generic)

instance ToJSON PointCloudLayerData where
  toJSON (PointCloudLayerData assetId format pointCount pointSize sizeAttenuation minPointSize maxPointSize colorMode uniformColor mColorGradient renderMode opacity depthTest depthWrite mBoundingBox showBoundingBox mLOD mOctree pointBudget mEDL mClipPlanes mClassificationFilter mIntensityRange) =
    let
      baseFields = ["assetId" .= assetId, "format" .= format, "pointCount" .= pointCount, "pointSize" .= pointSize, "sizeAttenuation" .= sizeAttenuation, "minPointSize" .= minPointSize, "maxPointSize" .= maxPointSize, "colorMode" .= colorMode, "uniformColor" .= uniformColor, "renderMode" .= renderMode, "opacity" .= opacity, "depthTest" .= depthTest, "depthWrite" .= depthWrite, "showBoundingBox" .= showBoundingBox, "pointBudget" .= pointBudget]
      f1 = case mColorGradient of Just g -> ("colorGradient" .= g) : baseFields; Nothing -> baseFields
      f2 = case mBoundingBox of Just b -> ("boundingBox" .= b) : f1; Nothing -> f1
      f3 = case mLOD of Just l -> ("lod" .= l) : f2; Nothing -> f2
      f4 = case mOctree of Just o -> ("octree" .= o) : f3; Nothing -> f3
      f5 = case mEDL of Just e -> ("edl" .= e) : f4; Nothing -> f4
      f6 = case mClipPlanes of Just c -> ("clipPlanes" .= c) : f5; Nothing -> f5
      f7 = case mClassificationFilter of Just f -> ("classificationFilter" .= f) : f6; Nothing -> f6
      f8 = case mIntensityRange of Just r -> ("intensityRange" .= object ["min" .= fst r, "max" .= snd r]) : f7; Nothing -> f7
    in object f8

instance FromJSON PointCloudLayerData where
  parseJSON = withObject "PointCloudLayerData" $ \o -> do
    assetId <- o .: "assetId"
    format <- o .: "format"
    pointCount <- o .: "pointCount"
    pointSize <- o .: "pointSize"
    sizeAttenuation <- o .: "sizeAttenuation"
    minPointSize <- o .: "minPointSize"
    maxPointSize <- o .: "maxPointSize"
    colorMode <- o .: "colorMode"
    uniformColor <- o .: "uniformColor"
    mColorGradient <- o .:? "colorGradient"
    renderMode <- o .: "renderMode"
    opacity <- o .: "opacity"
    depthTest <- o .: "depthTest"
    depthWrite <- o .: "depthWrite"
    mBoundingBox <- o .:? "boundingBox"
    showBoundingBox <- o .: "showBoundingBox"
    mLOD <- o .:? "lod"
    mOctree <- o .:? "octree"
    pointBudget <- o .: "pointBudget"
    mEDL <- o .:? "edl"
    mClipPlanes <- o .:? "clipPlanes"
    mClassificationFilter <- o .:? "classificationFilter"
    mIntensityRangeObj <- o .:? "intensityRange"
    mIntensityRange <- case mIntensityRangeObj of
      Nothing -> return Nothing
      Just obj -> do
        min_ <- obj .: "min"
        max_ <- obj .: "max"
        return (Just (min_, max_))
    -- Validate numeric values
    if validateFinite pointCount && validateFinite minPointSize &&
       validateFinite maxPointSize && validateFinite pointBudget &&
       validateNonNegative pointCount && validateNonNegative minPointSize &&
       validateNonNegative maxPointSize && validateNonNegative pointBudget &&
       minPointSize <= maxPointSize &&
       maybe True (\(min_, max_) -> validateFinite min_ && validateFinite max_ && min_ <= max_) mIntensityRange
      then return (PointCloudLayerData assetId format pointCount pointSize sizeAttenuation minPointSize maxPointSize colorMode uniformColor mColorGradient renderMode opacity depthTest depthWrite mBoundingBox showBoundingBox mLOD mOctree pointBudget mEDL mClipPlanes mClassificationFilter mIntensityRange)
      else fail "PointCloudLayerData: numeric values must be finite and within valid ranges"

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // camera // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Camera type
data CameraType
  = CameraTypeOneNode
  | CameraTypeTwoNode
  deriving (Eq, Show, Generic)

instance ToJSON CameraType where
  toJSON CameraTypeOneNode = "one-node"
  toJSON CameraTypeTwoNode = "two-node"

instance FromJSON CameraType where
  parseJSON = withText "CameraType" $ \s ->
    case s of
      t | t == T.pack "one-node" -> return CameraTypeOneNode
      t | t == T.pack "two-node" -> return CameraTypeTwoNode
      _ -> fail "Invalid CameraType"

-- | Camera 3D object (inline storage)
data Camera3D = Camera3D
  { camera3DType :: CameraType
  , camera3DPosition :: Vec3
  , camera3DPointOfInterest :: Vec3
  , camera3DZoom :: Double
  , camera3DDepthOfField :: Bool
  , camera3DFocusDistance :: Double
  , camera3DAperture :: Double
  , camera3DBlurLevel :: Double
  , camera3DXRotation :: Double
  , camera3DYRotation :: Double
  , camera3DZRotation :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON Camera3D where
  toJSON (Camera3D cType position poi zoom dof focusDist aperture blurLevel xRot yRot zRot) =
    object
      [ "type" .= cType
      , "position" .= position
      , "pointOfInterest" .= poi
      , "zoom" .= zoom
      , "depthOfField" .= dof
      , "focusDistance" .= focusDist
      , "aperture" .= aperture
      , "blurLevel" .= blurLevel
      , "xRotation" .= xRot
      , "yRotation" .= yRot
      , "zRotation" .= zRot
      ]

instance FromJSON Camera3D where
  parseJSON = withObject "Camera3D" $ \o -> do
    cType <- o .: "type"
    position <- o .: "position"
    poi <- o .: "pointOfInterest"
    zoom <- o .: "zoom"
    dof <- o .: "depthOfField"
    focusDist <- o .: "focusDistance"
    aperture <- o .: "aperture"
    blurLevel <- o .: "blurLevel"
    xRot <- o .: "xRotation"
    yRot <- o .: "yRotation"
    zRot <- o .: "zRotation"
    -- Validate numeric values
    if validateFinite zoom && validateFinite focusDist && validateFinite aperture &&
       validateFinite blurLevel && validateFinite xRot && validateFinite yRot &&
       validateFinite zRot && validateNonNegative focusDist && validateNonNegative aperture &&
       validateNonNegative blurLevel
      then return (Camera3D cType position poi zoom dof focusDist aperture blurLevel xRot yRot zRot)
      else fail "Camera3D: numeric values must be finite and within valid ranges"

-- | Camera depth of field
data CameraDepthOfField = CameraDepthOfField
  { cameraDepthOfFieldEnabled :: Bool
  , cameraDepthOfFieldFocusDistance :: Double
  , cameraDepthOfFieldAperture :: Double
  , cameraDepthOfFieldBlurLevel :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraDepthOfField where
  toJSON (CameraDepthOfField enabled focusDist aperture blurLevel) =
    object
      [ "enabled" .= enabled
      , "focusDistance" .= focusDist
      , "aperture" .= aperture
      , "blurLevel" .= blurLevel
      ]

instance FromJSON CameraDepthOfField where
  parseJSON = withObject "CameraDepthOfField" $ \o -> do
    enabled <- o .: "enabled"
    focusDist <- o .: "focusDistance"
    aperture <- o .: "aperture"
    blurLevel <- o .: "blurLevel"
    if validateFinite focusDist && validateFinite aperture && validateFinite blurLevel &&
       validateNonNegative focusDist && validateNonNegative aperture && validateNonNegative blurLevel
      then return (CameraDepthOfField enabled focusDist aperture blurLevel)
      else fail "CameraDepthOfField: numeric values must be finite and non-negative"

-- | Camera path following configuration (legacy)
data CameraPathFollowing = CameraPathFollowing
  { cameraPathFollowingEnabled :: Bool
  , cameraPathFollowingPathLayerId :: Text  -- ID of SplineLayer to follow
  , cameraPathFollowingParameter :: AnimatableProperty Double  -- 0-1 position along path (can be keyframed)
  , cameraPathFollowingLookAhead :: Double  -- Distance ahead to look (0-1 path units)
  , cameraPathFollowingBankingStrength :: Double  -- How much to bank on turns (0-1)
  , cameraPathFollowingOffsetY :: Double  -- Height offset from path
  , cameraPathFollowingAlignToPath :: Bool  -- Auto-orient camera along path tangent
  , cameraPathFollowingAutoAdvance :: Bool  -- Automatically advance along path each frame
  , cameraPathFollowingAutoAdvanceSpeed :: Double  -- Speed of auto-advance (path units per frame)
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraPathFollowing where
  toJSON (CameraPathFollowing enabled pathLayerId param lookAhead banking offsetY align autoAdvance speed) =
    object
      [ "enabled" .= enabled
      , "pathLayerId" .= pathLayerId
      , "parameter" .= param
      , "lookAhead" .= lookAhead
      , "bankingStrength" .= banking
      , "offsetY" .= offsetY
      , "alignToPath" .= align
      , "autoAdvance" .= autoAdvance
      , "autoAdvanceSpeed" .= speed
      ]

instance FromJSON CameraPathFollowing where
  parseJSON = withObject "CameraPathFollowing" $ \o -> do
    enabled <- o .: "enabled"
    pathLayerId <- o .: "pathLayerId"
    param <- o .: "parameter"
    lookAhead <- o .: "lookAhead"
    banking <- o .: "bankingStrength"
    offsetY <- o .: "offsetY"
    align <- o .: "alignToPath"
    autoAdvance <- o .: "autoAdvance"
    speed <- o .: "autoAdvanceSpeed"
    if validateFinite lookAhead && validateFinite banking && validateFinite offsetY &&
       validateFinite speed && validateNormalized01 lookAhead && validateNormalized01 banking
      then return (CameraPathFollowing enabled pathLayerId param lookAhead banking offsetY align autoAdvance speed)
      else fail "CameraPathFollowing: numeric values must be finite and within valid ranges"

-- | Camera shake type
data CameraShakeType
  = CameraShakeTypeHandheld
  | CameraShakeTypeImpact
  | CameraShakeTypeEarthquake
  | CameraShakeTypeSubtle
  | CameraShakeTypeCustom
  deriving (Eq, Show, Generic)

instance ToJSON CameraShakeType where
  toJSON CameraShakeTypeHandheld = "handheld"
  toJSON CameraShakeTypeImpact = "impact"
  toJSON CameraShakeTypeEarthquake = "earthquake"
  toJSON CameraShakeTypeSubtle = "subtle"
  toJSON CameraShakeTypeCustom = "custom"

instance FromJSON CameraShakeType where
  parseJSON = withText "CameraShakeType" $ \s ->
    case s of
      t | t == T.pack "handheld" -> return CameraShakeTypeHandheld
      t | t == T.pack "impact" -> return CameraShakeTypeImpact
      t | t == T.pack "earthquake" -> return CameraShakeTypeEarthquake
      t | t == T.pack "subtle" -> return CameraShakeTypeSubtle
      t | t == T.pack "custom" -> return CameraShakeTypeCustom
      _ -> fail "Invalid CameraShakeType"

-- | Camera shake configuration
data CameraShakeData = CameraShakeData
  { cameraShakeDataEnabled :: Bool
  , cameraShakeDataType :: CameraShakeType
  , cameraShakeDataIntensity :: Double
  , cameraShakeDataFrequency :: Double
  , cameraShakeDataRotationEnabled :: Bool
  , cameraShakeDataRotationScale :: Double
  , cameraShakeDataSeed :: Double
  , cameraShakeDataDecay :: Double
  , cameraShakeDataStartFrame :: Double
  , cameraShakeDataDuration :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraShakeData where
  toJSON (CameraShakeData enabled cType intensity freq rotEnabled rotScale seed decay startFrame duration) =
    object
      [ "enabled" .= enabled
      , "type" .= cType
      , "intensity" .= intensity
      , "frequency" .= freq
      , "rotationEnabled" .= rotEnabled
      , "rotationScale" .= rotScale
      , "seed" .= seed
      , "decay" .= decay
      , "startFrame" .= startFrame
      , "duration" .= duration
      ]

instance FromJSON CameraShakeData where
  parseJSON = withObject "CameraShakeData" $ \o -> do
    enabled <- o .: "enabled"
    cType <- o .: "type"
    intensity <- o .: "intensity"
    freq <- o .: "frequency"
    rotEnabled <- o .: "rotationEnabled"
    rotScale <- o .: "rotationScale"
    seed <- o .: "seed"
    decay <- o .: "decay"
    startFrame <- o .: "startFrame"
    duration <- o .: "duration"
    if validateFinite intensity && validateFinite freq && validateFinite rotScale &&
       validateFinite seed && validateFinite decay && validateFinite startFrame &&
       validateFinite duration && validateNonNegative intensity && validateNonNegative freq &&
       validateNonNegative rotScale && validateNormalized01 decay
      then return (CameraShakeData enabled cType intensity freq rotEnabled rotScale seed decay startFrame duration)
      else fail "CameraShakeData: numeric values must be finite and within valid ranges"

-- | Camera rack focus easing
data CameraRackFocusEasing
  = CameraRackFocusEasingLinear
  | CameraRackFocusEasingEaseIn
  | CameraRackFocusEasingEaseOut
  | CameraRackFocusEasingEaseInOut
  | CameraRackFocusEasingSnap
  deriving (Eq, Show, Generic)

instance ToJSON CameraRackFocusEasing where
  toJSON CameraRackFocusEasingLinear = "linear"
  toJSON CameraRackFocusEasingEaseIn = "ease-in"
  toJSON CameraRackFocusEasingEaseOut = "ease-out"
  toJSON CameraRackFocusEasingEaseInOut = "ease-in-out"
  toJSON CameraRackFocusEasingSnap = "snap"

instance FromJSON CameraRackFocusEasing where
  parseJSON = withText "CameraRackFocusEasing" $ \s ->
    case s of
      t | t == T.pack "linear" -> return CameraRackFocusEasingLinear
      t | t == T.pack "ease-in" -> return CameraRackFocusEasingEaseIn
      t | t == T.pack "ease-out" -> return CameraRackFocusEasingEaseOut
      t | t == T.pack "ease-in-out" -> return CameraRackFocusEasingEaseInOut
      t | t == T.pack "snap" -> return CameraRackFocusEasingSnap
      _ -> fail "Invalid CameraRackFocusEasing"

-- | Rack focus configuration
data CameraRackFocusData = CameraRackFocusData
  { cameraRackFocusDataEnabled :: Bool
  , cameraRackFocusDataStartDistance :: Double
  , cameraRackFocusDataEndDistance :: Double
  , cameraRackFocusDataDuration :: Double
  , cameraRackFocusDataStartFrame :: Double
  , cameraRackFocusDataEasing :: CameraRackFocusEasing
  , cameraRackFocusDataHoldStart :: Double
  , cameraRackFocusDataHoldEnd :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraRackFocusData where
  toJSON (CameraRackFocusData enabled startDist endDist duration startFrame easing holdStart holdEnd) =
    object
      [ "enabled" .= enabled
      , "startDistance" .= startDist
      , "endDistance" .= endDist
      , "duration" .= duration
      , "startFrame" .= startFrame
      , "easing" .= easing
      , "holdStart" .= holdStart
      , "holdEnd" .= holdEnd
      ]

instance FromJSON CameraRackFocusData where
  parseJSON = withObject "CameraRackFocusData" $ \o -> do
    enabled <- o .: "enabled"
    startDist <- o .: "startDistance"
    endDist <- o .: "endDistance"
    duration <- o .: "duration"
    startFrame <- o .: "startFrame"
    easing <- o .: "easing"
    holdStart <- o .: "holdStart"
    holdEnd <- o .: "holdEnd"
    if validateFinite startDist && validateFinite endDist && validateFinite duration &&
       validateFinite startFrame && validateFinite holdStart && validateFinite holdEnd &&
       validateNonNegative startDist && validateNonNegative endDist && validateNonNegative duration &&
       validateNonNegative startFrame && validateNonNegative holdStart && validateNonNegative holdEnd
      then return (CameraRackFocusData enabled startDist endDist duration startFrame easing holdStart holdEnd)
      else fail "CameraRackFocusData: numeric values must be finite and non-negative"

-- | Camera autofocus mode
data CameraAutoFocusMode
  = CameraAutoFocusModeCenter
  | CameraAutoFocusModePoint
  | CameraAutoFocusModeNearest
  | CameraAutoFocusModeFarthest
  deriving (Eq, Show, Generic)

instance ToJSON CameraAutoFocusMode where
  toJSON CameraAutoFocusModeCenter = "center"
  toJSON CameraAutoFocusModePoint = "point"
  toJSON CameraAutoFocusModeNearest = "nearest"
  toJSON CameraAutoFocusModeFarthest = "farthest"

instance FromJSON CameraAutoFocusMode where
  parseJSON = withText "CameraAutoFocusMode" $ \s ->
    case s of
      t | t == T.pack "center" -> return CameraAutoFocusModeCenter
      t | t == T.pack "point" -> return CameraAutoFocusModePoint
      t | t == T.pack "nearest" -> return CameraAutoFocusModeNearest
      t | t == T.pack "farthest" -> return CameraAutoFocusModeFarthest
      _ -> fail "Invalid CameraAutoFocusMode"

-- | Autofocus configuration
data CameraAutoFocusData = CameraAutoFocusData
  { cameraAutoFocusDataEnabled :: Bool
  , cameraAutoFocusDataMode :: CameraAutoFocusMode
  , cameraAutoFocusDataFocusPoint :: (Double, Double)  -- { x, y }
  , cameraAutoFocusDataSmoothing :: Double
  , cameraAutoFocusDataThreshold :: Double
  , cameraAutoFocusDataSampleRadius :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraAutoFocusData where
  toJSON (CameraAutoFocusData enabled mode (fx, fy) smoothing threshold radius) =
    object
      [ "enabled" .= enabled
      , "mode" .= mode
      , "focusPoint" .= object ["x" .= fx, "y" .= fy]
      , "smoothing" .= smoothing
      , "threshold" .= threshold
      , "sampleRadius" .= radius
      ]

instance FromJSON CameraAutoFocusData where
  parseJSON = withObject "CameraAutoFocusData" $ \o -> do
    enabled <- o .: "enabled"
    mode <- o .: "mode"
    focusPointObj <- o .: "focusPoint"
    fx <- focusPointObj .: "x"
    fy <- focusPointObj .: "y"
    smoothing <- o .: "smoothing"
    threshold <- o .: "threshold"
    radius <- o .: "sampleRadius"
    if validateFinite fx && validateFinite fy && validateFinite smoothing &&
       validateFinite threshold && validateFinite radius &&
       validateNonNegative smoothing && validateNonNegative threshold && validateNonNegative radius
      then return (CameraAutoFocusData enabled mode (fx, fy) smoothing threshold radius)
      else fail "CameraAutoFocusData: numeric values must be finite and within valid ranges"

-- | Camera look mode
data CameraLookMode
  = CameraLookModeTangent
  | CameraLookModeTarget
  | CameraLookModeFixed
  deriving (Eq, Show, Generic)

instance ToJSON CameraLookMode where
  toJSON CameraLookModeTangent = "tangent"
  toJSON CameraLookModeTarget = "target"
  toJSON CameraLookModeFixed = "fixed"

instance FromJSON CameraLookMode where
  parseJSON = withText "CameraLookMode" $ \s ->
    case s of
      t | t == T.pack "tangent" -> return CameraLookModeTangent
      t | t == T.pack "target" -> return CameraLookModeTarget
      t | t == T.pack "fixed" -> return CameraLookModeFixed
      _ -> fail "Invalid CameraLookMode"

-- | Simplified path following (for AI tools)
data CameraPathFollowingData = CameraPathFollowingData
  { cameraPathFollowingDataEnabled :: Bool
  , cameraPathFollowingDataSplineLayerId :: Maybe Text
  , cameraPathFollowingDataLookMode :: CameraLookMode
  , cameraPathFollowingDataLookTarget :: Maybe Vec3
  , cameraPathFollowingDataStartOffset :: Double
  , cameraPathFollowingDataSpeed :: Double
  , cameraPathFollowingDataBankAmount :: Double
  , cameraPathFollowingDataSmoothing :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraPathFollowingData where
  toJSON (CameraPathFollowingData enabled mSplineId lookMode mLookTarget startOffset speed bank smoothing) =
    let
      baseFields = ["enabled" .= enabled, "lookMode" .= lookMode, "startOffset" .= startOffset, "speed" .= speed, "bankAmount" .= bank, "smoothing" .= smoothing]
      withSplineId = case mSplineId of Just id -> ("splineLayerId" .= id) : baseFields; Nothing -> baseFields
      withLookTarget = case mLookTarget of Just t -> ("lookTarget" .= t) : withSplineId; Nothing -> withSplineId
    in object withLookTarget

instance FromJSON CameraPathFollowingData where
  parseJSON = withObject "CameraPathFollowingData" $ \o -> do
    enabled <- o .: "enabled"
    mSplineId <- o .:? "splineLayerId"
    lookMode <- o .: "lookMode"
    mLookTargetObj <- o .:? "lookTarget"
    mLookTarget <- case mLookTargetObj of
      Nothing -> return Nothing
      Just obj -> do
        x <- obj .: "x"
        y <- obj .: "y"
        z <- obj .: "z"
        return (Just (Vec3 x y z))
    startOffset <- o .: "startOffset"
    speed <- o .: "speed"
    bank <- o .: "bankAmount"
    smoothing <- o .: "smoothing"
    if validateFinite startOffset && validateFinite speed && validateFinite bank &&
       validateFinite smoothing && validateNonNegative smoothing
      then return (CameraPathFollowingData enabled mSplineId lookMode mLookTarget startOffset speed bank smoothing)
      else fail "CameraPathFollowingData: numeric values must be finite and within valid ranges"

-- | Camera trajectory keyframe for position
data CameraTrajectoryPositionKeyframe = CameraTrajectoryPositionKeyframe
  { cameraTrajectoryPositionKeyframeFrame :: Double
  , cameraTrajectoryPositionKeyframePosition :: Vec3
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraTrajectoryPositionKeyframe where
  toJSON (CameraTrajectoryPositionKeyframe frame position) =
    object ["frame" .= frame, "position" .= position]

instance FromJSON CameraTrajectoryPositionKeyframe where
  parseJSON = withObject "CameraTrajectoryPositionKeyframe" $ \o -> do
    frame <- o .: "frame"
    position <- o .: "position"
    if validateFinite frame && validateNonNegative frame
      then return (CameraTrajectoryPositionKeyframe frame position)
      else fail "CameraTrajectoryPositionKeyframe: frame must be finite and non-negative"

-- | Camera trajectory keyframe for point of interest
data CameraTrajectoryPOIKeyframe = CameraTrajectoryPOIKeyframe
  { cameraTrajectoryPOIKeyframeFrame :: Double
  , cameraTrajectoryPOIKeyframePointOfInterest :: Vec3
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraTrajectoryPOIKeyframe where
  toJSON (CameraTrajectoryPOIKeyframe frame poi) =
    object ["frame" .= frame, "pointOfInterest" .= poi]

instance FromJSON CameraTrajectoryPOIKeyframe where
  parseJSON = withObject "CameraTrajectoryPOIKeyframe" $ \o -> do
    frame <- o .: "frame"
    poi <- o .: "pointOfInterest"
    if validateFinite frame && validateNonNegative frame
      then return (CameraTrajectoryPOIKeyframe frame poi)
      else fail "CameraTrajectoryPOIKeyframe: frame must be finite and non-negative"

-- | Camera trajectory keyframe for zoom
data CameraTrajectoryZoomKeyframe = CameraTrajectoryZoomKeyframe
  { cameraTrajectoryZoomKeyframeFrame :: Double
  , cameraTrajectoryZoomKeyframeZoom :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraTrajectoryZoomKeyframe where
  toJSON (CameraTrajectoryZoomKeyframe frame zoom) =
    object ["frame" .= frame, "zoom" .= zoom]

instance FromJSON CameraTrajectoryZoomKeyframe where
  parseJSON = withObject "CameraTrajectoryZoomKeyframe" $ \o -> do
    frame <- o .: "frame"
    zoom <- o .: "zoom"
    if validateFinite frame && validateFinite zoom && validateNonNegative frame && validateNonNegative zoom
      then return (CameraTrajectoryZoomKeyframe frame zoom)
      else fail "CameraTrajectoryZoomKeyframe: frame and zoom must be finite and non-negative"

-- | Trajectory keyframes storage
data CameraTrajectoryKeyframes = CameraTrajectoryKeyframes
  { cameraTrajectoryKeyframesPosition :: [CameraTrajectoryPositionKeyframe]
  , cameraTrajectoryKeyframesPointOfInterest :: [CameraTrajectoryPOIKeyframe]
  , cameraTrajectoryKeyframesZoom :: Maybe [CameraTrajectoryZoomKeyframe]
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraTrajectoryKeyframes where
  toJSON (CameraTrajectoryKeyframes positions pois mZooms) =
    let
      baseFields = ["position" .= positions, "pointOfInterest" .= pois]
      withZooms = case mZooms of Just z -> ("zoom" .= z) : baseFields; Nothing -> baseFields
    in object withZooms

instance FromJSON CameraTrajectoryKeyframes where
  parseJSON = withObject "CameraTrajectoryKeyframes" $ \o -> do
    positions <- o .: "position"
    pois <- o .: "pointOfInterest"
    mZooms <- o .:? "zoom"
    return (CameraTrajectoryKeyframes positions pois mZooms)

-- | Camera layer data
data CameraLayerData = CameraLayerData
  { cameraLayerDataCameraId :: Maybe Text  -- Reference to the Camera3D object - CODE IS TRUTH (defaults create null)
  , cameraLayerDataIsActiveCamera :: Bool  -- Is this the composition's active camera?
  , cameraLayerDataCamera :: Maybe Camera3D  -- Camera3D object (inline storage)
  , cameraLayerDataAnimatedPosition :: Maybe (AnimatableProperty Vec3)  -- Optional animated camera properties
  , cameraLayerDataAnimatedTarget :: Maybe (AnimatableProperty Vec3)
  , cameraLayerDataAnimatedFov :: Maybe (AnimatableProperty Double)
  , cameraLayerDataAnimatedFocalLength :: Maybe (AnimatableProperty Double)
  , cameraLayerDataPathFollowing :: Maybe CameraPathFollowing  -- Path following (camera moves along a spline) - legacy
  , cameraLayerDataPathFollowingConfig :: Maybe CameraPathFollowingData  -- Simplified path following (for AI tools)
  , cameraLayerDataDepthOfField :: Maybe CameraDepthOfField  -- Depth of field settings
  , cameraLayerDataAnimatedFocusDistance :: Maybe (AnimatableProperty Double)
  , cameraLayerDataAnimatedAperture :: Maybe (AnimatableProperty Double)
  , cameraLayerDataAnimatedBlurLevel :: Maybe (AnimatableProperty Double)
  , cameraLayerDataShake :: Maybe CameraShakeData  -- Camera shake effect
  , cameraLayerDataRackFocus :: Maybe CameraRackFocusData  -- Rack focus effect
  , cameraLayerDataAutoFocus :: Maybe CameraAutoFocusData  -- Autofocus settings
  , cameraLayerDataTrajectoryKeyframes :: Maybe CameraTrajectoryKeyframes  -- Trajectory keyframes (generated from presets)
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraLayerData where
  toJSON (CameraLayerData mCameraId isActive mCamera mAnimatedPos mAnimatedTarget mAnimatedFov mAnimatedFocalLength mPathFollowing mPathFollowingConfig mDOF mAnimatedFocusDist mAnimatedAperture mAnimatedBlur mShake mRackFocus mAutoFocus mTrajectory) =
    let
      baseFields = ["isActiveCamera" .= isActive]
      f1 = case mCameraId of Just id -> ("cameraId" .= id) : baseFields; Nothing -> baseFields
      f2 = case mCamera of Just c -> ("camera" .= c) : f1; Nothing -> f1
      f3 = case mAnimatedPos of Just p -> ("animatedPosition" .= p) : f2; Nothing -> f2
      f4 = case mAnimatedTarget of Just t -> ("animatedTarget" .= t) : f3; Nothing -> f3
      f5 = case mAnimatedFov of Just f -> ("animatedFov" .= f) : f4; Nothing -> f4
      f6 = case mAnimatedFocalLength of Just fl -> ("animatedFocalLength" .= fl) : f5; Nothing -> f5
      f7 = case mPathFollowing of Just pf -> ("pathFollowing" .= pf) : f6; Nothing -> f6
      f8 = case mPathFollowingConfig of Just pfc -> ("pathFollowingConfig" .= pfc) : f7; Nothing -> f7
      f9 = case mDOF of Just dof -> ("depthOfField" .= dof) : f8; Nothing -> f8
      f10 = case mAnimatedFocusDist of Just fd -> ("animatedFocusDistance" .= fd) : f9; Nothing -> f9
      f11 = case mAnimatedAperture of Just a -> ("animatedAperture" .= a) : f10; Nothing -> f10
      f12 = case mAnimatedBlur of Just b -> ("animatedBlurLevel" .= b) : f11; Nothing -> f11
      f13 = case mShake of Just s -> ("shake" .= s) : f12; Nothing -> f12
      f14 = case mRackFocus of Just r -> ("rackFocus" .= r) : f13; Nothing -> f13
      f15 = case mAutoFocus of Just af -> ("autoFocus" .= af) : f14; Nothing -> f14
      f16 = case mTrajectory of Just tr -> ("trajectoryKeyframes" .= tr) : f15; Nothing -> f15
    in object f16

instance FromJSON CameraLayerData where
  parseJSON = withObject "CameraLayerData" $ \o -> do
    mCameraId <- o .:? "cameraId"
    isActive <- o .: "isActiveCamera"
    mCamera <- o .:? "camera"
    mAnimatedPos <- o .:? "animatedPosition"
    mAnimatedTarget <- o .:? "animatedTarget"
    mAnimatedFov <- o .:? "animatedFov"
    mAnimatedFocalLength <- o .:? "animatedFocalLength"
    mPathFollowing <- o .:? "pathFollowing"
    mPathFollowingConfig <- o .:? "pathFollowingConfig"
    mDOF <- o .:? "depthOfField"
    mAnimatedFocusDist <- o .:? "animatedFocusDistance"
    mAnimatedAperture <- o .:? "animatedAperture"
    mAnimatedBlur <- o .:? "animatedBlurLevel"
    mShake <- o .:? "shake"
    mRackFocus <- o .:? "rackFocus"
    mAutoFocus <- o .:? "autoFocus"
    mTrajectory <- o .:? "trajectoryKeyframes"
    return (CameraLayerData mCameraId isActive mCamera mAnimatedPos mAnimatedTarget mAnimatedFov mAnimatedFocalLength mPathFollowing mPathFollowingConfig mDOF mAnimatedFocusDist mAnimatedAperture mAnimatedBlur mShake mRackFocus mAutoFocus mTrajectory)
