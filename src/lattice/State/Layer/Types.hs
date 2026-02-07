-- |
-- Module      : Lattice.State.Layer.Types
-- Description : Option types for layer store operations
-- 
-- Migrated from ui/src/stores/layerStore/types.ts
-- Types for layer CRUD, batch operations, and time manipulation options
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.Layer.Types
  ( -- Layer source replacement
    LayerSourceReplacement (..),
    LayerSourceReplacementType (..),
    -- Layer creation options
    CreateLayerOptions (..),
    -- Layer deletion options
    DeleteLayerOptions (..),
    -- Layer duplication options
    DuplicateLayerOptions (..),
    -- Batch operation options
    SequenceLayersOptions (..),
    ExponentialScaleOptions (..),
    ExponentialScaleAxis (..),
    -- Time manipulation options
    TimeStretchOptions (..),
    TimeStretchHoldInPlace (..),
    -- Layer store state
    LayerState (..),
  )
where

import Data.Aeson
  ( ToJSON (..),
    FromJSON (..),
    withObject,
    withText,
    object,
    (.=),
    (.:),
    (.:?),
    Value (..),
  )
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Types.Animation (ClipboardKeyframe (..))
import Lattice.Types.Layer (Layer (..))
import Lattice.Types.Primitives
  ( Vec2 (..),
    validateFinite,
    validateNonNegative,
  )

-- ============================================================================
-- LAYER SOURCE REPLACEMENT
-- ============================================================================

-- | Layer source replacement type
data LayerSourceReplacementType
  = LayerSourceReplacementTypeAsset
  | LayerSourceReplacementTypeComposition
  | LayerSourceReplacementTypeOther Text -- For extensibility
  deriving (Eq, Show, Generic)

instance ToJSON LayerSourceReplacementType where
  toJSON LayerSourceReplacementTypeAsset = "asset"
  toJSON LayerSourceReplacementTypeComposition = "composition"
  toJSON (LayerSourceReplacementTypeOther s) = toJSON s

instance FromJSON LayerSourceReplacementType where
  parseJSON v = do
    s <- parseJSON v
    case s of
      "asset" -> return LayerSourceReplacementTypeAsset
      "composition" -> return LayerSourceReplacementTypeComposition
      other -> return (LayerSourceReplacementTypeOther other)

-- | Layer source replacement data for asset/composition swapping
data LayerSourceReplacement = LayerSourceReplacement
  { layerSourceReplacementType :: LayerSourceReplacementType,
    layerSourceReplacementName :: Text,
    layerSourceReplacementPath :: Maybe Text,
    layerSourceReplacementId :: Maybe Text,
    layerSourceReplacementAssetId :: Maybe Text,
    layerSourceReplacementData :: Maybe Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON LayerSourceReplacement where
  toJSON (LayerSourceReplacement typ name path id_ assetId data_) =
    let
      baseFields = ["type" .= typ, "name" .= name]
      withPath = case path of
        Just p -> ("path" .= p) : baseFields
        Nothing -> baseFields
      withId = case id_ of
        Just i -> ("id" .= i) : withPath
        Nothing -> withPath
      withAssetId = case assetId of
        Just a -> ("assetId" .= a) : withId
        Nothing -> withId
      withData = case data_ of
        Just d -> ("data" .= d) : withAssetId
        Nothing -> withAssetId
    in object withData

instance FromJSON LayerSourceReplacement where
  parseJSON = withObject "LayerSourceReplacement" $ \o -> do
    typ <- o .: "type"
    name <- o .: "name"
    path <- o .:? "path"
    id_ <- o .:? "id"
    assetId <- o .:? "assetId"
    data_ <- o .:? "data"
    return (LayerSourceReplacement typ name path id_ assetId data_)

-- ============================================================================
-- LAYER CREATION OPTIONS
-- ============================================================================

-- | Options for creating a new layer
data CreateLayerOptions = CreateLayerOptions
  { createLayerOptionsName :: Maybe Text,
    createLayerOptionsPosition :: Maybe Vec2,
    createLayerOptionsSize :: Maybe Vec2, -- width, height
    createLayerOptionsData :: Maybe Value, -- Partial LayerDataUnion (TODO: use proper type when available)
    createLayerOptionsParentId :: Maybe Text,
    createLayerOptionsInsertIndex :: Maybe Int
  }
  deriving (Eq, Show, Generic)

instance ToJSON CreateLayerOptions where
  toJSON (CreateLayerOptions name position size data_ parentId insertIndex) =
    let
      baseFields = []
      withName = case name of
        Just n -> ("name" .= n) : baseFields
        Nothing -> baseFields
      withPosition = case position of
        Just p -> ("position" .= p) : withName
        Nothing -> withName
      withSize = case size of
        Just s -> ("size" .= s) : withPosition
        Nothing -> withPosition
      withData = case data_ of
        Just d -> ("data" .= d) : withSize
        Nothing -> withSize
      withParentId = case parentId of
        Just p -> ("parentId" .= p) : withData
        Nothing -> withData
      withInsertIndex = case insertIndex of
        Just i -> ("insertIndex" .= i) : withParentId
        Nothing -> withParentId
    in object withInsertIndex

instance FromJSON CreateLayerOptions where
  parseJSON = withObject "CreateLayerOptions" $ \o -> do
    name <- o .:? "name"
    position <- o .:? "position"
    size <- o .:? "size"
    data_ <- o .:? "data"
    parentId <- o .:? "parentId"
    insertIndex <- o .:? "insertIndex"
    -- Validate insertIndex is non-negative if present
    case insertIndex of
      Just idx ->
        if idx < 0
          then fail "CreateLayerOptions: insertIndex must be non-negative"
          else return ()
      Nothing -> return ()
    return (CreateLayerOptions name position size data_ parentId insertIndex)

-- ============================================================================
-- LAYER DELETION OPTIONS
-- ============================================================================

-- | Options for deleting a layer
-- NOTE: onRemoveFromSelection callback is not migrated (side effect, handled at FFI boundary)
data DeleteLayerOptions = DeleteLayerOptions
  { deleteLayerOptionsSkipHistory :: Maybe Bool,
    deleteLayerOptionsDeleteChildren :: Maybe Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON DeleteLayerOptions where
  toJSON (DeleteLayerOptions skipHistory deleteChildren) =
    let
      baseFields = []
      withSkipHistory = case skipHistory of
        Just s -> ("skipHistory" .= s) : baseFields
        Nothing -> baseFields
      withDeleteChildren = case deleteChildren of
        Just d -> ("deleteChildren" .= d) : withSkipHistory
        Nothing -> withSkipHistory
    in object withDeleteChildren

instance FromJSON DeleteLayerOptions where
  parseJSON = withObject "DeleteLayerOptions" $ \o -> do
    skipHistory <- o .:? "skipHistory"
    deleteChildren <- o .:? "deleteChildren"
    return (DeleteLayerOptions skipHistory deleteChildren)

-- ============================================================================
-- LAYER DUPLICATION OPTIONS
-- ============================================================================

-- | Options for duplicating a layer
data DuplicateLayerOptions = DuplicateLayerOptions
  { duplicateLayerOptionsNewName :: Maybe Text,
    duplicateLayerOptionsOffsetPosition :: Maybe Bool,
    duplicateLayerOptionsIncludeChildren :: Maybe Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON DuplicateLayerOptions where
  toJSON (DuplicateLayerOptions newName offsetPosition includeChildren) =
    let
      baseFields = []
      withNewName = case newName of
        Just n -> ("newName" .= n) : baseFields
        Nothing -> baseFields
      withOffsetPosition = case offsetPosition of
        Just o -> ("offsetPosition" .= o) : withNewName
        Nothing -> withNewName
      withIncludeChildren = case includeChildren of
        Just i -> ("includeChildren" .= i) : withOffsetPosition
        Nothing -> withOffsetPosition
    in object withIncludeChildren

instance FromJSON DuplicateLayerOptions where
  parseJSON = withObject "DuplicateLayerOptions" $ \o -> do
    newName <- o .:? "newName"
    offsetPosition <- o .:? "offsetPosition"
    includeChildren <- o .:? "includeChildren"
    return (DuplicateLayerOptions newName offsetPosition includeChildren)

-- ============================================================================
-- BATCH OPERATION OPTIONS
-- ============================================================================

-- | Options for sequencing layers
data SequenceLayersOptions = SequenceLayersOptions
  { sequenceLayersOptionsGapFrames :: Maybe Double, -- Gap between layers in frames (positive = gap, negative = overlap)
    sequenceLayersOptionsStartFrame :: Maybe Double, -- Starting frame for the sequence
    sequenceLayersOptionsReverse :: Maybe Bool -- Whether to maintain layer order or reverse
  }
  deriving (Eq, Show, Generic)

instance ToJSON SequenceLayersOptions where
  toJSON (SequenceLayersOptions gapFrames startFrame reverse_) =
    let
      baseFields = []
      withGapFrames = case gapFrames of
        Just g -> ("gapFrames" .= g) : baseFields
        Nothing -> baseFields
      withStartFrame = case startFrame of
        Just s -> ("startFrame" .= s) : withGapFrames
        Nothing -> withGapFrames
      withReverse = case reverse_ of
        Just r -> ("reverse" .= r) : withStartFrame
        Nothing -> withStartFrame
    in object withReverse

instance FromJSON SequenceLayersOptions where
  parseJSON = withObject "SequenceLayersOptions" $ \o -> do
    gapFrames <- o .:? "gapFrames"
    startFrame <- o .:? "startFrame"
    reverse_ <- o .:? "reverse"
    -- Validate numeric fields are finite
    case gapFrames of
      Just g ->
        if not (validateFinite g)
          then fail "SequenceLayersOptions: gapFrames must be finite"
          else return ()
      Nothing -> return ()
    case startFrame of
      Just s ->
        if not (validateFinite s) || s < 0
          then fail "SequenceLayersOptions: startFrame must be finite and non-negative"
          else return ()
      Nothing -> return ()
    return (SequenceLayersOptions gapFrames startFrame reverse_)

-- | Axis for exponential scale animation
data ExponentialScaleAxis
  = ExponentialScaleAxisBoth
  | ExponentialScaleAxisX
  | ExponentialScaleAxisY
  deriving (Eq, Show, Generic)

instance ToJSON ExponentialScaleAxis where
  toJSON ExponentialScaleAxisBoth = "both"
  toJSON ExponentialScaleAxisX = "x"
  toJSON ExponentialScaleAxisY = "y"

instance FromJSON ExponentialScaleAxis where
  parseJSON = withText "ExponentialScaleAxis" $ \s ->
    case () of
      _ | s == T.pack "both" -> return ExponentialScaleAxisBoth
      _ | s == T.pack "x" -> return ExponentialScaleAxisX
      _ | s == T.pack "y" -> return ExponentialScaleAxisY
      _ -> fail "Invalid ExponentialScaleAxis"

-- | Options for exponential scale animation
data ExponentialScaleOptions = ExponentialScaleOptions
  { exponentialScaleOptionsStartScale :: Maybe Double, -- Starting scale percentage
    exponentialScaleOptionsEndScale :: Maybe Double, -- Ending scale percentage
    exponentialScaleOptionsStartFrame :: Maybe Double, -- Starting frame
    exponentialScaleOptionsEndFrame :: Maybe Double, -- Ending frame
    exponentialScaleOptionsKeyframeCount :: Maybe Int, -- Number of keyframes to create (more = smoother)
    exponentialScaleOptionsAxis :: Maybe ExponentialScaleAxis -- Whether to apply to X, Y, or both
  }
  deriving (Eq, Show, Generic)

instance ToJSON ExponentialScaleOptions where
  toJSON (ExponentialScaleOptions startScale endScale startFrame endFrame keyframeCount axis) =
    let
      baseFields = []
      withStartScale = case startScale of
        Just s -> ("startScale" .= s) : baseFields
        Nothing -> baseFields
      withEndScale = case endScale of
        Just e -> ("endScale" .= e) : withStartScale
        Nothing -> withStartScale
      withStartFrame = case startFrame of
        Just s -> ("startFrame" .= s) : withEndScale
        Nothing -> withEndScale
      withEndFrame = case endFrame of
        Just e -> ("endFrame" .= e) : withStartFrame
        Nothing -> withStartFrame
      withKeyframeCount = case keyframeCount of
        Just k -> ("keyframeCount" .= k) : withEndFrame
        Nothing -> withEndFrame
      withAxis = case axis of
        Just a -> ("axis" .= a) : withKeyframeCount
        Nothing -> withKeyframeCount
    in object withAxis

instance FromJSON ExponentialScaleOptions where
  parseJSON = withObject "ExponentialScaleOptions" $ \o -> do
    startScale <- o .:? "startScale"
    endScale <- o .:? "endScale"
    startFrame <- o .:? "startFrame"
    endFrame <- o .:? "endFrame"
    keyframeCount <- o .:? "keyframeCount"
    axis <- o .:? "axis"
    -- Validate numeric fields are finite and in valid ranges
    case startScale of
      Just s ->
        if not (validateFinite s) || s < 0
          then fail "ExponentialScaleOptions: startScale must be finite and non-negative"
          else return ()
      Nothing -> return ()
    case endScale of
      Just e ->
        if not (validateFinite e) || e < 0
          then fail "ExponentialScaleOptions: endScale must be finite and non-negative"
          else return ()
      Nothing -> return ()
    case startFrame of
      Just s ->
        if not (validateFinite s) || s < 0
          then fail "ExponentialScaleOptions: startFrame must be finite and non-negative"
          else return ()
      Nothing -> return ()
    case endFrame of
      Just e ->
        if not (validateFinite e) || e < 0
          then fail "ExponentialScaleOptions: endFrame must be finite and non-negative"
          else return ()
      Nothing -> return ()
    case keyframeCount of
      Just k ->
        if k < 1 || k > 1000
          then fail "ExponentialScaleOptions: keyframeCount must be between 1 and 1000"
          else return ()
      Nothing -> return ()
    return (ExponentialScaleOptions startScale endScale startFrame endFrame keyframeCount axis)

-- ============================================================================
-- TIME MANIPULATION OPTIONS
-- ============================================================================

-- | Hold in place option for time stretch
data TimeStretchHoldInPlace
  = TimeStretchHoldInPoint
  | TimeStretchHoldCurrentFrame
  | TimeStretchHoldOutPoint
  deriving (Eq, Show, Generic)

instance ToJSON TimeStretchHoldInPlace where
  toJSON TimeStretchHoldInPoint = "in-point"
  toJSON TimeStretchHoldCurrentFrame = "current-frame"
  toJSON TimeStretchHoldOutPoint = "out-point"

instance FromJSON TimeStretchHoldInPlace where
  parseJSON = withText "TimeStretchHoldInPlace" $ \s ->
    case () of
      _ | s == T.pack "in-point" -> return TimeStretchHoldInPoint
      _ | s == T.pack "current-frame" -> return TimeStretchHoldCurrentFrame
      _ | s == T.pack "out-point" -> return TimeStretchHoldOutPoint
      _ -> fail "Invalid TimeStretchHoldInPlace"

-- | Options for time stretch operation
data TimeStretchOptions = TimeStretchOptions
  { timeStretchOptionsStretchFactor :: Double, -- 100% = normal, 200% = half speed, 50% = double speed
    timeStretchOptionsHoldInPlace :: TimeStretchHoldInPlace,
    timeStretchOptionsReverse :: Bool,
    timeStretchOptionsNewStartFrame :: Double,
    timeStretchOptionsNewEndFrame :: Double,
    timeStretchOptionsSpeed :: Double -- Computed speed value (100 / stretchFactor)
  }
  deriving (Eq, Show, Generic)

instance ToJSON TimeStretchOptions where
  toJSON (TimeStretchOptions stretchFactor holdInPlace reverse_ newStartFrame newEndFrame speed_) =
    object
      [ "stretchFactor" .= stretchFactor,
        "holdInPlace" .= holdInPlace,
        "reverse" .= reverse_,
        "newStartFrame" .= newStartFrame,
        "newEndFrame" .= newEndFrame,
        "speed" .= speed_
      ]

instance FromJSON TimeStretchOptions where
  parseJSON = withObject "TimeStretchOptions" $ \o -> do
    stretchFactor <- o .: "stretchFactor"
    holdInPlace <- o .: "holdInPlace"
    reverse_ <- o .: "reverse"
    newStartFrame <- o .: "newStartFrame"
    newEndFrame <- o .: "newEndFrame"
    speed_ <- o .: "speed"
    -- Validate numeric fields
    if validateFinite stretchFactor && validateFinite newStartFrame && validateFinite newEndFrame && validateFinite speed_ &&
       stretchFactor > 0 &&
       validateNonNegative newStartFrame &&
       validateNonNegative newEndFrame &&
       newEndFrame >= newStartFrame
      then return (TimeStretchOptions stretchFactor holdInPlace reverse_ newStartFrame newEndFrame speed_)
      else fail "TimeStretchOptions: numeric values must be finite and within valid ranges, and endFrame >= startFrame"

-- ============================================================================
-- LAYER STORE STATE
-- ============================================================================

-- | Layer store state
-- NOTE: Layers are stored in project.compositions[x].layers
-- This store provides methods to access/modify them
-- Clipboard is the only state managed by the layer store itself
data LayerState = LayerState
  { layerStateClipboard :: LayerStateClipboard
  }
  deriving (Eq, Show, Generic)

-- | Clipboard for layer copy/paste operations
data LayerStateClipboard = LayerStateClipboard
  { layerStateClipboardLayers :: [Layer],
    layerStateClipboardKeyframes :: [ClipboardKeyframe]
  }
  deriving (Eq, Show, Generic)

instance ToJSON LayerStateClipboard where
  toJSON (LayerStateClipboard layers keyframes) =
    object
      [ "layers" .= layers,
        "keyframes" .= keyframes
      ]

instance FromJSON LayerStateClipboard where
  parseJSON = withObject "LayerStateClipboard" $ \o -> do
    layers <- o .: "layers"
    keyframes <- o .: "keyframes"
    return (LayerStateClipboard layers keyframes)

instance ToJSON LayerState where
  toJSON (LayerState clipboard) =
    object
      [ "clipboard" .= clipboard
      ]

instance FromJSON LayerState where
  parseJSON = withObject "LayerState" $ \o -> do
    clipboard <- o .: "clipboard"
    return (LayerState clipboard)
