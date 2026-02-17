-- |
-- Module      : Lattice.Types.Masks.Core
-- Description : Core types for layer masks and track mattes
-- 
-- Migrated from ui/src/types/masks.ts
-- Defines types for bezier path masks that clip layer content
-- and track mattes that use layers above as matte sources
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Masks.Core
  ( -- Track matte types
    TrackMatteType (..),
    -- Mask mode
    MaskMode (..),
    -- Mask path types
    MaskPath (..),
    MaskVertex (..),
    -- Layer mask
    LayerMask (..),
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
import Lattice.Types.Animation
  ( AnimatableProperty (..),
    PropertyType (..),
  )
import Lattice.Schema.SharedValidation (validateBoundedArray)
import Lattice.Types.Primitives (validateFinite, validateNonNegative)

-- ============================================================================
-- TRACK MATTE TYPES
-- ============================================================================

-- | Track matte type (uses layer above as matte source)
data TrackMatteType
  = TrackMatteTypeNone -- No matte source
  | TrackMatteTypeAlpha -- Use alpha channel of matte layer
  | TrackMatteTypeAlphaInverted -- Invert alpha of matte layer
  | TrackMatteTypeLuma -- Use luminance of matte layer
  | TrackMatteTypeLumaInverted -- Invert luminance of matte layer
  deriving (Eq, Show, Generic)

instance ToJSON TrackMatteType where
  toJSON TrackMatteTypeNone = "none"
  toJSON TrackMatteTypeAlpha = "alpha"
  toJSON TrackMatteTypeAlphaInverted = "alpha_inverted"
  toJSON TrackMatteTypeLuma = "luma"
  toJSON TrackMatteTypeLumaInverted = "luma_inverted"

instance FromJSON TrackMatteType where
  parseJSON = withText "TrackMatteType" $ \s ->
    case s of
      t | t == T.pack "none" -> return TrackMatteTypeNone
      t | t == T.pack "alpha" -> return TrackMatteTypeAlpha
      t | t == T.pack "alpha_inverted" -> return TrackMatteTypeAlphaInverted
      t | t == T.pack "luma" -> return TrackMatteTypeLuma
      t | t == T.pack "luma_inverted" -> return TrackMatteTypeLumaInverted
      _ -> fail "Invalid TrackMatteType"

-- ============================================================================
-- MASK MODE
-- ============================================================================

-- | Mask mode determines how multiple masks combine
data MaskMode
  = MaskModeAdd -- Union of masks (default)
  | MaskModeSubtract -- Subtract this mask from previous
  | MaskModeIntersect -- Intersection with previous
  | MaskModeLighten -- Max of mask values
  | MaskModeDarken -- Min of mask values
  | MaskModeDifference -- Absolute difference
  | MaskModeNone -- Mask is disabled
  deriving (Eq, Show, Generic)

instance ToJSON MaskMode where
  toJSON MaskModeAdd = "add"
  toJSON MaskModeSubtract = "subtract"
  toJSON MaskModeIntersect = "intersect"
  toJSON MaskModeLighten = "lighten"
  toJSON MaskModeDarken = "darken"
  toJSON MaskModeDifference = "difference"
  toJSON MaskModeNone = "none"

instance FromJSON MaskMode where
  parseJSON = withText "MaskMode" $ \s ->
    case s of
      t | t == T.pack "add" -> return MaskModeAdd
      t | t == T.pack "subtract" -> return MaskModeSubtract
      t | t == T.pack "intersect" -> return MaskModeIntersect
      t | t == T.pack "lighten" -> return MaskModeLighten
      t | t == T.pack "darken" -> return MaskModeDarken
      t | t == T.pack "difference" -> return MaskModeDifference
      t | t == T.pack "none" -> return MaskModeNone
      _ -> fail "Invalid MaskMode"

-- ============================================================================
-- MASK PATH AND VERTICES
-- ============================================================================

-- | Mask vertex - point with optional bezier handles
-- Position is relative to layer bounds (0-1 or pixel coordinates)
data MaskVertex = MaskVertex
  { maskVertexX :: Double, -- Position (relative to layer bounds, 0-1 or pixel coordinates)
    maskVertexY :: Double,
    maskVertexInTangentX :: Double, -- Incoming tangent (from previous vertex)
    maskVertexInTangentY :: Double,
    maskVertexOutTangentX :: Double, -- Outgoing tangent (to next vertex)
    maskVertexOutTangentY :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON MaskVertex where
  toJSON (MaskVertex x y inTangentX inTangentY outTangentX outTangentY) =
    object
      [ "x" .= x,
        "y" .= y,
        "inTangentX" .= inTangentX,
        "inTangentY" .= inTangentY,
        "outTangentX" .= outTangentX,
        "outTangentY" .= outTangentY
      ]

instance FromJSON MaskVertex where
  parseJSON = withObject "MaskVertex" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    inTangentX <- o .: "inTangentX"
    inTangentY <- o .: "inTangentY"
    outTangentX <- o .: "outTangentX"
    outTangentY <- o .: "outTangentY"
    if validateFinite x && validateFinite y &&
       validateFinite inTangentX && validateFinite inTangentY &&
       validateFinite outTangentX && validateFinite outTangentY
      then return (MaskVertex x y inTangentX inTangentY outTangentX outTangentY)
      else fail "MaskVertex: all components must be finite numbers"

-- | Mask path - collection of bezier vertices forming a closed shape
data MaskPath = MaskPath
  { maskPathClosed :: Bool,
    maskPathVertices :: [MaskVertex]
  }
  deriving (Eq, Show, Generic)

instance ToJSON MaskPath where
  toJSON (MaskPath closed vertices) =
    object
      [ "closed" .= closed,
        "vertices" .= vertices
      ]

instance FromJSON MaskPath where
  parseJSON = withObject "MaskPath" $ \o -> do
    closed <- o .: "closed"
    verticesRaw <- o .: "vertices"
    -- Validate max 100,000 vertices per mask path
    vertices <- case validateBoundedArray 100000 verticesRaw of
      Left err -> fail (T.unpack err)
      Right vs ->
        -- Closed paths must have at least 3 vertices
        if closed && length vs < 3
          then fail "Closed mask paths must have at least 3 vertices"
          else return vs
    return (MaskPath closed vertices)

-- ============================================================================
-- LAYER MASK
-- ============================================================================

-- | Layer mask - bezier path that clips layer content
data LayerMask = LayerMask
  { layerMaskId :: Text,
    layerMaskName :: Text,
    layerMaskEnabled :: Bool,
    layerMaskLocked :: Bool,
    layerMaskMode :: MaskMode,
    layerMaskInverted :: Bool,
    layerMaskPath :: AnimatableProperty MaskPath, -- Mask path (bezier curve)
    layerMaskOpacity :: AnimatableProperty Double, -- 0-100
    layerMaskFeather :: AnimatableProperty Double, -- Blur amount in pixels
    layerMaskFeatherX :: Maybe (AnimatableProperty Double), -- Horizontal feather (if different)
    layerMaskFeatherY :: Maybe (AnimatableProperty Double), -- Vertical feather (if different)
    layerMaskExpansion :: AnimatableProperty Double, -- Expand/contract mask boundary
    layerMaskColor :: Text -- Hex color for visualization
  }
  deriving (Eq, Show, Generic)

instance ToJSON LayerMask where
  toJSON (LayerMask id_ name enabled locked mode inverted path opacity feather featherX featherY expansion color) =
    object $
      concat
        [ [ "id" .= id_,
            "name" .= name,
            "enabled" .= enabled,
            "locked" .= locked,
            "mode" .= mode,
            "inverted" .= inverted,
            "path" .= path,
            "opacity" .= opacity,
            "feather" .= feather,
            "expansion" .= expansion,
            "color" .= color
          ],
          maybe [] (\fx -> ["featherX" .= fx]) featherX,
          maybe [] (\fy -> ["featherY" .= fy]) featherY
        ]

instance FromJSON LayerMask where
  parseJSON = withObject "LayerMask" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    enabled <- o .: "enabled"
    locked <- o .: "locked"
    mode <- o .: "mode"
    inverted <- o .: "inverted"
    path <- o .: "path"
    opacity <- o .: "opacity"
    feather <- o .: "feather"
    featherX <- o .:? "featherX"
    featherY <- o .:? "featherY"
    expansion <- o .: "expansion"
    color <- o .: "color"
    return (LayerMask id_ name enabled locked mode inverted path opacity feather featherX featherY expansion color)
