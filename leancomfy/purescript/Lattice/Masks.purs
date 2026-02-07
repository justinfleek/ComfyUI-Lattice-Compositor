-- | Lattice.Masks - Layer masks and track mattes
-- |
-- | Source: leancomfy/lean/Lattice/Masks.lean

module Lattice.Masks
  ( MatteType(..)
  , MaskModeCombine(..)
  , MaskVertex
  , MaskPath
  , LayerMask
  , defaultMaskColor
  , defaultEllipseMaskColor
  , bezierKappa
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Matte Type
--------------------------------------------------------------------------------

-- | Matte source types (uses layer above as matte source)
data MatteType
  = MTNone           -- No matte source
  | MTAlpha          -- Use alpha channel of matte layer
  | MTAlphaInverted  -- Invert alpha of matte layer
  | MTLuma           -- Use luminance of matte layer
  | MTLumaInverted   -- Invert luminance of matte layer

derive instance Eq MatteType
derive instance Generic MatteType _
instance Show MatteType where show = genericShow

--------------------------------------------------------------------------------
-- Mask Mode
--------------------------------------------------------------------------------

-- | Mask mode determines how multiple masks combine
data MaskModeCombine
  = MMAdd        -- Union of masks (default)
  | MMSubtract   -- Subtract this mask from previous
  | MMIntersect  -- Intersection with previous
  | MMLighten    -- Max of mask values
  | MMDarken     -- Min of mask values
  | MMDifference -- Absolute difference
  | MMNone       -- Mask is disabled

derive instance Eq MaskModeCombine
derive instance Generic MaskModeCombine _
instance Show MaskModeCombine where show = genericShow

--------------------------------------------------------------------------------
-- Mask Vertex
--------------------------------------------------------------------------------

-- | Mask vertex with bezier handles
type MaskVertex =
  { x          :: FiniteFloat
  , y          :: FiniteFloat
  , inTangentX :: FiniteFloat
  , inTangentY :: FiniteFloat
  , outTangentX :: FiniteFloat
  , outTangentY :: FiniteFloat
  }

--------------------------------------------------------------------------------
-- Mask Path
--------------------------------------------------------------------------------

-- | Mask path - collection of bezier vertices forming a shape
type MaskPath =
  { closed   :: Boolean
  , vertices :: Array MaskVertex
  }

--------------------------------------------------------------------------------
-- Layer Mask
--------------------------------------------------------------------------------

-- | Layer mask - bezier path that clips layer content
type LayerMask =
  { id                :: NonEmptyString
  , name              :: NonEmptyString
  , enabled           :: Boolean
  , locked            :: Boolean
  , mode              :: MaskModeCombine
  , inverted          :: Boolean
  , pathPropertyId    :: NonEmptyString      -- AnimatableProperty ID for path
  , opacityPropertyId :: NonEmptyString      -- AnimatableProperty ID (0-100)
  , featherPropertyId :: NonEmptyString      -- AnimatableProperty ID (pixels)
  , featherXPropertyId :: Maybe NonEmptyString  -- Optional horizontal feather
  , featherYPropertyId :: Maybe NonEmptyString  -- Optional vertical feather
  , expansionPropertyId :: NonEmptyString    -- AnimatableProperty ID (expand/contract)
  , color             :: NonEmptyString      -- Hex color for UI visualization
  }

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Kappa constant for bezier circle approximation
bezierKappa :: Number
bezierKappa = 0.5522847498

-- | Default mask color (yellow)
defaultMaskColor :: String
defaultMaskColor = "#FFFF00"

-- | Default ellipse mask color (cyan)
defaultEllipseMaskColor :: String
defaultEllipseMaskColor = "#00FFFF"
