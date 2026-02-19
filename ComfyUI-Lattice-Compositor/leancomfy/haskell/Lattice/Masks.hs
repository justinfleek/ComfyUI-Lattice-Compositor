{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Masks
Description : Layer masks and track mattes
Copyright   : (c) Lattice, 2026
License     : MIT

Source: leancomfy/lean/Lattice/Masks.lean
-}

module Lattice.Masks
  ( -- * Enumerations
    MatteType(..)
  , MaskModeCombine(..)
    -- * Mask Vertex
  , MaskVertex(..)
    -- * Mask Path
  , MaskPath(..)
    -- * Layer Mask
  , LayerMask(..)
    -- * Helpers
  , defaultMaskColor
  , defaultEllipseMaskColor
  , bezierKappa
  ) where

import GHC.Generics (Generic)
import Data.Vector (Vector)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Matte Type
--------------------------------------------------------------------------------

-- | Matte source types (uses layer above as matte source)
data MatteType
  = MTNone           -- ^ No matte source
  | MTAlpha          -- ^ Use alpha channel of matte layer
  | MTAlphaInverted  -- ^ Invert alpha of matte layer
  | MTLuma           -- ^ Use luminance of matte layer
  | MTLumaInverted   -- ^ Invert luminance of matte layer
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Mask Mode
--------------------------------------------------------------------------------

-- | Mask mode determines how multiple masks combine
data MaskModeCombine
  = MMAdd        -- ^ Union of masks (default)
  | MMSubtract   -- ^ Subtract this mask from previous
  | MMIntersect  -- ^ Intersection with previous
  | MMLighten    -- ^ Max of mask values
  | MMDarken     -- ^ Min of mask values
  | MMDifference -- ^ Absolute difference
  | MMNone       -- ^ Mask is disabled
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Mask Vertex
--------------------------------------------------------------------------------

-- | Mask vertex with bezier handles
data MaskVertex = MaskVertex
  { mvX          :: !FiniteFloat
  , mvY          :: !FiniteFloat
  , mvInTangentX :: !FiniteFloat
  , mvInTangentY :: !FiniteFloat
  , mvOutTangentX :: !FiniteFloat
  , mvOutTangentY :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Mask Path
--------------------------------------------------------------------------------

-- | Mask path - collection of bezier vertices forming a shape
data MaskPath = MaskPath
  { mpClosed   :: !Bool
  , mpVertices :: !(Vector MaskVertex)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Layer Mask
--------------------------------------------------------------------------------

-- | Layer mask - bezier path that clips layer content
data LayerMask = LayerMask
  { lmId                :: !NonEmptyString
  , lmName              :: !NonEmptyString
  , lmEnabled           :: !Bool
  , lmLocked            :: !Bool
  , lmMode              :: !MaskModeCombine
  , lmInverted          :: !Bool
  , lmPathPropertyId    :: !NonEmptyString      -- ^ AnimatableProperty ID for path
  , lmOpacityPropertyId :: !NonEmptyString      -- ^ AnimatableProperty ID (0-100)
  , lmFeatherPropertyId :: !NonEmptyString      -- ^ AnimatableProperty ID (pixels)
  , lmFeatherXPropertyId :: !(Maybe NonEmptyString)  -- ^ Optional horizontal feather
  , lmFeatherYPropertyId :: !(Maybe NonEmptyString)  -- ^ Optional vertical feather
  , lmExpansionPropertyId :: !NonEmptyString    -- ^ AnimatableProperty ID (expand/contract)
  , lmColor             :: !NonEmptyString      -- ^ Hex color for UI visualization
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Kappa constant for bezier circle approximation
bezierKappa :: Double
bezierKappa = 0.5522847498

-- | Default mask color (yellow)
defaultMaskColor :: String
defaultMaskColor = "#FFFF00"

-- | Default ellipse mask color (cyan)
defaultEllipseMaskColor :: String
defaultEllipseMaskColor = "#00FFFF"
