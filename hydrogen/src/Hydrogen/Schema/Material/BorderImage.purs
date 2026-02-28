-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // material // border-image
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BorderImage - image-based border specification.
-- |
-- | CSS border-image allows using an image (or gradient) as the border,
-- | with control over how it's sliced, scaled, and repeated.
-- |
-- | ## CSS Border-Image Properties
-- |
-- | - **source**: Image URL or gradient
-- | - **slice**: How to cut the image into 9 regions (4 corners, 4 edges, center)
-- | - **width**: Width of the border image area
-- | - **outset**: How far the border extends beyond the border box
-- | - **repeat**: How edge regions are scaled (stretch, repeat, round, space)
-- |
-- | ## The 9-Slice Model
-- |
-- | ```
-- | ┌───────┬───────────────┬───────┐
-- | │ TL    │     TOP       │    TR │
-- | ├───────┼───────────────┼───────┤
-- | │ LEFT  │    CENTER     │ RIGHT │
-- | ├───────┼───────────────┼───────┤
-- | │ BL    │    BOTTOM     │    BR │
-- | └───────┴───────────────┴───────┘
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded

module Hydrogen.Schema.Material.BorderImage
  ( -- * Repeat Mode
    BorderImageRepeat(..)
  
  -- * Slice
  , BorderImageSlice(BorderImageSlice)
  , sliceUniform
  , sliceSymmetric
  , sliceCustom
  
  -- * Types
  , BorderImage(BorderImage)
  , BorderImageConfig
  
  -- * Constructors
  , borderImage
  , borderImageSimple
  , borderImageNone
  
  -- * Accessors
  , source
  , slice
  , width
  , outset
  , repeatMode
  , fillCenter
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (clampNumber) as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // repeat mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How border image edges are scaled/repeated.
data BorderImageRepeat
  = Stretch   -- ^ Scale to fill (may distort)
  | Repeat    -- ^ Tile without scaling (may clip)
  | Round     -- ^ Tile, scale to fit whole number of tiles
  | Space     -- ^ Tile with even spacing between

derive instance eqBorderImageRepeat :: Eq BorderImageRepeat
derive instance ordBorderImageRepeat :: Ord BorderImageRepeat

instance showBorderImageRepeat :: Show BorderImageRepeat where
  show Stretch = "stretch"
  show Repeat = "repeat"
  show Round = "round"
  show Space = "space"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // slice
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border image slice - defines how to cut the source image.
-- |
-- | Values are offsets from the edges (top, right, bottom, left).
-- | Can be in pixels or percentages.
newtype BorderImageSlice = BorderImageSlice
  { top :: Number       -- ^ Offset from top edge
  , right :: Number     -- ^ Offset from right edge
  , bottom :: Number    -- ^ Offset from bottom edge
  , left :: Number      -- ^ Offset from left edge
  , isPercent :: Boolean -- ^ True if values are percentages
  }

derive instance eqBorderImageSlice :: Eq BorderImageSlice

instance showBorderImageSlice :: Show BorderImageSlice where
  show (BorderImageSlice s) = 
    "(Slice " <> show s.top 
      <> " " <> show s.right 
      <> " " <> show s.bottom 
      <> " " <> show s.left
      <> (if s.isPercent then "%" else "px")
      <> ")"

-- | Create uniform slice (same value all sides)
sliceUniform :: Number -> Boolean -> BorderImageSlice
sliceUniform value isPercent = BorderImageSlice
  { top: clampSlice value
  , right: clampSlice value
  , bottom: clampSlice value
  , left: clampSlice value
  , isPercent
  }

-- | Create symmetric slice (vertical, horizontal)
sliceSymmetric :: Number -> Number -> Boolean -> BorderImageSlice
sliceSymmetric vertical horizontal isPercent = BorderImageSlice
  { top: clampSlice vertical
  , right: clampSlice horizontal
  , bottom: clampSlice vertical
  , left: clampSlice horizontal
  , isPercent
  }

-- | Create custom slice with all four values
sliceCustom :: Number -> Number -> Number -> Number -> Boolean -> BorderImageSlice
sliceCustom t r b l isPercent = BorderImageSlice
  { top: clampSlice t
  , right: clampSlice r
  , bottom: clampSlice b
  , left: clampSlice l
  , isPercent
  }

-- Helper: clamp slice value to non-negative
clampSlice :: Number -> Number
clampSlice = Bounded.clampNumber 0.0 100000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // border-image
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration record for creating BorderImage
type BorderImageConfig =
  { source :: String              -- ^ Image URL or gradient CSS
  , slice :: BorderImageSlice     -- ^ 9-slice configuration
  , width :: Number               -- ^ Border width in pixels
  , outset :: Number              -- ^ How far border extends outward
  , repeatMode :: BorderImageRepeat -- ^ Edge repeat mode
  , fillCenter :: Boolean         -- ^ Whether to fill center region
  }

-- | BorderImage - image-based border compound.
-- |
-- | Describes a border using an image source with 9-slice scaling.
newtype BorderImage = BorderImage
  { source :: Maybe String        -- ^ Image URL or gradient (Nothing = none)
  , slice :: BorderImageSlice     -- ^ How to slice the source
  , width :: Number               -- ^ Border width
  , outset :: Number              -- ^ Extension beyond border box
  , repeatMode :: BorderImageRepeat -- ^ Edge fill mode
  , fillCenter :: Boolean         -- ^ Fill center with center slice
  }

derive instance eqBorderImage :: Eq BorderImage

instance showBorderImage :: Show BorderImage where
  show (BorderImage b) = case b.source of
    Nothing -> "(BorderImage none)"
    Just src -> "(BorderImage src:" <> src 
      <> " " <> show b.slice
      <> " width:" <> show b.width
      <> " " <> show b.repeatMode
      <> (if b.fillCenter then " fill" else "")
      <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create BorderImage from full configuration
borderImage :: BorderImageConfig -> BorderImage
borderImage cfg = BorderImage
  { source: Just cfg.source
  , slice: cfg.slice
  , width: Bounded.clampNumber 0.0 10000.0 cfg.width
  , outset: Bounded.clampNumber 0.0 1000.0 cfg.outset
  , repeatMode: cfg.repeatMode
  , fillCenter: cfg.fillCenter
  }

-- | Create simple BorderImage with defaults
-- |
-- | - Uniform slice of 30%
-- | - Stretch repeat mode
-- | - No center fill
borderImageSimple :: String -> Number -> BorderImage
borderImageSimple src borderWidth = BorderImage
  { source: Just src
  , slice: sliceUniform 30.0 true
  , width: Bounded.clampNumber 0.0 10000.0 borderWidth
  , outset: 0.0
  , repeatMode: Stretch
  , fillCenter: false
  }

-- | No border image
borderImageNone :: BorderImage
borderImageNone = BorderImage
  { source: Nothing
  , slice: sliceUniform 0.0 false
  , width: 0.0
  , outset: 0.0
  , repeatMode: Stretch
  , fillCenter: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get image source (Nothing if none)
source :: BorderImage -> Maybe String
source (BorderImage b) = b.source

-- | Get slice configuration
slice :: BorderImage -> BorderImageSlice
slice (BorderImage b) = b.slice

-- | Get border width
width :: BorderImage -> Number
width (BorderImage b) = b.width

-- | Get outset value
outset :: BorderImage -> Number
outset (BorderImage b) = b.outset

-- | Get repeat mode
repeatMode :: BorderImage -> BorderImageRepeat
repeatMode (BorderImage b) = b.repeatMode

-- | Get fill center flag
fillCenter :: BorderImage -> Boolean
fillCenter (BorderImage b) = b.fillCenter
