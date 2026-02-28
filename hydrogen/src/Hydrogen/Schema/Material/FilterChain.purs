-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // material // filter-chain
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterChain - composable sequence of CSS/image filters.
-- |
-- | Chains multiple filter operations in sequence. Filters are applied
-- | in order, with each filter operating on the output of the previous.
-- |
-- | ## Supported Filters
-- |
-- | - blur, brightness, contrast, grayscale
-- | - hue-rotate, invert, opacity, saturate
-- | - sepia, drop-shadow
-- |
-- | ## Order Matters
-- |
-- | ```
-- | grayscale -> sepia  ≠  sepia -> grayscale
-- | ```
-- |
-- | The first produces sepia-toned gray, the second produces gray.
-- |
-- | ## Dependencies
-- |
-- | - Material filter atoms (FilterBrightness, FilterContrast, etc.)

module Hydrogen.Schema.Material.FilterChain
  ( -- * Filter Operation
    FilterOp(..)
  
  -- * Types
  , FilterChain(FilterChain)
  
  -- * Constructors
  , filterChain
  , filterChainEmpty
  , filterChainSingle
  
  -- * Operations
  , addFilter
  , prependFilter
  , getFilters
  , filterCount
  
  -- * Presets
  , vintageFilter
  , dramaticFilter
  , softFocusFilter
  , highContrastFilter
  , warmFilter
  , coolFilter
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
  , negate
  , (<>)
  )

import Data.Array (length, snoc, cons) as Array

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // filter op
-- ═════════════════════════════════════════════════════════════════════════════

-- | Individual filter operation.
-- |
-- | Each operation takes a single numeric parameter.
-- | These map directly to CSS filter functions.
data FilterOp
  = Blur Number            -- ^ Gaussian blur in pixels
  | Brightness Number      -- ^ 0.0 = black, 1.0 = normal, 2.0 = 2x bright
  | Contrast Number        -- ^ 0.0 = gray, 1.0 = normal, 2.0 = 2x contrast
  | Grayscale Number       -- ^ 0.0 = normal, 1.0 = full grayscale
  | HueRotate Number       -- ^ Rotation in degrees (0-360)
  | Invert Number          -- ^ 0.0 = normal, 1.0 = fully inverted
  | Opacity Number         -- ^ 0.0 = transparent, 1.0 = opaque
  | Saturate Number        -- ^ 0.0 = desaturated, 1.0 = normal, 2.0 = 2x
  | Sepia Number           -- ^ 0.0 = normal, 1.0 = full sepia

derive instance eqFilterOp :: Eq FilterOp
derive instance ordFilterOp :: Ord FilterOp

instance showFilterOp :: Show FilterOp where
  show (Blur n) = "blur(" <> show n <> "px)"
  show (Brightness n) = "brightness(" <> show n <> ")"
  show (Contrast n) = "contrast(" <> show n <> ")"
  show (Grayscale n) = "grayscale(" <> show n <> ")"
  show (HueRotate n) = "hue-rotate(" <> show n <> "deg)"
  show (Invert n) = "invert(" <> show n <> ")"
  show (Opacity n) = "opacity(" <> show n <> ")"
  show (Saturate n) = "saturate(" <> show n <> ")"
  show (Sepia n) = "sepia(" <> show n <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // filter-chain
-- ═════════════════════════════════════════════════════════════════════════════

-- | FilterChain - ordered sequence of filter operations.
-- |
-- | Filters are applied in array order, each operating on the
-- | result of the previous operation.
newtype FilterChain = FilterChain (Array FilterOp)

derive instance eqFilterChain :: Eq FilterChain

instance showFilterChain :: Show FilterChain where
  show (FilterChain ops) = "(FilterChain " <> show ops <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create filter chain from array of operations
filterChain :: Array FilterOp -> FilterChain
filterChain = FilterChain

-- | Empty filter chain (no effect)
filterChainEmpty :: FilterChain
filterChainEmpty = FilterChain []

-- | Single-filter chain
filterChainSingle :: FilterOp -> FilterChain
filterChainSingle op = FilterChain [op]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add filter to end of chain
addFilter :: FilterOp -> FilterChain -> FilterChain
addFilter op (FilterChain ops) = FilterChain (Array.snoc ops op)

-- | Add filter to beginning of chain
prependFilter :: FilterOp -> FilterChain -> FilterChain
prependFilter op (FilterChain ops) = FilterChain (Array.cons op ops)

-- | Get array of filter operations
getFilters :: FilterChain -> Array FilterOp
getFilters (FilterChain ops) = ops

-- | Get number of filters in chain
filterCount :: FilterChain -> Int
filterCount (FilterChain ops) = Array.length ops

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vintage/retro look
-- |
-- | Sepia tint, reduced contrast, slight blur.
vintageFilter :: FilterChain
vintageFilter = FilterChain
  [ Sepia 0.4
  , Contrast 0.9
  , Brightness 1.1
  , Saturate 0.8
  ]

-- | Dramatic/cinematic look
-- |
-- | High contrast, slight desaturation, darkened.
dramaticFilter :: FilterChain
dramaticFilter = FilterChain
  [ Contrast 1.3
  , Brightness 0.9
  , Saturate 0.85
  ]

-- | Soft focus/dreamy look
-- |
-- | Slight blur, brightened, reduced contrast.
softFocusFilter :: FilterChain
softFocusFilter = FilterChain
  [ Blur 1.5
  , Brightness 1.1
  , Contrast 0.9
  ]

-- | High contrast black and white
highContrastFilter :: FilterChain
highContrastFilter = FilterChain
  [ Grayscale 1.0
  , Contrast 1.5
  , Brightness 1.05
  ]

-- | Warm/sunny look
-- |
-- | Increased saturation, slight sepia, brightened.
warmFilter :: FilterChain
warmFilter = FilterChain
  [ Saturate 1.2
  , Sepia 0.1
  , Brightness 1.05
  , HueRotate (-10.0)
  ]

-- | Cool/blue look
-- |
-- | Reduced saturation, blue shift.
coolFilter :: FilterChain
coolFilter = FilterChain
  [ Saturate 0.9
  , HueRotate 15.0
  , Brightness 1.0
  , Contrast 1.05
  ]
