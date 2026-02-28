-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // dimension // swatch
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Swatch dimension atoms — measurements for color swatches and patterns.
-- |
-- | ## Design Philosophy
-- |
-- | Swatches are bounded visual elements for displaying colors. They appear in:
-- | - Color pickers (selectable swatches)
-- | - Palettes (color collections)
-- | - Form inputs (color preview)
-- | - Design system documentation
-- |
-- | ## Atoms Provided
-- |
-- | | Atom             | Min  | Max   | Behavior | Purpose                    |
-- | |------------------|------|-------|----------|----------------------------|
-- | | SwatchSize       | 8px  | 128px | clamps   | Swatch width/height        |
-- | | CheckerboardSize | 2px  | 32px  | clamps   | Transparency pattern cell  |
-- |
-- | ## Why These Bounds?
-- |
-- | - **SwatchSize 8px min**: Smaller is not usably clickable/tappable.
-- |   8px is the absolute minimum for a touch target component.
-- |
-- | - **SwatchSize 128px max**: Larger swatches are just color blocks.
-- |   For display purposes beyond 128px, use a generic box with fill.
-- |
-- | - **CheckerboardSize 2px min**: Smaller patterns aren't visible.
-- |   2px creates a barely-perceptible texture for transparency.
-- |
-- | - **CheckerboardSize 32px max**: Larger checkers are distracting.
-- |   The pattern should indicate transparency, not dominate visually.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Dimension.Swatch as Swatch
-- |
-- | -- Standard swatch in a color picker
-- | pickerSwatch = Swatch.swatchSizeMd  -- 32px
-- |
-- | -- Small swatch for inline display
-- | inlineSwatch = Swatch.swatchSizeSm  -- 16px
-- |
-- | -- Checkerboard for transparency indication
-- | checker = Swatch.checkerboardSizeMd  -- 8px cells
-- | ```

module Hydrogen.Schema.Dimension.Swatch
  ( -- * Swatch Size (bounded)
    SwatchSize
  , swatchSize
  , swatchSizeXs
  , swatchSizeSm
  , swatchSizeMd
  , swatchSizeLg
  , swatchSizeXl
  , swatchSizeValue
  , swatchSizeToCss
  , swatchSizeBounds
  , addSwatchSize
  , subtractSwatchSize
  , scaleSwatchSize
  , isSwatchSizeMin
  , isSwatchSizeMax
  
  -- * Checkerboard Size (bounded)
  , CheckerboardSize
  , checkerboardSize
  , checkerboardSizeXs
  , checkerboardSizeSm
  , checkerboardSizeMd
  , checkerboardSizeLg
  , checkerboardSizeValue
  , checkerboardSizeToCss
  , checkerboardSizeBounds
  , isCheckerboardSizeMin
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (==)
  , (<)
  , (>)
  , (-)
  , (+)
  , (*)
  , (<>)
  , (&&)
  )

import Hydrogen.Schema.Bounded (NumberBounds, numberBounds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // swatch size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Swatch size in pixels (bounded)
-- |
-- | Minimum: 8px (minimum touch target for a swatch)
-- | Maximum: 128px (beyond this, use a generic colored box)
-- | Behavior: clamps to [8, 128]
-- |
-- | Swatches are typically square, so this represents both width and height.
newtype SwatchSize = SwatchSize Number

derive instance eqSwatchSize :: Eq SwatchSize
derive instance ordSwatchSize :: Ord SwatchSize

instance showSwatchSize :: Show SwatchSize where
  show (SwatchSize n) = show n <> "px"

-- | Swatch size bounds documentation
swatchSizeBounds :: NumberBounds
swatchSizeBounds = numberBounds 8.0 128.0 "swatch-size"
  "Size of a color swatch in pixels. Min 8px for touch targets, max 128px."

-- | Create a swatch size, clamping to valid range [8, 128]
swatchSize :: Number -> SwatchSize
swatchSize n
  | n < 8.0 = SwatchSize 8.0
  | n > 128.0 = SwatchSize 128.0
  | otherwise = SwatchSize n

-- | Extra small swatch (8px) - minimum size, dense grids
swatchSizeXs :: SwatchSize
swatchSizeXs = SwatchSize 8.0

-- | Small swatch (16px) - inline display, compact pickers
swatchSizeSm :: SwatchSize
swatchSizeSm = SwatchSize 16.0

-- | Medium swatch (32px) - standard picker size (default)
swatchSizeMd :: SwatchSize
swatchSizeMd = SwatchSize 32.0

-- | Large swatch (48px) - prominent display, touch-friendly
swatchSizeLg :: SwatchSize
swatchSizeLg = SwatchSize 48.0

-- | Extra large swatch (64px) - hero display, accessibility
swatchSizeXl :: SwatchSize
swatchSizeXl = SwatchSize 64.0

-- | Extract the numeric value
swatchSizeValue :: SwatchSize -> Number
swatchSizeValue (SwatchSize n) = n

-- | Convert to CSS string
swatchSizeToCss :: SwatchSize -> String
swatchSizeToCss (SwatchSize n) = show n <> "px"

-- | Add two swatch sizes (result clamped to bounds)
addSwatchSize :: SwatchSize -> SwatchSize -> SwatchSize
addSwatchSize (SwatchSize a) (SwatchSize b) = swatchSize (a + b)

-- | Subtract swatch sizes (result clamped to bounds)
subtractSwatchSize :: SwatchSize -> SwatchSize -> SwatchSize
subtractSwatchSize (SwatchSize a) (SwatchSize b) = swatchSize (a - b)

-- | Scale swatch size by a factor (result clamped to bounds)
scaleSwatchSize :: Number -> SwatchSize -> SwatchSize
scaleSwatchSize factor (SwatchSize n) = swatchSize (n * factor)

-- | Check if swatch is at minimum size
isSwatchSizeMin :: SwatchSize -> Boolean
isSwatchSizeMin (SwatchSize n) = n == 8.0

-- | Check if swatch is at maximum size
isSwatchSizeMax :: SwatchSize -> Boolean
isSwatchSizeMax (SwatchSize n) = n == 128.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // checkerboard size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Checkerboard cell size in pixels (bounded)
-- |
-- | Minimum: 2px (barely visible texture)
-- | Maximum: 32px (larger becomes distracting)
-- | Behavior: clamps to [2, 32]
-- |
-- | The checkerboard pattern indicates transparency in color displays.
-- | Each cell is this size; the pattern alternates light/dark cells.
newtype CheckerboardSize = CheckerboardSize Number

derive instance eqCheckerboardSize :: Eq CheckerboardSize
derive instance ordCheckerboardSize :: Ord CheckerboardSize

instance showCheckerboardSize :: Show CheckerboardSize where
  show (CheckerboardSize n) = show n <> "px"

-- | Checkerboard size bounds documentation
checkerboardSizeBounds :: NumberBounds
checkerboardSizeBounds = numberBounds 2.0 32.0 "checkerboard-size"
  "Size of checkerboard cells for transparency indication. 2-32px."

-- | Create a checkerboard size, clamping to valid range [2, 32]
checkerboardSize :: Number -> CheckerboardSize
checkerboardSize n
  | n < 2.0 = CheckerboardSize 2.0
  | n > 32.0 = CheckerboardSize 32.0
  | otherwise = CheckerboardSize n

-- | Extra small checkerboard (2px) - subtle, high-density displays
checkerboardSizeXs :: CheckerboardSize
checkerboardSizeXs = CheckerboardSize 2.0

-- | Small checkerboard (4px) - standard for small swatches
checkerboardSizeSm :: CheckerboardSize
checkerboardSizeSm = CheckerboardSize 4.0

-- | Medium checkerboard (8px) - default, clearly visible (default)
checkerboardSizeMd :: CheckerboardSize
checkerboardSizeMd = CheckerboardSize 8.0

-- | Large checkerboard (16px) - prominent, accessibility
checkerboardSizeLg :: CheckerboardSize
checkerboardSizeLg = CheckerboardSize 16.0

-- | Extract the numeric value
checkerboardSizeValue :: CheckerboardSize -> Number
checkerboardSizeValue (CheckerboardSize n) = n

-- | Convert to CSS string
checkerboardSizeToCss :: CheckerboardSize -> String
checkerboardSizeToCss (CheckerboardSize n) = show n <> "px"

-- | Check if checkerboard is at minimum size
-- |
-- | Useful for determining if further size reduction is possible
-- | when adapting to container constraints.
isCheckerboardSizeMin :: CheckerboardSize -> Boolean
isCheckerboardSizeMin (CheckerboardSize n) = n == 2.0 && n < 3.0
