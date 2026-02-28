-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // dimension // spacing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spacing — bounded dimension values for gaps, padding, margins.
-- |
-- | Spacing values represent distances in UI layout. Unlike raw numbers,
-- | Spacing carries its unit and is bounded to prevent invalid values.
-- |
-- | ## Supported Units
-- |
-- | - **px**: CSS pixels (device-independent reference pixels at 96 PPI)
-- | - **rem**: Relative to root font size (typically 16px)
-- | - **em**: Relative to current element's font size
-- | - **percent**: Percentage of containing block
-- | - **vw/vh**: Viewport width/height percentage
-- |
-- | ## Bounds
-- |
-- | All spacing values are clamped to non-negative values with a reasonable
-- | maximum (10000) to prevent layout-breaking extremes. Zero is valid.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Dimension.Spacing as S
-- |
-- | -- Pixel values
-- | S.px 16.0      -- 16px
-- | S.px 0.0       -- 0px (no spacing)
-- |
-- | -- Relative units
-- | S.rem 1.0      -- 1rem (typically 16px)
-- | S.em 0.5       -- 0.5em
-- |
-- | -- Percentages
-- | S.percent 50.0 -- 50%
-- | S.vw 100.0     -- 100vw (full viewport width)
-- | ```

module Hydrogen.Schema.Dimension.Spacing
  ( -- * Types
    Spacing
  , Unit(..)
  
  -- * Constructors
  , spacing
  , px
  , rem
  , em
  , percent
  , vw
  , vh
  , vmin
  , vmax
  , zero
  
  -- * Accessors
  , value
  , unit
  , unwrap
  
  -- * Operations
  , scale
  , add
  , negateSpacing
  , half
  , double
  , isZero
  
  -- * Semantic Scale (4px base grid)
  , space0
  , space1
  , space2
  , space3
  , space4
  , space5
  , space6
  , space8
  , space10
  , space12
  , space16
  , space20
  , space24
  , space32
  , space40
  , space48
  , space64
  
  -- * Output
  , toLegacyCss
  
  -- * Bounds
  , bounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , negate
  , (<>)
  , (==)
  , (+)
  , (-)
  , (*)
  , (<)
  , (>)
  , (&&)
  )

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // unit
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS length units supported by Spacing
data Unit
  = Px       -- ^ CSS pixels (reference pixels at 96 PPI)
  | Rem      -- ^ Root em (relative to html font-size)
  | Em       -- ^ Em (relative to element font-size)
  | Percent  -- ^ Percentage of containing block
  | Vw       -- ^ Viewport width percentage
  | Vh       -- ^ Viewport height percentage
  | Vmin     -- ^ Minimum of vw/vh
  | Vmax     -- ^ Maximum of vw/vh

derive instance eqUnit :: Eq Unit
derive instance ordUnit :: Ord Unit

instance showUnit :: Show Unit where
  show Px = "px"
  show Rem = "rem"
  show Em = "em"
  show Percent = "%"
  show Vw = "vw"
  show Vh = "vh"
  show Vmin = "vmin"
  show Vmax = "vmax"

-- | Convert unit to CSS suffix string
unitToCss :: Unit -> String
unitToCss Px = "px"
unitToCss Rem = "rem"
unitToCss Em = "em"
unitToCss Percent = "%"
unitToCss Vw = "vw"
unitToCss Vh = "vh"
unitToCss Vmin = "vmin"
unitToCss Vmax = "vmax"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounded spacing value with unit
-- |
-- | Values are clamped to [-10000, 10000] to prevent layout-breaking extremes.
-- | Negative values are allowed for margin offsets.
newtype Spacing = Spacing { value :: Number, unit :: Unit }

derive instance eqSpacing :: Eq Spacing

instance ordSpacing :: Ord Spacing where
  compare (Spacing a) (Spacing b) = compare a.value b.value

instance showSpacing :: Show Spacing where
  show = toLegacyCss

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a spacing value with explicit unit, clamped to bounds
spacing :: Number -> Unit -> Spacing
spacing n u = Spacing 
  { value: Bounded.clampNumber (-10000.0) 10000.0 (Bounded.ensureFinite n 0.0)
  , unit: u 
  }

-- | Create spacing in CSS pixels
-- |
-- | ```purescript
-- | px 16.0  -- "16px"
-- | px 0.0   -- "0px"
-- | ```
px :: Number -> Spacing
px n = spacing n Px

-- | Create spacing in root ems
-- |
-- | ```purescript
-- | rem 1.0   -- "1rem" (typically 16px)
-- | rem 0.5   -- "0.5rem" (typically 8px)
-- | ```
rem :: Number -> Spacing
rem n = spacing n Rem

-- | Create spacing in ems (relative to element font-size)
em :: Number -> Spacing
em n = spacing n Em

-- | Create spacing as percentage
-- |
-- | ```purescript
-- | percent 50.0   -- "50%"
-- | percent 100.0  -- "100%"
-- | ```
percent :: Number -> Spacing
percent n = spacing n Percent

-- | Create spacing as viewport width percentage
vw :: Number -> Spacing
vw n = spacing n Vw

-- | Create spacing as viewport height percentage
vh :: Number -> Spacing
vh n = spacing n Vh

-- | Create spacing as minimum of viewport dimensions
vmin :: Number -> Spacing
vmin n = spacing n Vmin

-- | Create spacing as maximum of viewport dimensions
vmax :: Number -> Spacing
vmax n = spacing n Vmax

-- | Zero spacing (0px)
zero :: Spacing
zero = Spacing { value: 0.0, unit: Px }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the numeric value
value :: Spacing -> Number
value (Spacing s) = s.value

-- | Extract the unit
unit :: Spacing -> Unit
unit (Spacing s) = s.unit

-- | Extract as record
unwrap :: Spacing -> { value :: Number, unit :: Unit }
unwrap (Spacing s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale spacing by a factor (preserves unit)
-- |
-- | ```purescript
-- | scale 2.0 (px 16.0)  -- px 32.0
-- | scale 0.5 (rem 1.0)  -- rem 0.5
-- | ```
scale :: Number -> Spacing -> Spacing
scale factor (Spacing s) = spacing (s.value * factor) s.unit

-- | Add two spacing values (must have same unit)
-- |
-- | If units differ, returns the first value unchanged.
-- | For cross-unit math, use calc() in CSS or convert to common unit first.
add :: Spacing -> Spacing -> Spacing
add (Spacing a) (Spacing b)
  | a.unit == b.unit = spacing (a.value + b.value) a.unit
  | true = Spacing a  -- Cannot add different units, return first

-- | Negate spacing (for negative margins)
negateSpacing :: Spacing -> Spacing
negateSpacing (Spacing s) = spacing (0.0 - s.value) s.unit

-- | Halve spacing
half :: Spacing -> Spacing
half = scale 0.5

-- | Double spacing
double :: Spacing -> Spacing
double = scale 2.0

-- | Check if spacing is zero
isZero :: Spacing -> Boolean
isZero (Spacing s) = s.value == 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // semantic scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | 0px - no spacing
space0 :: Spacing
space0 = px 0.0

-- | 4px - minimal spacing
space1 :: Spacing
space1 = px 4.0

-- | 8px - tight spacing
space2 :: Spacing
space2 = px 8.0

-- | 12px - compact spacing
space3 :: Spacing
space3 = px 12.0

-- | 16px - standard spacing (1rem default)
space4 :: Spacing
space4 = px 16.0

-- | 20px - comfortable spacing
space5 :: Spacing
space5 = px 20.0

-- | 24px - relaxed spacing
space6 :: Spacing
space6 = px 24.0

-- | 32px - loose spacing
space8 :: Spacing
space8 = px 32.0

-- | 40px - spacious
space10 :: Spacing
space10 = px 40.0

-- | 48px - generous
space12 :: Spacing
space12 = px 48.0

-- | 64px - expansive
space16 :: Spacing
space16 = px 64.0

-- | 80px - section spacing
space20 :: Spacing
space20 = px 80.0

-- | 96px - large section spacing
space24 :: Spacing
space24 = px 96.0

-- | 128px - major section spacing
space32 :: Spacing
space32 = px 128.0

-- | 160px - page section spacing
space40 :: Spacing
space40 = px 160.0

-- | 192px - hero spacing
space48 :: Spacing
space48 = px 192.0

-- | 256px - maximum spacing
space64 :: Spacing
space64 = px 256.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to legacy CSS string
-- |
-- | Generates CSS-compatible length value.
-- | NOT an FFI boundary - pure string generation.
-- |
-- | ```purescript
-- | toLegacyCss (px 16.0)      -- "16px"
-- | toLegacyCss (rem 1.5)      -- "1.5rem"
-- | toLegacyCss (percent 50.0) -- "50%"
-- | toLegacyCss zero           -- "0"
-- | ```
toLegacyCss :: Spacing -> String
toLegacyCss (Spacing s)
  | s.value == 0.0 = "0"
  | isWholeNumber s.value = show (Int.round s.value) <> unitToCss s.unit
  | true = show s.value <> unitToCss s.unit

-- | Check if a number is effectively a whole number (within floating point tolerance)
isWholeNumber :: Number -> Boolean
isWholeNumber n = 
  let rounded = Int.round n
      diff = n - Int.toNumber rounded
  in diff > (-0.0001) && diff < 0.0001

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds documentation for Spacing values
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds (-10000.0) 10000.0 "spacing" "Layout spacing value with unit"
