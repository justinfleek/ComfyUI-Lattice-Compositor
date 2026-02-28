-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // hue
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hue - position on the color wheel.
-- |
-- | Measured in degrees from 0 to 359:
-- | - **0°/360°**: Red
-- | - **60°**: Yellow  
-- | - **120°**: Green
-- | - **180°**: Cyan
-- | - **240°**: Blue
-- | - **300°**: Magenta
-- |
-- | Hue is cyclic - values outside 0-359 wrap around.

module Hydrogen.Schema.Color.Hue
  ( -- * Hue (0-359)
    Hue
  , hue
  , hueWrap
  , unwrap
  , rotate
  , complement
  , bounds
  , toNumber
  -- Operations
  , blend
  , blendShortestPath
  , lerp
  , toRadians
  , toDegrees
  , distance
  , shortestDistance
  -- Predicates
  , isWarm
  , isCool
  , isRed
  , isOrange
  , isYellow
  , isGreen
  , isCyan
  , isBlue
  , isMagenta
  , colorCategory
  -- Constants
  , red
  , orange
  , yellow
  , green
  , cyan
  , blue
  , magenta
  
  -- * HueShift (-180 to 180, wraps)
  , HueShift
  , hueShift
  , hueShiftWrap
  , unwrapHueShift
  , hueShiftBounds
  , applyHueShift
  , noHueShift
  , negateHueShift
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , mod
  , negate
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  )

import Data.Int (toNumber, round) as Int
import Data.Number (pi) as Number
import Data.Ord (abs) as Ord
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // hue
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hue value in degrees (0-359)
-- |
-- | Represents position on the color wheel. Red at 0°, cycling through
-- | yellow, green, cyan, blue, magenta, and back to red at 360°.
newtype Hue = Hue Int

derive instance eqHue :: Eq Hue
derive instance ordHue :: Ord Hue

instance showHue :: Show Hue where
  show (Hue h) = show h <> "°"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a hue, clamping to 0-359
hue :: Int -> Hue
hue n = Hue (Bounded.clampInt 0 359 n)

-- | Create a hue, wrapping values outside 0-359
-- |
-- | This is often what you want for rotations:
-- | - `hueWrap 370` = `hue 10`
-- | - `hueWrap (-30)` = `hue 330`
hueWrap :: Int -> Hue
hueWrap n = Hue (mod' n 360)
  where
  mod' a b = ((a `mod` b) + b) `mod` b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate hue by degrees (wraps around)
rotate :: Int -> Hue -> Hue
rotate degrees' (Hue h) = hueWrap (h + degrees')

-- | Get complementary hue (opposite on color wheel)
complement :: Hue -> Hue
complement = rotate 180

-- | Blend two hues by simple linear interpolation
-- |
-- | WARNING: This takes the "long way" around the color wheel for large
-- | differences. For perceptually correct blending, use `blendShortestPath`.
-- | ```purescript
-- | blend 0.5 (hue 10) (hue 350)  -- hue 180 (through green/cyan!)
-- | ```
blend :: Number -> Hue -> Hue -> Hue
blend weight (Hue a) (Hue b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
      result = Int.toNumber a * (1.0 - w) + Int.toNumber b * w
  in hueWrap (Int.round result)

-- | Blend two hues via shortest path around the color wheel
-- |
-- | This is perceptually correct for hue interpolation. It automatically
-- | chooses the shorter arc between two hues:
-- | ```purescript
-- | blendShortestPath 0.5 (hue 10) (hue 350)  -- hue 0 (through red!)
-- | blendShortestPath 0.5 red cyan            -- hue 90 (yellow-green)
-- | ```
blendShortestPath :: Number -> Hue -> Hue -> Hue
blendShortestPath weight (Hue a) (Hue b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
      diff = b - a
      -- Choose shorter direction around the wheel
      adjustedDiff = if diff > 180 then diff - 360
                     else if diff < negate 180 then diff + 360
                     else diff
      result = Int.toNumber a + Int.toNumber adjustedDiff * w
  in hueWrap (Int.round result)

-- | Linear interpolation (standard lerp signature)
-- |
-- | Uses shortest path blending for perceptual correctness:
-- | ```purescript
-- | lerp red blue 0.5  -- Hue at 300° (magenta)
-- | ```
lerp :: Hue -> Hue -> Number -> Hue
lerp from to t = blendShortestPath t from to

-- | Convert hue to radians (0° = 0, 360° = 2π)
-- |
-- | Useful for trigonometric calculations in color math:
-- | ```purescript
-- | toRadians (hue 180)  -- π (approximately 3.14159)
-- | toRadians red        -- 0.0
-- | ```
toRadians :: Hue -> Number
toRadians (Hue h) = Int.toNumber h * Number.pi / 180.0

-- | Convert hue to degrees as Number (for precision calculations)
toDegrees :: Hue -> Number
toDegrees (Hue h) = Int.toNumber h

-- | Angular distance between two hues (always positive, can be > 180)
-- |
-- | Simple absolute difference, doesn't account for wraparound:
-- | ```purescript
-- | distance (hue 10) (hue 350)  -- 340
-- | ```
distance :: Hue -> Hue -> Int
distance (Hue a) (Hue b) = Ord.abs (a - b)

-- | Shortest angular distance between two hues (0-180)
-- |
-- | Accounts for wraparound - always returns the shorter arc:
-- | ```purescript
-- | shortestDistance (hue 10) (hue 350)  -- 20 (through red)
-- | shortestDistance red cyan            -- 180
-- | ```
shortestDistance :: Hue -> Hue -> Int
shortestDistance (Hue a) (Hue b) =
  let diff = Ord.abs (a - b)
  in if diff > 180 then 360 - diff else diff

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if hue is warm (red through yellow, 0-60° and 300-360°)
-- |
-- | Warm colors advance visually and feel energetic:
-- | ```purescript
-- | isWarm red      -- true (0°)
-- | isWarm yellow   -- true (60°)
-- | isWarm magenta  -- true (300°)
-- | isWarm cyan     -- false (180°)
-- | ```
isWarm :: Hue -> Boolean
isWarm (Hue h) = h <= 60 || h >= 300

-- | Check if hue is cool (cyan through blue, 150-270°)
-- |
-- | Cool colors recede visually and feel calm:
-- | ```purescript
-- | isCool cyan  -- true (180°)
-- | isCool blue  -- true (240°)
-- | isCool red   -- false (0°)
-- | ```
isCool :: Hue -> Boolean
isCool (Hue h) = h >= 150 && h <= 270

-- | Check if hue is in the red range (330-30°, wrapping through 0)
isRed :: Hue -> Boolean
isRed (Hue h) = h >= 330 || h <= 30

-- | Check if hue is in the orange range (30-60°)
isOrange :: Hue -> Boolean
isOrange (Hue h) = h >= 30 && h < 60

-- | Check if hue is in the yellow range (60-90°)
isYellow :: Hue -> Boolean
isYellow (Hue h) = h >= 60 && h < 90

-- | Check if hue is in the green range (90-150°)
isGreen :: Hue -> Boolean
isGreen (Hue h) = h >= 90 && h < 150

-- | Check if hue is in the cyan range (150-210°)
isCyan :: Hue -> Boolean
isCyan (Hue h) = h >= 150 && h < 210

-- | Check if hue is in the blue range (210-270°)
isBlue :: Hue -> Boolean
isBlue (Hue h) = h >= 210 && h < 270

-- | Check if hue is in the magenta range (270-330°)
isMagenta :: Hue -> Boolean
isMagenta (Hue h) = h >= 270 && h < 330

-- | Classify a hue into its primary color category
-- |
-- | Returns a human-readable color name for the hue's region:
-- | ```purescript
-- | colorCategory red     -- "red"
-- | colorCategory (hue 45)  -- "orange"
-- | colorCategory cyan    -- "cyan"
-- | ```
colorCategory :: Hue -> String
colorCategory (Hue h)
  | h >= 330 || h < 30  = "red"
  | h >= 30 && h < 60   = "orange"
  | h >= 60 && h < 90   = "yellow"
  | h >= 90 && h < 150  = "green"
  | h >= 150 && h < 210 = "cyan"
  | h >= 210 && h < 270 = "blue"
  | otherwise           = "magenta"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Red (0°)
red :: Hue
red = Hue 0

-- | Orange (30°)
orange :: Hue
orange = Hue 30

-- | Yellow (60°)
yellow :: Hue
yellow = Hue 60

-- | Green (120°)
green :: Hue
green = Hue 120

-- | Cyan (180°)
cyan :: Hue
cyan = Hue 180

-- | Blue (240°)
blue :: Hue
blue = Hue 240

-- | Magenta (300°)
magenta :: Hue
magenta = Hue 300

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: Hue -> Int
unwrap (Hue h) = h

-- | Convert to Number for calculations
toNumber :: Hue -> Number
toNumber (Hue h) = Int.toNumber h

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 359 "hue" "Color wheel position in degrees"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // hue shift // ±180
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hue shift - adjustment to a hue value.
-- |
-- | Measured in degrees from -180 to 180:
-- | - **-180°**: Shift to complement (same as +180)
-- | - **0°**: No change
-- | - **+180°**: Shift to complement
-- |
-- | Used in color correction effects like Hue/Saturation adjustment.
-- | Values wrap: +200° becomes -160° (equivalent rotation).
newtype HueShift = HueShift Number

derive instance eqHueShift :: Eq HueShift
derive instance ordHueShift :: Ord HueShift

instance showHueShift :: Show HueShift where
  show (HueShift h) = show h <> "°"

-- | Create HueShift, wrapping to -180 to 180 range.
-- |
-- | This ensures values always represent the shortest path:
-- | - `hueShift 200` = `hueShift (-160)`
-- | - `hueShift (-270)` = `hueShift 90`
hueShift :: Number -> HueShift
hueShift n = HueShift (wrapHueShift n)

-- | Create HueShift with explicit wrapping (alias)
hueShiftWrap :: Number -> HueShift
hueShiftWrap = hueShift

-- | Extract the raw Number value (-180 to 180)
unwrapHueShift :: HueShift -> Number
unwrapHueShift (HueShift h) = h

-- | Apply hue shift to a Hue, returning rotated Hue.
applyHueShift :: HueShift -> Hue -> Hue
applyHueShift (HueShift shift) h = rotate (Int.round shift) h

-- | No change (0°)
noHueShift :: HueShift
noHueShift = HueShift 0.0

-- | Negate a hue shift
negateHueShift :: HueShift -> HueShift
negateHueShift (HueShift h) = HueShift (negate h)

-- | Bounds documentation for HueShift
hueShiftBounds :: Bounded.NumberBounds
hueShiftBounds = Bounded.numberBounds (-180.0) 180.0 "hueShift" 
  "Hue adjustment in degrees (-180 to 180)"

-- | Wrap value to -180 to 180 range.
-- |
-- | Ensures values represent shortest rotation path.
wrapHueShift :: Number -> Number
wrapHueShift n =
  let 
    -- Normalize to 0-360 first
    normalized = n - 360.0 * floor' (n / 360.0)
    -- Then shift to -180 to 180
  in if normalized > 180.0 
     then normalized - 360.0 
     else normalized
  where
  floor' :: Number -> Number
  floor' x = Int.toNumber (Int.round (x - 0.5))
