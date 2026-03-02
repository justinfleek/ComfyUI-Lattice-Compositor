-- | Lattice.Services.Interpolation - Pure interpolation functions
-- |
-- | Pure math functions for keyframe interpolation.
-- | Handles bezier curves, linear interpolation, and color blending.
-- |
-- | Source: ui/src/services/interpolation.ts (pure math portions)

module Lattice.Services.Interpolation
  ( -- * Types
    Vec2(..)
  , Vec3(..)
  , Color(..)
  , EasingPreset(..)
    -- * Linear Interpolation
  , lerp, safeLerp, lerpVec2, lerpVec3, lerpColor
    -- * Bezier Curves
  , bezierPoint, bezierDerivative, solveBezierX, cubicBezierEasing
    -- * Color
  , colorFromHex6, normalizeHex, colorToHex
    -- * Easing Presets
  , easeLinear, easeIn, easeOut, easeInOut, easeOutBack
  , applyEasingPreset
    -- * Keyframe Search
  , findKeyframeIndex
  ) where

import Prelude
import Data.Enum (fromEnum, toEnum)
import Data.Array (length, (!!))
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Int (floor, round, toNumber) as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (drop, take)
import Data.String.CodeUnits (charAt, singleton, toCharArray)
import Global (isNaN, isFinite) as Global
import Math (abs, max, min) as Math

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 2D vector
newtype Vec2 = Vec2 { x :: Number, y :: Number }

derive instance Generic Vec2 _
derive newtype instance Eq Vec2
instance Show Vec2 where show = genericShow

-- | 3D vector
newtype Vec3 = Vec3 { x :: Number, y :: Number, z :: Number }

derive instance Generic Vec3 _
derive newtype instance Eq Vec3
instance Show Vec3 where show = genericShow

-- | RGB color with components 0-255
newtype Color = Color { r :: Number, g :: Number, b :: Number, a :: Number }

derive instance Generic Color _
derive newtype instance Eq Color
instance Show Color where show = genericShow

-- | Easing preset with normalized 0-1 control points
newtype EasingPreset = EasingPreset
  { outX :: Number, outY :: Number, inX :: Number, inY :: Number }

derive instance Generic EasingPreset _
derive newtype instance Eq EasingPreset
instance Show EasingPreset where show = genericShow

--------------------------------------------------------------------------------
-- Linear Interpolation
--------------------------------------------------------------------------------

-- | Linear interpolation between two numbers
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Safe linear interpolation (handles extreme values)
safeLerp :: Number -> Number -> Number -> Number
safeLerp a b t =
  let result = lerp a b t
  in if Global.isNaN result || not (Global.isFinite result)
     then if t < 0.5 then a else b
     else result

-- | Interpolate Vec2
lerpVec2 :: Vec2 -> Vec2 -> Number -> Vec2
lerpVec2 (Vec2 a) (Vec2 b) t = Vec2
  { x: safeLerp a.x b.x t
  , y: safeLerp a.y b.y t }

-- | Interpolate Vec3
lerpVec3 :: Vec3 -> Vec3 -> Number -> Vec3
lerpVec3 (Vec3 a) (Vec3 b) t = Vec3
  { x: safeLerp a.x b.x t
  , y: safeLerp a.y b.y t
  , z: safeLerp a.z b.z t }

-- | Interpolate between two colors
lerpColor :: Color -> Color -> Number -> Color
lerpColor (Color c1) (Color c2) t = Color
  { r: Int.toNumber (Int.round (safeLerp c1.r c2.r t))
  , g: Int.toNumber (Int.round (safeLerp c1.g c2.g t))
  , b: Int.toNumber (Int.round (safeLerp c1.b c2.b t))
  , a: Int.toNumber (Int.round (safeLerp c1.a c2.a t)) }

--------------------------------------------------------------------------------
-- Bezier Curve Math
--------------------------------------------------------------------------------

-- | Cubic bezier point calculation
bezierPoint :: Number -> Number -> Number -> Number -> Number -> Number
bezierPoint t p0 p1 p2 p3 =
  let mt = 1.0 - t
  in mt * mt * mt * p0 +
     3.0 * mt * mt * t * p1 +
     3.0 * mt * t * t * p2 +
     t * t * t * p3

-- | Cubic bezier derivative
bezierDerivative :: Number -> Number -> Number -> Number -> Number -> Number
bezierDerivative t p0 p1 p2 p3 =
  let mt = 1.0 - t
  in 3.0 * mt * mt * (p1 - p0) +
     6.0 * mt * t * (p2 - p1) +
     3.0 * t * t * (p3 - p2)

-- | Find t for given x using Newton-Raphson iteration
solveBezierX :: Number -> Number -> Number -> Int -> Number
solveBezierX x x1 x2 maxIter = go x maxIter
  where
    epsilon = 1e-6
    go :: Number -> Int -> Number
    go guessT 0 = guessT
    go guessT n =
      let currentX = bezierPoint guessT 0.0 x1 x2 1.0
          err = currentX - x
      in if Math.abs err < epsilon then guessT
         else
           let slope = bezierDerivative guessT 0.0 x1 x2 1.0
           in if Math.abs slope < epsilon then guessT
              else
                let newT = guessT - err / slope
                    clampedT = Math.max 0.0 (Math.min 1.0 newT)
                in go clampedT (n - 1)

-- | Cubic bezier easing
cubicBezierEasing :: Number -> Number -> Number -> Number -> Number -> Number
cubicBezierEasing t x1 y1 x2 y2 =
  let solvedT = solveBezierX t x1 x2 8
  in bezierPoint solvedT 0.0 y1 y2 1.0

--------------------------------------------------------------------------------
-- Color Parsing
--------------------------------------------------------------------------------

-- | Parse hex digit to number
hexDigitToInt :: Char -> Int
hexDigitToInt c
  | c >= '0' && c <= '9' = fromEnum c - fromEnum '0'
  | c >= 'a' && c <= 'f' = fromEnum c - fromEnum 'a' + 10
  | c >= 'A' && c <= 'F' = fromEnum c - fromEnum 'A' + 10
  | otherwise = 0

-- | Parse two hex chars to byte value
parseHexByte :: Char -> Char -> Number
parseHexByte h1 h2 =
  Int.toNumber (hexDigitToInt h1 * 16 + hexDigitToInt h2)

-- | Get char at index, returning '0' if out of bounds
charAtOr0 :: Int -> String -> Char
charAtOr0 i s = fromMaybe '0' (charAt i s)

-- | Create color from 6+ digit hex string (without #)
colorFromHex6 :: String -> Color
colorFromHex6 s
  | Array.length (toCharArray s) < 6 = Color { r: 0.0, g: 0.0, b: 0.0, a: 255.0 }
  | otherwise =
      let chars = toCharArray s
          r = parseHexByte (charAtOr0 0 s) (charAtOr0 1 s)
          g = parseHexByte (charAtOr0 2 s) (charAtOr0 3 s)
          b = parseHexByte (charAtOr0 4 s) (charAtOr0 5 s)
          a = if Array.length chars >= 8
              then parseHexByte (charAtOr0 6 s) (charAtOr0 7 s)
              else 255.0
      in Color { r, g, b, a }

-- | Expand 3/4 char hex to 6/8 char
expandShortHex :: String -> String
expandShortHex s =
  let chars = toCharArray s
  in case chars of
    [r, g, b] -> singleton r <> singleton r <> singleton g <> singleton g <> singleton b <> singleton b
    [r, g, b, a] -> singleton r <> singleton r <> singleton g <> singleton g <> singleton b <> singleton b <> singleton a <> singleton a
    _ -> s

-- | Normalize hex color string
normalizeHex :: String -> String
normalizeHex hex =
  let s = if take 1 hex == "#" then drop 1 hex else hex
      len = Array.length (toCharArray s)
  in if len == 3 || len == 4
     then expandShortHex s
     else s

-- | Convert int to 2-digit hex
toHex2 :: Int -> String
toHex2 n =
  let clamped = Math.max 0.0 (Math.min 255.0 (Int.toNumber n))
      i = Int.floor clamped
      hi = i `div` 16
      lo = i `mod` 16
      hexDigit d = if d < 10
                   then singleton (fromMaybe '0' (toEnum (fromEnum '0' + d)))
                   else singleton (fromMaybe 'a' (toEnum (fromEnum 'a' + d - 10)))
  in hexDigit hi <> hexDigit lo

-- | Convert color to hex string
colorToHex :: Color -> Boolean -> String
colorToHex (Color c) includeAlpha =
  let clamp' x = Int.round (Math.max 0.0 (Math.min 255.0 x))
      rgb = "#" <> toHex2 (clamp' c.r) <> toHex2 (clamp' c.g) <> toHex2 (clamp' c.b)
  in if includeAlpha
     then rgb <> toHex2 (clamp' c.a)
     else rgb

--------------------------------------------------------------------------------
-- Easing Presets
--------------------------------------------------------------------------------

-- | Linear easing
easeLinear :: EasingPreset
easeLinear = EasingPreset { outX: 0.33, outY: 0.33, inX: 0.33, inY: 0.33 }

-- | Ease in (slow start)
easeIn :: EasingPreset
easeIn = EasingPreset { outX: 0.42, outY: 0.0, inX: 0.33, inY: 0.33 }

-- | Ease out (slow end)
easeOut :: EasingPreset
easeOut = EasingPreset { outX: 0.33, outY: 0.33, inX: 0.58, inY: 1.0 }

-- | Ease in-out
easeInOut :: EasingPreset
easeInOut = EasingPreset { outX: 0.42, outY: 0.0, inX: 0.58, inY: 1.0 }

-- | Ease out with overshoot
easeOutBack :: EasingPreset
easeOutBack = EasingPreset { outX: 0.33, outY: 0.33, inX: 0.34, inY: 1.56 }

-- | Apply easing preset to a ratio (0-1)
-- | Uses cubicBezierEasing (Newton-Raphson x-solve) with handle values directly.
-- | The preset stores absolute control point positions, not offsets from endpoints.
applyEasingPreset :: Number -> EasingPreset -> Number
applyEasingPreset ratio (EasingPreset preset) =
  let t = Math.max 0.0 (Math.min 1.0 ratio)
  in cubicBezierEasing t preset.outX preset.outY preset.inX preset.inY

--------------------------------------------------------------------------------
-- Binary Search for Keyframes
--------------------------------------------------------------------------------

-- | Binary search to find index where arr[i] <= value < arr[i+1]
findKeyframeIndex :: Array Number -> Number -> Int
findKeyframeIndex frames frame
  | length frames < 2 = 0
  | otherwise = binarySearch 0 (length frames - 2)
  where
    binarySearch :: Int -> Int -> Int
    binarySearch low high
      | low > high = min low (length frames - 2)
      | otherwise =
          let mid = (low + high) `div` 2
              midFrame = fromMaybe 0.0 (frames !! mid)
              nextFrame = fromMaybe 0.0 (frames !! (mid + 1))
          in if frame >= midFrame && frame <= nextFrame
             then mid
             else if frame < midFrame
             then if mid == 0 then 0 else binarySearch low (mid - 1)
             else binarySearch (mid + 1) high
