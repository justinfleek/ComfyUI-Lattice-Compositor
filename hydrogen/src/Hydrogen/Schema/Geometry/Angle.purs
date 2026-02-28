-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // geometry // angle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Angle — Angular measurement atoms with proper wrapping behavior.
-- |
-- | ## Design Philosophy
-- |
-- | Angles are **cyclic** values. 720 degrees is the same as 0 degrees.
-- | This module enforces that invariant through smart constructors that
-- | normalize values on construction.
-- |
-- | Three representations are provided:
-- | - **Degrees**: 0-360, most human-readable
-- | - **Radians**: 0-2π, mathematically natural
-- | - **Turns**: 0-1, useful for interpolation
-- |
-- | All representations are equivalent and freely convertible.
-- |
-- | ## Wrapping Behavior
-- |
-- | ```purescript
-- | degrees 720.0 == degrees 0.0    -- wraps
-- | degrees (-90.0) == degrees 270.0 -- negative wraps forward
-- | radians (4.0 * pi) == radians 0.0
-- | turns 1.5 == turns 0.5
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Semiring, Ring)
-- |
-- | ## Dependents
-- |
-- | - Schema.Geometry.Transform (rotation)
-- | - Schema.Geometry.Shape (polygon rotation, spiral)
-- | - Schema.Motion.Easing (angular interpolation)
-- | - Component.ColorPicker (hue wheel)
-- | - Component.Dial (rotary input)

module Hydrogen.Schema.Geometry.Angle
  ( -- * Core Types
    Degrees(Degrees)
  , Radians(Radians)
  , Turns(Turns)
  
  -- * Type Class
  , class AngularUnit
  , toDegrees
  , fromDegrees
  , toRadians
  , fromRadians
  , toTurns
  , fromTurns
  
  -- * Constructors (with normalization)
  , degrees
  , radians
  , turns
  , deg
  , rad
  
  -- * Unwrappers (raw value access)
  , unwrapDegrees
  , unwrapRadians
  , unwrapTurns
  
  -- * Common Angles
  , zero
  , quarter
  , half
  , threeQuarters
  , full
  , right
  , straight
  
  -- * Operations
  , addAngle
  , subtractAngle
  , negateAngle
  , multiplyAngle
  , divideAngle
  , complementary
  , supplementary
  , reflex
  
  -- * Interpolation
  , lerpAngle
  , shortestPath
  
  -- * Trigonometry
  , sinAngle
  , cosAngle
  , tanAngle
  , asinAngle
  , acosAngle
  , atanAngle
  , atan2Angle
  
  -- * Comparison
  , isAcute
  , isRight
  , isObtuse
  , isStraight
  , isReflex
  
  -- * Conversion
  , toLegacyCss
  , toRotateCss
  
  -- * Bounds
  , degreesBounds
  , radiansBounds
  , turnsBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semiring
  , class Ring
  , show
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (<)
  , (>)
  , (>=)
  , (&&)
  )

import Data.Number (pi, sin, cos, tan, asin, acos, atan, atan2, floor)

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Angle in degrees.
-- | Normalized to [0, 360) on construction.
newtype Degrees = Degrees Number

derive instance eqDegrees :: Eq Degrees
derive instance ordDegrees :: Ord Degrees

instance showDegrees :: Show Degrees where
  show (Degrees d) = show d <> "deg"

instance semiringDegrees :: Semiring Degrees where
  add (Degrees a) (Degrees b) = degrees (a + b)
  mul (Degrees a) (Degrees b) = degrees (a * b)
  zero = Degrees 0.0
  one = Degrees 1.0

instance ringDegrees :: Ring Degrees where
  sub (Degrees a) (Degrees b) = degrees (a - b)

-- | Angle in radians.
-- | Normalized to [0, 2π) on construction.
newtype Radians = Radians Number

derive instance eqRadians :: Eq Radians
derive instance ordRadians :: Ord Radians

instance showRadians :: Show Radians where
  show (Radians r) = show r <> "rad"

instance semiringRadians :: Semiring Radians where
  add (Radians a) (Radians b) = radians (a + b)
  mul (Radians a) (Radians b) = radians (a * b)
  zero = Radians 0.0
  one = Radians 1.0

instance ringRadians :: Ring Radians where
  sub (Radians a) (Radians b) = radians (a - b)

-- | Angle in turns (full rotations).
-- | Normalized to [0, 1) on construction.
-- | 1 turn = 360 degrees = 2π radians
newtype Turns = Turns Number

derive instance eqTurns :: Eq Turns
derive instance ordTurns :: Ord Turns

instance showTurns :: Show Turns where
  show (Turns t) = show t <> "turn"

instance semiringTurns :: Semiring Turns where
  add (Turns a) (Turns b) = turns (a + b)
  mul (Turns a) (Turns b) = turns (a * b)
  zero = Turns 0.0
  one = Turns 1.0

instance ringTurns :: Ring Turns where
  sub (Turns a) (Turns b) = turns (a - b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // type class
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type class for angular units.
-- | Enables generic angle operations across representations.
class AngularUnit a where
  toDegrees :: a -> Degrees
  fromDegrees :: Degrees -> a
  toRadians :: a -> Radians
  fromRadians :: Radians -> a
  toTurns :: a -> Turns
  fromTurns :: Turns -> a

instance angularUnitDegrees :: AngularUnit Degrees where
  toDegrees = identity
  fromDegrees = identity
  toRadians (Degrees d) = radians (d * pi / 180.0)
  fromRadians (Radians r) = degrees (r * 180.0 / pi)
  toTurns (Degrees d) = turns (d / 360.0)
  fromTurns (Turns t) = degrees (t * 360.0)

instance angularUnitRadians :: AngularUnit Radians where
  toDegrees (Radians r) = degrees (r * 180.0 / pi)
  fromDegrees (Degrees d) = radians (d * pi / 180.0)
  toRadians = identity
  fromRadians = identity
  toTurns (Radians r) = turns (r / (2.0 * pi))
  fromTurns (Turns t) = radians (t * 2.0 * pi)

instance angularUnitTurns :: AngularUnit Turns where
  toDegrees (Turns t) = degrees (t * 360.0)
  fromDegrees (Degrees d) = turns (d / 360.0)
  toRadians (Turns t) = radians (t * 2.0 * pi)
  fromRadians (Radians r) = turns (r / (2.0 * pi))
  toTurns = identity
  fromTurns = identity

-- | Identity function for type class instances
identity :: forall a. a -> a
identity x = x

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create angle in degrees with normalization to [0, 360).
-- |
-- | Handles negative values and values > 360:
-- | ```purescript
-- | degrees 720.0 == Degrees 0.0
-- | degrees (-90.0) == Degrees 270.0
-- | degrees 45.0 == Degrees 45.0
-- | ```
degrees :: Number -> Degrees
degrees n = Degrees (normalizeRange n 360.0)

-- | Alias for degrees
deg :: Number -> Degrees
deg = degrees

-- | Create angle in radians with normalization to [0, 2π).
radians :: Number -> Radians
radians n = Radians (normalizeRange n (2.0 * pi))

-- | Alias for radians
rad :: Number -> Radians
rad = radians

-- | Create angle in turns with normalization to [0, 1).
turns :: Number -> Turns
turns n = Turns (normalizeRange n 1.0)

-- | Normalize a value to [0, range).
-- | Handles negative values correctly.
normalizeRange :: Number -> Number -> Number
normalizeRange n range =
  let
    -- Use modulo that handles negatives correctly
    modded = n - range * floor (n / range)
  in
    -- Handle edge case where modded == range due to floating point
    if modded >= range then 0.0 else modded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // unwrappers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get raw degrees value
unwrapDegrees :: Degrees -> Number
unwrapDegrees (Degrees d) = d

-- | Get raw radians value
unwrapRadians :: Radians -> Number
unwrapRadians (Radians r) = r

-- | Get raw turns value
unwrapTurns :: Turns -> Number
unwrapTurns (Turns t) = t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common angles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zero angle (0 degrees)
zero :: Degrees
zero = Degrees 0.0

-- | Quarter turn (90 degrees)
quarter :: Degrees
quarter = Degrees 90.0

-- | Half turn (180 degrees)
half :: Degrees
half = Degrees 180.0

-- | Three-quarter turn (270 degrees)
threeQuarters :: Degrees
threeQuarters = Degrees 270.0

-- | Full turn (360 degrees = 0 degrees after normalization)
full :: Degrees
full = Degrees 0.0

-- | Right angle (90 degrees)
right :: Degrees
right = quarter

-- | Straight angle (180 degrees)
straight :: Degrees
straight = half

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two angles (result is normalized)
addAngle :: Degrees -> Degrees -> Degrees
addAngle (Degrees a) (Degrees b) = degrees (a + b)

-- | Subtract angles (result is normalized)
subtractAngle :: Degrees -> Degrees -> Degrees
subtractAngle (Degrees a) (Degrees b) = degrees (a - b)

-- | Negate angle (reflect across 0)
negateAngle :: Degrees -> Degrees
negateAngle (Degrees d) = degrees (negate d)

-- | Multiply angle by scalar
multiplyAngle :: Number -> Degrees -> Degrees
multiplyAngle n (Degrees d) = degrees (n * d)

-- | Divide angle by scalar
divideAngle :: Degrees -> Number -> Degrees
divideAngle (Degrees d) n = degrees (d / n)

-- | Complementary angle (90 - angle)
-- | Only meaningful for angles < 90
complementary :: Degrees -> Degrees
complementary (Degrees d) = degrees (90.0 - d)

-- | Supplementary angle (180 - angle)
-- | Only meaningful for angles < 180
supplementary :: Degrees -> Degrees
supplementary (Degrees d) = degrees (180.0 - d)

-- | Reflex angle (360 - angle)
reflex :: Degrees -> Degrees
reflex (Degrees d) = degrees (360.0 - d)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two angles.
-- |
-- | `t` is clamped to [0, 1]:
-- | - t = 0 returns `from`
-- | - t = 1 returns `to`
-- |
-- | Takes the direct path, not necessarily the shortest arc.
lerpAngle :: Number -> Degrees -> Degrees -> Degrees
lerpAngle t (Degrees from) (Degrees to) =
  let
    t' = clamp01 t
  in
    degrees (from + (to - from) * t')

-- | Find the shortest angular path between two angles.
-- |
-- | Returns a value in (-180, 180] representing the smallest
-- | rotation needed to get from `from` to `to`.
-- |
-- | ```purescript
-- | shortestPath (degrees 10.0) (degrees 350.0) == Degrees (-20.0)
-- | shortestPath (degrees 350.0) (degrees 10.0) == Degrees 20.0
-- | ```
shortestPath :: Degrees -> Degrees -> Degrees
shortestPath (Degrees from) (Degrees to) =
  let
    diff = to - from
    normalized = normalizeRange diff 360.0
  in
    if normalized > 180.0
      then Degrees (normalized - 360.0)
      else Degrees normalized

-- | Clamp value to [0, 1]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | true = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // trigonometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sine of angle
sinAngle :: Degrees -> Number
sinAngle d = sin (unwrapRadians (toRadians d))

-- | Cosine of angle
cosAngle :: Degrees -> Number
cosAngle d = cos (unwrapRadians (toRadians d))

-- | Tangent of angle
tanAngle :: Degrees -> Number
tanAngle d = tan (unwrapRadians (toRadians d))

-- | Arcsine (returns angle in degrees)
asinAngle :: Number -> Degrees
asinAngle n = fromRadians (Radians (asin n))

-- | Arccosine (returns angle in degrees)
acosAngle :: Number -> Degrees
acosAngle n = fromRadians (Radians (acos n))

-- | Arctangent (returns angle in degrees)
atanAngle :: Number -> Degrees
atanAngle n = fromRadians (Radians (atan n))

-- | Two-argument arctangent (returns angle in degrees)
-- | atan2(y, x) gives the angle from the positive X axis to point (x, y)
atan2Angle :: Number -> Number -> Degrees
atan2Angle y x = fromRadians (Radians (atan2 y x))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is angle acute (< 90 degrees)?
isAcute :: Degrees -> Boolean
isAcute (Degrees d) = d > 0.0 && d < 90.0

-- | Is angle a right angle (exactly 90 degrees)?
isRight :: Degrees -> Boolean
isRight (Degrees d) = d == 90.0

-- | Is angle obtuse (90 < angle < 180)?
isObtuse :: Degrees -> Boolean
isObtuse (Degrees d) = d > 90.0 && d < 180.0

-- | Is angle straight (exactly 180 degrees)?
isStraight :: Degrees -> Boolean
isStraight (Degrees d) = d == 180.0

-- | Is angle reflex (> 180 degrees)?
isReflex :: Degrees -> Boolean
isReflex (Degrees d) = d > 180.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert angle to legacy CSS string.
-- |
-- | Returns degrees format for maximum compatibility.
toLegacyCss :: Degrees -> String
toLegacyCss (Degrees d) = show d <> "deg"

-- | Convert angle to CSS rotate() transform value.
-- |
-- | ```purescript
-- | toRotateCss (degrees 45.0) == "rotate(45deg)"
-- | ```
toRotateCss :: Degrees -> String
toRotateCss d = "rotate(" <> toLegacyCss d <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Degrees (cyclic: values normalize to this range)
-- |
-- | Min: 0.0
-- | Max: 360.0 (exclusive, wraps to 0)
degreesBounds :: Bounded.NumberBounds
degreesBounds = Bounded.numberBounds 0.0 360.0 "degrees" "Angle in degrees (0-360, cyclic)"

-- | Bounds for Radians (cyclic: values normalize to this range)
-- |
-- | Min: 0.0
-- | Max: 2π (exclusive, wraps to 0)
radiansBounds :: Bounded.NumberBounds
radiansBounds = Bounded.numberBounds 0.0 (2.0 * pi) "radians" "Angle in radians (0-2π, cyclic)"

-- | Bounds for Turns (cyclic: values normalize to this range)
-- |
-- | Min: 0.0
-- | Max: 1.0 (exclusive, wraps to 0)
turnsBounds :: Bounded.NumberBounds
turnsBounds = Bounded.numberBounds 0.0 1.0 "turns" "Angle in turns (0-1, cyclic)"
