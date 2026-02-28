-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // dimension // angular
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Angular units - measurements of rotation and direction.
-- |
-- | Used for:
-- | - Rotation in 2D/3D transforms
-- | - Camera field of view
-- | - Hue in color wheels (0-360)
-- | - Latitude/longitude
-- | - Circular gradients
-- |
-- | ## Base Unit
-- |
-- | The base unit is **Radians** (mathematically natural, used by trig functions).
-- | All other units convert through radians.
-- |
-- | ## Full Circle
-- |
-- | - 2π radians = 360 degrees = 1 turn = 400 gradians

module Hydrogen.Schema.Dimension.Angular
  ( -- * Core Types
    Radians(Radians)
  , Degrees(Degrees)
  , Turns(Turns)
  , Gradians(Gradians)
  
  -- * Type Class
  , class AngularUnit
  , toRadians
  , fromRadians
  
  -- * Constructors
  , radians
  , rad
  , degrees
  , deg
  , turns
  , turn
  , gradians
  , grad
  
  -- * Conversions
  , convertAngle
  
  -- * Operations
  , addRadians
  , subtractRadians
  , scaleRadians
  , negateRadians
  , absRadians
  
  -- * Normalization
  , normalizeRadians
  , normalizeDegrees
  
  -- * Common Angles
  , rightAngle
  , straightAngle
  , fullRotation
  , halfTurn
  , quarterTurn
  
  -- * Accessors
  , unwrapRadians
  , unwrapDegrees
  , unwrapTurns
  , unwrapGradians
  
  -- * Bounds (for normalized values)
  , radiansBounds
  , degreesBounds
  , turnsBounds
  , gradiansBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Ring
  , class Semiring
  , class Show
  , identity
  , negate
  , one
  , show
  , zero
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<>)
  , (<<<)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radians - natural unit for trigonometry
-- | Full circle = 2π radians ≈ 6.283185...
-- | Used directly by sin, cos, tan, etc.
newtype Radians = Radians Number

derive instance eqRadians :: Eq Radians
derive instance ordRadians :: Ord Radians

instance showRadians :: Show Radians where
  show (Radians n) = show n <> " rad"

instance semiringRadians :: Semiring Radians where
  add (Radians a) (Radians b) = Radians (a + b)
  zero = Radians 0.0
  mul (Radians a) (Radians b) = Radians (a * b)
  one = Radians 1.0

instance ringRadians :: Ring Radians where
  sub (Radians a) (Radians b) = Radians (a - b)

-- | Degrees - common unit for human-readable angles
-- | Full circle = 360 degrees
-- | Right angle = 90 degrees
newtype Degrees = Degrees Number

derive instance eqDegrees :: Eq Degrees
derive instance ordDegrees :: Ord Degrees

instance showDegrees :: Show Degrees where
  show (Degrees n) = show n <> "°"

instance semiringDegrees :: Semiring Degrees where
  add (Degrees a) (Degrees b) = Degrees (a + b)
  zero = Degrees 0.0
  mul (Degrees a) (Degrees b) = Degrees (a * b)
  one = Degrees 1.0

instance ringDegrees :: Ring Degrees where
  sub (Degrees a) (Degrees b) = Degrees (a - b)

-- | Turns - intuitive unit for rotations
-- | Full circle = 1 turn
-- | Half rotation = 0.5 turns
newtype Turns = Turns Number

derive instance eqTurns :: Eq Turns
derive instance ordTurns :: Ord Turns

instance showTurns :: Show Turns where
  show (Turns n) = show n <> " turn"

-- | Gradians (gon) - used in surveying
-- | Full circle = 400 gradians
-- | Right angle = 100 gradians
newtype Gradians = Gradians Number

derive instance eqGradians :: Eq Gradians
derive instance ordGradians :: Ord Gradians

instance showGradians :: Show Gradians where
  show (Gradians n) = show n <> " grad"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // type class
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type class for angular units
-- | All conversions go through Radians as the canonical representation
class AngularUnit a where
  toRadians :: a -> Radians
  fromRadians :: Radians -> a

instance angularUnitRadians :: AngularUnit Radians where
  toRadians = identity
  fromRadians = identity

-- 360 degrees = 2π radians
-- 1 degree = π/180 radians
instance angularUnitDegrees :: AngularUnit Degrees where
  toRadians (Degrees d) = Radians (d * Math.pi / 180.0)
  fromRadians (Radians r) = Degrees (r * 180.0 / Math.pi)

-- 1 turn = 2π radians
instance angularUnitTurns :: AngularUnit Turns where
  toRadians (Turns t) = Radians (t * Math.tau)
  fromRadians (Radians r) = Turns (r / Math.tau)

-- 400 gradians = 2π radians
-- 1 gradian = π/200 radians
instance angularUnitGradians :: AngularUnit Gradians where
  toRadians (Gradians g) = Radians (g * Math.pi / 200.0)
  fromRadians (Radians r) = Gradians (r * 200.0 / Math.pi)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Radians value
radians :: Number -> Radians
radians = Radians

-- | Alias for radians
rad :: Number -> Radians
rad = Radians

-- | Create a Degrees value
degrees :: Number -> Degrees
degrees = Degrees

-- | Alias for degrees
deg :: Number -> Degrees
deg = Degrees

-- | Create a Turns value
turns :: Number -> Turns
turns = Turns

-- | Alias for turns (singular)
turn :: Number -> Turns
turn = Turns

-- | Create a Gradians value
gradians :: Number -> Gradians
gradians = Gradians

-- | Alias for gradians
grad :: Number -> Gradians
grad = Gradians

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert between any two angular units
convertAngle :: forall a b. AngularUnit a => AngularUnit b => a -> b
convertAngle = fromRadians <<< toRadians

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two Radians values
addRadians :: Radians -> Radians -> Radians
addRadians (Radians a) (Radians b) = Radians (a + b)

-- | Subtract two Radians values
subtractRadians :: Radians -> Radians -> Radians
subtractRadians (Radians a) (Radians b) = Radians (a - b)

-- | Scale a Radians value by a dimensionless factor
scaleRadians :: Number -> Radians -> Radians
scaleRadians factor (Radians n) = Radians (n * factor)

-- | Negate a Radians value
negateRadians :: Radians -> Radians
negateRadians (Radians n) = Radians (negate n)

-- | Absolute value of Radians
absRadians :: Radians -> Radians
absRadians (Radians n) = Radians (Math.abs n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // normalization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalize radians to [0, 2π)
normalizeRadians :: Radians -> Radians
normalizeRadians (Radians r) =
  let modded = r - Math.floor (r / Math.tau) * Math.tau
  in Radians (if modded < 0.0 then modded + Math.tau else modded)

-- | Normalize degrees to [0, 360)
normalizeDegrees :: Degrees -> Degrees
normalizeDegrees (Degrees d) =
  let modded = d - Math.floor (d / 360.0) * 360.0
  in Degrees (if modded < 0.0 then modded + 360.0 else modded)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common angles
-- ═════════════════════════════════════════════════════════════════════════════

-- | 90 degrees (π/2 radians)
rightAngle :: Radians
rightAngle = Radians (Math.pi / 2.0)

-- | 180 degrees (π radians)
straightAngle :: Radians
straightAngle = Radians Math.pi

-- | 360 degrees (2π radians)
fullRotation :: Radians
fullRotation = Radians Math.tau

-- | 0.5 turns (180 degrees)
halfTurn :: Turns
halfTurn = Turns 0.5

-- | 0.25 turns (90 degrees)
quarterTurn :: Turns
quarterTurn = Turns 0.25

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number from Radians
unwrapRadians :: Radians -> Number
unwrapRadians (Radians n) = n

-- | Extract the raw Number from Degrees
unwrapDegrees :: Degrees -> Number
unwrapDegrees (Degrees n) = n

-- | Extract the raw Number from Turns
unwrapTurns :: Turns -> Number
unwrapTurns (Turns n) = n

-- | Extract the raw Number from Gradians
unwrapGradians :: Gradians -> Number
unwrapGradians (Gradians n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for normalized Radians [0, 2π)
radiansBounds :: Bounded.NumberBounds
radiansBounds = Bounded.numberBounds 0.0 Math.tau "radians" "Angle in radians (0 to 2π)"

-- | Bounds for normalized Degrees [0, 360)
degreesBounds :: Bounded.NumberBounds
degreesBounds = Bounded.numberBounds 0.0 360.0 "degrees" "Angle in degrees (0-360)"

-- | Bounds for normalized Turns [0, 1)
turnsBounds :: Bounded.NumberBounds
turnsBounds = Bounded.numberBounds 0.0 1.0 "turns" "Angle in turns (0-1)"

-- | Bounds for normalized Gradians [0, 400)
gradiansBounds :: Bounded.NumberBounds
gradiansBounds = Bounded.numberBounds 0.0 400.0 "gradians" "Angle in gradians (0-400)"
