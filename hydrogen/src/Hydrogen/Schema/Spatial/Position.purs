-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // spatial // position
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Position and Coordinate Atoms — 3D spatial positioning.
-- |
-- | ## Coordinate
-- | Single axis position value. No bounds (can be any finite number).
-- | Used as building block for Vec3, Position3D.
-- |
-- | ## Position3D
-- | Full 3D position composed of three coordinates.
-- | World space position in meters.

module Hydrogen.Schema.Spatial.Position
  ( -- * Coordinate
    Coordinate
  , coordinate
  , unwrapCoordinate
  
  -- * Position3D
  , Position3D(..)
  , position3D
  , origin
  , positionX
  , positionY
  , positionZ
  , distanceBetween
  , translatePosition
  , midpoint
  ) where

import Prelude

import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3(Vec3), vec3, addVec3, scaleVec3, lengthVec3, subtractVec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // coordinate
-- ═════════════════════════════════════════════════════════════════════════════

-- | Single axis coordinate value
-- |
-- | Unbounded (any finite number). Represents position on one axis.
-- | Building block for Position3D and Vec3.
newtype Coordinate = Coordinate Number

derive instance eqCoordinate :: Eq Coordinate
derive instance ordCoordinate :: Ord Coordinate

instance showCoordinate :: Show Coordinate where
  show (Coordinate c) = show c

-- | Create a coordinate
coordinate :: Number -> Coordinate
coordinate = Coordinate

-- | Extract coordinate value
unwrapCoordinate :: Coordinate -> Number
unwrapCoordinate (Coordinate c) = c

-- Semigroup: addition
instance semigroupCoordinate :: Semigroup Coordinate where
  append (Coordinate a) (Coordinate b) = Coordinate (a + b)

-- Monoid: zero
instance monoidCoordinate :: Monoid Coordinate where
  mempty = Coordinate 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // position3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D position in world space
-- |
-- | Composed of three coordinates (X, Y, Z).
-- | Units are meters by convention.
newtype Position3D = Position3D
  { x :: Coordinate
  , y :: Coordinate
  , z :: Coordinate
  }

derive instance eqPosition3D :: Eq Position3D
derive instance ordPosition3D :: Ord Position3D

instance showPosition3D :: Show Position3D where
  show (Position3D p) =
    "Position3D(" <> show p.x <> ", " <> show p.y <> ", " <> show p.z <> ")"

-- | Create a 3D position from numbers
position3D :: Number -> Number -> Number -> Position3D
position3D x y z = Position3D
  { x: Coordinate x
  , y: Coordinate y
  , z: Coordinate z
  }

-- | Origin point (0, 0, 0)
origin :: Position3D
origin = Position3D
  { x: Coordinate 0.0
  , y: Coordinate 0.0
  , z: Coordinate 0.0
  }

-- | Get X coordinate
positionX :: Position3D -> Number
positionX (Position3D p) = unwrapCoordinate p.x

-- | Get Y coordinate
positionY :: Position3D -> Number
positionY (Position3D p) = unwrapCoordinate p.y

-- | Get Z coordinate
positionZ :: Position3D -> Number
positionZ (Position3D p) = unwrapCoordinate p.z

-- | Convert to Vec3
toVec3 :: Position3D -> Vec3 Number
toVec3 (Position3D p) = vec3
  (unwrapCoordinate p.x)
  (unwrapCoordinate p.y)
  (unwrapCoordinate p.z)

-- | Convert from Vec3
fromVec3 :: Vec3 Number -> Position3D
fromVec3 (Vec3 x y z) = position3D x y z

-- | Distance between two positions (Euclidean)
distanceBetween :: Position3D -> Position3D -> Number
distanceBetween p1 p2 =
  let v1 = toVec3 p1
      v2 = toVec3 p2
      diff = subtractVec3 v2 v1
  in lengthVec3 diff

-- | Translate a position by an offset
translatePosition :: Vec3 Number -> Position3D -> Position3D
translatePosition offset pos =
  let v = toVec3 pos
      translated = addVec3 v offset
  in fromVec3 translated

-- | Midpoint between two positions
midpoint :: Position3D -> Position3D -> Position3D
midpoint p1 p2 =
  let v1 = toVec3 p1
      v2 = toVec3 p2
      sum = addVec3 v1 v2
      mid = scaleVec3 0.5 sum
  in fromVec3 mid
