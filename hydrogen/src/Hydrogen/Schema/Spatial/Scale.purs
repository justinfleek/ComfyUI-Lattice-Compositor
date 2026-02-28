-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // spatial // scale
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scale Atoms — 3D scaling factors.
-- |
-- | ## Scale
-- | Uniform scale factor. 0 = collapsed, 1 = identity, >1 = enlarged.
-- | Bounded to non-negative (can't have negative uniform scale).
-- |
-- | ## ScaleX, ScaleY, ScaleZ
-- | Per-axis scale factors. Can be negative (mirror/flip).
-- |
-- | ## Scale3D
-- | Complete 3D scale composed of three axis scales.

module Hydrogen.Schema.Spatial.Scale
  ( -- * Uniform Scale
    Scale
  , scale
  , unwrapScale
  , identityScale
  , halfScale
  , doubleScale
  
  -- * Axis Scales
  , ScaleX
  , scaleX
  , unwrapScaleX
  , ScaleY
  , scaleY
  , unwrapScaleY
  , ScaleZ
  , scaleZ
  , unwrapScaleZ
  
  -- * Scale3D
  , Scale3D(..)
  , scale3D
  , uniformScale3D
  , identityScale3D
  , flipX
  , flipY
  , flipZ
  , scaleVolume
  , multiplyScales
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // uniform scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Uniform scale factor (non-negative)
-- |
-- | 0 = collapsed to point, 1 = identity, 2 = double size.
-- | Clamped to >= 0 (negative uniform scale not allowed).
newtype Scale = Scale Number

derive instance eqScale :: Eq Scale
derive instance ordScale :: Ord Scale

instance showScale :: Show Scale where
  show (Scale s) = "Scale " <> show s

-- | Create a uniform scale (clamped to non-negative)
scale :: Number -> Scale
scale n = Scale (if n < 0.0 then 0.0 else n)

-- | Extract scale value
unwrapScale :: Scale -> Number
unwrapScale (Scale s) = s

-- | Identity scale (1.0)
identityScale :: Scale
identityScale = Scale 1.0

-- | Half scale (0.5)
halfScale :: Scale
halfScale = Scale 0.5

-- | Double scale (2.0)
doubleScale :: Scale
doubleScale = Scale 2.0

-- Semigroup: multiplication
instance semigroupScale :: Semigroup Scale where
  append (Scale a) (Scale b) = Scale (a * b)

-- Monoid: identity (1.0)
instance monoidScale :: Monoid Scale where
  mempty = Scale 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // axis scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | X-axis scale factor
-- |
-- | Can be negative (mirror along X axis).
newtype ScaleX = ScaleX Number

derive instance eqScaleX :: Eq ScaleX
derive instance ordScaleX :: Ord ScaleX

instance showScaleX :: Show ScaleX where
  show (ScaleX s) = "ScaleX " <> show s

-- | Create X-axis scale
scaleX :: Number -> ScaleX
scaleX = ScaleX

-- | Extract X scale value
unwrapScaleX :: ScaleX -> Number
unwrapScaleX (ScaleX s) = s

-- | Y-axis scale factor
-- |
-- | Can be negative (mirror along Y axis).
newtype ScaleY = ScaleY Number

derive instance eqScaleY :: Eq ScaleY
derive instance ordScaleY :: Ord ScaleY

instance showScaleY :: Show ScaleY where
  show (ScaleY s) = "ScaleY " <> show s

-- | Create Y-axis scale
scaleY :: Number -> ScaleY
scaleY = ScaleY

-- | Extract Y scale value
unwrapScaleY :: ScaleY -> Number
unwrapScaleY (ScaleY s) = s

-- | Z-axis scale factor
-- |
-- | Can be negative (mirror along Z axis).
newtype ScaleZ = ScaleZ Number

derive instance eqScaleZ :: Eq ScaleZ
derive instance ordScaleZ :: Ord ScaleZ

instance showScaleZ :: Show ScaleZ where
  show (ScaleZ s) = "ScaleZ " <> show s

-- | Create Z-axis scale
scaleZ :: Number -> ScaleZ
scaleZ = ScaleZ

-- | Extract Z scale value
unwrapScaleZ :: ScaleZ -> Number
unwrapScaleZ (ScaleZ s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // scale3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D scale with per-axis values
-- |
-- | Negative values mirror along that axis.
newtype Scale3D = Scale3D
  { x :: ScaleX
  , y :: ScaleY
  , z :: ScaleZ
  }

derive instance eqScale3D :: Eq Scale3D
derive instance ordScale3D :: Ord Scale3D

instance showScale3D :: Show Scale3D where
  show (Scale3D s) =
    "Scale3D(" <> show s.x <> ", " <> show s.y <> ", " <> show s.z <> ")"

-- | Create a 3D scale from numbers
scale3D :: Number -> Number -> Number -> Scale3D
scale3D x y z = Scale3D
  { x: ScaleX x
  , y: ScaleY y
  , z: ScaleZ z
  }

-- | Create uniform 3D scale
uniformScale3D :: Number -> Scale3D
uniformScale3D s = scale3D s s s

-- | Identity scale (1, 1, 1)
identityScale3D :: Scale3D
identityScale3D = scale3D 1.0 1.0 1.0

-- | Flip along X axis
flipX :: Scale3D
flipX = scale3D (-1.0) 1.0 1.0

-- | Flip along Y axis
flipY :: Scale3D
flipY = scale3D 1.0 (-1.0) 1.0

-- | Flip along Z axis
flipZ :: Scale3D
flipZ = scale3D 1.0 1.0 (-1.0)

-- | Compute volume scale factor (product of all axes)
scaleVolume :: Scale3D -> Number
scaleVolume (Scale3D s) =
  let x = unwrapScaleX s.x
      y = unwrapScaleY s.y
      z = unwrapScaleZ s.z
  in abs (x * y * z)
  where
  abs :: Number -> Number
  abs n = if n < 0.0 then -n else n

-- | Multiply two 3D scales (component-wise)
multiplyScales :: Scale3D -> Scale3D -> Scale3D
multiplyScales (Scale3D a) (Scale3D b) = Scale3D
  { x: ScaleX (unwrapScaleX a.x * unwrapScaleX b.x)
  , y: ScaleY (unwrapScaleY a.y * unwrapScaleY b.y)
  , z: ScaleZ (unwrapScaleZ a.z * unwrapScaleZ b.z)
  }

-- Semigroup: component-wise multiplication
instance semigroupScale3D :: Semigroup Scale3D where
  append = multiplyScales

-- Monoid: identity scale
instance monoidScale3D :: Monoid Scale3D where
  mempty = identityScale3D
