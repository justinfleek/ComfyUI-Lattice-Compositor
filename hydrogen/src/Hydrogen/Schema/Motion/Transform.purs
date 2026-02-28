-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // motion // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layer transforms for motion graphics.
-- |
-- | Defines the complete transform system for animatable layers:
-- | - Position (2D and 3D)
-- | - Rotation (single axis or Euler XYZ)
-- | - Scale (uniform or per-axis)
-- | - Anchor Point (transform origin)
-- | - Opacity (visibility)
-- |
-- | ## Architecture
-- |
-- | This module mirrors `Lattice.Entities.LayerTransform` from the Lattice
-- | Haskell backend. All values use bounded primitives to ensure deterministic
-- | behavior at billion-agent scale.
-- |
-- | ## 2D vs 3D
-- |
-- | - `LayerTransform2D`: Standard 2D composition (After Effects style)
-- | - `LayerTransform3D`: Full 3D with separate X/Y/Z rotation, orientation

module Hydrogen.Schema.Motion.Transform
  ( -- * Layer Transform 2D
    LayerTransform2D(..)
  , defaultTransform2D
  , identityTransform2D
  , transform2DPosition
  , transform2DRotation
  , transform2DScale
  , transform2DAnchor
  , transform2DOpacity
  
  -- * Layer Transform 3D
  , LayerTransform3D(..)
  , defaultTransform3D
  , identityTransform3D
  , transform3DPosition
  , transform3DRotation
  , transform3DOrientation
  , transform3DScale
  , transform3DAnchor
  , transform3DOpacity
  
  -- * Position Types
  , Position2D(..)
  , Position3D(..)
  , mkPosition2D
  , mkPosition3D
  , positionZero2D
  , positionZero3D
  
  -- * Scale Types
  , Scale2D(..)
  , Scale3D(..)
  , mkScale2D
  , mkScale3D
  , scaleIdentity2D
  , scaleIdentity3D
  , scaleUniform2D
  , scaleUniform3D
  
  -- * Rotation Types
  , Rotation(..)
  , Rotation3D(..)
  , Orientation(..)
  , mkRotation
  , mkRotation3D
  , mkOrientation
  , rotationZero
  , rotation3DZero
  , orientationZero
  
  -- * Anchor Point
  , AnchorPoint2D(..)
  , AnchorPoint3D(..)
  , mkAnchorPoint2D
  , mkAnchorPoint3D
  , anchorCenter2D
  , anchorCenter3D
  , anchorTopLeft2D
  
  -- * Opacity
  , Opacity(..)
  , mkOpacity
  , opacityFull
  , opacityHalf
  , opacityZero
  , getOpacityValue
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (<>)
  , (*)
  , (/)
  )

import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // position
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D position in layer coordinate space.
-- |
-- | Values are finite floats (no Infinity, no NaN).
-- | Position is relative to composition origin (typically top-left).
newtype Position2D = Position2D { x :: Number, y :: Number }

derive instance eqPosition2D :: Eq Position2D
derive instance ordPosition2D :: Ord Position2D

instance showPosition2D :: Show Position2D where
  show (Position2D p) = "Position2D(" <> show p.x <> ", " <> show p.y <> ")"

-- | 3D position in layer coordinate space.
-- |
-- | Z axis extends "into" the screen (positive Z = further away).
newtype Position3D = Position3D { x :: Number, y :: Number, z :: Number }

derive instance eqPosition3D :: Eq Position3D
derive instance ordPosition3D :: Ord Position3D

instance showPosition3D :: Show Position3D where
  show (Position3D p) = 
    "Position3D(" <> show p.x <> ", " <> show p.y <> ", " <> show p.z <> ")"

-- | Create 2D position
mkPosition2D :: Number -> Number -> Position2D
mkPosition2D x y = Position2D { x, y }

-- | Create 3D position
mkPosition3D :: Number -> Number -> Number -> Position3D
mkPosition3D x y z = Position3D { x, y, z }

-- | Zero position (origin)
positionZero2D :: Position2D
positionZero2D = Position2D { x: 0.0, y: 0.0 }

-- | Zero position (origin) in 3D
positionZero3D :: Position3D
positionZero3D = Position3D { x: 0.0, y: 0.0, z: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D scale (percentage-based).
-- |
-- | 100.0 = normal size, 200.0 = double, 50.0 = half.
-- | Values are clamped to -10000.0 to 10000.0 (reasonable extremes).
-- | Negative values create flip/mirror effects.
newtype Scale2D = Scale2D { x :: Number, y :: Number }

derive instance eqScale2D :: Eq Scale2D
derive instance ordScale2D :: Ord Scale2D

instance showScale2D :: Show Scale2D where
  show (Scale2D s) = "Scale2D(" <> show s.x <> "%, " <> show s.y <> "%)"

-- | 3D scale (percentage-based).
newtype Scale3D = Scale3D { x :: Number, y :: Number, z :: Number }

derive instance eqScale3D :: Eq Scale3D
derive instance ordScale3D :: Ord Scale3D

instance showScale3D :: Show Scale3D where
  show (Scale3D s) = 
    "Scale3D(" <> show s.x <> "%, " <> show s.y <> "%, " <> show s.z <> "%)"

-- | Clamp scale value to reasonable bounds
clampScale :: Number -> Number
clampScale = clampNumber (-10000.0) 10000.0

-- | Create 2D scale
mkScale2D :: Number -> Number -> Scale2D
mkScale2D x y = Scale2D { x: clampScale x, y: clampScale y }

-- | Create 3D scale
mkScale3D :: Number -> Number -> Number -> Scale3D
mkScale3D x y z = Scale3D { x: clampScale x, y: clampScale y, z: clampScale z }

-- | Identity scale (100%)
scaleIdentity2D :: Scale2D
scaleIdentity2D = Scale2D { x: 100.0, y: 100.0 }

-- | Identity scale (100%) in 3D
scaleIdentity3D :: Scale3D
scaleIdentity3D = Scale3D { x: 100.0, y: 100.0, z: 100.0 }

-- | Uniform 2D scale
scaleUniform2D :: Number -> Scale2D
scaleUniform2D s = 
  let clamped = clampScale s
  in Scale2D { x: clamped, y: clamped }

-- | Uniform 3D scale
scaleUniform3D :: Number -> Scale3D
scaleUniform3D s = 
  let clamped = clampScale s
  in Scale3D { x: clamped, y: clamped, z: clamped }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // rotation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Single-axis rotation in degrees.
-- |
-- | Used for 2D transforms. Positive = clockwise.
-- | Values are NOT clamped (can exceed 360 for multiple rotations).
newtype Rotation = Rotation { degrees :: Number }

derive instance eqRotation :: Eq Rotation
derive instance ordRotation :: Ord Rotation

instance showRotation :: Show Rotation where
  show (Rotation r) = "Rotation(" <> show r.degrees <> "°)"

-- | 3D rotation (Euler angles in degrees).
-- |
-- | Rotation order is typically X, then Y, then Z (After Effects convention).
newtype Rotation3D = Rotation3D { x :: Number, y :: Number, z :: Number }

derive instance eqRotation3D :: Eq Rotation3D
derive instance ordRotation3D :: Ord Rotation3D

instance showRotation3D :: Show Rotation3D where
  show (Rotation3D r) = 
    "Rotation3D(" <> show r.x <> "°, " <> show r.y <> "°, " <> show r.z <> "°)"

-- | 3D orientation (separate from rotation, used in camera/3D layers).
-- |
-- | Unlike rotation, orientation typically doesn't accumulate past 360.
newtype Orientation = Orientation { x :: Number, y :: Number, z :: Number }

derive instance eqOrientation :: Eq Orientation
derive instance ordOrientation :: Ord Orientation

instance showOrientation :: Show Orientation where
  show (Orientation o) = 
    "Orientation(" <> show o.x <> "°, " <> show o.y <> "°, " <> show o.z <> "°)"

-- | Create rotation
mkRotation :: Number -> Rotation
mkRotation degrees = Rotation { degrees }

-- | Create 3D rotation
mkRotation3D :: Number -> Number -> Number -> Rotation3D
mkRotation3D x y z = Rotation3D { x, y, z }

-- | Create orientation
mkOrientation :: Number -> Number -> Number -> Orientation
mkOrientation x y z = Orientation { x, y, z }

-- | Zero rotation
rotationZero :: Rotation
rotationZero = Rotation { degrees: 0.0 }

-- | Zero 3D rotation
rotation3DZero :: Rotation3D
rotation3DZero = Rotation3D { x: 0.0, y: 0.0, z: 0.0 }

-- | Zero orientation
orientationZero :: Orientation
orientationZero = Orientation { x: 0.0, y: 0.0, z: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // anchor // point
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D anchor point (transform origin).
-- |
-- | Position within the layer where transforms are applied from.
-- | (0, 0) = top-left corner of layer bounds.
newtype AnchorPoint2D = AnchorPoint2D { x :: Number, y :: Number }

derive instance eqAnchorPoint2D :: Eq AnchorPoint2D
derive instance ordAnchorPoint2D :: Ord AnchorPoint2D

instance showAnchorPoint2D :: Show AnchorPoint2D where
  show (AnchorPoint2D a) = "Anchor2D(" <> show a.x <> ", " <> show a.y <> ")"

-- | 3D anchor point (transform origin).
newtype AnchorPoint3D = AnchorPoint3D { x :: Number, y :: Number, z :: Number }

derive instance eqAnchorPoint3D :: Eq AnchorPoint3D
derive instance ordAnchorPoint3D :: Ord AnchorPoint3D

instance showAnchorPoint3D :: Show AnchorPoint3D where
  show (AnchorPoint3D a) = 
    "Anchor3D(" <> show a.x <> ", " <> show a.y <> ", " <> show a.z <> ")"

-- | Create 2D anchor point
mkAnchorPoint2D :: Number -> Number -> AnchorPoint2D
mkAnchorPoint2D x y = AnchorPoint2D { x, y }

-- | Create 3D anchor point
mkAnchorPoint3D :: Number -> Number -> Number -> AnchorPoint3D
mkAnchorPoint3D x y z = AnchorPoint3D { x, y, z }

-- | Centered anchor (typical default for motion graphics)
anchorCenter2D :: Number -> Number -> AnchorPoint2D
anchorCenter2D width height = AnchorPoint2D { x: width / 2.0, y: height / 2.0 }

-- | Centered anchor in 3D
anchorCenter3D :: Number -> Number -> Number -> AnchorPoint3D
anchorCenter3D width height depth = 
  AnchorPoint3D { x: width / 2.0, y: height / 2.0, z: depth / 2.0 }

-- | Top-left anchor (web convention)
anchorTopLeft2D :: AnchorPoint2D
anchorTopLeft2D = AnchorPoint2D { x: 0.0, y: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // opacity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layer opacity (0.0 to 1.0).
-- |
-- | Clamped to valid range. Used for layer visibility and blending.
newtype Opacity = Opacity Number

derive instance eqOpacity :: Eq Opacity
derive instance ordOpacity :: Ord Opacity

instance showOpacity :: Show Opacity where
  show (Opacity o) = "Opacity(" <> show (o * 100.0) <> "%)"

-- | Create opacity (clamped to 0.0-1.0)
mkOpacity :: Number -> Opacity
mkOpacity n = Opacity (clampNumber 0.0 1.0 n)

-- | Full opacity (100%)
opacityFull :: Opacity
opacityFull = Opacity 1.0

-- | Half opacity (50%)
opacityHalf :: Opacity
opacityHalf = Opacity 0.5

-- | Zero opacity (invisible)
opacityZero :: Opacity
opacityZero = Opacity 0.0

-- | Get underlying opacity value
getOpacityValue :: Opacity -> Number
getOpacityValue (Opacity o) = o

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // layer // transform // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 2D layer transform.
-- |
-- | Mirrors `Lattice.Entities.LayerTransform` from the Haskell backend.
-- | Contains all animatable transform properties for a 2D layer.
newtype LayerTransform2D = LayerTransform2D
  { position :: Position2D
  , rotation :: Rotation
  , scale :: Scale2D
  , anchor :: AnchorPoint2D
  , opacity :: Opacity
  }

derive instance eqLayerTransform2D :: Eq LayerTransform2D

instance showLayerTransform2D :: Show LayerTransform2D where
  show (LayerTransform2D t) = 
    "Transform2D { pos: " <> show t.position <> 
    ", rot: " <> show t.rotation <>
    ", scale: " <> show t.scale <>
    ", anchor: " <> show t.anchor <>
    ", opacity: " <> show t.opacity <> " }"

-- | Default 2D transform (centered at origin, no transformation)
defaultTransform2D :: LayerTransform2D
defaultTransform2D = LayerTransform2D
  { position: positionZero2D
  , rotation: rotationZero
  , scale: scaleIdentity2D
  , anchor: anchorTopLeft2D
  , opacity: opacityFull
  }

-- | Identity transform (no change)
identityTransform2D :: LayerTransform2D
identityTransform2D = defaultTransform2D

-- | Get position from 2D transform
transform2DPosition :: LayerTransform2D -> Position2D
transform2DPosition (LayerTransform2D t) = t.position

-- | Get rotation from 2D transform
transform2DRotation :: LayerTransform2D -> Rotation
transform2DRotation (LayerTransform2D t) = t.rotation

-- | Get scale from 2D transform
transform2DScale :: LayerTransform2D -> Scale2D
transform2DScale (LayerTransform2D t) = t.scale

-- | Get anchor point from 2D transform
transform2DAnchor :: LayerTransform2D -> AnchorPoint2D
transform2DAnchor (LayerTransform2D t) = t.anchor

-- | Get opacity from 2D transform
transform2DOpacity :: LayerTransform2D -> Opacity
transform2DOpacity (LayerTransform2D t) = t.opacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // layer // transform // 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 3D layer transform.
-- |
-- | Used for 3D layers, cameras, and lights. Includes both rotation
-- | (animatable Euler angles) and orientation (fixed direction).
newtype LayerTransform3D = LayerTransform3D
  { position :: Position3D
  , rotation :: Rotation3D
  , orientation :: Orientation
  , scale :: Scale3D
  , anchor :: AnchorPoint3D
  , opacity :: Opacity
  }

derive instance eqLayerTransform3D :: Eq LayerTransform3D

instance showLayerTransform3D :: Show LayerTransform3D where
  show (LayerTransform3D t) = 
    "Transform3D { pos: " <> show t.position <> 
    ", rot: " <> show t.rotation <>
    ", orient: " <> show t.orientation <>
    ", scale: " <> show t.scale <>
    ", anchor: " <> show t.anchor <>
    ", opacity: " <> show t.opacity <> " }"

-- | Default 3D transform
defaultTransform3D :: LayerTransform3D
defaultTransform3D = LayerTransform3D
  { position: positionZero3D
  , rotation: rotation3DZero
  , orientation: orientationZero
  , scale: scaleIdentity3D
  , anchor: AnchorPoint3D { x: 0.0, y: 0.0, z: 0.0 }
  , opacity: opacityFull
  }

-- | Identity 3D transform
identityTransform3D :: LayerTransform3D
identityTransform3D = defaultTransform3D

-- | Get position from 3D transform
transform3DPosition :: LayerTransform3D -> Position3D
transform3DPosition (LayerTransform3D t) = t.position

-- | Get rotation from 3D transform
transform3DRotation :: LayerTransform3D -> Rotation3D
transform3DRotation (LayerTransform3D t) = t.rotation

-- | Get orientation from 3D transform
transform3DOrientation :: LayerTransform3D -> Orientation
transform3DOrientation (LayerTransform3D t) = t.orientation

-- | Get scale from 3D transform
transform3DScale :: LayerTransform3D -> Scale3D
transform3DScale (LayerTransform3D t) = t.scale

-- | Get anchor point from 3D transform
transform3DAnchor :: LayerTransform3D -> AnchorPoint3D
transform3DAnchor (LayerTransform3D t) = t.anchor

-- | Get opacity from 3D transform
transform3DOpacity :: LayerTransform3D -> Opacity
transform3DOpacity (LayerTransform3D t) = t.opacity
