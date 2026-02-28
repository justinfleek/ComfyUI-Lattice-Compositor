-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // geometry // transform3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform3D — 3D transformation primitives for spatial UI.
-- |
-- | ## Design Philosophy
-- |
-- | 3D transforms enable:
-- | - Perspective effects (card flips, cube rotations)
-- | - Depth-based UI (layered interfaces, z-ordering)
-- | - Camera-relative positioning (looking at targets)
-- | - Spatial animation (orbiting, zooming, dollying)
-- |
-- | All transforms use the right-handed coordinate system:
-- | - X: positive to the right
-- | - Y: positive upward
-- | - Z: positive toward the viewer
-- |
-- | ## CSS Transform Order
-- |
-- | CSS applies transforms right-to-left in the string, but conceptually:
-- | translate → rotate → scale (the standard order)
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Angle (Degrees for rotation)
-- | - Schema.Geometry.Point (Point3D for positions)
-- | - Schema.Geometry.Vector (Vector3D for directions)

module Hydrogen.Schema.Geometry.Transform3D
  ( -- * Translate3D
    Translate3D(Translate3D)
  , translate3D
  , translateX3D
  , translateY3D
  , translateZ3D
  , translate3DNone
  , getTranslate3DX
  , getTranslate3DY
  , getTranslate3DZ
  , addTranslate3D
  , translate3DToLegacyCss
  
  -- * Rotate3D
  , Rotate3D(Rotate3D)
  , rotateX3D
  , rotateY3D
  , rotateZ3D
  , rotate3D
  , rotate3DNone
  , getRotateX
  , getRotateY
  , getRotateZ
  , addRotation3D
  , rotate3DToLegacyCss
  
  -- * Scale3D
  , Scale3D(Scale3D)
  , scale3D
  , scale3DUniform
  , scaleX3D
  , scaleY3D
  , scaleZ3D
  , scale3DIdentity
  , getScale3DX
  , getScale3DY
  , getScale3DZ
  , scale3DToLegacyCss
  , scale3DBounds
  
  -- * Perspective
  , Perspective(Perspective)
  , perspective
  , perspectiveNone
  , getPerspective
  , perspectiveToLegacyCss
  , perspectiveBounds
  
  -- * Perspective Origin
  , PerspectiveOrigin(PerspectiveOrigin)
  , perspectiveOrigin
  , perspectiveOriginCenter
  , getPerspectiveOriginX
  , getPerspectiveOriginY
  , perspectiveOriginToLegacyCss
  
  -- * Composed Transform3D
  , Transform3D(Transform3D)
  , transform3D
  , identity3D
  , withTranslate3D
  , withRotate3D
  , withScale3D
  , withPerspective
  , withPerspectiveOrigin
  , transform3DToLegacyCss
  
  -- * Camera Utilities
  , lookAt
  , orbitAround
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , map
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (&&)
  )

import Data.Array (uncons)
import Data.Maybe (Maybe(Nothing, Just))

import Data.Foldable (foldl)
import Data.Ord (min, max)
import Data.Number (sqrt, sin, cos, atan2, pi)

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Geometry.Angle (Degrees, degrees, unwrapDegrees, addAngle)
import Hydrogen.Schema.Geometry.Point (Point3D(Point3D), point3D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // translate3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D translation in pixels.
newtype Translate3D = Translate3D { x :: Number, y :: Number, z :: Number }

derive instance eqTranslate3D :: Eq Translate3D
derive instance ordTranslate3D :: Ord Translate3D

instance showTranslate3D :: Show Translate3D where
  show (Translate3D t) = "(Translate3D " <> show t.x <> " " <> show t.y <> " " <> show t.z <> ")"

-- | Create 3D translation
translate3D :: Number -> Number -> Number -> Translate3D
translate3D x y z = Translate3D { x, y, z }

-- | Translate only on X axis
translateX3D :: Number -> Translate3D
translateX3D x = Translate3D { x, y: 0.0, z: 0.0 }

-- | Translate only on Y axis
translateY3D :: Number -> Translate3D
translateY3D y = Translate3D { x: 0.0, y, z: 0.0 }

-- | Translate only on Z axis
translateZ3D :: Number -> Translate3D
translateZ3D z = Translate3D { x: 0.0, y: 0.0, z }

-- | No translation (identity)
translate3DNone :: Translate3D
translate3DNone = Translate3D { x: 0.0, y: 0.0, z: 0.0 }

-- | Get X translation
getTranslate3DX :: Translate3D -> Number
getTranslate3DX (Translate3D t) = t.x

-- | Get Y translation
getTranslate3DY :: Translate3D -> Number
getTranslate3DY (Translate3D t) = t.y

-- | Get Z translation
getTranslate3DZ :: Translate3D -> Number
getTranslate3DZ (Translate3D t) = t.z

-- | Combine translations
addTranslate3D :: Translate3D -> Translate3D -> Translate3D
addTranslate3D (Translate3D a) (Translate3D b) =
  Translate3D { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z }

-- | Convert to CSS
translate3DToLegacyCss :: Translate3D -> String
translate3DToLegacyCss (Translate3D t) =
  "translate3d(" <> show t.x <> "px, " <> show t.y <> "px, " <> show t.z <> "px)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // rotate3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D rotation using Euler angles (X, Y, Z rotations).
-- |
-- | Applied in order: rotateX → rotateY → rotateZ
-- | This is the "intrinsic" or "Tait-Bryan" rotation convention.
newtype Rotate3D = Rotate3D { x :: Degrees, y :: Degrees, z :: Degrees }

derive instance eqRotate3D :: Eq Rotate3D
derive instance ordRotate3D :: Ord Rotate3D

instance showRotate3D :: Show Rotate3D where
  show (Rotate3D r) = "(Rotate3D x:" <> show r.x <> " y:" <> show r.y <> " z:" <> show r.z <> ")"

-- | Rotate only around X axis
rotateX3D :: Degrees -> Rotate3D
rotateX3D x = Rotate3D { x, y: degrees 0.0, z: degrees 0.0 }

-- | Rotate only around Y axis
rotateY3D :: Degrees -> Rotate3D
rotateY3D y = Rotate3D { x: degrees 0.0, y, z: degrees 0.0 }

-- | Rotate only around Z axis
rotateZ3D :: Degrees -> Rotate3D
rotateZ3D z = Rotate3D { x: degrees 0.0, y: degrees 0.0, z }

-- | Create rotation with all three axes
rotate3D :: Degrees -> Degrees -> Degrees -> Rotate3D
rotate3D x y z = Rotate3D { x, y, z }

-- | No rotation (identity)
rotate3DNone :: Rotate3D
rotate3DNone = Rotate3D { x: degrees 0.0, y: degrees 0.0, z: degrees 0.0 }

-- | Get X rotation
getRotateX :: Rotate3D -> Degrees
getRotateX (Rotate3D r) = r.x

-- | Get Y rotation
getRotateY :: Rotate3D -> Degrees
getRotateY (Rotate3D r) = r.y

-- | Get Z rotation
getRotateZ :: Rotate3D -> Degrees
getRotateZ (Rotate3D r) = r.z

-- | Combine rotations (add Euler angles)
-- | Note: This is approximate — true rotation composition requires quaternions
addRotation3D :: Rotate3D -> Rotate3D -> Rotate3D
addRotation3D (Rotate3D a) (Rotate3D b) = Rotate3D
  { x: addAngle a.x b.x
  , y: addAngle a.y b.y
  , z: addAngle a.z b.z
  }

-- | Convert to CSS
rotate3DToLegacyCss :: Rotate3D -> String
rotate3DToLegacyCss (Rotate3D r) =
  let
    xDeg = unwrapDegrees r.x
    yDeg = unwrapDegrees r.y
    zDeg = unwrapDegrees r.z
    parts = []
      <> (if xDeg == 0.0 then [] else ["rotateX(" <> show xDeg <> "deg)"])
      <> (if yDeg == 0.0 then [] else ["rotateY(" <> show yDeg <> "deg)"])
      <> (if zDeg == 0.0 then [] else ["rotateZ(" <> show zDeg <> "deg)"])
  in
    joinParts parts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // scale3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D scale with bounded values (-10.0 to 10.0).
newtype Scale3D = Scale3D { x :: Number, y :: Number, z :: Number }

derive instance eqScale3D :: Eq Scale3D
derive instance ordScale3D :: Ord Scale3D

instance showScale3D :: Show Scale3D where
  show (Scale3D s) = "(Scale3D " <> show s.x <> " " <> show s.y <> " " <> show s.z <> ")"

-- | Clamp scale to valid range (-10.0 to 10.0)
clampScale :: Number -> Number
clampScale = Bounded.clampNumber (-10.0) 10.0

-- | Create 3D scale
scale3D :: Number -> Number -> Number -> Scale3D
scale3D x y z = Scale3D 
  { x: clampScale x
  , y: clampScale y
  , z: clampScale z
  }

-- | Uniform scale (same on all axes)
scale3DUniform :: Number -> Scale3D
scale3DUniform n = 
  let clamped = clampScale n
  in Scale3D { x: clamped, y: clamped, z: clamped }

-- | Scale only on X axis
scaleX3D :: Number -> Scale3D
scaleX3D x = Scale3D { x: clampScale x, y: 1.0, z: 1.0 }

-- | Scale only on Y axis
scaleY3D :: Number -> Scale3D
scaleY3D y = Scale3D { x: 1.0, y: clampScale y, z: 1.0 }

-- | Scale only on Z axis
scaleZ3D :: Number -> Scale3D
scaleZ3D z = Scale3D { x: 1.0, y: 1.0, z: clampScale z }

-- | Identity scale (no change)
scale3DIdentity :: Scale3D
scale3DIdentity = Scale3D { x: 1.0, y: 1.0, z: 1.0 }

-- | Get X scale
getScale3DX :: Scale3D -> Number
getScale3DX (Scale3D s) = s.x

-- | Get Y scale
getScale3DY :: Scale3D -> Number
getScale3DY (Scale3D s) = s.y

-- | Get Z scale
getScale3DZ :: Scale3D -> Number
getScale3DZ (Scale3D s) = s.z

-- | Convert to CSS
scale3DToLegacyCss :: Scale3D -> String
scale3DToLegacyCss (Scale3D s) =
  if s.x == s.y && s.y == s.z
    then "scale3d(" <> show s.x <> ", " <> show s.x <> ", " <> show s.x <> ")"
    else "scale3d(" <> show s.x <> ", " <> show s.y <> ", " <> show s.z <> ")"

-- | Bounds for Scale3D components.
-- |
-- | Scale values are bounded -10.0 to 10.0 to prevent:
-- | - Extreme distortion that breaks layouts
-- | - Negative scales beyond mirroring (meaningful up to -1.0)
-- | - Values that cause GPU precision issues
scale3DBounds :: Bounded.NumberBounds
scale3DBounds = Bounded.numberBounds (-10.0) 10.0 "Scale3D"
  "3D scale factor per axis, allowing inversion via negative values"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // perspective
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perspective depth in pixels.
-- |
-- | Lower values = more extreme perspective (fishbowl effect)
-- | Higher values = flatter perspective (telephoto effect)
-- | Common values: 500-1500px for UI, 200-500px for dramatic effects
newtype Perspective = Perspective Number

derive instance eqPerspective :: Eq Perspective
derive instance ordPerspective :: Ord Perspective

instance showPerspective :: Show Perspective where
  show (Perspective p) = "(Perspective " <> show p <> ")"

-- | Create perspective.
-- | Values are clamped to 1.0-10000.0 to avoid division issues and
-- | ensure meaningful perspective effects.
perspective :: Number -> Perspective
perspective n = Perspective (Bounded.clampNumber 1.0 10000.0 n)

-- | No perspective (flat)
perspectiveNone :: Perspective
perspectiveNone = Perspective 0.0

-- | Get perspective value
getPerspective :: Perspective -> Number
getPerspective (Perspective p) = p

-- | Convert to CSS
perspectiveToLegacyCss :: Perspective -> String
perspectiveToLegacyCss (Perspective p) =
  if p == 0.0
    then "none"
    else "perspective(" <> show p <> "px)"

-- | Bounds for Perspective depth.
-- |
-- | Perspective values are bounded 1.0 to 10000.0 pixels:
-- | - Minimum 1.0 avoids division by zero and extreme fisheye
-- | - Maximum 10000.0 is effectively flat (no visible perspective)
-- | - Common UI values: 500-1500px
-- | - Dramatic effects: 200-500px
-- | - Note: perspectiveNone (0.0) is a special case meaning "no perspective"
perspectiveBounds :: Bounded.NumberBounds
perspectiveBounds = Bounded.numberBounds 1.0 10000.0 "Perspective"
  "Perspective depth in pixels controlling 3D foreshortening"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // perspective origin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perspective origin (vanishing point) in percentages.
newtype PerspectiveOrigin = PerspectiveOrigin { x :: Number, y :: Number }

derive instance eqPerspectiveOrigin :: Eq PerspectiveOrigin
derive instance ordPerspectiveOrigin :: Ord PerspectiveOrigin

instance showPerspectiveOrigin :: Show PerspectiveOrigin where
  show (PerspectiveOrigin o) = "(PerspectiveOrigin " <> show o.x <> " " <> show o.y <> ")"

-- | Create perspective origin from percentages
perspectiveOrigin :: Number -> Number -> PerspectiveOrigin
perspectiveOrigin x y = PerspectiveOrigin { x, y }

-- | Center perspective origin (default)
perspectiveOriginCenter :: PerspectiveOrigin
perspectiveOriginCenter = PerspectiveOrigin { x: 50.0, y: 50.0 }

-- | Get X origin
getPerspectiveOriginX :: PerspectiveOrigin -> Number
getPerspectiveOriginX (PerspectiveOrigin o) = o.x

-- | Get Y origin
getPerspectiveOriginY :: PerspectiveOrigin -> Number
getPerspectiveOriginY (PerspectiveOrigin o) = o.y

-- | Convert to CSS
perspectiveOriginToLegacyCss :: PerspectiveOrigin -> String
perspectiveOriginToLegacyCss (PerspectiveOrigin o) =
  show o.x <> "% " <> show o.y <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // composed transform3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 3D transform.
newtype Transform3D = Transform3D
  { translate :: Maybe Translate3D
  , rotate :: Maybe Rotate3D
  , scale :: Maybe Scale3D
  , perspective :: Maybe Perspective
  , perspectiveOrigin :: PerspectiveOrigin
  }

derive instance eqTransform3D :: Eq Transform3D

instance showTransform3D :: Show Transform3D where
  show (Transform3D t) = "(Transform3D"
    <> " translate:" <> show t.translate
    <> " rotate:" <> show t.rotate
    <> " scale:" <> show t.scale
    <> " perspective:" <> show t.perspective
    <> " perspectiveOrigin:" <> show t.perspectiveOrigin
    <> ")"

-- | Create a 3D transform with all components
transform3D
  :: Maybe Translate3D
  -> Maybe Rotate3D
  -> Maybe Scale3D
  -> Maybe Perspective
  -> PerspectiveOrigin
  -> Transform3D
transform3D t r s p po = Transform3D
  { translate: t
  , rotate: r
  , scale: s
  , perspective: p
  , perspectiveOrigin: po
  }

-- | Identity 3D transform
identity3D :: Transform3D
identity3D = Transform3D
  { translate: Nothing
  , rotate: Nothing
  , scale: Nothing
  , perspective: Nothing
  , perspectiveOrigin: perspectiveOriginCenter
  }

-- | Set translate
withTranslate3D :: Translate3D -> Transform3D -> Transform3D
withTranslate3D t (Transform3D tr) = Transform3D (tr { translate = Just t })

-- | Set rotate
withRotate3D :: Rotate3D -> Transform3D -> Transform3D
withRotate3D r (Transform3D tr) = Transform3D (tr { rotate = Just r })

-- | Set scale
withScale3D :: Scale3D -> Transform3D -> Transform3D
withScale3D s (Transform3D tr) = Transform3D (tr { scale = Just s })

-- | Set perspective
withPerspective :: Perspective -> Transform3D -> Transform3D
withPerspective p (Transform3D tr) = Transform3D (tr { perspective = Just p })

-- | Set perspective origin
withPerspectiveOrigin :: PerspectiveOrigin -> Transform3D -> Transform3D
withPerspectiveOrigin po (Transform3D tr) = Transform3D (tr { perspectiveOrigin = po })

-- | Convert to CSS transform property value.
-- | Order: perspective → translate → rotate → scale
transform3DToLegacyCss :: Transform3D -> String
transform3DToLegacyCss (Transform3D t) =
  let
    parts =
      maybeToArray (map perspectiveToLegacyCss t.perspective) <>
      maybeToArray (map translate3DToLegacyCss t.translate) <>
      maybeToArray (map rotate3DToLegacyCss t.rotate) <>
      maybeToArray (map scale3DToLegacyCss t.scale)
  in
    joinParts parts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // camera utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute rotation to look at a target point from current position.
-- |
-- | Returns Y rotation (yaw) and X rotation (pitch) to face the target.
-- | Useful for camera-following effects.
lookAt :: Point3D -> Point3D -> Rotate3D
lookAt (Point3D from) (Point3D to) =
  let
    dx = to.x - from.x
    dy = to.y - from.y
    dz = to.z - from.z
    
    -- Horizontal angle (yaw) - rotation around Y axis
    yaw = atan2 dx dz * 180.0 / pi
    
    -- Vertical angle (pitch) - rotation around X axis
    horizontalDist = sqrt (dx * dx + dz * dz)
    pitch = atan2 dy horizontalDist * 180.0 / pi
  in
    Rotate3D
      { x: degrees (negate pitch)  -- Negate for screen coordinates
      , y: degrees yaw
      , z: degrees 0.0
      }

-- | Compute position on orbit around a center point.
-- |
-- | Given center, radius, and angle, returns position on circular orbit.
-- | Useful for carousel effects, rotating menus, etc.
orbitAround :: Point3D -> Number -> Degrees -> Point3D
orbitAround (Point3D center) radius angle =
  let
    rad = unwrapDegrees angle * pi / 180.0
    x = center.x + radius * sin rad
    z = center.z + radius * cos rad
  in
    point3D x center.y z

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Maybe to singleton or empty array
maybeToArray :: forall a. Maybe a -> Array a
maybeToArray Nothing = []
maybeToArray (Just x) = [x]

-- | Join array with spaces
joinParts :: Array String -> String
joinParts arr = case uncons arr of
  Nothing -> ""
  Just { head, tail } ->
    case uncons tail of
      Nothing -> head
      Just _ -> foldl (\acc x -> acc <> " " <> x) head tail
