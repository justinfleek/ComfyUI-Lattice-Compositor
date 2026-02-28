-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // geometry // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform - 2D/3D transformation primitives for UI elements.
-- |
-- | Complete transformation system with bounded values for:
-- | - Scale: 0.0 to 10.0 (0% to 1000%)
-- | - Translate: Physical/logical directions, RTL-aware
-- | - Rotate: Degrees with full circle support
-- | - Skew: X/Y axis skewing
-- | - Origin: Transform origin point
-- |
-- | ## Bounded Design
-- |
-- | All values are clamped to sensible ranges to prevent:
-- | - Negative scales (use flip instead)
-- | - Extreme values that break layout
-- | - Invalid transforms at billion-agent scale
-- |
-- | ## Button Press Effect
-- |
-- | ```purescript
-- | pressScale = scale 0.98  -- subtle press feedback
-- | hoverScale = scale 1.02  -- subtle hover lift
-- | ```

module Hydrogen.Schema.Geometry.Transform
  ( -- * Scale (bounded -10.0 to 10.0)
    Scale(Scale)
  , scale
  , scaleXY
  , scaleIdentity
  , scaleNone
  , scaleDouble
  , scaleHalf
  , scaleButtonPress
  , scaleButtonHover
  , scaleFlipX
  , scaleFlipY
  , scaleFlipBoth
  , getScaleX
  , getScaleY
  , isUniformScale
  , isFlippedX
  , isFlippedY
  , scaleToPercent
  , scaleToLegacyCss
  
  -- * Translate
  , Translate(Translate)
  , translate
  , translateX
  , translateY
  , translateNone
  , getTranslateX
  , getTranslateY
  , addTranslate
  , negateTranslate
  , translateToLegacyCss
  
  -- * Rotate
  , Rotate(Rotate)
  , rotate
  , rotateNone
  , rotate90
  , rotate180
  , rotate270
  , getRotation
  , addRotation
  , rotateToLegacyCss
  
  -- * Skew
  , Skew(Skew)
  , skew
  , skewX
  , skewY
  , skewNone
  , getSkewX
  , getSkewY
  , skewToLegacyCss
  
  -- * Transform Origin
  , Origin(Origin)
  , origin
  , originCenter
  , originTopLeft
  , originTopRight
  , originBottomLeft
  , originBottomRight
  , originTop
  , originBottom
  , originLeft
  , originRight
  , getOriginX
  , getOriginY
  , originToLegacyCss
  
  -- * Composed Transform
  , Transform2D(Transform2D)
  , transform2D
  , identityTransform
  , composeTransform
  , withScale
  , withTranslate
  , withRotate
  , withSkew
  , withOrigin
  , transform2DToLegacyCss
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (+)
  , (-)
  , (==)
  , (<)
  , (*)
  , (<>)
  )

import Data.Array (uncons)
import Data.Maybe (Maybe(Nothing, Just), maybe)
import Data.Ord (min, max)
import Data.Foldable (foldl)

import Hydrogen.Schema.Geometry.Angle (Degrees, degrees, unwrapDegrees, addAngle)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D scale transform with bounded values.
-- |
-- | Scale factors are clamped to -10.0 to 10.0:
-- | - 1.0 = 100% (identity)
-- | - 0.0 = 0% (invisible)
-- | - 2.0 = 200% (double size)
-- | - 0.5 = 50% (half size)
-- | - -1.0 = flip (mirror)
-- |
-- | Negative values create mirror/flip effects.
newtype Scale = Scale { x :: Number, y :: Number }

derive instance eqScale :: Eq Scale
derive instance ordScale :: Ord Scale

instance showScale :: Show Scale where
  show (Scale s) = "(Scale " <> show s.x <> " " <> show s.y <> ")"

-- | Clamp scale value to valid range (-10.0 to 10.0).
clampScale :: Number -> Number
clampScale n = max (-10.0) (min 10.0 n)

-- | Create uniform scale (same X and Y), clamped.
scale :: Number -> Scale
scale n = 
  let clamped = clampScale n
  in Scale { x: clamped, y: clamped }

-- | Create non-uniform scale (different X and Y), both clamped.
scaleXY :: Number -> Number -> Scale
scaleXY x y = Scale { x: clampScale x, y: clampScale y }

-- | Identity scale (1.0) — no change.
scaleIdentity :: Scale
scaleIdentity = Scale { x: 1.0, y: 1.0 }

-- | Zero scale — element becomes invisible.
scaleNone :: Scale
scaleNone = Scale { x: 0.0, y: 0.0 }

-- | Double size (200%).
scaleDouble :: Scale
scaleDouble = Scale { x: 2.0, y: 2.0 }

-- | Half size (50%).
scaleHalf :: Scale
scaleHalf = Scale { x: 0.5, y: 0.5 }

-- | Button press feedback scale (98%).
-- |
-- | Standard subtle scale-down for active/pressed state.
scaleButtonPress :: Scale
scaleButtonPress = Scale { x: 0.98, y: 0.98 }

-- | Button hover lift scale (102%).
-- |
-- | Standard subtle scale-up for hover state.
scaleButtonHover :: Scale
scaleButtonHover = Scale { x: 1.02, y: 1.02 }

-- | Flip horizontally (mirror X axis).
scaleFlipX :: Scale
scaleFlipX = Scale { x: -1.0, y: 1.0 }

-- | Flip vertically (mirror Y axis).
scaleFlipY :: Scale
scaleFlipY = Scale { x: 1.0, y: -1.0 }

-- | Flip both axes (180° rotation equivalent).
scaleFlipBoth :: Scale
scaleFlipBoth = Scale { x: -1.0, y: -1.0 }

-- | Get X scale factor.
getScaleX :: Scale -> Number
getScaleX (Scale s) = s.x

-- | Get Y scale factor.
getScaleY :: Scale -> Number
getScaleY (Scale s) = s.y

-- | Is this a uniform scale (same X and Y)?
isUniformScale :: Scale -> Boolean
isUniformScale (Scale s) = s.x == s.y

-- | Is X axis flipped (negative)?
isFlippedX :: Scale -> Boolean
isFlippedX (Scale s) = s.x < 0.0

-- | Is Y axis flipped (negative)?
isFlippedY :: Scale -> Boolean
isFlippedY (Scale s) = s.y < 0.0

-- | Convert scale to percentage string.
-- |
-- | scaleToPercent (scale 0.5) = "50%"
-- | scaleToPercent (scaleXY 1.0 2.0) = "100% x 200%"
scaleToPercent :: Scale -> String
scaleToPercent (Scale s) =
  let 
    xPct = show (s.x * 100.0) <> "%"
    yPct = show (s.y * 100.0) <> "%"
  in
    if s.x == s.y
      then xPct
      else xPct <> " x " <> yPct

-- | Convert scale to legacy CSS transform string.
scaleToLegacyCss :: Scale -> String
scaleToLegacyCss (Scale s) =
  if s.x == s.y
    then "scale(" <> show s.x <> ")"
    else "scale(" <> show s.x <> ", " <> show s.y <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // translate
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D translation in pixels.
-- |
-- | Unbounded — elements can translate anywhere.
newtype Translate = Translate { x :: Number, y :: Number }

derive instance eqTranslate :: Eq Translate
derive instance ordTranslate :: Ord Translate

instance showTranslate :: Show Translate where
  show (Translate t) = "(Translate " <> show t.x <> " " <> show t.y <> ")"

-- | Create translation
translate :: Number -> Number -> Translate
translate x y = Translate { x, y }

-- | Translate only on X axis
translateX :: Number -> Translate
translateX x = Translate { x, y: 0.0 }

-- | Translate only on Y axis
translateY :: Number -> Translate
translateY y = Translate { x: 0.0, y }

-- | No translation (identity)
translateNone :: Translate
translateNone = Translate { x: 0.0, y: 0.0 }

-- | Get X translation
getTranslateX :: Translate -> Number
getTranslateX (Translate t) = t.x

-- | Get Y translation
getTranslateY :: Translate -> Number
getTranslateY (Translate t) = t.y

-- | Combine translations (add)
addTranslate :: Translate -> Translate -> Translate
addTranslate (Translate a) (Translate b) =
  Translate { x: a.x + b.x, y: a.y + b.y }

-- | Negate translation
negateTranslate :: Translate -> Translate
negateTranslate (Translate t) = Translate { x: negate t.x, y: negate t.y }

-- | Convert to CSS
translateToLegacyCss :: Translate -> String
translateToLegacyCss (Translate t) =
  "translate(" <> show t.x <> "px, " <> show t.y <> "px)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // rotate
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D rotation using Degrees atom from Angle module.
-- |
-- | Rotation is automatically normalized to [0, 360) via the Degrees type.
newtype Rotate = Rotate { angle :: Degrees }

derive instance eqRotate :: Eq Rotate
derive instance ordRotate :: Ord Rotate

instance showRotate :: Show Rotate where
  show (Rotate r) = "(Rotate " <> show r.angle <> ")"

-- | Create rotation from degrees
rotate :: Degrees -> Rotate
rotate angle = Rotate { angle }

-- | No rotation (0 degrees)
rotateNone :: Rotate
rotateNone = Rotate { angle: degrees 0.0 }

-- | 90 degree rotation
rotate90 :: Rotate
rotate90 = Rotate { angle: degrees 90.0 }

-- | 180 degree rotation
rotate180 :: Rotate
rotate180 = Rotate { angle: degrees 180.0 }

-- | 270 degree rotation (-90)
rotate270 :: Rotate
rotate270 = Rotate { angle: degrees 270.0 }

-- | Get rotation angle
getRotation :: Rotate -> Degrees
getRotation (Rotate r) = r.angle

-- | Combine rotations (add angles)
addRotation :: Rotate -> Rotate -> Rotate
addRotation (Rotate a) (Rotate b) =
  Rotate { angle: addAngle a.angle b.angle }

-- | Convert to CSS
rotateToLegacyCss :: Rotate -> String
rotateToLegacyCss (Rotate r) =
  "rotate(" <> show (unwrapDegrees r.angle) <> "deg)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // skew
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D skew transform in degrees.
-- |
-- | Skew angles are clamped to [-89, 89] to prevent extreme distortion.
-- | At 90 degrees, the transform becomes degenerate.
newtype Skew = Skew { x :: Number, y :: Number }

derive instance eqSkew :: Eq Skew
derive instance ordSkew :: Ord Skew

instance showSkew :: Show Skew where
  show (Skew s) = "(Skew " <> show s.x <> " " <> show s.y <> ")"

-- | Clamp skew to safe range
clampSkew :: Number -> Number
clampSkew n = max (-89.0) (min 89.0 n)

-- | Create skew transform
skew :: Number -> Number -> Skew
skew x y = Skew { x: clampSkew x, y: clampSkew y }

-- | Skew only on X axis
skewX :: Number -> Skew
skewX x = Skew { x: clampSkew x, y: 0.0 }

-- | Skew only on Y axis
skewY :: Number -> Skew
skewY y = Skew { x: 0.0, y: clampSkew y }

-- | No skew (identity)
skewNone :: Skew
skewNone = Skew { x: 0.0, y: 0.0 }

-- | Get X skew angle
getSkewX :: Skew -> Number
getSkewX (Skew s) = s.x

-- | Get Y skew angle
getSkewY :: Skew -> Number
getSkewY (Skew s) = s.y

-- | Convert to CSS
skewToLegacyCss :: Skew -> String
skewToLegacyCss (Skew s) =
  if s.y == 0.0 then
    "skewX(" <> show s.x <> "deg)"
  else if s.x == 0.0 then
    "skewY(" <> show s.y <> "deg)"
  else
    "skew(" <> show s.x <> "deg, " <> show s.y <> "deg)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // transform origin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform origin point.
-- |
-- | Coordinates are percentages (0-100) or pixel values.
-- | For simplicity, this uses percentages.
newtype Origin = Origin { x :: Number, y :: Number }

derive instance eqOrigin :: Eq Origin
derive instance ordOrigin :: Ord Origin

instance showOrigin :: Show Origin where
  show (Origin o) = "(Origin " <> show o.x <> " " <> show o.y <> ")"

-- | Create origin from percentages
origin :: Number -> Number -> Origin
origin x y = Origin { x, y }

-- | Center origin (50%, 50%) — default
originCenter :: Origin
originCenter = Origin { x: 50.0, y: 50.0 }

-- | Top-left origin
originTopLeft :: Origin
originTopLeft = Origin { x: 0.0, y: 0.0 }

-- | Top-right origin
originTopRight :: Origin
originTopRight = Origin { x: 100.0, y: 0.0 }

-- | Bottom-left origin
originBottomLeft :: Origin
originBottomLeft = Origin { x: 0.0, y: 100.0 }

-- | Bottom-right origin
originBottomRight :: Origin
originBottomRight = Origin { x: 100.0, y: 100.0 }

-- | Top center origin
originTop :: Origin
originTop = Origin { x: 50.0, y: 0.0 }

-- | Bottom center origin
originBottom :: Origin
originBottom = Origin { x: 50.0, y: 100.0 }

-- | Left center origin
originLeft :: Origin
originLeft = Origin { x: 0.0, y: 50.0 }

-- | Right center origin
originRight :: Origin
originRight = Origin { x: 100.0, y: 50.0 }

-- | Get X origin percentage
getOriginX :: Origin -> Number
getOriginX (Origin o) = o.x

-- | Get Y origin percentage
getOriginY :: Origin -> Number
getOriginY (Origin o) = o.y

-- | Convert to CSS
originToLegacyCss :: Origin -> String
originToLegacyCss (Origin o) = show o.x <> "% " <> show o.y <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // composed transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 2D transform combining all transform types.
-- |
-- | Transform order in CSS: translate, rotate, scale, skew
-- | This matches the mathematical convention for composing transforms.
newtype Transform2D = Transform2D
  { translate :: Maybe Translate
  , rotate :: Maybe Rotate
  , scale :: Maybe Scale
  , skew :: Maybe Skew
  , origin :: Origin
  }

derive instance eqTransform2D :: Eq Transform2D

instance showTransform2D :: Show Transform2D where
  show (Transform2D t) = "(Transform2D"
    <> " translate:" <> show t.translate
    <> " rotate:" <> show t.rotate
    <> " scale:" <> show t.scale
    <> " skew:" <> show t.skew
    <> " origin:" <> show t.origin
    <> ")"

-- | Create a transform with all components
transform2D 
  :: Maybe Translate 
  -> Maybe Rotate 
  -> Maybe Scale 
  -> Maybe Skew 
  -> Origin 
  -> Transform2D
transform2D t r s sk o = Transform2D
  { translate: t
  , rotate: r
  , scale: s
  , skew: sk
  , origin: o
  }

-- | Identity transform (no transformation)
identityTransform :: Transform2D
identityTransform = Transform2D
  { translate: Nothing
  , rotate: Nothing
  , scale: Nothing
  , skew: Nothing
  , origin: originCenter
  }

-- | Compose two transforms (second applied after first)
composeTransform :: Transform2D -> Transform2D -> Transform2D
composeTransform (Transform2D a) (Transform2D b) = Transform2D
  { translate: composeMaybe addTranslate a.translate b.translate
  , rotate: composeMaybe addRotation a.rotate b.rotate
  , scale: composeMaybe composeScale a.scale b.scale
  , skew: composeMaybe composeSkew a.skew b.skew
  , origin: b.origin  -- Use second transform's origin
  }
  where
    composeMaybe :: forall x. (x -> x -> x) -> Maybe x -> Maybe x -> Maybe x
    composeMaybe _ Nothing Nothing = Nothing
    composeMaybe _ (Just x) Nothing = Just x
    composeMaybe _ Nothing (Just y) = Just y
    composeMaybe f (Just x) (Just y) = Just (f x y)
    
    composeScale :: Scale -> Scale -> Scale
    composeScale (Scale s1) (Scale s2) = 
      Scale { x: s1.x * s2.x, y: s1.y * s2.y }
    
    composeSkew :: Skew -> Skew -> Skew
    composeSkew (Skew sk1) (Skew sk2) =
      skew (sk1.x + sk2.x) (sk1.y + sk2.y)

-- | Set scale on transform
withScale :: Scale -> Transform2D -> Transform2D
withScale s (Transform2D t) = Transform2D (t { scale = Just s })

-- | Set translate on transform
withTranslate :: Translate -> Transform2D -> Transform2D
withTranslate tr (Transform2D t) = Transform2D (t { translate = Just tr })

-- | Set rotate on transform
withRotate :: Rotate -> Transform2D -> Transform2D
withRotate r (Transform2D t) = Transform2D (t { rotate = Just r })

-- | Set skew on transform
withSkew :: Skew -> Transform2D -> Transform2D
withSkew sk (Transform2D t) = Transform2D (t { skew = Just sk })

-- | Set origin on transform
withOrigin :: Origin -> Transform2D -> Transform2D
withOrigin o (Transform2D t) = Transform2D (t { origin = o })

-- | Convert composed transform to CSS.
-- |
-- | Outputs transform and transform-origin as separate values.
-- | Order: translate → rotate → scale → skew
transform2DToLegacyCss :: Transform2D -> String
transform2DToLegacyCss (Transform2D t) =
  let
    parts = 
      maybeToArray (maybe [] (\x -> [translateToLegacyCss x]) t.translate) <>
      maybeToArray (maybe [] (\x -> [rotateToLegacyCss x]) t.rotate) <>
      maybeToArray (maybe [] (\x -> [scaleToLegacyCss x]) t.scale) <>
      maybeToArray (maybe [] (\x -> [skewToLegacyCss x]) t.skew)
  in
    joinParts parts

-- | Helper to convert Maybe to singleton or empty array
maybeToArray :: forall a. Array a -> Array a
maybeToArray = \arr -> arr

-- | Join transform parts with spaces
joinParts :: Array String -> String
joinParts arr = case uncons arr of
  Nothing -> ""
  Just { head, tail } -> 
    case uncons tail of
      Nothing -> head
      Just _ -> foldl (\acc x -> acc <> " " <> x) head tail
