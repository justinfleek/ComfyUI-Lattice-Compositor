-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // animation // algebra
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure animation algebra for typography and element animations.
-- |
-- | All combinators are lawful (Semigroup, Monoid, Applicative).
-- | Time is bounded. Transforms compose. Everything is deterministic.

module Hydrogen.Animation.Algebra
  ( -- Time primitives
    Duration(Duration)
  , Milliseconds
  , Progress(Progress)
  , normalizeProgress
  
  -- Easing
  , Easing
      ( Linear
      , EaseIn
      , EaseOut
      , EaseInOut
      , EaseInQuad
      , EaseOutQuad
      , EaseInOutQuad
      , EaseInCubic
      , EaseOutCubic
      , EaseInOutCubic
      , EaseInQuart
      , EaseOutQuart
      , EaseInOutQuart
      , EaseInQuint
      , EaseOutQuint
      , EaseInOutQuint
      , EaseInExpo
      , EaseOutExpo
      , EaseInOutExpo
      , EaseInCirc
      , EaseOutCirc
      , EaseInOutCirc
      , EaseInBack
      , EaseOutBack
      , EaseInOutBack
      , EaseInElastic
      , EaseOutElastic
      , EaseInOutElastic
      , EaseInBounce
      , EaseOutBounce
      , EaseInOutBounce
      , Spring
      , CubicBezier
      , Steps
      , Custom
      )
  , EasingFunction
  , applyEasing
  , SpringConfig(SpringConfig)
  , BezierCurve(BezierCurve)
  
  -- Transforms
  , Transform2D(Transform2D)
  , Transform3D(Transform3D)
  , TransformOrigin(TransformOrigin)
  , Opacity(Opacity)
  
  -- Core animation type
  , Animation(Animation)
  , AnimationF
  , runAnimation
  , duration
  
  -- Combinators
  , sequential
  , parallel
  , stagger
  , delay
  , timeScale
  , reverse
  , pingPong
  , repeat
  
  -- Stagger patterns
  , StaggerPattern(LinearStagger, RandomStagger, CustomStagger)
  , StaggerDirection(LeftToRight, RightToLeft, CenterOut, EdgesIn)
  , applyStagger
  
  -- Transform animations
  , translateX
  , translateY
  , translate
  , scale
  , scaleXY
  , rotate
  , rotate3D
  , skewX
  , skewY
  , opacity
  
  -- Path animations
  , Point2D
  , PathSegment(MoveTo, LineTo, QuadraticTo, CubicTo, ArcTo, ClosePath)
  , AnimationPath(AnimationPath)
  , followPath
  , morphPath
  
  -- Character/Word targeting
  , AnimationTarget(TargetCharacter, TargetWord, TargetLine, TargetRange, TargetAll)
  , TargetSelector(SelectAll, SelectOdd, SelectEven, SelectEvery, SelectRange, SelectIndices, SelectWhere)
  , targeted
  ) where

import Prelude

import Data.Array (length, foldl)
import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(Nothing, Just))
import Data.Newtype (class Newtype, unwrap)
import Data.Ord (abs)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §1 Time Primitives
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Duration in milliseconds, bounded to reasonable animation lengths.
-- | Maximum duration: 10 minutes (600000ms) — sufficient for any UI animation.
-- | Minimum duration: 0ms (instant).
type Milliseconds = Int

newtype Duration = Duration Milliseconds

derive instance Newtype Duration _
derive instance Eq Duration
derive instance Ord Duration

instance Semigroup Duration where
  append (Duration a) (Duration b) = Duration (a + b)

instance Monoid Duration where
  mempty = Duration 0

-- | Progress through an animation, normalized to [0, 1].
-- | This is the fundamental bounded time unit.
-- | 0.0 = animation start
-- | 1.0 = animation end
-- | Values outside [0,1] are clamped by normalizeProgress.
newtype Progress = Progress Number

derive instance Newtype Progress _
derive instance Eq Progress
derive instance Ord Progress

-- | Clamp progress to valid range [0, 1].
-- | This ensures all animation calculations operate on bounded values.
normalizeProgress :: Number -> Progress
normalizeProgress n
  | n < 0.0 = Progress 0.0
  | n > 1.0 = Progress 1.0
  | otherwise = Progress n

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §2 Easing Functions
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Easing function type: Progress → Progress.
-- | Transforms linear time into curved time.
-- | Must satisfy: f(0) = 0, f(1) = 1 (boundary preservation).
type EasingFunction = Progress -> Progress

-- | Spring physics configuration.
-- | All parameters are bounded to physically meaningful ranges.
newtype SpringConfig = SpringConfig
  { tension :: Number    -- Stiffness [0, 1000], default 170
  , friction :: Number   -- Damping [0, 100], default 26
  , mass :: Number       -- Mass [0.1, 10], default 1
  }

derive instance Eq SpringConfig

-- | Cubic bezier control points for custom easing.
-- | P0 = (0, 0), P3 = (1, 1) are fixed.
-- | P1 and P2 are the control points we specify.
newtype BezierCurve = BezierCurve
  { x1 :: Number  -- P1.x ∈ [0, 1]
  , y1 :: Number  -- P1.y ∈ [-2, 2] (can overshoot)
  , x2 :: Number  -- P2.x ∈ [0, 1]
  , y2 :: Number  -- P2.y ∈ [-2, 2] (can overshoot)
  }

derive instance Eq BezierCurve

-- | Easing algebraic data type.
-- | Each constructor represents a different time-warping function.
data Easing
  = Linear
  | EaseIn
  | EaseOut
  | EaseInOut
  | EaseInQuad
  | EaseOutQuad
  | EaseInOutQuad
  | EaseInCubic
  | EaseOutCubic
  | EaseInOutCubic
  | EaseInQuart
  | EaseOutQuart
  | EaseInOutQuart
  | EaseInQuint
  | EaseOutQuint
  | EaseInOutQuint
  | EaseInExpo
  | EaseOutExpo
  | EaseInOutExpo
  | EaseInCirc
  | EaseOutCirc
  | EaseInOutCirc
  | EaseInBack
  | EaseOutBack
  | EaseInOutBack
  | EaseInElastic
  | EaseOutElastic
  | EaseInOutElastic
  | EaseInBounce
  | EaseOutBounce
  | EaseInOutBounce
  | Spring SpringConfig
  | CubicBezier BezierCurve
  | Steps Int           -- Step function with n steps
  | Custom EasingFunction

-- | Manual Eq instance because Custom contains a function type.
-- | Custom easings are never considered equal (functions aren't comparable).
instance Eq Easing where
  eq Linear Linear = true
  eq EaseIn EaseIn = true
  eq EaseOut EaseOut = true
  eq EaseInOut EaseInOut = true
  eq EaseInQuad EaseInQuad = true
  eq EaseOutQuad EaseOutQuad = true
  eq EaseInOutQuad EaseInOutQuad = true
  eq EaseInCubic EaseInCubic = true
  eq EaseOutCubic EaseOutCubic = true
  eq EaseInOutCubic EaseInOutCubic = true
  eq EaseInQuart EaseInQuart = true
  eq EaseOutQuart EaseOutQuart = true
  eq EaseInOutQuart EaseInOutQuart = true
  eq EaseInQuint EaseInQuint = true
  eq EaseOutQuint EaseOutQuint = true
  eq EaseInOutQuint EaseInOutQuint = true
  eq EaseInExpo EaseInExpo = true
  eq EaseOutExpo EaseOutExpo = true
  eq EaseInOutExpo EaseInOutExpo = true
  eq EaseInCirc EaseInCirc = true
  eq EaseOutCirc EaseOutCirc = true
  eq EaseInOutCirc EaseInOutCirc = true
  eq EaseInBack EaseInBack = true
  eq EaseOutBack EaseOutBack = true
  eq EaseInOutBack EaseInOutBack = true
  eq EaseInElastic EaseInElastic = true
  eq EaseOutElastic EaseOutElastic = true
  eq EaseInOutElastic EaseInOutElastic = true
  eq EaseInBounce EaseInBounce = true
  eq EaseOutBounce EaseOutBounce = true
  eq EaseInOutBounce EaseInOutBounce = true
  eq (Spring a) (Spring b) = a == b
  eq (CubicBezier a) (CubicBezier b) = a == b
  eq (Steps a) (Steps b) = a == b
  eq (Custom _) (Custom _) = false  -- Functions cannot be compared
  eq _ _ = false

-- | Apply easing function to progress.
-- | Pure function: same progress + same easing = same output.
applyEasing :: Easing -> Progress -> Progress
applyEasing easing (Progress t) = Progress (applyEasingNumber easing t)

-- | Internal: apply easing to raw number.
applyEasingNumber :: Easing -> Number -> Number
applyEasingNumber Linear t = t
applyEasingNumber EaseIn t = t * t
applyEasingNumber EaseOut t = t * (2.0 - t)
applyEasingNumber EaseInOut t =
  if t < 0.5
    then 2.0 * t * t
    else (-1.0) + (4.0 - 2.0 * t) * t
applyEasingNumber EaseInQuad t = t * t
applyEasingNumber EaseOutQuad t = t * (2.0 - t)
applyEasingNumber EaseInOutQuad t =
  if t < 0.5
    then 2.0 * t * t
    else (-1.0) + (4.0 - 2.0 * t) * t
applyEasingNumber EaseInCubic t = t * t * t
applyEasingNumber EaseOutCubic t =
  let t' = t - 1.0
  in t' * t' * t' + 1.0
applyEasingNumber EaseInOutCubic t =
  if t < 0.5
    then 4.0 * t * t * t
    else (t - 1.0) * (2.0 * t - 2.0) * (2.0 * t - 2.0) + 1.0
applyEasingNumber EaseInQuart t = t * t * t * t
applyEasingNumber EaseOutQuart t =
  let t' = t - 1.0
  in 1.0 - t' * t' * t' * t'
applyEasingNumber EaseInOutQuart t =
  if t < 0.5
    then 8.0 * t * t * t * t
    else 1.0 - 8.0 * (t - 1.0) * (t - 1.0) * (t - 1.0) * (t - 1.0)
applyEasingNumber EaseInQuint t = t * t * t * t * t
applyEasingNumber EaseOutQuint t =
  let t' = t - 1.0
  in 1.0 + t' * t' * t' * t' * t'
applyEasingNumber EaseInOutQuint t =
  if t < 0.5
    then 16.0 * t * t * t * t * t
    else 1.0 + 16.0 * (t - 1.0) * (t - 1.0) * (t - 1.0) * (t - 1.0) * (t - 1.0)
applyEasingNumber EaseInExpo t =
  if t == 0.0 then 0.0 else pow 2.0 (10.0 * (t - 1.0))
applyEasingNumber EaseOutExpo t =
  if t == 1.0 then 1.0 else 1.0 - pow 2.0 ((-10.0) * t)
applyEasingNumber EaseInOutExpo t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | t < 0.5 = pow 2.0 (20.0 * t - 10.0) / 2.0
  | otherwise = (2.0 - pow 2.0 ((-20.0) * t + 10.0)) / 2.0
applyEasingNumber EaseInCirc t = 1.0 - sqrt (1.0 - t * t)
applyEasingNumber EaseOutCirc t = sqrt (1.0 - (t - 1.0) * (t - 1.0))
applyEasingNumber EaseInOutCirc t =
  if t < 0.5
    then (1.0 - sqrt (1.0 - 4.0 * t * t)) / 2.0
    else (sqrt (1.0 - ((-2.0) * t + 2.0) * ((-2.0) * t + 2.0)) + 1.0) / 2.0
applyEasingNumber EaseInBack t =
  let c1 = 1.70158
      c3 = c1 + 1.0
  in c3 * t * t * t - c1 * t * t
applyEasingNumber EaseOutBack t =
  let c1 = 1.70158
      c3 = c1 + 1.0
      t' = t - 1.0
  in 1.0 + c3 * t' * t' * t' + c1 * t' * t'
applyEasingNumber EaseInOutBack t =
  let c1 = 1.70158
      c2 = c1 * 1.525
  in if t < 0.5
    then (2.0 * t) * (2.0 * t) * ((c2 + 1.0) * 2.0 * t - c2) / 2.0
    else ((2.0 * t - 2.0) * (2.0 * t - 2.0) * ((c2 + 1.0) * (t * 2.0 - 2.0) + c2) + 2.0) / 2.0
applyEasingNumber EaseInElastic t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise =
      let c4 = (2.0 * pi) / 3.0
      in (-(pow 2.0 (10.0 * t - 10.0))) * sin ((t * 10.0 - 10.75) * c4)
applyEasingNumber EaseOutElastic t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | otherwise =
      let c4 = (2.0 * pi) / 3.0
      in pow 2.0 ((-10.0) * t) * sin ((t * 10.0 - 0.75) * c4) + 1.0
applyEasingNumber EaseInOutElastic t
  | t == 0.0 = 0.0
  | t == 1.0 = 1.0
  | t < 0.5 =
      let c5 = (2.0 * pi) / 4.5
      in (-(pow 2.0 (20.0 * t - 10.0) * sin ((20.0 * t - 11.125) * c5))) / 2.0
  | otherwise =
      let c5 = (2.0 * pi) / 4.5
      in (pow 2.0 ((-20.0) * t + 10.0) * sin ((20.0 * t - 11.125) * c5)) / 2.0 + 1.0
applyEasingNumber EaseInBounce t = 1.0 - easeOutBounceImpl (1.0 - t)
applyEasingNumber EaseOutBounce t = easeOutBounceImpl t
applyEasingNumber EaseInOutBounce t =
  if t < 0.5
    then (1.0 - applyEasingNumber EaseOutBounce (1.0 - 2.0 * t)) / 2.0
    else (1.0 + applyEasingNumber EaseOutBounce (2.0 * t - 1.0)) / 2.0
applyEasingNumber (Spring (SpringConfig cfg)) t =
  -- Simplified spring approximation using damped harmonic oscillator
  let omega = sqrt cfg.tension / cfg.mass
      zeta = cfg.friction / (2.0 * sqrt (cfg.tension * cfg.mass))
      dampedFreq = omega * sqrt (1.0 - zeta * zeta)
      envelope = exp ((-zeta) * omega * t * 3.0) -- Scale time for reasonable animation
  in 1.0 - envelope * cos (dampedFreq * t * 3.0)
applyEasingNumber (CubicBezier (BezierCurve b)) t =
  -- Approximate cubic bezier using de Casteljau
  cubicBezierValue b.x1 b.y1 b.x2 b.y2 t
applyEasingNumber (Steps n) t =
  let step = Int.toNumber n
  in nativeFloor (t * step) / step
applyEasingNumber (Custom f) t = unwrap (f (Progress t))

-- | Bounce easing implementation.
-- | Extracted to avoid PureScript guard scoping issues with where clauses.
easeOutBounceImpl :: Number -> Number
easeOutBounceImpl t =
  let n1 = 7.5625
      d1 = 2.75
  in if t < 1.0 / d1
       then n1 * t * t
       else if t < 2.0 / d1
         then
           let t' = t - 1.5 / d1
           in n1 * t' * t' + 0.75
         else if t < 2.5 / d1
           then
             let t' = t - 2.25 / d1
             in n1 * t' * t' + 0.9375
           else
             let t' = t - 2.625 / d1
             in n1 * t' * t' + 0.984375

-- | Power function for easing calculations.
pow :: Number -> Number -> Number
pow base exponent = 
  -- JavaScript Math.pow semantics
  if base == 0.0 then 0.0
  else if exponent == 0.0 then 1.0
  else exp (exponent * ln base)

-- | Natural logarithm (approximation for pure implementation).
ln :: Number -> Number
ln x = nativeLog x

-- | Exponential function (approximation for pure implementation).
exp :: Number -> Number
exp x = nativeExp x

-- | Square root.
sqrt :: Number -> Number
sqrt x = nativeSqrt x

-- | Sine function.
sin :: Number -> Number
sin x = nativeSin x

-- | Cosine function.
cos :: Number -> Number
cos x = nativeCos x

-- | Pi constant.
pi :: Number
pi = 3.141592653589793

-- Native math functions (these would be FFI in real implementation,
-- but we include them here for completeness)
foreign import nativeLog :: Number -> Number
foreign import nativeExp :: Number -> Number
foreign import nativeSqrt :: Number -> Number
foreign import nativeSin :: Number -> Number
foreign import nativeCos :: Number -> Number
foreign import nativeFloor :: Number -> Number

-- | Cubic bezier evaluation using Newton-Raphson method.
cubicBezierValue :: Number -> Number -> Number -> Number -> Number -> Number
cubicBezierValue x1 y1 x2 y2 t =
  -- For x(t), solve for parameter u where x(u) = t
  -- Then return y(u)
  let u = solveCubicBezierX x1 x2 t 8 -- 8 iterations
  in bezierY y1 y2 u
  where
    -- | CSS timing function bezier: P0=(0,0), P1=(p1,y1), P2=(p2,y2), P3=(1,1)
    -- | B(t) = (1-t)³*P0 + 3*(1-t)²*t*P1 + 3*(1-t)*t²*P2 + t³*P3
    -- | Since P0=(0,0), the (1-t)³ term vanishes. Since P3=(1,1), the t³ term is just u3.
    bezierX :: Number -> Number -> Number -> Number
    bezierX p1 p2 u =
      let u2 = u * u
          u3 = u2 * u
          mt = 1.0 - u
          mt2 = mt * mt
          -- mt3 = mt2 * mt — vanishes because P0 = (0,0)
      in 3.0 * mt2 * u * p1 + 3.0 * mt * u2 * p2 + u3

    bezierY :: Number -> Number -> Number -> Number
    bezierY p1 p2 u =
      let u2 = u * u
          u3 = u2 * u
          mt = 1.0 - u
          mt2 = mt * mt
          -- mt3 = mt2 * mt — vanishes because P0 = (0,0)
      in 3.0 * mt2 * u * p1 + 3.0 * mt * u2 * p2 + u3

    solveCubicBezierX :: Number -> Number -> Number -> Int -> Number
    solveCubicBezierX p1 p2 target iterations =
      go t iterations
      where
        go :: Number -> Int -> Number
        go guess 0 = guess
        go guess n =
          let currentX = bezierX p1 p2 guess
              derivative = bezierDerivativeX p1 p2 guess
          in if abs derivative < 0.0001
               then guess
               else go (guess - (currentX - target) / derivative) (n - 1)

        bezierDerivativeX :: Number -> Number -> Number -> Number
        bezierDerivativeX pp1 pp2 u =
          let mt = 1.0 - u
          in 3.0 * mt * mt * pp1 + 6.0 * mt * u * (pp2 - pp1) + 3.0 * u * u * (1.0 - pp2)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §3 Transform Types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 2D affine transform represented as a 3x3 matrix (6 values).
-- | [ a c e ]
-- | [ b d f ]
-- | [ 0 0 1 ]
newtype Transform2D = Transform2D
  { a :: Number  -- scale x
  , b :: Number  -- skew y
  , c :: Number  -- skew x
  , d :: Number  -- scale y
  , e :: Number  -- translate x
  , f :: Number  -- translate y
  }

derive instance Eq Transform2D

-- | Transform composition is matrix multiplication.
-- | This is associative but NOT commutative.
instance Semigroup Transform2D where
  append (Transform2D t1) (Transform2D t2) = Transform2D
    { a: t1.a * t2.a + t1.c * t2.b
    , b: t1.b * t2.a + t1.d * t2.b
    , c: t1.a * t2.c + t1.c * t2.d
    , d: t1.b * t2.c + t1.d * t2.d
    , e: t1.a * t2.e + t1.c * t2.f + t1.e
    , f: t1.b * t2.e + t1.d * t2.f + t1.f
    }

-- | Identity transform.
instance Monoid Transform2D where
  mempty = Transform2D { a: 1.0, b: 0.0, c: 0.0, d: 1.0, e: 0.0, f: 0.0 }

-- | 3D transform for perspective and rotation.
-- | Represented as a 4x4 matrix (16 values).
newtype Transform3D = Transform3D
  { m11 :: Number, m12 :: Number, m13 :: Number, m14 :: Number
  , m21 :: Number, m22 :: Number, m23 :: Number, m24 :: Number
  , m31 :: Number, m32 :: Number, m33 :: Number, m34 :: Number
  , m41 :: Number, m42 :: Number, m43 :: Number, m44 :: Number
  }

derive instance Eq Transform3D

instance Semigroup Transform3D where
  append (Transform3D a) (Transform3D b) = Transform3D
    { m11: a.m11*b.m11 + a.m12*b.m21 + a.m13*b.m31 + a.m14*b.m41
    , m12: a.m11*b.m12 + a.m12*b.m22 + a.m13*b.m32 + a.m14*b.m42
    , m13: a.m11*b.m13 + a.m12*b.m23 + a.m13*b.m33 + a.m14*b.m43
    , m14: a.m11*b.m14 + a.m12*b.m24 + a.m13*b.m34 + a.m14*b.m44
    , m21: a.m21*b.m11 + a.m22*b.m21 + a.m23*b.m31 + a.m24*b.m41
    , m22: a.m21*b.m12 + a.m22*b.m22 + a.m23*b.m32 + a.m24*b.m42
    , m23: a.m21*b.m13 + a.m22*b.m23 + a.m23*b.m33 + a.m24*b.m43
    , m24: a.m21*b.m14 + a.m22*b.m24 + a.m23*b.m34 + a.m24*b.m44
    , m31: a.m31*b.m11 + a.m32*b.m21 + a.m33*b.m31 + a.m34*b.m41
    , m32: a.m31*b.m12 + a.m32*b.m22 + a.m33*b.m32 + a.m34*b.m42
    , m33: a.m31*b.m13 + a.m32*b.m23 + a.m33*b.m33 + a.m34*b.m43
    , m34: a.m31*b.m14 + a.m32*b.m24 + a.m33*b.m34 + a.m34*b.m44
    , m41: a.m41*b.m11 + a.m42*b.m21 + a.m43*b.m31 + a.m44*b.m41
    , m42: a.m41*b.m12 + a.m42*b.m22 + a.m43*b.m32 + a.m44*b.m42
    , m43: a.m41*b.m13 + a.m42*b.m23 + a.m43*b.m33 + a.m44*b.m43
    , m44: a.m41*b.m14 + a.m42*b.m24 + a.m43*b.m34 + a.m44*b.m44
    }

instance Monoid Transform3D where
  mempty = Transform3D
    { m11: 1.0, m12: 0.0, m13: 0.0, m14: 0.0
    , m21: 0.0, m22: 1.0, m23: 0.0, m24: 0.0
    , m31: 0.0, m32: 0.0, m33: 1.0, m34: 0.0
    , m41: 0.0, m42: 0.0, m43: 0.0, m44: 1.0
    }

-- | Transform origin point for rotations and scaling.
newtype TransformOrigin = TransformOrigin
  { x :: Number  -- 0.0 = left, 0.5 = center, 1.0 = right
  , y :: Number  -- 0.0 = top, 0.5 = center, 1.0 = bottom
  }

derive instance Eq TransformOrigin

-- | Opacity value, bounded [0, 1].
newtype Opacity = Opacity Number

derive instance Newtype Opacity _
derive instance Eq Opacity
derive instance Ord Opacity

-- | Opacity composes multiplicatively.
-- | This models layered transparency: 0.5 * 0.5 = 0.25.
instance Semigroup Opacity where
  append (Opacity a) (Opacity b) = Opacity (a * b)

-- | Full opacity (1.0) is the identity.
instance Monoid Opacity where
  mempty = Opacity 1.0

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §4 Core Animation Type
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | The animation value type: what gets animated.
-- | This is a Semigroup/Monoid to allow composition.
data AnimationValue
  = TransformValue Transform2D
  | Transform3DValue Transform3D
  | OpacityValue Opacity
  | CompositeValue (Array AnimationValue)

derive instance Eq AnimationValue

instance Semigroup AnimationValue where
  append (TransformValue a) (TransformValue b) = TransformValue (a <> b)
  append (Transform3DValue a) (Transform3DValue b) = Transform3DValue (a <> b)
  append (OpacityValue (Opacity a)) (OpacityValue (Opacity b)) = 
    OpacityValue (Opacity (a * b)) -- Opacity composes multiplicatively
  append (CompositeValue a) (CompositeValue b) = CompositeValue (a <> b)
  append a b = CompositeValue [a, b]

instance Monoid AnimationValue where
  mempty = CompositeValue []

-- | Core animation functor: Progress → a
-- | An animation is a function from normalized time to a value.
type AnimationF a = Progress -> a

-- | Complete animation with duration, easing, and value function.
-- | This is the primary type for defining animations.
newtype Animation a = Animation
  { dur :: Duration
  , easing :: Easing
  , sample :: AnimationF a
  }

-- | Run an animation at a specific progress point.
runAnimation :: forall a. Animation a -> Progress -> a
runAnimation (Animation anim) progress =
  anim.sample (applyEasing anim.easing progress)

-- | Get the duration of an animation.
duration :: forall a. Animation a -> Duration
duration (Animation anim) = anim.dur

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §5 Animation Instances (Lawful!)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Functor: transform the output value.
instance Functor Animation where
  map f (Animation anim) = Animation
    { dur: anim.dur
    , easing: anim.easing
    , sample: \p -> f (anim.sample p)
    }

-- | Apply: parallel composition with matching durations.
-- | Takes the longer duration, runs both animations in parallel.
instance Apply Animation where
  apply (Animation f) (Animation a) = Animation
    { dur: max f.dur a.dur
    , easing: Linear -- Combined easing is complex; use Linear by default
    , sample: \p -> (f.sample p) (a.sample p)
    }

-- | Applicative: lift a pure value into a zero-duration animation.
instance Applicative Animation where
  pure a = Animation
    { dur: Duration 0
    , easing: Linear
    , sample: \_ -> a
    }

-- | Semigroup: sequential composition.
-- | a <> b means "first a, then b".
instance Semigroup a => Semigroup (Animation a) where
  append a1 a2 = sequential a1 a2

-- | Monoid: empty animation (zero duration, identity value).
instance Monoid a => Monoid (Animation a) where
  mempty = Animation
    { dur: Duration 0
    , easing: Linear
    , sample: \_ -> mempty
    }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §6 Animation Combinators
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sequential composition: run a1 then a2.
-- | Time is remapped: [0, 0.5) → a1, [0.5, 1] → a2 (proportionally).
sequential :: forall a. Semigroup a => Animation a -> Animation a -> Animation a
sequential (Animation a1) (Animation a2) = Animation
  { dur: a1.dur <> a2.dur
  , easing: Linear
  , sample: \(Progress p) ->
      let (Duration d1) = a1.dur
          (Duration d2) = a2.dur
          totalDur = Int.toNumber (d1 + d2)
          boundary = if totalDur == 0.0 then 0.5 else Int.toNumber d1 / totalDur
      in if p < boundary
           then a1.sample (Progress (if boundary == 0.0 then 0.0 else p / boundary))
           else let p2 = if boundary == 1.0 then 1.0 else (p - boundary) / (1.0 - boundary)
                in a1.sample (Progress 1.0) <> a2.sample (Progress p2)
  }

-- | Parallel composition: run a1 and a2 simultaneously.
-- | Total duration is max of both. Values are combined via Semigroup.
parallel :: forall a. Semigroup a => Animation a -> Animation a -> Animation a
parallel (Animation a1) (Animation a2) = Animation
  { dur: max a1.dur a2.dur
  , easing: Linear
  , sample: \p -> a1.sample p <> a2.sample p
  }

-- | Stagger an array of animations.
-- | Each animation starts after a delay relative to the previous one.
stagger :: forall a. Monoid a => Duration -> Array (Animation a) -> Animation a
stagger delayBetween animations =
  case Array.uncons animations of
    Nothing -> mempty
    Just { head, tail } -> 
      foldl (\acc anim -> sequential acc (sequential (delay delayBetween mempty) anim)) head tail

-- | Add a delay before an animation.
delay :: forall a. Duration -> a -> Animation a
delay dur value = Animation
  { dur
  , easing: Linear
  , sample: \_ -> value
  }

-- | Scale the time of an animation (speed up or slow down).
-- | factor > 1 = faster, factor < 1 = slower.
timeScale :: forall a. Number -> Animation a -> Animation a
timeScale factor (Animation anim) =
  let (Duration d) = anim.dur
      newDur = Duration (max 0 (Int.floor (Int.toNumber d / factor)))
  in Animation
    { dur: newDur
    , easing: anim.easing
    , sample: anim.sample
    }

-- | Reverse an animation (play backwards).
reverse :: forall a. Animation a -> Animation a
reverse (Animation anim) = Animation
  { dur: anim.dur
  , easing: anim.easing
  , sample: \(Progress p) -> anim.sample (Progress (1.0 - p))
  }

-- | Ping-pong: play forward then backward.
pingPong :: forall a. Semigroup a => Animation a -> Animation a
pingPong anim = sequential anim (reverse anim)

-- | Repeat an animation n times.
repeat :: forall a. Semigroup a => Int -> Animation a -> Animation a
repeat n anim
  | n <= 0 = Animation { dur: Duration 0, easing: Linear, sample: \_ -> runAnimation anim (Progress 0.0) }
  | n == 1 = anim
  | otherwise = sequential anim (repeat (n - 1) anim)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §7 Stagger Patterns
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Direction for linear stagger patterns.
data StaggerDirection
  = LeftToRight
  | RightToLeft
  | CenterOut
  | EdgesIn

derive instance Eq StaggerDirection

-- | Stagger pattern determines delay for each element.
data StaggerPattern
  = LinearStagger StaggerDirection Duration
  | RandomStagger Int Duration   -- seed, max delay
  | CustomStagger (Int -> Int -> Duration)  -- index -> total -> delay

-- | Apply stagger pattern to get delay for element at index.
applyStagger :: StaggerPattern -> Int -> Int -> Duration
applyStagger pattern index total =
  case pattern of
    LinearStagger dir delayPer ->
      let (Duration d) = delayPer
          factor = case dir of
            LeftToRight -> index
            RightToLeft -> total - 1 - index
            CenterOut ->
              let center = Int.toNumber total / 2.0
              in Int.floor (abs (Int.toNumber index - center))
            EdgesIn ->
              let center = Int.toNumber total / 2.0
                  maxDist = center
              in Int.floor (maxDist - abs (Int.toNumber index - center))
      in Duration (d * factor)
    
    RandomStagger seed maxDelay ->
      let (Duration maxD) = maxDelay
          -- Simple deterministic pseudo-random based on seed and index
          hash = ((seed * 31) + index * 17) `mod` 10000
          factor = Int.toNumber hash / 10000.0
      in Duration (Int.floor (Int.toNumber maxD * factor))
    
    CustomStagger f -> f index total

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §8 Transform Animations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Translate along X axis.
translateX :: Number -> Number -> Duration -> Easing -> Animation Transform2D
translateX from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let value = from + (to - from) * p
      in Transform2D { a: 1.0, b: 0.0, c: 0.0, d: 1.0, e: value, f: 0.0 }
  }

-- | Translate along Y axis.
translateY :: Number -> Number -> Duration -> Easing -> Animation Transform2D
translateY from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let value = from + (to - from) * p
      in Transform2D { a: 1.0, b: 0.0, c: 0.0, d: 1.0, e: 0.0, f: value }
  }

-- | Translate in 2D.
translate 
  :: { fromX :: Number, fromY :: Number, toX :: Number, toY :: Number }
  -> Duration 
  -> Easing 
  -> Animation Transform2D
translate coords dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let x = coords.fromX + (coords.toX - coords.fromX) * p
          y = coords.fromY + (coords.toY - coords.fromY) * p
      in Transform2D { a: 1.0, b: 0.0, c: 0.0, d: 1.0, e: x, f: y }
  }

-- | Uniform scale animation.
scale :: Number -> Number -> Duration -> Easing -> Animation Transform2D
scale from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let value = from + (to - from) * p
      in Transform2D { a: value, b: 0.0, c: 0.0, d: value, e: 0.0, f: 0.0 }
  }

-- | Non-uniform scale animation.
scaleXY 
  :: { fromX :: Number, fromY :: Number, toX :: Number, toY :: Number }
  -> Duration 
  -> Easing 
  -> Animation Transform2D
scaleXY coords dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let sx = coords.fromX + (coords.toX - coords.fromX) * p
          sy = coords.fromY + (coords.toY - coords.fromY) * p
      in Transform2D { a: sx, b: 0.0, c: 0.0, d: sy, e: 0.0, f: 0.0 }
  }

-- | 2D rotation animation (radians).
rotate :: Number -> Number -> Duration -> Easing -> Animation Transform2D
rotate from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let angle = from + (to - from) * p
          c = cos angle
          s = sin angle
      in Transform2D { a: c, b: s, c: negate s, d: c, e: 0.0, f: 0.0 }
  }

-- | 3D rotation animation around arbitrary axis.
rotate3D
  :: { x :: Number, y :: Number, z :: Number }  -- axis (normalized)
  -> Number  -- from angle (radians)
  -> Number  -- to angle (radians)
  -> Duration
  -> Easing
  -> Animation Transform3D
rotate3D axis from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let angle = from + (to - from) * p
          c = cos angle
          s = sin angle
          t = 1.0 - c
          x = axis.x
          y = axis.y
          z = axis.z
      in Transform3D
        { m11: t*x*x + c,     m12: t*x*y - s*z,   m13: t*x*z + s*y,   m14: 0.0
        , m21: t*x*y + s*z,   m22: t*y*y + c,     m23: t*y*z - s*x,   m24: 0.0
        , m31: t*x*z - s*y,   m32: t*y*z + s*x,   m33: t*z*z + c,     m34: 0.0
        , m41: 0.0,           m42: 0.0,           m43: 0.0,           m44: 1.0
        }
  }

-- | Skew along X axis.
skewX :: Number -> Number -> Duration -> Easing -> Animation Transform2D
skewX from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let angle = from + (to - from) * p
          t = tan angle
      in Transform2D { a: 1.0, b: 0.0, c: t, d: 1.0, e: 0.0, f: 0.0 }
  }
  where
    tan :: Number -> Number
    tan x = sin x / cos x

-- | Skew along Y axis.
skewY :: Number -> Number -> Duration -> Easing -> Animation Transform2D
skewY from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let angle = from + (to - from) * p
          t = tan angle
      in Transform2D { a: 1.0, b: t, c: 0.0, d: 1.0, e: 0.0, f: 0.0 }
  }
  where
    tan :: Number -> Number
    tan x = sin x / cos x

-- | Opacity fade animation.
opacity :: Number -> Number -> Duration -> Easing -> Animation Opacity
opacity from to dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) ->
      let value = from + (to - from) * p
      in Opacity (max 0.0 (min 1.0 value))
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §9 Path Animations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A point in 2D space.
type Point2D = { x :: Number, y :: Number }

-- | Path segment types for bezier paths.
data PathSegment
  = MoveTo Point2D
  | LineTo Point2D
  | QuadraticTo Point2D Point2D           -- control, end
  | CubicTo Point2D Point2D Point2D       -- control1, control2, end
  | ArcTo Point2D Number Boolean Boolean  -- end, radius, largeArc, sweep
  | ClosePath

derive instance Eq PathSegment

-- | A complete animation path.
newtype AnimationPath = AnimationPath (Array PathSegment)

derive instance Newtype AnimationPath _
derive instance Eq AnimationPath

-- | Animate an element following a path.
-- | Returns the position along the path at each progress point.
followPath :: AnimationPath -> Duration -> Easing -> Animation Point2D
followPath (AnimationPath segments) dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) -> samplePath segments p
  }

-- | Sample a point along the path at progress t ∈ [0, 1].
samplePath :: Array PathSegment -> Number -> Point2D
samplePath segments t =
  case Array.head segments of
    Nothing -> { x: 0.0, y: 0.0 }
    Just (MoveTo start) -> samplePathFrom start (Array.drop 1 segments) t
    Just _ -> { x: 0.0, y: 0.0 } -- Path must start with MoveTo

samplePathFrom :: Point2D -> Array PathSegment -> Number -> Point2D
samplePathFrom start segments t =
  let total = length segments
  in if total == 0
       then start
       else 
         let segmentIndex = Int.floor (t * Int.toNumber total)
             boundedIndex = max 0 (min (total - 1) segmentIndex)
             localT = t * Int.toNumber total - Int.toNumber boundedIndex
         in case Array.index segments boundedIndex of
              Nothing -> start
              Just seg -> sampleSegment start seg localT

-- | Sample a single path segment.
sampleSegment :: Point2D -> PathSegment -> Number -> Point2D
sampleSegment start segment t =
  case segment of
    MoveTo p -> p
    LineTo end -> lerp2D start end t
    QuadraticTo control end -> quadraticBezier start control end t
    CubicTo c1 c2 end -> cubicBezier start c1 c2 end t
    ArcTo end _ _ _ -> lerp2D start end t -- Simplified arc
    ClosePath -> start

-- | Linear interpolation in 2D.
lerp2D :: Point2D -> Point2D -> Number -> Point2D
lerp2D a b t =
  { x: a.x + (b.x - a.x) * t
  , y: a.y + (b.y - a.y) * t
  }

-- | Quadratic bezier interpolation.
quadraticBezier :: Point2D -> Point2D -> Point2D -> Number -> Point2D
quadraticBezier p0 p1 p2 t =
  let mt = 1.0 - t
      mt2 = mt * mt
      t2 = t * t
  in { x: mt2 * p0.x + 2.0 * mt * t * p1.x + t2 * p2.x
     , y: mt2 * p0.y + 2.0 * mt * t * p1.y + t2 * p2.y
     }

-- | Cubic bezier interpolation.
cubicBezier :: Point2D -> Point2D -> Point2D -> Point2D -> Number -> Point2D
cubicBezier p0 p1 p2 p3 t =
  let mt = 1.0 - t
      mt2 = mt * mt
      mt3 = mt2 * mt
      t2 = t * t
      t3 = t2 * t
  in { x: mt3 * p0.x + 3.0 * mt2 * t * p1.x + 3.0 * mt * t2 * p2.x + t3 * p3.x
     , y: mt3 * p0.y + 3.0 * mt2 * t * p1.y + 3.0 * mt * t2 * p2.y + t3 * p3.y
     }

-- | Morph between two paths.
-- | Both paths must have the same structure (same number/types of segments).
morphPath :: AnimationPath -> AnimationPath -> Duration -> Easing -> Animation AnimationPath
morphPath (AnimationPath from) (AnimationPath to) dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) -> AnimationPath (Array.zipWith (morphSegment p) from to)
  }

-- | Morph between two path segments.
morphSegment :: Number -> PathSegment -> PathSegment -> PathSegment
morphSegment t seg1 seg2 =
  case seg1, seg2 of
    MoveTo a, MoveTo b -> MoveTo (lerp2D a b t)
    LineTo a, LineTo b -> LineTo (lerp2D a b t)
    QuadraticTo c1 e1, QuadraticTo c2 e2 -> 
      QuadraticTo (lerp2D c1 c2 t) (lerp2D e1 e2 t)
    CubicTo c1a c1b e1, CubicTo c2a c2b e2 ->
      CubicTo (lerp2D c1a c2a t) (lerp2D c1b c2b t) (lerp2D e1 e2 t)
    ArcTo e1 r1 la1 sw1, ArcTo e2 r2 _ _ ->
      ArcTo (lerp2D e1 e2 t) (r1 + (r2 - r1) * t) la1 sw1
    ClosePath, ClosePath -> ClosePath
    _, _ -> seg1 -- Incompatible segments, keep first

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §10 Animation Targeting
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | What can be animated in typography.
data AnimationTarget
  = TargetCharacter Int              -- Single character by index
  | TargetWord Int                   -- Single word by index
  | TargetLine Int                   -- Single line by index
  | TargetRange Int Int              -- Character range [start, end)
  | TargetAll                        -- All characters

derive instance Eq AnimationTarget

-- | Selector for which elements to animate.
data TargetSelector
  = SelectAll
  | SelectOdd
  | SelectEven
  | SelectEvery Int Int              -- every nth starting at offset
  | SelectRange Int Int              -- indices [start, end)
  | SelectIndices (Array Int)        -- specific indices
  | SelectWhere (Int -> Boolean)     -- custom predicate

-- | Create a targeted animation that applies to specific characters/words.
targeted :: forall a. TargetSelector -> Animation a -> Array Int -> Array (Animation a)
targeted selector anim indices =
  let matches = case selector of
        SelectAll -> indices
        SelectOdd -> Array.filter (\i -> i `mod` 2 == 1) indices
        SelectEven -> Array.filter (\i -> i `mod` 2 == 0) indices
        SelectEvery n offset -> Array.filter (\i -> (i - offset) `mod` n == 0) indices
        SelectRange start end -> Array.filter (\i -> i >= start && i < end) indices
        SelectIndices specific -> Array.filter (\i -> Array.elem i specific) indices
        SelectWhere pred -> Array.filter pred indices
  in map (\_ -> anim) matches
