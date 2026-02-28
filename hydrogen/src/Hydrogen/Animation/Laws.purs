-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // animation // laws
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Laws that must hold for the animation algebra.
-- |
-- | These serve as documentation, test specifications, and proof obligations.
-- | Every combinator must satisfy these laws for the algebra to be lawful.

module Hydrogen.Animation.Laws 
  ( module Hydrogen.Animation.Algebra
  ) where

-- Re-export the entire algebra module for consumers who want lawful animations.
-- This module provides documentation and law specifications.
-- The full algebra is re-exported so consumers get complete access.

import Hydrogen.Animation.Algebra 
  ( -- Time primitives
    Duration(Duration)
  , Milliseconds
  , Progress(Progress)
  , normalizeProgress
  
  -- Easing
  , Easing(Linear, EaseIn, EaseOut, EaseInOut, EaseInQuad, EaseOutQuad, EaseInOutQuad, EaseInCubic, EaseOutCubic, EaseInOutCubic, EaseInQuart, EaseOutQuart, EaseInOutQuart, EaseInQuint, EaseOutQuint, EaseInOutQuint, EaseInExpo, EaseOutExpo, EaseInOutExpo, EaseInCirc, EaseOutCirc, EaseInOutCirc, EaseInBack, EaseOutBack, EaseInOutBack, EaseInElastic, EaseOutElastic, EaseInOutElastic, EaseInBounce, EaseOutBounce, EaseInOutBounce, Spring, CubicBezier, Steps, Custom)
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
  ) as Hydrogen.Animation.Algebra

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §1 Semigroup Laws for Animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Sequential composition (<>) forms a Semigroup.
-- This is the foundation of animation composition.

{-|
Law: Associativity of Sequential Composition

For all animations a, b, c:
  (a <> b) <> c ≡ a <> (b <> c)

Proof sketch:
  Let dur(a) = d_a, dur(b) = d_b, dur(c) = d_c
  Total duration = d_a + d_b + d_c (same for both)
  
  At any time t ∈ [0, 1]:
  - If t ∈ [0, d_a/total): sample a
  - If t ∈ [d_a/total, (d_a+d_b)/total): sample b  
  - If t ∈ [(d_a+d_b)/total, 1]: sample c
  
  The grouping doesn't change which animation plays at time t.

Example:
  Given:
    fadeIn  = opacity 0 1 (Duration 200) EaseIn
    hold    = opacity 1 1 (Duration 100) Linear
    fadeOut = opacity 1 0 (Duration 200) EaseOut
  
  Then:
    (fadeIn <> hold) <> fadeOut ≡ fadeIn <> (hold <> fadeOut)
    
  Both produce a 500ms animation that fades in, holds, fades out.
-}

{-|
Law: Duration Homomorphism

For all animations a, b:
  duration (a <> b) ≡ duration a <> duration b
  
This follows from Duration being a Monoid under addition.
Sequential composition adds durations.
-}

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §2 Monoid Laws for Animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- With the identity element (mempty), Animation forms a Monoid.

{-|
Law: Right Identity

For all animations a:
  a <> mempty ≡ a

Proof:
  mempty has Duration 0, so:
  - Total duration = dur(a) + 0 = dur(a)
  - a occupies [0, 1] of the time
  - mempty contributes nothing
  
Example:
  fadeIn <> mempty ≡ fadeIn
-}

{-|
Law: Left Identity

For all animations a:
  mempty <> a ≡ a

Proof:
  mempty has Duration 0, so:
  - Total duration = 0 + dur(a) = dur(a)
  - mempty occupies [0, 0] (zero width)
  - a occupies [0, 1]
  
Example:
  mempty <> fadeIn ≡ fadeIn
-}

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §3 Functor Laws
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Animation is a Functor, allowing transformation of output values.

{-|
Law: Identity

  map identity a ≡ a

Proof:
  map identity wraps the sample function: sample p → identity (sample p)
  identity x = x, so this is the same as the original sample.

Example:
  map identity fadeIn ≡ fadeIn
-}

{-|
Law: Composition

  map (f >>> g) a ≡ map g (map f a)

Proof:
  Left side: sample p → (f >>> g) (sample p) = g (f (sample p))
  Right side: 
    map f a → sample p → f (sample p)
    map g of that → sample p → g (f (sample p))
  Both produce g (f (sample p)).

Example:
  map (clamp >>> round) position ≡ map round (map clamp position)
-}

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §4 Applicative Laws
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Animation is Applicative, enabling parallel composition of effects.

{-|
Law: Identity

  pure identity <*> a ≡ a

Proof:
  pure identity creates a zero-duration animation returning identity.
  <*> combines: at each progress p, applies identity to (sample p).
  identity (sample p) = sample p.
  Duration = max(0, dur(a)) = dur(a).

Example:
  pure identity <*> fadeIn ≡ fadeIn
-}

{-|
Law: Homomorphism

  pure f <*> pure x ≡ pure (f x)

Proof:
  pure f: zero duration, returns f
  pure x: zero duration, returns x
  <*> applies f to x at every progress
  Result: zero duration, returns f x
  This is exactly pure (f x).
-}

{-|
Law: Interchange

  a <*> pure x ≡ pure (\f -> f x) <*> a

Both apply the function from 'a' to the value 'x'.
-}

{-|
Law: Composition

  pure (>>>) <*> a <*> b <*> c ≡ a <*> (b <*> c)

Composition of animations respects function composition.
-}

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §5 Transform2D Semigroup Laws
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Transform2D composition (matrix multiplication) forms a Semigroup.
-- NOTE: NOT commutative — order matters!

{-|
Law: Associativity of Transform Composition

  (t1 <> t2) <> t3 ≡ t1 <> (t2 <> t3)

This is matrix multiplication, which is associative.
Both produce the same resulting transformation.

Example:
  (rotate 45° <> scale 2) <> translate 10 0
  ≡ rotate 45° <> (scale 2 <> translate 10 0)

IMPORTANT: Transform composition is NOT commutative!
  rotate 45° <> translate 10 0 ≢ translate 10 0 <> rotate 45°
  
  First case: rotate, then translate along rotated axis
  Second case: translate, then rotate around origin
-}

{-|
Law: Identity Transform

  mempty <> t ≡ t
  t <> mempty ≡ t

The identity matrix leaves all transforms unchanged.
-}

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §6 Parallel Composition Laws
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Parallel composition runs animations simultaneously.

{-|
Law: Parallel Associativity

  parallel (parallel a b) c ≡ parallel a (parallel b c)

All three animations run at the same time; grouping doesn't matter.
-}

{-|
Law: Parallel Duration

  duration (parallel a b) ≡ max (duration a) (duration b)

The parallel combination lasts as long as the longest component.
-}

{-|
Law: Parallel with Identity

For Monoid values:
  parallel a (pure mempty) ≡ a

Composing with an identity animation has no effect.
-}

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §7 Easing Laws
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Easing functions must preserve boundaries and be deterministic.

{-|
Law: Boundary Preservation

For all easing functions f:
  f(0) ≡ 0
  f(1) ≡ 1

Animations start at their start state and end at their end state.
Easing affects the journey, not the destination.
-}

{-|
Law: Determinism

For all easing functions f and progress values p:
  f(p) at time T₁ ≡ f(p) at time T₂

Easing functions are pure. Same input, same output. Always.
-}

{-|
Law: Linear Identity

  applyEasing Linear p ≡ p

Linear easing is the identity on progress.
-}

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §8 Stagger Laws
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Stagger patterns are deterministic functions from index to delay.

{-|
Law: Stagger Determinism

For stagger pattern s, index i, total n:
  applyStagger s i n at time T₁ ≡ applyStagger s i n at time T₂

Stagger delays are computed purely from the pattern and indices.
No randomness (RandomStagger uses deterministic seeded pseudo-random).
-}

{-|
Law: LinearStagger LeftToRight Order

For LinearStagger LeftToRight d:
  applyStagger pattern 0 n < applyStagger pattern 1 n < ... < applyStagger pattern (n-1) n

Each successive character starts after the previous one.
-}

{-|
Law: LinearStagger Symmetry

For CenterOut and EdgesIn patterns:
  applyStagger (LinearStagger CenterOut d) i n 
  ≡ applyStagger (LinearStagger EdgesIn d) (mirror i n) n
  
where mirror i n = (n - 1) - i

CenterOut and EdgesIn are inverses of each other.
-}

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §9 Time Laws
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Time is bounded and normalized.

{-|
Law: Progress Boundedness

For all Progress values p:
  0 ≤ unwrap p ≤ 1

normalizeProgress ensures this invariant.
-}

{-|
Law: Duration Non-negativity

For all Duration values d:
  unwrap d ≥ 0

Negative durations are not representable.
-}

{-|
Law: Reverse Involution

  reverse (reverse a) ≡ a

Reversing twice returns to the original animation.

Proof:
  reverse a: sample p → a.sample(1 - p)
  reverse (reverse a): sample p → (reverse a).sample(1 - p) 
                                → a.sample(1 - (1 - p))
                                → a.sample(p)
  This is the original animation.
-}

{-|
Law: TimeScale Composition

  timeScale s1 (timeScale s2 a) ≡ timeScale (s1 * s2) a

Scaling time is multiplicative.
-}

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §10 Path Laws
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Path animations follow continuous curves.

{-|
Law: Path Boundary Values

For followPath path dur easing:
  runAnimation (followPath path dur easing) (Progress 0) ≡ startPoint path
  runAnimation (followPath path dur easing) (Progress 1) ≡ endPoint path

Path animations start at the path start and end at the path end.
-}

{-|
Law: Path Continuity

For any ε > 0, there exists δ > 0 such that:
  |p1 - p2| < δ ⟹ |followPath(p1) - followPath(p2)| < ε

Path animations are continuous (no teleportation).
-}

{-|
Law: Morph Identity

  morphPath path path dur easing ≡ followPath path dur easing

Morphing a path to itself is equivalent to following that path.
(Though technically morphPath returns the path, not a point.)
-}
