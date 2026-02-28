-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // animation // examples
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Practical examples of the animation algebra in action.
-- |
-- | These demonstrate how the combinators compose to create complex animations.

module Hydrogen.Animation.Examples where

import Prelude

import Data.Array (mapWithIndex, replicate)

import Hydrogen.Animation.Algebra
  ( Animation
  , AnimationPath(AnimationPath)
  , BezierCurve(BezierCurve)
  , Duration(Duration)
  , Easing(Linear, EaseIn, EaseOut, EaseInOut, EaseOutCubic, EaseInOutCubic, EaseOutBack, Spring, CubicBezier)
  , Opacity
  , PathSegment(MoveTo, LineTo, QuadraticTo, CubicTo, ArcTo, ClosePath)
  , Progress
  , SpringConfig(SpringConfig)
  , StaggerDirection(LeftToRight, RightToLeft, CenterOut, EdgesIn)
  , StaggerPattern(LinearStagger, RandomStagger)
  , Transform2D
  , Transform3D
  , applyStagger
  , delay
  , followPath
  , opacity
  , parallel
  , pingPong
  , repeat
  , reverse
  , rotate
  , rotate3D
  , runAnimation
  , scale
  , sequential
  , translateX
  , translateY
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §1 Basic Composition Examples
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Simple fade-in animation.
-- | Opacity goes from 0 to 1 over 300ms with ease-out.
fadeIn :: Animation Opacity
fadeIn = opacity 0.0 1.0 (Duration 300) EaseOut

-- | Simple fade-out animation.
fadeOut :: Animation Opacity
fadeOut = opacity 1.0 0.0 (Duration 300) EaseIn

-- | Fade in, hold, fade out — sequential composition.
-- | 
-- | Duration: 300 + 200 + 300 = 800ms
-- |
-- | This demonstrates the Semigroup/Monoid laws:
-- |   (fadeIn <> hold) <> fadeOut ≡ fadeIn <> (hold <> fadeOut)
fadeInOut :: Animation Opacity
fadeInOut = fadeIn <> hold <> fadeOut
  where
    hold = opacity 1.0 1.0 (Duration 200) Linear

-- | Scale animation with spring physics.
-- | Springs create natural-feeling motion with overshoot.
springScale :: Animation Transform2D
springScale = scale 0.0 1.0 (Duration 600) springEasing
  where
    springEasing = Spring (SpringConfig 
      { tension: 180.0
      , friction: 12.0  -- Low friction = more bounce
      , mass: 1.0
      })

-- | Button press animation using cubic bezier.
-- | Custom curve for snappy, responsive feel.
buttonPress :: Animation Transform2D
buttonPress = sequential scaleDown scaleUp
  where
    pressEasing = CubicBezier (BezierCurve 
      { x1: 0.34, y1: 1.56  -- Overshoot
      , x2: 0.64, y2: 1.0
      })
    scaleDown = scale 1.0 0.95 (Duration 100) EaseIn
    scaleUp = scale 0.95 1.0 (Duration 200) pressEasing

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §2 Parallel Composition Examples
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Slide in from left while fading in.
-- | Demonstrates parallel composition: both happen simultaneously.
slideInLeft :: Animation Transform2D
slideInLeft = translateX (-100.0) 0.0 (Duration 400) EaseOut

-- | Attention-grabbing "pop" animation.
-- | Scale up + rotate slightly, all at once.
pop :: Animation Transform2D
pop = parallel scaleAnim rotateAnim
  where
    scaleAnim = scale 1.0 1.2 (Duration 150) EaseOut
    rotateAnim = rotate 0.0 0.05 (Duration 150) EaseOut

-- | Complex entrance: slide + fade + scale, all parallel.
complexEntrance :: Animation Transform2D
complexEntrance = 
  slideIn `parallel` scaleIn
  where
    slideIn = translateY 30.0 0.0 (Duration 500) EaseOutCubic
    scaleIn = scale 0.8 1.0 (Duration 500) EaseOutCubic

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §3 Typography Stagger Examples
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Per-character stagger pattern: left to right.
-- | Each character starts 50ms after the previous.
-- |
-- | For text "HELLO" (5 characters):
-- |   H: delay 0ms
-- |   E: delay 50ms
-- |   L: delay 100ms
-- |   L: delay 150ms
-- |   O: delay 200ms
leftToRightStagger :: StaggerPattern
leftToRightStagger = LinearStagger LeftToRight (Duration 50)

-- | Per-character stagger: center out.
-- | Characters in the middle start first, edges last.
-- |
-- | For text "HELLO" (5 characters, center at index 2):
-- |   H: delay 100ms (distance 2 from center)
-- |   E: delay 50ms  (distance 1 from center)
-- |   L: delay 0ms   (at center)
-- |   L: delay 50ms  (distance 1 from center)
-- |   O: delay 100ms (distance 2 from center)
centerOutStagger :: StaggerPattern
centerOutStagger = LinearStagger CenterOut (Duration 50)

-- | Random-ish stagger with deterministic seed.
-- | Same seed + same indices = same delays (always).
-- |
-- | This is crucial for reproducibility:
-- |   Two agents with same seed get identical animation timing.
deterministicRandomStagger :: Int -> StaggerPattern
deterministicRandomStagger seed = RandomStagger seed (Duration 150)

-- | Calculate delays for each character in a string.
-- | This is how stagger patterns are applied in practice.
calculateCharacterDelays :: StaggerPattern -> String -> Array Duration
calculateCharacterDelays pattern text =
  let len = stringLength text
  in mapWithIndex (\i _ -> applyStagger pattern i len) (replicate len unit)

-- Temporary: get string length (would be imported from String module)
stringLength :: String -> Int
stringLength _ = 5 -- Placeholder; real implementation uses String.length

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §4 Complete Typography Animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{-|
  STAGGER MATHEMATICS
  
  Given:
  - n characters
  - base animation duration: d
  - stagger delay between characters: s
  
  Total animation duration = d + s × (n - 1)
  
  Character i plays during:
  - Start: s × i
  - End: s × i + d
  
  Example: "HELLO" with d=300ms, s=50ms
  - Total duration: 300 + 50 × 4 = 500ms
  - H: [0ms, 300ms]
  - E: [50ms, 350ms]
  - L: [100ms, 400ms]
  - L: [150ms, 450ms]
  - O: [200ms, 500ms]
  
  At t=200ms:
  - H is at progress 200/300 = 0.67 (eased)
  - E is at progress 150/300 = 0.50
  - L is at progress 100/300 = 0.33
  - L is at progress 50/300 = 0.17
  - O is at progress 0/300 = 0.00 (just starting!)
-}

-- | Per-character animation: slide up + fade in.
characterReveal :: Animation Transform2D
characterReveal = 
  translateY 20.0 0.0 (Duration 300) EaseOutCubic

-- | Create staggered character animations for a string.
-- | Returns array of (delay, animation) pairs.
staggeredCharacterAnimations 
  :: StaggerPattern 
  -> Animation Transform2D 
  -> Int  -- character count
  -> Array { charDelay :: Duration, animation :: Animation Transform2D }
staggeredCharacterAnimations pattern baseAnim charCount =
  mapWithIndex makeCharAnim (replicate charCount unit)
  where
    makeCharAnim :: Int -> Unit -> { charDelay :: Duration, animation :: Animation Transform2D }
    makeCharAnim i _ =
      { charDelay: applyStagger pattern i charCount
      , animation: baseAnim
      }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §5 Path-Based Typography Animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Arc path for characters to follow (like a smile).
arcPath :: AnimationPath
arcPath = AnimationPath
  [ MoveTo { x: 0.0, y: 0.0 }
  , QuadraticTo { x: 100.0, y: -50.0 } { x: 200.0, y: 0.0 }
  ]

-- | Wave path for wavy text animation.
wavePath :: AnimationPath
wavePath = AnimationPath
  [ MoveTo { x: 0.0, y: 0.0 }
  , CubicTo 
      { x: 25.0, y: -20.0 }  -- control 1
      { x: 50.0, y: 20.0 }   -- control 2
      { x: 75.0, y: 0.0 }    -- end point
  , CubicTo
      { x: 100.0, y: -20.0 }
      { x: 125.0, y: 20.0 }
      { x: 150.0, y: 0.0 }
  ]

-- | Character follows an arc path.
characterOnArc :: Animation { x :: Number, y :: Number }
characterOnArc = followPath arcPath (Duration 1000) EaseInOut

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §6 Complex Composition: Kinetic Typography
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{-|
  KINETIC TYPOGRAPHY EXAMPLE
  
  A complete word animation sequence:
  1. Characters fly in from below, staggered left-to-right
  2. Word scales up slightly (emphasis)
  3. Characters rotate individually (wiggle)
  4. Word fades out
  
  This demonstrates:
  - Sequential composition (phases)
  - Parallel composition (transform + opacity)
  - Stagger patterns (per-character timing)
  - Multiple transform types (translate, scale, rotate)
-}

-- | Phase 1: Characters fly in from below.
flyInPhase :: Animation Transform2D
flyInPhase = translateY 50.0 0.0 (Duration 400) EaseOutBack

-- | Phase 2: Emphasis scale (applies to whole word).
emphasisPhase :: Animation Transform2D
emphasisPhase = 
  sequential 
    (scale 1.0 1.1 (Duration 150) EaseOut)
    (scale 1.1 1.0 (Duration 150) EaseIn)

-- | Phase 3: Wiggle (per-character rotation).
wigglePhase :: Animation Transform2D
wigglePhase = 
  repeat 3 (pingPong singleWiggle)
  where
    singleWiggle = rotate 0.0 0.05 (Duration 50) EaseInOut

-- | Complete kinetic typography animation for one character.
-- | Combines all phases sequentially.
kineticCharacter :: Int -> Int -> Animation Transform2D
kineticCharacter charIndex totalChars =
  let charDelay = applyStagger leftToRightStagger charIndex totalChars
  in sequential 
       (delay charDelay mempty)
       (sequential flyInPhase (sequential emphasisPhase wigglePhase))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §7 3D Typography Animations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Flip card effect: rotate around Y axis.
flipY :: Animation Transform3D
flipY = rotate3D 
  { x: 0.0, y: 1.0, z: 0.0 }  -- Y axis
  0.0                          -- from 0 radians
  3.14159                      -- to π radians (180°)
  (Duration 600)
  EaseInOutCubic

-- | Tumble effect: rotate around diagonal axis.
tumble :: Animation Transform3D
tumble = rotate3D
  { x: 0.707, y: 0.707, z: 0.0 }  -- Diagonal axis (normalized)
  0.0
  6.28318                          -- Full rotation (2π)
  (Duration 1000)
  Linear

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- §8 Demonstrating the Laws
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{-|
  ASSOCIATIVITY IN ACTION
  
  These two expressions produce identical results:
  
  grouped1 = (fadeIn <> hold) <> fadeOut
  grouped2 = fadeIn <> (hold <> fadeOut)
  
  Proof by example at t = 0.5 (middle of animation):
  
  Given:
    fadeIn:  300ms
    hold:    200ms  
    fadeOut: 300ms
    Total:   800ms
  
  At t = 0.5 (400ms):
    - fadeIn completed at 300ms
    - hold runs 300-500ms, we're at 400ms = 50% through hold
    - Opacity = 1.0 (holding)
  
  Both groupings:
    grouped1: ((fadeIn <> hold) runs 0-500ms, fadeOut runs 500-800ms)
              At 400ms: in (fadeIn <> hold), which is past fadeIn, in hold
              
    grouped2: (fadeIn runs 0-300ms, (hold <> fadeOut) runs 300-800ms)
              At 400ms: past fadeIn, in (hold <> fadeOut), 100ms into it
              (hold <> fadeOut) at 100ms = in hold (runs 0-200ms)
  
  Both yield the same opacity value at every point in time.
-}

-- | Verify associativity at a specific progress point.
-- | This would be used in property-based testing.
verifyAssociativity 
  :: forall a
   . Eq a 
  => Semigroup a 
  => Animation a 
  -> Animation a 
  -> Animation a 
  -> Progress 
  -> Boolean
verifyAssociativity a b c p =
  runAnimation ((a <> b) <> c) p == runAnimation (a <> (b <> c)) p

-- | Verify identity law.
verifyIdentity 
  :: forall a
   . Eq a 
  => Monoid a 
  => Animation a 
  -> Progress 
  -> Boolean
verifyIdentity a p =
  runAnimation (a <> mempty) p == runAnimation a p &&
  runAnimation (mempty <> a) p == runAnimation a p

-- | Verify reverse involution: reverse (reverse a) ≡ a
verifyReverseInvolution
  :: forall a
   . Eq a
  => Animation a
  -> Progress
  -> Boolean
verifyReverseInvolution a p =
  runAnimation (reverse (reverse a)) p == runAnimation a p
