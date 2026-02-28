-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // element // carousel // render // layout
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Layout — 3D spatial transforms for slide positioning.
-- |
-- | ## Design Philosophy
-- |
-- | Layout paths determine how slides are arranged in 3D space.
-- | Each path computes per-slide CSS transforms based on:
-- | - Slide index relative to current
-- | - Total slide count
-- | - Path-specific geometry (radius, angle, etc.)
-- |
-- | ## Layout Paths
-- |
-- | - Circular: Slides on XY plane circle
-- | - Helix: 3D spiral upward
-- | - Sphere: Fibonacci distribution on sphere surface
-- | - Cylinder: Wrapped around vertical cylinder
-- | - Möbius: Twisted loop with half-twist
-- | - Arc: Partial circle (-60° to +60°)
-- | - Stack: Tinder-style stacked cards
-- |
-- | ## Dependencies
-- |
-- | - Carousel.Types (LayoutPath)

module Hydrogen.Element.Compound.Carousel.Render.Layout
  ( -- * Layout Transform
    computeLayoutTransform
  
  -- * Individual Transforms
  , circularTransform
  , helixTransform
  , sphereTransform
  , cylinderTransform
  , mobiusTransform
  , arcTransform
  , stackTransform
  
  -- * Math Helpers
  , sin
  , cos
  , asin
  , acos
  , abs
  , absInt
  , toInt
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  , (<)
  , negate
  )

import Data.Int (toNumber)
import Data.Ord (max, min)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Element.Compound.Carousel.Types 
  ( LayoutPath
      ( PathCircular
      , PathHelix
      , PathSphere
      , PathCylinder
      , PathMobius
      , PathArc
      , PathStack
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // layout transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute slide-specific 3D transform based on layout path
computeLayoutTransform :: LayoutPath -> Int -> Int -> Int -> Array (Tuple String String)
computeLayoutTransform layoutPath slideIndex' currentIndex total =
  let 
    offset = slideIndex' - currentIndex
    offsetF = toNumber offset
    totalF = toNumber total
  in case layoutPath of
    PathCircular -> circularTransform offsetF totalF
    PathHelix -> helixTransform offsetF totalF
    PathSphere -> sphereTransform offsetF totalF
    PathCylinder -> cylinderTransform offsetF totalF
    PathMobius -> mobiusTransform offsetF totalF
    PathArc -> arcTransform offsetF totalF
    PathStack -> stackTransform offsetF
    _ -> []  -- Linear/Grid/Masonry handled by track

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // circular path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Circular arrangement (slides arranged in a circle on XY plane)
circularTransform :: Number -> Number -> Array (Tuple String String)
circularTransform offset total =
  let
    anglePerSlide = 360.0 / total
    angle = offset * anglePerSlide
    radius = 300.0
    angleRad = angle * 3.14159 / 180.0
    x = radius * sin angleRad
    z = radius * (1.0 - cos angleRad)
  in
    [ Tuple "transform" ("translateX(" <> show x <> "px) translateZ(" <> show (negate z) <> "px) rotateY(" <> show angle <> "deg)")
    , Tuple "position" "absolute"
    , Tuple "left" "50%"
    , Tuple "margin-left" "-150px"
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // helix path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Helix/spiral arrangement (slides spiral upward in 3D)
helixTransform :: Number -> Number -> Array (Tuple String String)
helixTransform offset total =
  let
    anglePerSlide = 360.0 / total
    angle = offset * anglePerSlide
    radius = 250.0
    heightStep = 80.0
    angleRad = angle * 3.14159 / 180.0
    x = radius * sin angleRad
    z = radius * (1.0 - cos angleRad)
    y = offset * heightStep
  in
    [ Tuple "transform" ("translate3d(" <> show x <> "px, " <> show y <> "px, " <> show (negate z) <> "px) rotateY(" <> show angle <> "deg)")
    , Tuple "position" "absolute"
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // sphere path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sphere arrangement (slides on surface of a sphere)
sphereTransform :: Number -> Number -> Array (Tuple String String)
sphereTransform offset total =
  let
    goldenRatio = 1.618033988749895
    i = offset + total / 2.0
    theta = 2.0 * 3.14159 * i / goldenRatio
    phi = acos (1.0 - 2.0 * (i + 0.5) / total)
    radius = 350.0
    x = radius * sin phi * cos theta
    y = radius * sin phi * sin theta
    z = radius * cos phi
    rotateX' = phi * 180.0 / 3.14159 - 90.0
    rotateY' = theta * 180.0 / 3.14159
  in
    [ Tuple "transform" ("translate3d(" <> show x <> "px, " <> show y <> "px, " <> show z <> "px) rotateX(" <> show rotateX' <> "deg) rotateY(" <> show rotateY' <> "deg)")
    , Tuple "position" "absolute"
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // cylinder path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cylinder arrangement (slides wrapped around a cylinder)
cylinderTransform :: Number -> Number -> Array (Tuple String String)
cylinderTransform offset total =
  let
    anglePerSlide = 360.0 / total
    angle = offset * anglePerSlide
    radius = 300.0
    angleRad = angle * 3.14159 / 180.0
    x = radius * sin angleRad
    z = negate (radius * cos angleRad)
  in
    [ Tuple "transform" ("translateX(" <> show x <> "px) translateZ(" <> show z <> "px) rotateY(" <> show angle <> "deg)")
    , Tuple "position" "absolute"
    , Tuple "backface-visibility" "hidden"
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // mobius path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Möbius strip arrangement (twisted loop)
mobiusTransform :: Number -> Number -> Array (Tuple String String)
mobiusTransform offset total =
  let
    anglePerSlide = 360.0 / total
    angle = offset * anglePerSlide
    radius = 300.0
    angleRad = angle * 3.14159 / 180.0
    twistAngle = angle / 2.0
    x = radius * sin angleRad
    z = negate (radius * cos angleRad)
  in
    [ Tuple "transform" ("translateX(" <> show x <> "px) translateZ(" <> show z <> "px) rotateY(" <> show angle <> "deg) rotateZ(" <> show twistAngle <> "deg)")
    , Tuple "position" "absolute"
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // arc path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Arc arrangement (partial circle)
arcTransform :: Number -> Number -> Array (Tuple String String)
arcTransform offset _total =
  let
    angleRange = 120.0
    anglePerOffset = 30.0
    angle = offset * anglePerOffset
    clampedAngle = max (negate (angleRange / 2.0)) (min (angleRange / 2.0) angle)
    radius = 400.0
    angleRad = clampedAngle * 3.14159 / 180.0
    x = radius * sin angleRad
    z = radius * (1.0 - cos angleRad)
  in
    [ Tuple "transform" ("translateX(" <> show x <> "px) translateZ(" <> show (negate z) <> "px) rotateY(" <> show clampedAngle <> "deg)")
    , Tuple "position" "absolute"
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // stack path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stack arrangement (Tinder-style stacked cards)
stackTransform :: Number -> Array (Tuple String String)
stackTransform offset =
  let
    zOffset = negate (offset * 20.0)
    scale = 1.0 - (abs offset * 0.05)
    yOffset = offset * 10.0
  in
    [ Tuple "transform" ("translateY(" <> show yOffset <> "px) translateZ(" <> show zOffset <> "px) scale(" <> show scale <> ")")
    , Tuple "position" "absolute"
    , Tuple "z-index" (show (100 - absInt (toInt offset)))
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // math helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Simple sine function approximation (Taylor series)
sin :: Number -> Number
sin x = sinApprox (normalizeAngle x)
  where
    normalizeAngle a = a - (toNumber (toInt (a / (2.0 * 3.14159)))) * 2.0 * 3.14159
    sinApprox a = a - (a * a * a / 6.0) + (a * a * a * a * a / 120.0)

-- | Simple cosine function approximation
cos :: Number -> Number
cos x = sin (x + 3.14159 / 2.0)

-- | Simple acos approximation
acos :: Number -> Number
acos x = 3.14159 / 2.0 - asin x

-- | Simple asin approximation (Taylor series)
asin :: Number -> Number
asin x = x + (x * x * x / 6.0) + (3.0 * x * x * x * x * x / 40.0)

-- | Absolute value for Number
abs :: Number -> Number
abs x = if x < 0.0 then negate x else x

-- | Absolute value for Int
absInt :: Int -> Int
absInt x = if x < 0 then negate x else x

-- | Convert Number to Int (truncate toward zero)
toInt :: Number -> Int
toInt n = if n >= 0.0 then toIntPos n 0 else negate (toIntPos (negate n) 0)
  where
    toIntPos :: Number -> Int -> Int
    toIntPos x acc = if x < 1.0 then acc else toIntPos (x - 1.0) (acc + 1)
