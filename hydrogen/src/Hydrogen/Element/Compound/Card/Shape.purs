-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // component // card // shape
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Shape — Geometric masking for cards.
-- |
-- | ## Design Philosophy
-- |
-- | Cards can be clipped to arbitrary shapes using CSS clip-path or
-- | SVG masks. This module provides configuration for:
-- | - Predefined shapes (circle, star, hexagon, heart)
-- | - Custom SVG paths
-- | - Animated shape morphing
-- |
-- | ## Use Cases
-- |
-- | - Star-shaped product cards
-- | - Hexagonal profile cards
-- | - Custom branded shapes
-- | - Shape transitions on hover
-- |
-- | ## CSS Implementation
-- |
-- | Shapes are rendered as clip-path or SVG mask, depending on complexity.
-- | Simple shapes use clip-path for performance.
-- | Complex/animated shapes use SVG masks.
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Shape (shape primitives)

module Hydrogen.Element.Compound.Card.Shape
  ( -- * Card Shape Config
    CardShape
  , cardShape
  , noShape
  
  -- * Predefined Shapes
  , circleShape
  , starShape
  , hexagonShape
  , heartShape
  , octagonShape
  , diamondShape
  
  -- * Custom Shape
  , customPath
  
  -- * Shape Animation
  , ShapeAnimation
  , shapeAnimation
  , noShapeAnimation
  , morphOnHover
  
  -- * CSS Generation
  , shapeToClipPath
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , (<>)
  , (==)
  , (/)
  , (-)
  , (*)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // card shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card shape configuration
data CardShape
  = ShapeNone               -- ^ No clipping (rectangle)
  | ShapeCircle             -- ^ Circle (clips to inscribed circle)
  | ShapeStar Int           -- ^ Star with N points
  | ShapeHexagon            -- ^ Regular hexagon
  | ShapeHeart              -- ^ Heart shape
  | ShapeOctagon            -- ^ Regular octagon
  | ShapeDiamond            -- ^ Diamond/rhombus
  | ShapeCustom String      -- ^ Custom SVG path data

derive instance eqCardShape :: Eq CardShape

instance showCardShape :: Show CardShape where
  show ShapeNone = "none"
  show ShapeCircle = "circle"
  show (ShapeStar n) = "star-" <> showInt n
  show ShapeHexagon = "hexagon"
  show ShapeHeart = "heart"
  show ShapeOctagon = "octagon"
  show ShapeDiamond = "diamond"
  show (ShapeCustom _) = "custom"

-- | Show Int helper
showInt :: Int -> String
showInt n = showIntImpl n ""
  where
    showIntImpl :: Int -> String -> String
    showIntImpl 0 acc = if acc == "" then "0" else acc
    showIntImpl i acc = 
      let digit = i - (i / 10) * 10
          char = digitToChar digit
      in showIntImpl (i / 10) (char <> acc)
    
    digitToChar :: Int -> String
    digitToChar 0 = "0"
    digitToChar 1 = "1"
    digitToChar 2 = "2"
    digitToChar 3 = "3"
    digitToChar 4 = "4"
    digitToChar 5 = "5"
    digitToChar 6 = "6"
    digitToChar 7 = "7"
    digitToChar 8 = "8"
    digitToChar _ = "9"

-- | Create card shape
cardShape :: CardShape -> CardShape
cardShape = \s -> s

-- | No shape (default rectangle)
noShape :: CardShape
noShape = ShapeNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // predefined shapes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Circle shape
circleShape :: CardShape
circleShape = ShapeCircle

-- | Star shape with specified number of points
starShape :: Int -> CardShape
starShape points = ShapeStar points

-- | Hexagon shape
hexagonShape :: CardShape
hexagonShape = ShapeHexagon

-- | Heart shape
heartShape :: CardShape
heartShape = ShapeHeart

-- | Octagon shape
octagonShape :: CardShape
octagonShape = ShapeOctagon

-- | Diamond shape
diamondShape :: CardShape
diamondShape = ShapeDiamond

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // custom shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Custom SVG path shape
customPath :: String -> CardShape
customPath = ShapeCustom

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // shape animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape animation configuration
data ShapeAnimation
  = NoAnimation             -- ^ Static shape
  | MorphOnHover CardShape  -- ^ Morph to different shape on hover

derive instance eqShapeAnimation :: Eq ShapeAnimation

instance showShapeAnimation :: Show ShapeAnimation where
  show NoAnimation = "none"
  show (MorphOnHover _) = "morph-on-hover"

-- | Create shape animation
shapeAnimation :: ShapeAnimation -> ShapeAnimation
shapeAnimation = \a -> a

-- | No animation
noShapeAnimation :: ShapeAnimation
noShapeAnimation = NoAnimation

-- | Morph to different shape on hover
morphOnHover :: CardShape -> ShapeAnimation
morphOnHover = MorphOnHover

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // css generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate CSS clip-path value for shape
shapeToClipPath :: CardShape -> String
shapeToClipPath ShapeNone = "none"
shapeToClipPath ShapeCircle = "circle(50% at 50% 50%)"
shapeToClipPath (ShapeStar 5) = starClipPath5
shapeToClipPath (ShapeStar 6) = starClipPath6
shapeToClipPath (ShapeStar _) = starClipPath5  -- Default to 5-point
shapeToClipPath ShapeHexagon = hexagonClipPath
shapeToClipPath ShapeHeart = heartClipPath
shapeToClipPath ShapeOctagon = octagonClipPath
shapeToClipPath ShapeDiamond = diamondClipPath
shapeToClipPath (ShapeCustom path) = "path('" <> path <> "')"

-- | 5-point star clip path
starClipPath5 :: String
starClipPath5 = "polygon(50% 0%, 61% 35%, 98% 35%, 68% 57%, 79% 91%, 50% 70%, 21% 91%, 32% 57%, 2% 35%, 39% 35%)"

-- | 6-point star clip path
starClipPath6 :: String
starClipPath6 = "polygon(50% 0%, 61% 25%, 93% 25%, 75% 50%, 93% 75%, 61% 75%, 50% 100%, 39% 75%, 7% 75%, 25% 50%, 7% 25%, 39% 25%)"

-- | Hexagon clip path
hexagonClipPath :: String
hexagonClipPath = "polygon(25% 0%, 75% 0%, 100% 50%, 75% 100%, 25% 100%, 0% 50%)"

-- | Heart clip path (approximation)
heartClipPath :: String
heartClipPath = "path('M50,88 C20,62 0,40 0,25 C0,10 10,0 25,0 C40,0 50,15 50,15 C50,15 60,0 75,0 C90,0 100,10 100,25 C100,40 80,62 50,88 Z')"

-- | Octagon clip path
octagonClipPath :: String
octagonClipPath = "polygon(30% 0%, 70% 0%, 100% 30%, 100% 70%, 70% 100%, 30% 100%, 0% 70%, 0% 30%)"

-- | Diamond clip path
diamondClipPath :: String
diamondClipPath = "polygon(50% 0%, 100% 50%, 50% 100%, 0% 50%)"
