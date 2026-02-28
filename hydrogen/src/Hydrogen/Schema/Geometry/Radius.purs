-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // geometry // radius
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Border radius and corner primitives for the Hydrogen Schema.
-- |
-- | Shape defines personality. This module provides type-safe
-- | border radius and corner definitions.
-- |
-- | ## Design Principles
-- |
-- | 1. **Scale-based**: Consistent radius scale across UI
-- | 2. **Per-corner control**: Each corner can be different
-- | 3. **Semantic naming**: none, sm, md, lg, full
-- | 4. **Composable**: Mix and match corners

module Hydrogen.Schema.Geometry.Radius
  ( -- * Core Types
    Radius(..)
  , Corners
  
  -- * Radius Constructors
  , px
  , percent
  , rem
  
  -- * Semantic Scale
  , none
  , xs
  , sm
  , md
  , lg
  , xl
  , xl2
  , full
  
  -- * Corner Constructors
  , corners
  , cornersAll
  , cornersTop
  , cornersBottom
  , cornersLeft
  , cornersRight
  , cornersTopLeft
  , cornersTopRight
  , cornersBottomLeft
  , cornersBottomRight
  
  -- * Operations
  , scale
  , double
  , half
  
  -- * Conversion
  , toLegacyCss
  , cornersToLegacyCss
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (&&)
  , (<>)
  , (*)
  )

import Data.Int as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border radius value
data Radius
  = RadiusPx Number      -- Pixels
  | RadiusPercent Number -- Percentage
  | RadiusRem Number     -- Rem units
  | RadiusFull           -- 9999px (pill/circle)
  | RadiusNone           -- 0

derive instance eqRadius :: Eq Radius

instance showRadius :: Show Radius where
  show = case _ of
    RadiusPx n -> "(RadiusPx " <> show n <> ")"
    RadiusPercent n -> "(RadiusPercent " <> show n <> ")"
    RadiusRem n -> "(RadiusRem " <> show n <> ")"
    RadiusFull -> "(RadiusFull)"
    RadiusNone -> "(RadiusNone)"

-- | Per-corner radius control
type Corners =
  { topLeft :: Radius
  , topRight :: Radius
  , bottomRight :: Radius
  , bottomLeft :: Radius
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // radius constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create radius in pixels
px :: Number -> Radius
px = RadiusPx

-- | Create radius in percentage
percent :: Number -> Radius
percent = RadiusPercent

-- | Create radius in rem
rem :: Number -> Radius
rem = RadiusRem

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // semantic scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | No radius (sharp corners)
none :: Radius
none = RadiusNone

-- | Extra small radius (2px)
xs :: Radius
xs = RadiusPx 2.0

-- | Small radius (4px)
sm :: Radius
sm = RadiusPx 4.0

-- | Medium radius (6px)
md :: Radius
md = RadiusPx 6.0

-- | Large radius (8px)
lg :: Radius
lg = RadiusPx 8.0

-- | Extra large radius (12px)
xl :: Radius
xl = RadiusPx 12.0

-- | 2x extra large radius (16px)
xl2 :: Radius
xl2 = RadiusPx 16.0

-- | Full radius (pill shape)
full :: Radius
full = RadiusFull

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // corner constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create corners with different radius for each
corners :: Radius -> Radius -> Radius -> Radius -> Corners
corners topLeft topRight bottomRight bottomLeft =
  { topLeft, topRight, bottomRight, bottomLeft }

-- | Same radius on all corners
cornersAll :: Radius -> Corners
cornersAll r = corners r r r r

-- | Radius only on top corners
cornersTop :: Radius -> Corners
cornersTop r = corners r r none none

-- | Radius only on bottom corners
cornersBottom :: Radius -> Corners
cornersBottom r = corners none none r r

-- | Radius only on left corners
cornersLeft :: Radius -> Corners
cornersLeft r = corners r none none r

-- | Radius only on right corners
cornersRight :: Radius -> Corners
cornersRight r = corners none r r none

-- | Radius only on top-left
cornersTopLeft :: Radius -> Corners
cornersTopLeft r = corners r none none none

-- | Radius only on top-right
cornersTopRight :: Radius -> Corners
cornersTopRight r = corners none r none none

-- | Radius only on bottom-left
cornersBottomLeft :: Radius -> Corners
cornersBottomLeft r = corners none none none r

-- | Radius only on bottom-right
cornersBottomRight :: Radius -> Corners
cornersBottomRight r = corners none none r none

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale radius by a factor
scale :: Number -> Radius -> Radius
scale factor = case _ of
  RadiusPx n -> RadiusPx (n * factor)
  RadiusPercent n -> RadiusPercent (n * factor)
  RadiusRem n -> RadiusRem (n * factor)
  RadiusFull -> RadiusFull
  RadiusNone -> RadiusNone

-- | Double the radius
double :: Radius -> Radius
double = scale 2.0

-- | Halve the radius
half :: Radius -> Radius
half = scale 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert radius to legacy CSS string
-- |
-- | This generates a CSS-compatible string for use with legacy rendering.
-- | NOT an FFI boundary - pure string generation.
toLegacyCss :: Radius -> String
toLegacyCss = case _ of
  RadiusPx n -> showNum n <> "px"
  RadiusPercent n -> showNum n <> "%"
  RadiusRem n -> showNum n <> "rem"
  RadiusFull -> "9999px"
  RadiusNone -> "0"

-- | Convert corners to legacy CSS border-radius string
-- |
-- | This generates a CSS-compatible string for use with legacy rendering.
-- | NOT an FFI boundary - pure string generation.
cornersToLegacyCss :: Corners -> String
cornersToLegacyCss { topLeft, topRight, bottomRight, bottomLeft } =
  if allSame then toLegacyCss topLeft
  else if topSame && bottomSame then toLegacyCss topLeft <> " " <> toLegacyCss bottomRight
  else toLegacyCss topLeft <> " " <> toLegacyCss topRight <> " " <> toLegacyCss bottomRight <> " " <> toLegacyCss bottomLeft
  where
    allSame = topLeft == topRight && topRight == bottomRight && bottomRight == bottomLeft
    topSame = topLeft == topRight
    bottomSame = bottomRight == bottomLeft

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show number cleanly
showNum :: Number -> String
showNum n =
  let rounded = Int.round n
  in if Int.toNumber rounded == n
    then show rounded
    else show n
