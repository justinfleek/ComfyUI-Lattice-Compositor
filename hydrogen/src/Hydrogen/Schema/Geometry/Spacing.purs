-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // geometry // spacing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spacing - padding, margin, and inset primitives.
-- |
-- | Defines bounded spacing atoms for consistent layout across components.
-- | Each edge can be specified independently or uniformly.
-- |
-- | ## Design Philosophy
-- |
-- | Spacing is NOT a single Number — it's a 4-sided value with semantic meaning:
-- | - Padding: Inner spacing (content to border)
-- | - Margin: Outer spacing (border to siblings)
-- | - Inset: Shorthand for positioning offsets
-- |
-- | ## CSS Mapping
-- |
-- | All spacing types support `toLegacyCss` for CSS output.

module Hydrogen.Schema.Geometry.Spacing
  ( -- * Spacing Value
    SpacingValue(SpacingValue)
  , spacingValue
  , spacingZero
  , spacingXs
  , spacingSm
  , spacingMd
  , spacingLg
  , spacingXl
  , spacing2xl
  , spacing3xl
  , unwrapSpacing
  , toLegacyCss
  -- * Padding (4-sided inner spacing)
  , Padding
  , padding
  , paddingAll
  , paddingXY
  , paddingTop
  , paddingRight
  , paddingBottom
  , paddingLeft
  , paddingNone
  , paddingToLegacyCss
  -- * Margin (4-sided outer spacing)
  , Margin
  , margin
  , marginAll
  , marginXY
  , marginTop
  , marginRight
  , marginBottom
  , marginLeft
  , marginNone
  , marginToLegacyCss
  
  -- * Bounds
  , spacingValueBounds
  ) where

import Data.Ord (max)

import Hydrogen.Schema.Bounded as Bounded

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (&&)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // spacing value
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single spacing value in pixels.
-- |
-- | Non-negative. Represents padding, margin, or inset on one edge.
newtype SpacingValue = SpacingValue Number

derive instance eqSpacingValue :: Eq SpacingValue
derive instance ordSpacingValue :: Ord SpacingValue

instance showSpacingValue :: Show SpacingValue where
  show (SpacingValue n) = "(SpacingValue " <> show n <> ")"

-- | Create a spacing value, clamping to non-negative.
spacingValue :: Number -> SpacingValue
spacingValue n = SpacingValue (max 0.0 n)

-- | Zero spacing
spacingZero :: SpacingValue
spacingZero = SpacingValue 0.0

-- | Extra small spacing (4px)
spacingXs :: SpacingValue
spacingXs = SpacingValue 4.0

-- | Small spacing (8px)
spacingSm :: SpacingValue
spacingSm = SpacingValue 8.0

-- | Medium spacing (16px) — default
spacingMd :: SpacingValue
spacingMd = SpacingValue 16.0

-- | Large spacing (24px)
spacingLg :: SpacingValue
spacingLg = SpacingValue 24.0

-- | Extra large spacing (32px)
spacingXl :: SpacingValue
spacingXl = SpacingValue 32.0

-- | 2x extra large spacing (48px)
spacing2xl :: SpacingValue
spacing2xl = SpacingValue 48.0

-- | 3x extra large spacing (64px)
spacing3xl :: SpacingValue
spacing3xl = SpacingValue 64.0

-- | Extract raw number from spacing value.
unwrapSpacing :: SpacingValue -> Number
unwrapSpacing (SpacingValue n) = n

-- | Convert spacing value to legacy CSS string.
-- |
-- | CSS is a legacy format. The atom is the source of truth.
toLegacyCss :: SpacingValue -> String
toLegacyCss (SpacingValue n) = show n <> "px"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // padding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Four-sided padding (inner spacing from border to content).
-- |
-- | Each edge is specified independently for full control.
type Padding =
  { top :: SpacingValue
  , right :: SpacingValue
  , bottom :: SpacingValue
  , left :: SpacingValue
  }

-- | Create padding with all four sides specified.
padding :: SpacingValue -> SpacingValue -> SpacingValue -> SpacingValue -> Padding
padding top right bottom left =
  { top, right, bottom, left }

-- | Create uniform padding (same on all sides).
paddingAll :: SpacingValue -> Padding
paddingAll v = { top: v, right: v, bottom: v, left: v }

-- | Create padding with horizontal and vertical values.
-- |
-- | paddingXY horizontal vertical
paddingXY :: SpacingValue -> SpacingValue -> Padding
paddingXY x y = { top: y, right: x, bottom: y, left: x }

-- | Get top padding.
paddingTop :: Padding -> SpacingValue
paddingTop p = p.top

-- | Get right padding.
paddingRight :: Padding -> SpacingValue
paddingRight p = p.right

-- | Get bottom padding.
paddingBottom :: Padding -> SpacingValue
paddingBottom p = p.bottom

-- | Get left padding.
paddingLeft :: Padding -> SpacingValue
paddingLeft p = p.left

-- | Zero padding on all sides.
paddingNone :: Padding
paddingNone = paddingAll spacingZero

-- | Convert padding to legacy CSS string.
-- |
-- | Uses shorthand when possible:
-- | - All same: "16px"
-- | - Vertical/horizontal: "16px 24px"
-- | - Different: "16px 24px 16px 24px"
paddingToLegacyCss :: Padding -> String
paddingToLegacyCss p =
  let
    t = toLegacyCss p.top
    r = toLegacyCss p.right
    b = toLegacyCss p.bottom
    l = toLegacyCss p.left
  in
    if t == r && r == b && b == l then
      t
    else if t == b && r == l then
      t <> " " <> r
    else
      t <> " " <> r <> " " <> b <> " " <> l

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // margin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Four-sided margin (outer spacing from border to siblings).
-- |
-- | Each edge is specified independently for full control.
type Margin =
  { top :: SpacingValue
  , right :: SpacingValue
  , bottom :: SpacingValue
  , left :: SpacingValue
  }

-- | Create margin with all four sides specified.
margin :: SpacingValue -> SpacingValue -> SpacingValue -> SpacingValue -> Margin
margin top right bottom left =
  { top, right, bottom, left }

-- | Create uniform margin (same on all sides).
marginAll :: SpacingValue -> Margin
marginAll v = { top: v, right: v, bottom: v, left: v }

-- | Create margin with horizontal and vertical values.
-- |
-- | marginXY horizontal vertical
marginXY :: SpacingValue -> SpacingValue -> Margin
marginXY x y = { top: y, right: x, bottom: y, left: x }

-- | Get top margin.
marginTop :: Margin -> SpacingValue
marginTop m = m.top

-- | Get right margin.
marginRight :: Margin -> SpacingValue
marginRight m = m.right

-- | Get bottom margin.
marginBottom :: Margin -> SpacingValue
marginBottom m = m.bottom

-- | Get left margin.
marginLeft :: Margin -> SpacingValue
marginLeft m = m.left

-- | Zero margin on all sides.
marginNone :: Margin
marginNone = marginAll spacingZero

-- | Convert margin to legacy CSS string.
-- |
-- | Uses shorthand when possible:
-- | - All same: "16px"
-- | - Vertical/horizontal: "16px 24px"
-- | - Different: "16px 24px 16px 24px"
marginToLegacyCss :: Margin -> String
marginToLegacyCss m =
  let
    t = toLegacyCss m.top
    r = toLegacyCss m.right
    b = toLegacyCss m.bottom
    l = toLegacyCss m.left
  in
    if t == r && r == b && b == l then
      t
    else if t == b && r == l then
      t <> " " <> r
    else
      t <> " " <> r <> " " <> b <> " " <> l

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for SpacingValue
-- |
-- | Min: 0.0 (no spacing)
-- | Max: 1000.0 (practical limit for UI spacing)
spacingValueBounds :: Bounded.NumberBounds
spacingValueBounds = Bounded.numberBounds 0.0 1000.0 "spacingValue" "Spacing in pixels (0-1000)"
