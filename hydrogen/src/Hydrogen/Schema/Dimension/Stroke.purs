-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // dimension // stroke
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stroke dimension atoms — measurements for borders, outlines, and paths.
-- |
-- | ## Design Philosophy
-- |
-- | These atoms represent the DIMENSIONAL properties of strokes: widths,
-- | dash lengths, gaps, and offsets. For stroke GEOMETRY (style, caps, joins),
-- | see `Geometry.Stroke`.
-- |
-- | ## Atoms Provided
-- |
-- | | Atom           | Min   | Max    | Behavior | Purpose                    |
-- | |----------------|-------|--------|----------|----------------------------|
-- | | StrokeWidth    | 0     | 64px   | clamps   | Border/stroke thickness    |
-- | | DashLength     | 0     | 1000px | clamps   | Dash segment length        |
-- | | DashGap        | 0     | 1000px | clamps   | Gap between dashes         |
-- | | DashOffset     | -∞    | +∞     | finite   | Pattern start offset       |
-- | | OutlineOffset  | -32px | 32px   | clamps   | Outline distance from edge |
-- |
-- | ## Why These Bounds?
-- |
-- | - **StrokeWidth 64px max**: Decorative borders rarely exceed this.
-- |   For thicker elements, use a shape fill instead.
-- |
-- | - **DashLength 1000px max**: Very long dashes for special effects.
-- |   Most practical use is under 100px.
-- |
-- | - **DashOffset unbounded**: Can be animated continuously for
-- |   "marching ants" effects. Must be finite (no Infinity/NaN).
-- |
-- | - **OutlineOffset ±32px**: Outline can be inset (negative) or outset
-- |   (positive). 32px covers most focus ring use cases.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Dimension.Stroke as Stroke
-- |
-- | -- Border width
-- | border = Stroke.strokeWidth 2.0
-- |
-- | -- Dash pattern: 10px dash, 5px gap
-- | dashLen = Stroke.dashLength 10.0
-- | gapLen = Stroke.dashGap 5.0
-- |
-- | -- Animated offset for marching ants
-- | offset = Stroke.dashOffset animatedValue
-- | ```

module Hydrogen.Schema.Dimension.Stroke
  (   -- * Stroke Width (bounded)
    StrokeWidth
  , strokeWidth
  , strokeWidthNone
  , strokeWidthHairline
  , strokeWidthThin
  , strokeWidthMedium
  , strokeWidthThick
  , strokeWidthValue
  , strokeWidthToCss
  , strokeWidthBounds
  , addStrokeWidth
  , subtractStrokeWidth
  , isStrokeWidthZero
  
  -- * Dash Offset Operations
  , subtractDashOffset
  , isDashOffsetZero
  
  -- * Pattern Predicates
  , isDashPatternSolid
  , isDashPatternEffectivelyEmpty
  
  -- * Dash Length (bounded)
  , DashLength
  , dashLength
  , dashLengthValue
  , dashLengthToCss
  , dashLengthBounds
  
  -- * Dash Gap (bounded)
  , DashGap
  , dashGap
  , dashGapValue
  , dashGapToCss
  , dashGapBounds
  
  -- * Dash Offset (finite, unbounded)
  , DashOffset
  , dashOffset
  , dashOffsetZero
  , dashOffsetValue
  , dashOffsetToCss
  , addDashOffset
  , negateDashOffset
  
  -- * Outline Offset (bounded)
  , OutlineOffset
  , outlineOffset
  , outlineOffsetZero
  , outlineOffsetValue
  , outlineOffsetToCss
  , outlineOffsetBounds
  
  -- * Dash Pattern (molecule)
  , DashPattern
  , dashPattern
  , dashPatternSolid
  , dashPatternDotted
  , dashPatternDashed
  , dashPatternToCss
  , dashPatternSegments
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , map
  , (==)
  , (<)
  , (>)
  , (-)
  , (+)
  , (<>)
  , (&&)
  )

import Data.Array (length, intercalate, concatMap, foldl)
import Data.Number (isFinite) as Number
import Hydrogen.Schema.Bounded (NumberBounds, numberBounds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // stroke width
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stroke width in pixels (bounded)
-- |
-- | Minimum: 0 (no stroke)
-- | Maximum: 64px (very thick decorative border)
-- | Behavior: clamps to [0, 64]
-- |
-- | For thicker visual elements, consider using a shape with fill
-- | rather than a stroke.
newtype StrokeWidth = StrokeWidth Number

derive instance eqStrokeWidth :: Eq StrokeWidth
derive instance ordStrokeWidth :: Ord StrokeWidth

instance showStrokeWidth :: Show StrokeWidth where
  show (StrokeWidth n) = show n <> "px"

-- | Stroke width bounds documentation
strokeWidthBounds :: NumberBounds
strokeWidthBounds = numberBounds 0.0 64.0 "stroke-width"
  "Stroke thickness in pixels. 0 = no stroke, max 64px for decorative use."

-- | Create a stroke width, clamping to valid range [0, 64]
strokeWidth :: Number -> StrokeWidth
strokeWidth n
  | n < 0.0 = StrokeWidth 0.0
  | n > 64.0 = StrokeWidth 64.0
  | otherwise = StrokeWidth n

-- | No stroke (0px)
strokeWidthNone :: StrokeWidth
strokeWidthNone = StrokeWidth 0.0

-- | Hairline stroke (0.5px)
-- | Note: May render as 1px on non-retina displays
strokeWidthHairline :: StrokeWidth
strokeWidthHairline = StrokeWidth 0.5

-- | Thin stroke (1px) - most common for subtle borders
strokeWidthThin :: StrokeWidth
strokeWidthThin = StrokeWidth 1.0

-- | Medium stroke (2px) - visible borders, focus rings
strokeWidthMedium :: StrokeWidth
strokeWidthMedium = StrokeWidth 2.0

-- | Thick stroke (4px) - emphasis, decorative
strokeWidthThick :: StrokeWidth
strokeWidthThick = StrokeWidth 4.0

-- | Extract the numeric value
strokeWidthValue :: StrokeWidth -> Number
strokeWidthValue (StrokeWidth n) = n

-- | Convert to CSS string
strokeWidthToCss :: StrokeWidth -> String
strokeWidthToCss (StrokeWidth n) = show n <> "px"

-- | Add two stroke widths (result is clamped to bounds)
-- |
-- | Useful for composing border effects or calculating total stroke size.
addStrokeWidth :: StrokeWidth -> StrokeWidth -> StrokeWidth
addStrokeWidth (StrokeWidth a) (StrokeWidth b) = strokeWidth (a + b)

-- | Subtract stroke widths (result is clamped to bounds)
-- |
-- | Returns 0 if result would be negative.
subtractStrokeWidth :: StrokeWidth -> StrokeWidth -> StrokeWidth
subtractStrokeWidth (StrokeWidth a) (StrokeWidth b) = strokeWidth (a - b)

-- | Check if stroke width is zero (no stroke)
-- |
-- | Useful for conditionally rendering stroke-related styles.
isStrokeWidthZero :: StrokeWidth -> Boolean
isStrokeWidthZero (StrokeWidth n) = n == 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // dash length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dash segment length in pixels (bounded)
-- |
-- | Minimum: 0 (degenerate, effectively a gap)
-- | Maximum: 1000px (very long dashes for decorative effects)
-- | Behavior: clamps to [0, 1000]
-- |
-- | Used in stroke-dasharray for SVG/Canvas. Combined with DashGap
-- | to create custom dash patterns.
newtype DashLength = DashLength Number

derive instance eqDashLength :: Eq DashLength
derive instance ordDashLength :: Ord DashLength

instance showDashLength :: Show DashLength where
  show (DashLength n) = show n <> "px"

-- | Dash length bounds documentation
dashLengthBounds :: NumberBounds
dashLengthBounds = numberBounds 0.0 1000.0 "dash-length"
  "Length of a dash segment in pixels for stroke-dasharray."

-- | Create a dash length, clamping to valid range [0, 1000]
dashLength :: Number -> DashLength
dashLength n
  | n < 0.0 = DashLength 0.0
  | n > 1000.0 = DashLength 1000.0
  | otherwise = DashLength n

-- | Extract the numeric value
dashLengthValue :: DashLength -> Number
dashLengthValue (DashLength n) = n

-- | Convert to CSS string (unitless for dasharray)
dashLengthToCss :: DashLength -> String
dashLengthToCss (DashLength n) = show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // dash gap
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gap between dashes in pixels (bounded)
-- |
-- | Minimum: 0 (no gap, effectively solid)
-- | Maximum: 1000px (very sparse dashing)
-- | Behavior: clamps to [0, 1000]
-- |
-- | Used in stroke-dasharray for SVG/Canvas. Combined with DashLength
-- | to create custom dash patterns.
newtype DashGap = DashGap Number

derive instance eqDashGap :: Eq DashGap
derive instance ordDashGap :: Ord DashGap

instance showDashGap :: Show DashGap where
  show (DashGap n) = show n <> "px"

-- | Dash gap bounds documentation
dashGapBounds :: NumberBounds
dashGapBounds = numberBounds 0.0 1000.0 "dash-gap"
  "Length of gap between dashes in pixels for stroke-dasharray."

-- | Create a dash gap, clamping to valid range [0, 1000]
dashGap :: Number -> DashGap
dashGap n
  | n < 0.0 = DashGap 0.0
  | n > 1000.0 = DashGap 1000.0
  | otherwise = DashGap n

-- | Extract the numeric value
dashGapValue :: DashGap -> Number
dashGapValue (DashGap n) = n

-- | Convert to CSS string (unitless for dasharray)
dashGapToCss :: DashGap -> String
dashGapToCss (DashGap n) = show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // dash offset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dash pattern offset in pixels (unbounded but finite)
-- |
-- | This value can be negative or positive, and can exceed the pattern
-- | length (it wraps). It's commonly animated for "marching ants" effects.
-- |
-- | Behavior: Must be finite (no Infinity, no NaN)
-- |
-- | Example: Animating from 0 to -patternLength creates a forward march.
newtype DashOffset = DashOffset Number

derive instance eqDashOffset :: Eq DashOffset
derive instance ordDashOffset :: Ord DashOffset

instance showDashOffset :: Show DashOffset where
  show (DashOffset n) = show n <> "px"

-- | Create a dash offset
-- |
-- | Returns 0 if input is not finite (Infinity, NaN)
dashOffset :: Number -> DashOffset
dashOffset n = 
  if Number.isFinite n 
    then DashOffset n 
    else DashOffset 0.0

-- | Zero offset (default)
dashOffsetZero :: DashOffset
dashOffsetZero = DashOffset 0.0

-- | Extract the numeric value
dashOffsetValue :: DashOffset -> Number
dashOffsetValue (DashOffset n) = n

-- | Convert to CSS string
dashOffsetToCss :: DashOffset -> String
dashOffsetToCss (DashOffset n) = show n <> "px"

-- | Add two offsets (for animation)
addDashOffset :: DashOffset -> DashOffset -> DashOffset
addDashOffset (DashOffset a) (DashOffset b) = dashOffset (a + b)

-- | Negate an offset (reverse direction)
negateDashOffset :: DashOffset -> DashOffset
negateDashOffset (DashOffset n) = DashOffset (negate n)

-- | Subtract offsets (for relative animation)
subtractDashOffset :: DashOffset -> DashOffset -> DashOffset
subtractDashOffset (DashOffset a) (DashOffset b) = dashOffset (a - b)

-- | Check if offset is zero
isDashOffsetZero :: DashOffset -> Boolean
isDashOffsetZero (DashOffset n) = n == 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // outline offset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Outline offset from element edge in pixels (bounded)
-- |
-- | Unlike borders, outlines don't affect layout. The offset controls
-- | how far the outline is drawn from the element's border edge.
-- |
-- | Minimum: -32px (inset into element)
-- | Maximum: 32px (outset from element)
-- | Behavior: clamps to [-32, 32]
-- |
-- | Common use: Focus rings with small positive offset (2-4px)
newtype OutlineOffset = OutlineOffset Number

derive instance eqOutlineOffset :: Eq OutlineOffset
derive instance ordOutlineOffset :: Ord OutlineOffset

instance showOutlineOffset :: Show OutlineOffset where
  show (OutlineOffset n) = show n <> "px"

-- | Outline offset bounds documentation
outlineOffsetBounds :: NumberBounds
outlineOffsetBounds = numberBounds (-32.0) 32.0 "outline-offset"
  "Distance of outline from element edge. Negative = inset, positive = outset."

-- | Create an outline offset, clamping to valid range [-32, 32]
outlineOffset :: Number -> OutlineOffset
outlineOffset n
  | n < (-32.0) = OutlineOffset (-32.0)
  | n > 32.0 = OutlineOffset 32.0
  | otherwise = OutlineOffset n

-- | Zero offset (outline touches border edge)
outlineOffsetZero :: OutlineOffset
outlineOffsetZero = OutlineOffset 0.0

-- | Extract the numeric value
outlineOffsetValue :: OutlineOffset -> Number
outlineOffsetValue (OutlineOffset n) = n

-- | Convert to CSS string
outlineOffsetToCss :: OutlineOffset -> String
outlineOffsetToCss (OutlineOffset n) = show n <> "px"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // dash pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dash pattern (molecule) — alternating dash/gap lengths
-- |
-- | Composes DashLength and DashGap values into a full pattern.
-- | The pattern repeats: [dash, gap, dash, gap, ...]
-- |
-- | For odd-length arrays, CSS duplicates the pattern to make it even.
-- | We enforce even length at construction to be explicit.
newtype DashPattern = DashPattern (Array Number)

derive instance eqDashPattern :: Eq DashPattern

instance showDashPattern :: Show DashPattern where
  show = dashPatternToCss

-- | Create a dash pattern from alternating dash/gap values
-- |
-- | Takes pairs of (dash, gap) values. All values are clamped to [0, 1000].
dashPattern :: Array { dash :: Number, gap :: Number } -> DashPattern
dashPattern pairs = DashPattern (concatMap (\p -> [clampDash p.dash, clampDash p.gap]) pairs)
  where
    clampDash n
      | n < 0.0 = 0.0
      | n > 1000.0 = 1000.0
      | otherwise = n

-- | Solid stroke (no dashing) — empty pattern
dashPatternSolid :: DashPattern
dashPatternSolid = DashPattern []

-- | Standard dotted pattern (1px dot, 2px gap)
dashPatternDotted :: DashPattern
dashPatternDotted = DashPattern [1.0, 2.0]

-- | Standard dashed pattern (4px dash, 4px gap)
dashPatternDashed :: DashPattern
dashPatternDashed = DashPattern [4.0, 4.0]

-- | Convert to CSS stroke-dasharray string
-- |
-- | Returns "none" for empty pattern (solid stroke)
dashPatternToCss :: DashPattern -> String
dashPatternToCss (DashPattern segments) =
  if length segments == 0
    then "none"
    else intercalate " " (map show segments)

-- | Get the raw segments
dashPatternSegments :: DashPattern -> Array Number
dashPatternSegments (DashPattern segments) = segments

-- | Check if pattern is solid (no dashing)
-- |
-- | True when the pattern has no segments (empty array).
isDashPatternSolid :: DashPattern -> Boolean
isDashPatternSolid (DashPattern segments) = length segments == 0

-- | Check if pattern renders as effectively empty (all zeros)
-- |
-- | A pattern like [0, 0, 0, 0] is technically dashed but renders as nothing.
-- | This predicate returns true when all segments are zero (or array is empty).
-- |
-- | Uses (&&) in the fold to check each segment.
isDashPatternEffectivelyEmpty :: DashPattern -> Boolean
isDashPatternEffectivelyEmpty (DashPattern segments) =
  foldl (\acc n -> acc && n == 0.0) true segments
