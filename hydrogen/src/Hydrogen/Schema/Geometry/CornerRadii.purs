-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // geometry // corner-radii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CornerRadii — per-corner radius specification for rounded rectangles.
-- |
-- | ## Design Philosophy
-- |
-- | Corners are specified individually for maximum flexibility:
-- | - topLeft, topRight, bottomRight, bottomLeft
-- | - Each radius is a non-negative Number (pixels or relative units)
-- |
-- | Common patterns (uniform, symmetric) have convenience constructors.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- |
-- | ## Dependents
-- |
-- | - CSS border-radius
-- | - Canvas rounded rectangles
-- | - Button and card components

module Hydrogen.Schema.Geometry.CornerRadii
  ( -- * CornerRadii Type
    CornerRadii(CornerRadii)
  , mkCornerRadii
  , topLeft
  , topRight
  , bottomRight
  , bottomLeft
  
  -- * Constructors
  , uniform
  , symmetricX
  , symmetricY
  , custom
  , none
  , pill
  
  -- * Operations
  , maxRadius
  , minRadius
  , averageRadius
  , radiusSpread
  , isUniform
  , isNone
  , hasAnyLargeCorner
  , hasAnySmallCorner
  , fitsWithinBounds
  
  -- * Transformations
  , scaleRadii
  , clampRadii
  
  -- * Comparison
  , compareByMax
  
  -- * Display
  , showCornerRadii
  , toCssString
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering
  , (>)
  , (>=)
  , (<=)
  , (<)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (&&)
  , (||)
  , (==)
  , compare
  , show
  , max
  , min
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cornerradii type
-- ═════════════════════════════════════════════════════════════════════════════

-- | CornerRadii molecule.
-- |
-- | Per-corner radius specification for rounded rectangles.
-- | All radii are non-negative (validated via smart constructor).
newtype CornerRadii = CornerRadii
  { topLeft :: Number
  , topRight :: Number
  , bottomRight :: Number
  , bottomLeft :: Number
  }

derive instance eqCornerRadii :: Eq CornerRadii
derive instance ordCornerRadii :: Ord CornerRadii

instance showCornerRadiiInstance :: Show CornerRadii where
  show (CornerRadii r) = "(CornerRadii " 
    <> show r.topLeft <> " " 
    <> show r.topRight <> " " 
    <> show r.bottomRight <> " " 
    <> show r.bottomLeft <> ")"

-- | Create corner radii with validation.
-- |
-- | Returns Nothing if any radius is negative.
mkCornerRadii :: Number -> Number -> Number -> Number -> Maybe CornerRadii
mkCornerRadii tl tr br bl =
  if tl >= 0.0 && tr >= 0.0 && br >= 0.0 && bl >= 0.0
  then Just (CornerRadii { topLeft: tl, topRight: tr, bottomRight: br, bottomLeft: bl })
  else Nothing

-- | Get top-left radius.
topLeft :: CornerRadii -> Number
topLeft (CornerRadii r) = r.topLeft

-- | Get top-right radius.
topRight :: CornerRadii -> Number
topRight (CornerRadii r) = r.topRight

-- | Get bottom-right radius.
bottomRight :: CornerRadii -> Number
bottomRight (CornerRadii r) = r.bottomRight

-- | Get bottom-left radius.
bottomLeft :: CornerRadii -> Number
bottomLeft (CornerRadii r) = r.bottomLeft

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Uniform radius on all corners.
uniform :: Number -> CornerRadii
uniform r = CornerRadii { topLeft: r', topRight: r', bottomRight: r', bottomLeft: r' }
  where r' = if r < 0.0 then 0.0 else r

-- | Symmetric on X axis (left sides same, right sides same).
symmetricX :: Number -> Number -> CornerRadii
symmetricX left right = CornerRadii 
  { topLeft: l, topRight: r, bottomRight: r, bottomLeft: l }
  where 
    l = if left < 0.0 then 0.0 else left
    r = if right < 0.0 then 0.0 else right

-- | Symmetric on Y axis (top sides same, bottom sides same).
symmetricY :: Number -> Number -> CornerRadii
symmetricY top bottom = CornerRadii 
  { topLeft: t, topRight: t, bottomRight: b, bottomLeft: b }
  where 
    t = if top < 0.0 then 0.0 else top
    b = if bottom < 0.0 then 0.0 else bottom

-- | Custom per-corner radii (clamped to non-negative).
custom :: Number -> Number -> Number -> Number -> CornerRadii
custom tl tr br bl = CornerRadii 
  { topLeft: clamp tl
  , topRight: clamp tr
  , bottomRight: clamp br
  , bottomLeft: clamp bl
  }
  where clamp n = if n < 0.0 then 0.0 else n

-- | No rounding (all radii zero).
none :: CornerRadii
none = CornerRadii { topLeft: 0.0, topRight: 0.0, bottomRight: 0.0, bottomLeft: 0.0 }

-- | Pill shape (maximum rounding).
-- |
-- | Takes the container height to calculate half as radius.
pill :: Number -> CornerRadii
pill height = uniform (height / 2.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the maximum radius among all corners.
maxRadius :: CornerRadii -> Number
maxRadius (CornerRadii r) = 
  max r.topLeft (max r.topRight (max r.bottomRight r.bottomLeft))

-- | Get the minimum radius among all corners.
minRadius :: CornerRadii -> Number
minRadius (CornerRadii r) = 
  min r.topLeft (min r.topRight (min r.bottomRight r.bottomLeft))

-- | Get the average radius.
averageRadius :: CornerRadii -> Number
averageRadius (CornerRadii r) = 
  (r.topLeft + r.topRight + r.bottomRight + r.bottomLeft) / 4.0

-- | Check if all corners have the same radius.
isUniform :: CornerRadii -> Boolean
isUniform (CornerRadii r) = 
  r.topLeft == r.topRight && r.topRight == r.bottomRight && r.bottomRight == r.bottomLeft

-- | Check if all radii are zero.
isNone :: CornerRadii -> Boolean
isNone (CornerRadii r) = 
  r.topLeft == 0.0 && r.topRight == 0.0 && r.bottomRight == 0.0 && r.bottomLeft == 0.0

-- | Spread between max and min radius.
-- |
-- | Uses (-) to calculate difference between largest and smallest corner.
-- | Useful for detecting asymmetric corners.
radiusSpread :: CornerRadii -> Number
radiusSpread cr = maxRadius cr - minRadius cr

-- | Check if any corner exceeds a threshold.
-- |
-- | Uses (||) for compound boolean logic.
hasAnyLargeCorner :: Number -> CornerRadii -> Boolean
hasAnyLargeCorner threshold (CornerRadii r) =
  r.topLeft > threshold || r.topRight > threshold || 
  r.bottomRight > threshold || r.bottomLeft > threshold

-- | Check if any corner is below a threshold.
-- |
-- | Uses (<=) for inclusive comparison.
hasAnySmallCorner :: Number -> CornerRadii -> Boolean
hasAnySmallCorner threshold (CornerRadii r) =
  r.topLeft <= threshold || r.topRight <= threshold || 
  r.bottomRight <= threshold || r.bottomLeft <= threshold

-- | Check if all radii fit within container bounds.
-- |
-- | For a rectangle of given width and height, radii should not exceed
-- | half of the smaller dimension.
fitsWithinBounds :: Number -> Number -> CornerRadii -> Boolean
fitsWithinBounds width height cr =
  let maxAllowed = if width <= height then width / 2.0 else height / 2.0
  in maxRadius cr <= maxAllowed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale all radii by a factor.
-- |
-- | Negative factors are treated as zero.
scaleRadii :: Number -> CornerRadii -> CornerRadii
scaleRadii factor (CornerRadii r) =
  let f = if factor < 0.0 then 0.0 else factor
  in CornerRadii
    { topLeft: r.topLeft * f
    , topRight: r.topRight * f
    , bottomRight: r.bottomRight * f
    , bottomLeft: r.bottomLeft * f
    }

-- | Clamp all radii to a maximum value.
-- |
-- | Useful for ensuring radii don't exceed half the container dimension.
clampRadii :: Number -> CornerRadii -> CornerRadii
clampRadii maxVal (CornerRadii r) =
  let clamp n = if n > maxVal then maxVal else n
  in CornerRadii
    { topLeft: clamp r.topLeft
    , topRight: clamp r.topRight
    , bottomRight: clamp r.bottomRight
    , bottomLeft: clamp r.bottomLeft
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare corner radii by maximum radius.
compareByMax :: CornerRadii -> CornerRadii -> Ordering
compareByMax r1 r2 = compare (maxRadius r1) (maxRadius r2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format corner radii for display.
showCornerRadii :: CornerRadii -> String
showCornerRadii (CornerRadii r) =
  "CornerRadii { tl: " <> show r.topLeft 
  <> ", tr: " <> show r.topRight 
  <> ", br: " <> show r.bottomRight 
  <> ", bl: " <> show r.bottomLeft <> " }"

-- | Convert to CSS border-radius string.
-- |
-- | Format: "tl tr br bl" (e.g., "8px 8px 0 0")
toCssString :: CornerRadii -> String
toCssString (CornerRadii r) =
  show r.topLeft <> "px " 
  <> show r.topRight <> "px " 
  <> show r.bottomRight <> "px " 
  <> show r.bottomLeft <> "px"
