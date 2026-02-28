-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // dimension // size2d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Size2D — Width and Height composite for 2D dimensions.
-- |
-- | **WHY SIZE2D?**
-- | Size2D represents the dimensions of a rectangular region:
-- | - Width (horizontal extent)
-- | - Height (vertical extent)
-- |
-- | Unlike Vec2 which represents direction/displacement, Size2D represents
-- | spatial extent and is always non-negative.
-- |
-- | **Use cases:**
-- | - Element dimensions (width: 200px, height: 100px)
-- | - Image/canvas size
-- | - Viewport dimensions
-- | - Bounding box extents
-- |
-- | **Parameterized by unit type:**
-- | ```purescript
-- | Size2D Pixel     -- Device pixels
-- | Size2D CSSPixel  -- CSS reference pixels
-- | Size2D Number    -- Abstract/normalized
-- | Size2D Meter     -- Physical dimensions
-- | ```

module Hydrogen.Schema.Dimension.Size2D
  ( -- * Types
    Size2D(Size2D)
  
  -- * Constructors
  , size2D
  , size2DFromRecord
  , size2DSquare
  , size2DZero
  
  -- * Accessors
  , width
  , height
  , toRecord
  
  -- * Operations
  , area
  , perimeter
  , aspectRatio
  , scale
  , scaleWidth
  , scaleHeight
  , add
  , subtract
  , max
  , min
  , lerp
  , clamp
  
  -- * Predicates
  , isSquare
  , isPortrait
  , isLandscape
  , isZero
  , contains
  , fitsWithin
  
  -- * Transformations
  , transpose
  , expand
  , contract
  , growTo
  , shrinkTo
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // size2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D size with width and height.
-- |
-- | Parameterized by the unit type (Pixel, Number, Meter, etc.)
-- | Values are stored as-is; non-negativity is enforced by constructors.
data Size2D a = Size2D a a

derive instance eqSize2D :: Eq a => Eq (Size2D a)
derive instance ordSize2D :: Ord a => Ord (Size2D a)

instance showSize2D :: Show a => Show (Size2D a) where
  show (Size2D w h) = "Size2D(" <> show w <> " × " <> show h <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Size2D from width and height.
-- |
-- | ```purescript
-- | size2D 200.0 100.0  -- 200×100
-- | ```
size2D :: Number -> Number -> Size2D Number
size2D w h = Size2D (absNum w) (absNum h)

-- | Create from a record.
size2DFromRecord :: { width :: Number, height :: Number } -> Size2D Number
size2DFromRecord { width: w, height: h } = size2D w h

-- | Create a square size (width = height).
size2DSquare :: Number -> Size2D Number
size2DSquare s = size2D s s

-- | Zero size.
size2DZero :: Size2D Number
size2DZero = Size2D 0.0 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get width.
width :: forall a. Size2D a -> a
width (Size2D w _) = w

-- | Get height.
height :: forall a. Size2D a -> a
height (Size2D _ h) = h

-- | Convert to record.
toRecord :: Size2D Number -> { width :: Number, height :: Number }
toRecord (Size2D w h) = { width: w, height: h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate area (width × height).
area :: Size2D Number -> Number
area (Size2D w h) = w * h

-- | Calculate perimeter (2 × (width + height)).
perimeter :: Size2D Number -> Number
perimeter (Size2D w h) = 2.0 * (w + h)

-- | Calculate aspect ratio (width / height).
-- |
-- | Returns 1.0 if height is zero (to avoid division by zero).
aspectRatio :: Size2D Number -> Number
aspectRatio (Size2D w h) =
  if h == 0.0 then 1.0 else w / h

-- | Scale both dimensions by a factor.
scale :: Number -> Size2D Number -> Size2D Number
scale factor (Size2D w h) = Size2D (w * factor) (h * factor)

-- | Scale only width.
scaleWidth :: Number -> Size2D Number -> Size2D Number
scaleWidth factor (Size2D w h) = Size2D (w * factor) h

-- | Scale only height.
scaleHeight :: Number -> Size2D Number -> Size2D Number
scaleHeight factor (Size2D w h) = Size2D w (h * factor)

-- | Add two sizes (component-wise).
add :: Size2D Number -> Size2D Number -> Size2D Number
add (Size2D w1 h1) (Size2D w2 h2) = Size2D (w1 + w2) (h1 + h2)

-- | Subtract sizes (component-wise, clamped to zero).
subtract :: Size2D Number -> Size2D Number -> Size2D Number
subtract (Size2D w1 h1) (Size2D w2 h2) = 
  Size2D (maxNum 0.0 (w1 - w2)) (maxNum 0.0 (h1 - h2))

-- | Component-wise maximum.
max :: Size2D Number -> Size2D Number -> Size2D Number
max (Size2D w1 h1) (Size2D w2 h2) = 
  Size2D (maxNum w1 w2) (maxNum h1 h2)

-- | Component-wise minimum.
min :: Size2D Number -> Size2D Number -> Size2D Number
min (Size2D w1 h1) (Size2D w2 h2) = 
  Size2D (minNum w1 w2) (minNum h1 h2)

-- | Linear interpolation between two sizes.
-- |
-- | `lerp s1 s2 0.0` = s1
-- | `lerp s1 s2 1.0` = s2
-- | `lerp s1 s2 0.5` = midpoint
lerp :: Size2D Number -> Size2D Number -> Number -> Size2D Number
lerp (Size2D w1 h1) (Size2D w2 h2) t =
  let t' = clamp01 t
      w = w1 + (w2 - w1) * t'
      h = h1 + (h2 - h1) * t'
  in Size2D w h

-- | Clamp size to be within min and max bounds.
clamp :: Size2D Number -> Size2D Number -> Size2D Number -> Size2D Number
clamp (Size2D minW minH) (Size2D maxW maxH) (Size2D w h) =
  Size2D (clampNum minW maxW w) (clampNum minH maxH h)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if width equals height.
isSquare :: Size2D Number -> Boolean
isSquare (Size2D w h) = w == h

-- | Check if height > width (portrait orientation).
isPortrait :: Size2D Number -> Boolean
isPortrait (Size2D w h) = h > w

-- | Check if width > height (landscape orientation).
isLandscape :: Size2D Number -> Boolean
isLandscape (Size2D w h) = w > h

-- | Check if both dimensions are zero.
isZero :: Size2D Number -> Boolean
isZero (Size2D w h) = w == 0.0 && h == 0.0

-- | Check if this size contains another size.
-- |
-- | `a.contains(b)` = true if b fits within a.
contains :: Size2D Number -> Size2D Number -> Boolean
contains (Size2D w1 h1) (Size2D w2 h2) = w1 >= w2 && h1 >= h2

-- | Check if this size fits within another size.
-- |
-- | `a.fitsWithin(b)` = true if a fits within b.
fitsWithin :: Size2D Number -> Size2D Number -> Boolean
fitsWithin (Size2D w1 h1) (Size2D w2 h2) = w1 <= w2 && h1 <= h2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Swap width and height.
transpose :: forall a. Size2D a -> Size2D a
transpose (Size2D w h) = Size2D h w

-- | Expand size by amount on all sides.
-- |
-- | `expand 10.0 (Size2D 100.0 50.0)` = Size2D 120.0 70.0
expand :: Number -> Size2D Number -> Size2D Number
expand amount (Size2D w h) = 
  Size2D (w + 2.0 * amount) (h + 2.0 * amount)

-- | Contract size by amount on all sides.
-- |
-- | Clamped to zero (can't have negative dimensions).
contract :: Number -> Size2D Number -> Size2D Number
contract amount (Size2D w h) = 
  Size2D (maxNum 0.0 (w - 2.0 * amount)) (maxNum 0.0 (h - 2.0 * amount))

-- | Grow to at least the given minimum size.
growTo :: Size2D Number -> Size2D Number -> Size2D Number
growTo = max

-- | Shrink to at most the given maximum size.
shrinkTo :: Size2D Number -> Size2D Number -> Size2D Number
shrinkTo = min

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Absolute value
absNum :: Number -> Number
absNum n
  | n < 0.0 = 0.0 - n
  | otherwise = n

-- | Maximum of two numbers
maxNum :: Number -> Number -> Number
maxNum a b
  | a >= b = a
  | otherwise = b

-- | Minimum of two numbers
minNum :: Number -> Number -> Number
minNum a b
  | a <= b = a
  | otherwise = b

-- | Clamp value to range
clampNum :: Number -> Number -> Number -> Number
clampNum minVal maxVal val
  | val < minVal = minVal
  | val > maxVal = maxVal
  | otherwise = val

-- | Clamp to 0.0-1.0
clamp01 :: Number -> Number
clamp01 = clampNum 0.0 1.0
