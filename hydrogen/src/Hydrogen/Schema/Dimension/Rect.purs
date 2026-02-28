-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // dimension // rect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Rect — Rectangle defined by origin point and size.
-- |
-- | **WHY RECT?**
-- | Rect represents an axis-aligned rectangular region:
-- | - Origin (top-left corner position)
-- | - Size (width and height)
-- |
-- | This is the fundamental 2D bounding primitive, used for:
-- | - Element bounds
-- | - Hit testing
-- | - Layout regions
-- | - Clipping areas
-- | - Viewports
-- |
-- | **Coordinate convention:**
-- | Origin is at top-left (CSS/screen convention).
-- | Y increases downward.

module Hydrogen.Schema.Dimension.Rect
  ( -- * Types
    Rect(Rect)
  
  -- * Constructors
  , rect
  , rectFromRecord
  , rectFromCorners
  , rectFromCenter
  , rectZero
  , rectUnit
  
  -- * Accessors
  , origin
  , size
  , x
  , y
  , width
  , height
  , toRecord
  
  -- * Corner Points
  , topLeft
  , topRight
  , bottomLeft
  , bottomRight
  , center
  
  -- * Edge Values
  , left
  , right
  , top
  , bottom
  
  -- * Operations
  , area
  , perimeter
  , translate
  , scale
  , scaleFromCenter
  , expand
  , contract
  , inset
  , union
  , intersection
  , lerp
  
  -- * Predicates
  , isEmpty
  , containsPoint
  , containsRect
  , intersects
  , isEqual
  
  -- * Conversions
  , normalize
  , toInset
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
  , (||)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Dimension.Point2D (Point2D(Point2D))
import Hydrogen.Schema.Dimension.Point2D as P
import Hydrogen.Schema.Dimension.Size2D (Size2D(Size2D))
import Hydrogen.Schema.Dimension.Size2D as S
import Hydrogen.Schema.Dimension.Inset (Inset)
import Hydrogen.Schema.Dimension.Inset as I

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // rect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis-aligned rectangle defined by origin and size.
-- |
-- | Origin is the top-left corner (screen coordinates).
-- | Size is width and height (always non-negative after normalization).
data Rect = Rect Point2D (Size2D Number)

derive instance eqRect :: Eq Rect
derive instance ordRect :: Ord Rect

instance showRect :: Show Rect where
  show (Rect (Point2D px py) (Size2D w h)) = 
    "Rect(" <> show px <> ", " <> show py <> ", " <> show w <> "×" <> show h <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Rect from origin x, y and size width, height.
-- |
-- | ```purescript
-- | rect 100.0 50.0 200.0 100.0  -- x=100, y=50, width=200, height=100
-- | ```
rect :: Number -> Number -> Number -> Number -> Rect
rect px py w h = Rect (Point2D px py) (Size2D (absNum w) (absNum h))

-- | Create from a record.
rectFromRecord :: { x :: Number, y :: Number, width :: Number, height :: Number } -> Rect
rectFromRecord { x: px, y: py, width: w, height: h } = rect px py w h

-- | Create from two corner points.
-- |
-- | The rectangle is normalized so origin is top-left.
rectFromCorners :: Point2D -> Point2D -> Rect
rectFromCorners (Point2D x1 y1) (Point2D x2 y2) =
  let minX = minNum x1 x2
      minY = minNum y1 y2
      maxX = maxNum x1 x2
      maxY = maxNum y1 y2
  in Rect (Point2D minX minY) (Size2D (maxX - minX) (maxY - minY))

-- | Create from center point and size.
rectFromCenter :: Point2D -> Size2D Number -> Rect
rectFromCenter (Point2D cx cy) (Size2D w h) =
  let halfW = w / 2.0
      halfH = h / 2.0
  in Rect (Point2D (cx - halfW) (cy - halfH)) (Size2D w h)

-- | Zero rect at origin.
rectZero :: Rect
rectZero = Rect (Point2D 0.0 0.0) (Size2D 0.0 0.0)

-- | Unit rect (0,0,1,1).
rectUnit :: Rect
rectUnit = Rect (Point2D 0.0 0.0) (Size2D 1.0 1.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get origin point (top-left).
origin :: Rect -> Point2D
origin (Rect o _) = o

-- | Get size.
size :: Rect -> Size2D Number
size (Rect _ s) = s

-- | Get x coordinate of origin.
x :: Rect -> Number
x (Rect o _) = P.x o

-- | Get y coordinate of origin.
y :: Rect -> Number
y (Rect o _) = P.y o

-- | Get width.
width :: Rect -> Number
width (Rect _ s) = S.width s

-- | Get height.
height :: Rect -> Number
height (Rect _ s) = S.height s

-- | Convert to record.
toRecord :: Rect -> { x :: Number, y :: Number, width :: Number, height :: Number }
toRecord r = { x: x r, y: y r, width: width r, height: height r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // corner points
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get top-left corner (same as origin).
topLeft :: Rect -> Point2D
topLeft = origin

-- | Get top-right corner.
topRight :: Rect -> Point2D
topRight r = Point2D (x r + width r) (y r)

-- | Get bottom-left corner.
bottomLeft :: Rect -> Point2D
bottomLeft r = Point2D (x r) (y r + height r)

-- | Get bottom-right corner.
bottomRight :: Rect -> Point2D
bottomRight r = Point2D (x r + width r) (y r + height r)

-- | Get center point.
center :: Rect -> Point2D
center r = Point2D (x r + width r / 2.0) (y r + height r / 2.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // edge values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get left edge x coordinate.
left :: Rect -> Number
left = x

-- | Get right edge x coordinate.
right :: Rect -> Number
right r = x r + width r

-- | Get top edge y coordinate.
top :: Rect -> Number
top = y

-- | Get bottom edge y coordinate.
bottom :: Rect -> Number
bottom r = y r + height r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate area.
area :: Rect -> Number
area r = width r * height r

-- | Calculate perimeter.
perimeter :: Rect -> Number
perimeter r = 2.0 * (width r + height r)

-- | Translate rect by dx, dy.
translate :: Number -> Number -> Rect -> Rect
translate dx dy (Rect o s) = Rect (P.translate dx dy o) s

-- | Scale rect from origin by factor.
scale :: Number -> Rect -> Rect
scale factor (Rect (Point2D px py) (Size2D w h)) =
  Rect (Point2D (px * factor) (py * factor)) (Size2D (w * factor) (h * factor))

-- | Scale rect from its center by factor.
scaleFromCenter :: Number -> Rect -> Rect
scaleFromCenter factor r =
  let c = center r
      newW = width r * factor
      newH = height r * factor
  in rectFromCenter c (Size2D newW newH)

-- | Expand rect by amount on all sides.
expand :: Number -> Rect -> Rect
expand amount (Rect (Point2D px py) (Size2D w h)) =
  Rect 
    (Point2D (px - amount) (py - amount)) 
    (Size2D (w + 2.0 * amount) (h + 2.0 * amount))

-- | Contract rect by amount on all sides.
-- |
-- | Size is clamped to zero (can't have negative dimensions).
contract :: Number -> Rect -> Rect
contract amount (Rect (Point2D px py) (Size2D w h)) =
  let newW = maxNum 0.0 (w - 2.0 * amount)
      newH = maxNum 0.0 (h - 2.0 * amount)
      -- Adjust origin to keep center
      newX = px + minNum amount (w / 2.0)
      newY = py + minNum amount (h / 2.0)
  in Rect (Point2D newX newY) (Size2D newW newH)

-- | Apply inset to rect (shrink by inset amounts).
inset :: Inset -> Rect -> Rect
inset ins (Rect (Point2D px py) (Size2D w h)) =
  let newX = px + I.left ins
      newY = py + I.top ins
      newW = maxNum 0.0 (w - I.totalHorizontal ins)
      newH = maxNum 0.0 (h - I.totalVertical ins)
  in Rect (Point2D newX newY) (Size2D newW newH)

-- | Calculate union of two rects (smallest rect containing both).
union :: Rect -> Rect -> Rect
union r1 r2 =
  let minX = minNum (left r1) (left r2)
      minY = minNum (top r1) (top r2)
      maxX = maxNum (right r1) (right r2)
      maxY = maxNum (bottom r1) (bottom r2)
  in Rect (Point2D minX minY) (Size2D (maxX - minX) (maxY - minY))

-- | Calculate intersection of two rects.
-- |
-- | Returns Nothing if rects don't intersect.
intersection :: Rect -> Rect -> Maybe Rect
intersection r1 r2 =
  let minX = maxNum (left r1) (left r2)
      minY = maxNum (top r1) (top r2)
      maxX = minNum (right r1) (right r2)
      maxY = minNum (bottom r1) (bottom r2)
  in if minX < maxX && minY < maxY
     then Just (Rect (Point2D minX minY) (Size2D (maxX - minX) (maxY - minY)))
     else Nothing

-- | Linear interpolation between two rects.
lerp :: Rect -> Rect -> Number -> Rect
lerp r1 r2 t =
  let t' = clamp01 t
      px = x r1 + (x r2 - x r1) * t'
      py = y r1 + (y r2 - y r1) * t'
      w = width r1 + (width r2 - width r1) * t'
      h = height r1 + (height r2 - height r1) * t'
  in Rect (Point2D px py) (Size2D w h)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if rect has zero area.
isEmpty :: Rect -> Boolean
isEmpty r = width r == 0.0 || height r == 0.0

-- | Check if rect contains a point.
containsPoint :: Point2D -> Rect -> Boolean
containsPoint (Point2D px py) r =
  px >= left r && px <= right r && py >= top r && py <= bottom r

-- | Check if this rect fully contains another rect.
containsRect :: Rect -> Rect -> Boolean
containsRect inner outer =
  left inner >= left outer &&
  right inner <= right outer &&
  top inner >= top outer &&
  bottom inner <= bottom outer

-- | Check if two rects intersect.
intersects :: Rect -> Rect -> Boolean
intersects r1 r2 =
  left r1 < right r2 &&
  right r1 > left r2 &&
  top r1 < bottom r2 &&
  bottom r1 > top r2

-- | Check if two rects are equal.
isEqual :: Rect -> Rect -> Boolean
isEqual r1 r2 =
  x r1 == x r2 && y r1 == y r2 && width r1 == width r2 && height r1 == height r2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalize rect so size is non-negative.
-- |
-- | If width or height is negative, adjusts origin and flips sign.
normalize :: Rect -> Rect
normalize (Rect (Point2D px py) (Size2D w h)) =
  let newX = if w < 0.0 then px + w else px
      newW = absNum w
      newY = if h < 0.0 then py + h else py
      newH = absNum h
  in Rect (Point2D newX newY) (Size2D newW newH)

-- | Convert rect bounds to Inset (distances from edges).
-- |
-- | Useful for converting rect position to padding/margin values
-- | relative to a container.
toInset :: Rect -> Rect -> Inset
toInset container inner =
  I.inset
    (top inner - top container)       -- top
    (right container - right inner)   -- right
    (bottom container - bottom inner) -- bottom
    (left inner - left container)     -- left

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

-- | Clamp to 0.0-1.0
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n <= 1.0 = n
  | otherwise = 1.0
