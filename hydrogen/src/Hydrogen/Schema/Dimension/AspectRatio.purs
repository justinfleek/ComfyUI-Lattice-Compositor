-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // dimension // aspect-ratio
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AspectRatio — Width to Height ratio.
-- |
-- | **WHY ASPECTRATIO?**
-- | AspectRatio represents the proportional relationship between width and height.
-- | It's used to maintain proportions when scaling or to define fixed proportions.
-- |
-- | **Use cases:**
-- | - Image/video aspect ratios (16:9, 4:3, 1:1)
-- | - Responsive element proportions
-- | - CSS aspect-ratio property
-- | - Cropping and resizing
-- |
-- | **Representation:**
-- | Stored as width:height ratio where height = 1.0 (normalized).
-- | A 16:9 ratio is stored as 1.777... (16/9).

module Hydrogen.Schema.Dimension.AspectRatio
  ( -- * Types
    AspectRatio(AspectRatio)
  
  -- * Constructors
  , aspectRatio
  , aspectRatioFromWH
  , aspectRatioFromSize
  
  -- * Common Ratios
  , square
  , ratio16x9
  , ratio4x3
  , ratio21x9
  , ratio3x2
  , ratio2x3
  , ratio9x16
  , ratioGolden
  
  -- * Accessors
  , toNumber
  , toWH
  , widthForHeight
  , heightForWidth
  
  -- * Operations
  , invert
  , scale
  , isWider
  , isNarrower
  
  -- * Predicates
  , isSquare
  , isLandscape
  , isPortrait
  , isEqual
  , isApproxEqual
  
  -- * Size Calculations
  , fitWidth
  , fitHeight
  , fitContain
  , fitCover
  
  -- * CSS Output
  , toCss
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (&&)
  , (||)
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

import Hydrogen.Schema.Dimension.Size2D (Size2D(Size2D))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // aspect-ratio
-- ═════════════════════════════════════════════════════════════════════════════

-- | Aspect ratio as width:height where height is normalized to 1.
-- |
-- | A value of 1.777... represents 16:9.
-- | A value of 1.0 represents square.
-- | A value of 0.5625 represents 9:16 (portrait).
newtype AspectRatio = AspectRatio Number

derive instance eqAspectRatio :: Eq AspectRatio
derive instance ordAspectRatio :: Ord AspectRatio

instance showAspectRatio :: Show AspectRatio where
  show ar = "AspectRatio(" <> toCss ar <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an AspectRatio from a numeric ratio.
-- |
-- | ```purescript
-- | aspectRatio 1.777  -- ~16:9
-- | aspectRatio 1.0    -- square
-- | ```
aspectRatio :: Number -> AspectRatio
aspectRatio n
  | n <= 0.0 = AspectRatio 1.0  -- Default to square for invalid input
  | otherwise = AspectRatio n

-- | Create from explicit width and height.
-- |
-- | ```purescript
-- | aspectRatioFromWH 16 9   -- 16:9
-- | aspectRatioFromWH 4 3    -- 4:3
-- | ```
aspectRatioFromWH :: Int -> Int -> AspectRatio
aspectRatioFromWH w h =
  if h == 0 || w == 0
    then AspectRatio 1.0
    else AspectRatio (intToNum w / intToNum h)

-- | Create from a Size2D.
aspectRatioFromSize :: Size2D Number -> AspectRatio
aspectRatioFromSize (Size2D w h) =
  if h == 0.0
    then AspectRatio 1.0
    else AspectRatio (w / h)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common ratios
-- ═════════════════════════════════════════════════════════════════════════════

-- | Square (1:1)
square :: AspectRatio
square = AspectRatio 1.0

-- | Widescreen HD (16:9)
-- |
-- | Standard for HD video, monitors, TVs.
ratio16x9 :: AspectRatio
ratio16x9 = AspectRatio (16.0 / 9.0)

-- | Traditional TV (4:3)
-- |
-- | Standard for old TVs, iPad.
ratio4x3 :: AspectRatio
ratio4x3 = AspectRatio (4.0 / 3.0)

-- | Ultra-widescreen (21:9)
-- |
-- | Cinematic, ultra-wide monitors.
ratio21x9 :: AspectRatio
ratio21x9 = AspectRatio (21.0 / 9.0)

-- | Classic film/photo (3:2)
-- |
-- | 35mm film, many DSLR cameras.
ratio3x2 :: AspectRatio
ratio3x2 = AspectRatio (3.0 / 2.0)

-- | Portrait photo (2:3)
-- |
-- | Standard portrait orientation.
ratio2x3 :: AspectRatio
ratio2x3 = AspectRatio (2.0 / 3.0)

-- | Vertical video (9:16)
-- |
-- | TikTok, Instagram Reels, Stories.
ratio9x16 :: AspectRatio
ratio9x16 = AspectRatio (9.0 / 16.0)

-- | Golden ratio (~1.618:1)
-- |
-- | Aesthetically pleasing ratio used in design.
ratioGolden :: AspectRatio
ratioGolden = AspectRatio 1.618033988749895

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the numeric ratio value.
toNumber :: AspectRatio -> Number
toNumber (AspectRatio n) = n

-- | Get width and height as integers (simplified if possible).
-- |
-- | Returns closest simple integer ratio.
toWH :: AspectRatio -> { width :: Int, height :: Int }
toWH (AspectRatio n) =
  -- Common ratios get exact values
  if absNum (n - 16.0 / 9.0) < 0.001 then { width: 16, height: 9 }
  else if absNum (n - 4.0 / 3.0) < 0.001 then { width: 4, height: 3 }
  else if absNum (n - 21.0 / 9.0) < 0.001 then { width: 21, height: 9 }
  else if absNum (n - 3.0 / 2.0) < 0.001 then { width: 3, height: 2 }
  else if absNum (n - 2.0 / 3.0) < 0.001 then { width: 2, height: 3 }
  else if absNum (n - 9.0 / 16.0) < 0.001 then { width: 9, height: 16 }
  else if absNum (n - 1.0) < 0.001 then { width: 1, height: 1 }
  -- Fallback: scale to get reasonable integers
  else 
    let h = 100
        w = roundToInt (n * 100.0)
    in { width: w, height: h }

-- | Calculate width for a given height.
widthForHeight :: Number -> AspectRatio -> Number
widthForHeight h (AspectRatio ratio) = h * ratio

-- | Calculate height for a given width.
heightForWidth :: Number -> AspectRatio -> Number
heightForWidth w (AspectRatio ratio) =
  if ratio == 0.0 then w else w / ratio

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Invert the aspect ratio (swap width and height).
-- |
-- | ```purescript
-- | invert ratio16x9  -- ratio9x16
-- | ```
invert :: AspectRatio -> AspectRatio
invert (AspectRatio n) =
  if n == 0.0 then AspectRatio 1.0 else AspectRatio (1.0 / n)

-- | Scale the aspect ratio.
-- |
-- | ```purescript
-- | scale 2.0 square  -- 2:1 (twice as wide)
-- | ```
scale :: Number -> AspectRatio -> AspectRatio
scale factor (AspectRatio n) = AspectRatio (n * factor)

-- | Check if first ratio is wider than second.
isWider :: AspectRatio -> AspectRatio -> Boolean
isWider (AspectRatio a) (AspectRatio b) = a > b

-- | Check if first ratio is narrower than second.
isNarrower :: AspectRatio -> AspectRatio -> Boolean
isNarrower (AspectRatio a) (AspectRatio b) = a < b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if ratio is square (1:1).
isSquare :: AspectRatio -> Boolean
isSquare (AspectRatio n) = absNum (n - 1.0) < 0.001

-- | Check if ratio is landscape (width > height).
isLandscape :: AspectRatio -> Boolean
isLandscape (AspectRatio n) = n > 1.0

-- | Check if ratio is portrait (height > width).
isPortrait :: AspectRatio -> Boolean
isPortrait (AspectRatio n) = n < 1.0

-- | Check if two ratios are equal.
isEqual :: AspectRatio -> AspectRatio -> Boolean
isEqual (AspectRatio a) (AspectRatio b) = a == b

-- | Check if two ratios are approximately equal (within tolerance).
isApproxEqual :: Number -> AspectRatio -> AspectRatio -> Boolean
isApproxEqual tolerance (AspectRatio a) (AspectRatio b) =
  absNum (a - b) < tolerance

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // size calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate size that fits within width while maintaining ratio.
fitWidth :: Number -> AspectRatio -> Size2D Number
fitWidth w ar = Size2D w (heightForWidth w ar)

-- | Calculate size that fits within height while maintaining ratio.
fitHeight :: Number -> AspectRatio -> Size2D Number
fitHeight h ar = Size2D (widthForHeight h ar) h

-- | Calculate size that fits within bounds (contain mode).
-- |
-- | The result fits entirely within the bounds, potentially with letterboxing.
fitContain :: Size2D Number -> AspectRatio -> Size2D Number
fitContain (Size2D boundW boundH) ar =
  let targetRatio = toNumber ar
      boundRatio = if boundH == 0.0 then 1.0 else boundW / boundH
  in if targetRatio > boundRatio
     -- Target is wider than bounds: fit to width
     then Size2D boundW (heightForWidth boundW ar)
     -- Target is taller than bounds: fit to height
     else Size2D (widthForHeight boundH ar) boundH

-- | Calculate size that covers bounds (cover mode).
-- |
-- | The result covers the entire bounds, potentially with cropping.
fitCover :: Size2D Number -> AspectRatio -> Size2D Number
fitCover (Size2D boundW boundH) ar =
  let targetRatio = toNumber ar
      boundRatio = if boundH == 0.0 then 1.0 else boundW / boundH
  in if targetRatio > boundRatio
     -- Target is wider than bounds: fit to height (crop width)
     then Size2D (widthForHeight boundH ar) boundH
     -- Target is taller than bounds: fit to width (crop height)
     else Size2D boundW (heightForWidth boundW ar)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to CSS aspect-ratio value.
-- |
-- | Uses simplified integer ratios when possible.
-- |
-- | ```purescript
-- | toCss ratio16x9  -- "16 / 9"
-- | toCss square     -- "1 / 1"
-- | ```
toCss :: AspectRatio -> String
toCss ar =
  let wh = toWH ar
  in show wh.width <> " / " <> show wh.height

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Absolute value
absNum :: Number -> Number
absNum n
  | n < 0.0 = 0.0 - n
  | otherwise = n

-- | Convert Int to Number
intToNum :: Int -> Number
intToNum i = intToNumber i
  where
  intToNumber :: Int -> Number
  intToNumber n
    | n == 0 = 0.0
    | n > 0 = 1.0 + intToNumber (n - 1)
    | otherwise = intToNumber (n + 1) - 1.0

-- | Round Number to Int
roundToInt :: Number -> Int
roundToInt n
  | n < 0.0 = 0 - roundPositive (0.0 - n)
  | otherwise = roundPositive n

-- | Round positive Number to Int
roundPositive :: Number -> Int
roundPositive n =
  let floored = floorPositive n
      frac = n - intToNum floored
  in if frac >= 0.5 then floored + 1 else floored

-- | Floor positive Number to Int
floorPositive :: Number -> Int
floorPositive n
  | n < 1.0 = 0
  | n < 2.0 = 1
  | n < 3.0 = 2
  | n < 4.0 = 3
  | n < 5.0 = 4
  | n < 10.0 = 5 + floorPositive (n - 5.0)
  | n < 100.0 = 10 + floorPositive (n - 10.0)
  | n < 1000.0 = 100 + floorPositive (n - 100.0)
  | otherwise = 1000 + floorPositive (n - 1000.0)
