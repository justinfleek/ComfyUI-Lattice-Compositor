-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // lch
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LCH - CIE L*C*h° perceptually uniform color space (cylindrical LAB).
-- |
-- | **WHY LCH?**
-- | LCH is LAB expressed in cylindrical coordinates, like HSL but perceptually
-- | uniform. This makes it easier to:
-- | - Adjust saturation (chroma) independently
-- | - Rotate hue while maintaining perceptual correctness
-- | - Create harmonious palettes with accurate color relationships
-- |
-- | **Components:**
-- | - **L*** (Lightness): 0 (black) to 100 (white) - same as LAB
-- | - **C*** (Chroma): 0 (gray) to ~230 (most saturated), unbounded
-- | - **h°** (Hue): 0-360 degrees on perceptual color wheel
-- |
-- | **Advantage over HSL:**
-- | HSL's "saturation" and "lightness" are NOT perceptually uniform.
-- | LCH's "chroma" and "lightness" ARE perceptually uniform.
-- |
-- | **Use cases:**
-- | - Color wheel with accurate perceptual distances
-- | - "More saturated" operations that actually look more saturated
-- | - Hue rotation that preserves perceived brightness
-- | - Professional color grading

module Hydrogen.Schema.Color.LCH
  ( -- * Types
    LCH
  , LchL
  , LchC
  , LchH
  
  -- * Constructors
  , lch
  , lchFromRecord
  
  -- * Accessors
  , lchL
  , lchC
  , lchH
  , lchToRecord
  , toRecord
  
  -- * Operations (perceptually uniform)
  , increaseLuminance
  , decreaseLuminance
  , increaseChroma
  , decreaseChroma
  , rotateHue
  
  -- * Conversion
  , labToLch
  , lchToLab
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (&&)
  , (<>)
  )

import Data.Number (sqrt, atan2, cos, sin, pi, floor)
import Hydrogen.Schema.Color.LAB as LAB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | L* component (Lightness): 0-100 (same as LAB)
newtype LchL = LchL Number

derive instance eqLchL :: Eq LchL
derive instance ordLchL :: Ord LchL

instance showLchL :: Show LchL where
  show (LchL n) = "LchL " <> show n

lchLValue :: Number -> LchL
lchLValue n
  | n < 0.0 = LchL 0.0
  | n > 100.0 = LchL 100.0
  | otherwise = LchL n

unwrapLchL :: LchL -> Number
unwrapLchL (LchL n) = n

-- | C* component (Chroma/Saturation): 0+ (unbounded, but typically 0-230)
newtype LchC = LchC Number

derive instance eqLchC :: Eq LchC
derive instance ordLchC :: Ord LchC

instance showLchC :: Show LchC where
  show (LchC n) = "LchC " <> show n

lchCValue :: Number -> LchC
lchCValue n
  | n < 0.0 = LchC 0.0
  | otherwise = LchC n

unwrapLchC :: LchC -> Number
unwrapLchC (LchC n) = n

-- | h° component (Hue): 0-360 degrees (wraps)
newtype LchH = LchH Number

derive instance eqLchH :: Eq LchH
derive instance ordLchH :: Ord LchH

instance showLchH :: Show LchH where
  show (LchH n) = "LchH " <> show n

lchHValue :: Number -> LchH
lchHValue n =
  let wrapped = if n >= 0.0 && n < 360.0
                then n
                else n - 360.0 * floor (n / 360.0)
      normalized = if wrapped < 0.0 then wrapped + 360.0 else wrapped
  in LchH normalized

unwrapLchH :: LchH -> Number
unwrapLchH (LchH n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | LCH color - perceptually uniform cylindrical color space
type LCH =
  { l :: LchL  -- ^ Lightness (0-100)
  , c :: LchC  -- ^ Chroma (0+, unbounded)
  , h :: LchH  -- ^ Hue (0-360°, wraps)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create LCH color from components
-- |
-- | ```purescript
-- | lch 50.0 50.0 0.0    -- Red-ish
-- | lch 50.0 0.0 0.0     -- Gray (no chroma)
-- | lch 100.0 0.0 0.0    -- White
-- | ```
lch :: Number -> Number -> Number -> LCH
lch l c h =
  { l: lchLValue l
  , c: lchCValue c
  , h: lchHValue h
  }

-- | Create from record
lchFromRecord :: { l :: Number, c :: Number, h :: Number } -> LCH
lchFromRecord { l, c, h } = lch l c h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get L* (lightness) component
lchL :: LCH -> LchL
lchL color = color.l

-- | Get C* (chroma) component
lchC :: LCH -> LchC
lchC color = color.c

-- | Get h° (hue) component
lchH :: LCH -> LchH
lchH color = color.h

-- | Convert to record - explicitly named for backend persistence
lchToRecord :: LCH -> { l :: Number, c :: Number, h :: Number }
lchToRecord color =
  { l: unwrapLchL color.l
  , c: unwrapLchC color.c
  , h: unwrapLchH color.h
  }

-- | Generic alias for lchToRecord
toRecord :: LCH -> { l :: Number, c :: Number, h :: Number }
toRecord = lchToRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- ═════════════════════════════════════════════════════════════════════════════
--                                      // operations // perceptually // uniform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Increase LCH L* (luminance) by percentage - PERCEPTUALLY UNIFORM.
-- |
-- | Same as LAB.increaseLuminance but operates directly on cylindrical LCH.
-- |
-- | **Semantically explicit:** `increaseLuminance` distinguishes from HSL.increaseLightness.
-- |
-- | ```purescript
-- | increaseLuminance 10.0 color  -- Actually looks 10% lighter (perceptual)
-- | ```
increaseLuminance :: Number -> LCH -> LCH
increaseLuminance percent color =
  let l = unwrapLchL color.l
      l' = l + percent
  in color { l = lchLValue l' }

-- | Decrease LCH L* (luminance) by percentage - PERCEPTUALLY UNIFORM.
-- |
-- | ```purescript
-- | decreaseLuminance 10.0 color  -- Actually looks 10% darker (perceptual)
-- | ```
decreaseLuminance :: Number -> LCH -> LCH
decreaseLuminance percent color =
  let l = unwrapLchL color.l
      l' = l - percent
  in color { l = lchLValue l' }

-- | Increase LCH C (chroma) by percentage - PERCEPTUALLY UNIFORM.
-- |
-- | **Chroma vs Saturation:** LCH C is perceptually uniform chroma, distinct from
-- | HSL saturation. Use this for accurate "20% more vivid" operations.
-- |
-- | **Semantically explicit:** `increaseChroma` distinguishes from HSL.increaseSaturation.
-- |
-- | ```purescript
-- | increaseChroma 20.0 color  -- 20% more vivid (perceptually accurate)
-- | ```
increaseChroma :: Number -> LCH -> LCH
increaseChroma percent color =
  let c = unwrapLchC color.c
      c' = c * (1.0 + percent / 100.0)
  in color { c = lchCValue c' }

-- | Decrease LCH C (chroma) by percentage - PERCEPTUALLY UNIFORM.
-- |
-- | ```purescript
-- | decreaseChroma 20.0 color  -- 20% less vivid (perceptually accurate)
-- | ```
decreaseChroma :: Number -> LCH -> LCH
decreaseChroma percent color =
  let c = unwrapLchC color.c
      c' = c * (1.0 - percent / 100.0)
  in color { c = lchCValue c' }

-- | Rotate hue by degrees
-- |
-- | ```purescript
-- | rotateHue 180.0 color  -- Complementary color (perceptually accurate)
-- | rotateHue 120.0 color  -- Triadic relationship
-- | ```
rotateHue :: Number -> LCH -> LCH
rotateHue degrees color =
  let h = unwrapLchH color.h
      h' = h + degrees
  in color { h = lchHValue h' }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert LAB to LCH (rectangular to cylindrical)
-- |
-- | ```purescript
-- | labToLch labColor  -- Convert to cylindrical for easier hue manipulation
-- | ```
labToLch :: LAB.LAB -> LCH
labToLch labColor =
  let rec = LAB.toRecord labColor
      l = rec.l
      a = rec.a
      b = rec.b
      
      -- Calculate chroma (distance from gray axis)
      c = sqrt (a * a + b * b)
      
      -- Calculate hue angle (degrees)
      -- atan2 returns radians, convert to degrees
      hRad = atan2 b a
      hDeg = hRad * 180.0 / pi
      -- Normalize to 0-360
      h = if hDeg < 0.0 then hDeg + 360.0 else hDeg
  in
    lch l c h

-- | Convert LCH to LAB (cylindrical to rectangular)
-- |
-- | ```purescript
-- | lchToLab lchColor  -- Convert back to LAB for other operations
-- | ```
lchToLab :: LCH -> LAB.LAB
lchToLab lchColor =
  let l = unwrapLchL lchColor.l
      c = unwrapLchC lchColor.c
      h = unwrapLchH lchColor.h
      
      -- Convert hue to radians
      hRad = h * pi / 180.0
      
      -- Calculate a* and b* from polar coordinates
      a = c * cos hRad
      b = c * sin hRad
  in
    LAB.lab l a b
