-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // color // lcha
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LCHA - CIE L*C*h° with alpha transparency.
-- |
-- | **WHY LCHA?**
-- | LCHA extends LCH with an opacity channel, enabling:
-- | - Perceptually uniform transparent colors
-- | - Proper alpha blending in perceptual space
-- | - Accurate color compositing for professional workflows
-- |
-- | **Components:**
-- | - **L*** (Lightness): 0 (black) to 100 (white)
-- | - **C*** (Chroma): 0 (gray) to ~230 (most saturated)
-- | - **h°** (Hue): 0-360 degrees on perceptual color wheel
-- | - **α** (Alpha): 0-100% opacity (0 = transparent, 100 = opaque)
-- |
-- | **Advantages over HSLA:**
-- | - Perceptually uniform lightness adjustments
-- | - Accurate chroma manipulation (vs. HSL's flawed saturation)
-- | - Hue rotation that preserves perceived brightness
-- |
-- | **Use cases:**
-- | - Transparent overlays with perceptually accurate colors
-- | - Color grading with transparency
-- | - UI components with perceptually uniform hover states

module Hydrogen.Schema.Color.LCHA
  ( -- * Types
    LCHA
  
  -- * Constructors
  , lcha
  , lchaFromRecord
  , fromLCH
  , withAlpha
  
  -- * Accessors
  , toLCH
  , alpha
  , lchaToRecord
  
  -- * Operations
  , increaseLuminance
  , decreaseLuminance
  , increaseChroma
  , decreaseChroma
  , rotateHue
  , fadeIn
  , fadeOut
  , setAlpha
  
  -- * CSS Output
  , lchaToCss
  
  -- * Comparison
  , isEqual
  , isFullyOpaque
  , isFullyTransparent
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (==)
  , (&&)
  , (<>)
  )

import Hydrogen.Schema.Color.LCH as LCH
import Hydrogen.Schema.Color.Opacity as Op

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // lcha
-- ═════════════════════════════════════════════════════════════════════════════

-- | LCHA color value — LCH with an alpha channel.
-- |
-- | Composes LCH (perceptually uniform color) with Opacity (0-100%).
-- | 0% = fully transparent, 100% = fully opaque.
newtype LCHA = LCHA
  { color :: LCH.LCH
  , alpha :: Op.Opacity
  }

derive instance eqLCHA :: Eq LCHA
derive instance ordLCHA :: Ord LCHA

instance showLCHA :: Show LCHA where
  show = lchaToCss

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an LCHA color from raw values.
-- |
-- | - L* (Lightness): 0-100
-- | - C* (Chroma): 0+ (typically 0-230)
-- | - h° (Hue): 0-360 degrees (wraps)
-- | - α (Alpha): 0-100 (percentage): 0 = transparent, 100 = opaque
-- |
-- | ```purescript
-- | lcha 50.0 80.0 30.0 100  -- Saturated orange, fully opaque
-- | lcha 70.0 50.0 200.0 50  -- Cyan-ish, half transparent
-- | lcha 0.0 0.0 0.0 0       -- Black, fully transparent
-- | ```
lcha :: Number -> Number -> Number -> Int -> LCHA
lcha l c h a = LCHA
  { color: LCH.lch l c h
  , alpha: Op.opacity a
  }

-- | Create an LCHA color from a record.
lchaFromRecord :: { l :: Number, c :: Number, h :: Number, a :: Int } -> LCHA
lchaFromRecord { l, c, h, a } = lcha l c h a

-- | Create LCHA from LCH with full opacity.
fromLCH :: LCH.LCH -> LCHA
fromLCH lchColor = LCHA
  { color: lchColor
  , alpha: Op.opacity 100
  }

-- | Create LCHA from LCH with specified alpha.
withAlpha :: LCH.LCH -> Int -> LCHA
withAlpha lchColor a = LCHA
  { color: lchColor
  , alpha: Op.opacity a
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the LCH portion (without alpha).
toLCH :: LCHA -> LCH.LCH
toLCH (LCHA lcha') = lcha'.color

-- | Extract the alpha (opacity).
alpha :: LCHA -> Op.Opacity
alpha (LCHA lcha') = lcha'.alpha

-- | Convert LCHA to a record of raw values.
lchaToRecord :: LCHA -> { l :: Number, c :: Number, h :: Number, a :: Int }
lchaToRecord (LCHA lcha') =
  let rec = LCH.lchToRecord lcha'.color
  in { l: rec.l
     , c: rec.c
     , h: rec.h
     , a: Op.unwrap lcha'.alpha
     }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Increase L* (luminance) by percentage — PERCEPTUALLY UNIFORM.
-- |
-- | ```purescript
-- | increaseLuminance 10.0 color  -- Actually looks 10% lighter
-- | ```
increaseLuminance :: Number -> LCHA -> LCHA
increaseLuminance percent (LCHA lcha') = LCHA
  { color: LCH.increaseLuminance percent lcha'.color
  , alpha: lcha'.alpha
  }

-- | Decrease L* (luminance) by percentage — PERCEPTUALLY UNIFORM.
decreaseLuminance :: Number -> LCHA -> LCHA
decreaseLuminance percent (LCHA lcha') = LCHA
  { color: LCH.decreaseLuminance percent lcha'.color
  , alpha: lcha'.alpha
  }

-- | Increase C* (chroma) by percentage — PERCEPTUALLY UNIFORM.
-- |
-- | ```purescript
-- | increaseChroma 20.0 color  -- 20% more vivid
-- | ```
increaseChroma :: Number -> LCHA -> LCHA
increaseChroma percent (LCHA lcha') = LCHA
  { color: LCH.increaseChroma percent lcha'.color
  , alpha: lcha'.alpha
  }

-- | Decrease C* (chroma) by percentage — PERCEPTUALLY UNIFORM.
decreaseChroma :: Number -> LCHA -> LCHA
decreaseChroma percent (LCHA lcha') = LCHA
  { color: LCH.decreaseChroma percent lcha'.color
  , alpha: lcha'.alpha
  }

-- | Rotate hue by degrees.
-- |
-- | ```purescript
-- | rotateHue 180.0 color  -- Complementary color
-- | rotateHue 120.0 color  -- Triadic relationship
-- | ```
rotateHue :: Number -> LCHA -> LCHA
rotateHue degrees (LCHA lcha') = LCHA
  { color: LCH.rotateHue degrees lcha'.color
  , alpha: lcha'.alpha
  }

-- | Increase opacity (make more opaque).
-- |
-- | ```purescript
-- | fadeIn 20 color  -- 20% more opaque
-- | ```
fadeIn :: Int -> LCHA -> LCHA
fadeIn amount (LCHA lcha') =
  let current = Op.unwrap lcha'.alpha
      new = current + amount
  in LCHA { color: lcha'.color, alpha: Op.opacity new }

-- | Decrease opacity (make more transparent).
-- |
-- | ```purescript
-- | fadeOut 20 color  -- 20% more transparent
-- | ```
fadeOut :: Int -> LCHA -> LCHA
fadeOut amount (LCHA lcha') =
  let current = Op.unwrap lcha'.alpha
      new = current - amount
  in LCHA { color: lcha'.color, alpha: Op.opacity new }

-- | Set alpha to a specific value.
setAlpha :: Int -> LCHA -> LCHA
setAlpha a (LCHA lcha') = LCHA { color: lcha'.color, alpha: Op.opacity a }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to CSS lch() function with alpha.
-- |
-- | ```purescript
-- | lchaToCss (lcha 50.0 80.0 30.0 75)
-- | -- "lch(50 80 30 / 0.75)"
-- | ```
lchaToCss :: LCHA -> String
lchaToCss (LCHA lcha') =
  let rec = LCH.lchToRecord lcha'.color
      l = show rec.l
      c = show rec.c
      h = show rec.h
      a = Op.toUnitInterval lcha'.alpha
  in "lch(" <> l <> " " <> c <> " " <> h <> " / " <> show a <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two LCHA colors are equal.
isEqual :: LCHA -> LCHA -> Boolean
isEqual (LCHA a) (LCHA b) =
  let recA = LCH.lchToRecord a.color
      recB = LCH.lchToRecord b.color
  in recA.l == recB.l &&
     recA.c == recB.c &&
     recA.h == recB.h &&
     Op.unwrap a.alpha == Op.unwrap b.alpha

-- | Check if color is fully opaque (alpha = 100%).
isFullyOpaque :: LCHA -> Boolean
isFullyOpaque (LCHA lcha') = Op.unwrap lcha'.alpha == 100

-- | Check if color is fully transparent (alpha = 0%).
isFullyTransparent :: LCHA -> Boolean
isFullyTransparent (LCHA lcha') = Op.unwrap lcha'.alpha == 0
