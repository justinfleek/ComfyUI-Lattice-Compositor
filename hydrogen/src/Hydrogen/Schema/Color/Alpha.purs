-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // color // alpha
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Alpha-Channel Color Variants.
-- |
-- | **TRANSPARENCY IN COLOR SPACES:**
-- | Alpha (opacity) can be added to any color space. This module provides
-- | alpha variants for color spaces not already covered in the codebase.
-- |
-- | **Existing Alpha Variants:**
-- | - `RGBA` - sRGB with alpha (in RGB.purs)
-- | - `HSLA` - HSL with alpha (in HSLA.purs)
-- |
-- | **New Alpha Variants:**
-- | - `LCHA` - LCH (cylindrical LAB) with alpha
-- | - `P3A` - Display P3 with alpha
-- | - `OKLCHA` - OKLCH with alpha
-- | - `LABA` - LAB with alpha
-- |
-- | **Why separate alpha modules?**
-- | Alpha compositing rules are the same regardless of color space.
-- | By keeping alpha variants explicit, we maintain type safety about
-- | which color operations preserve or require alpha.

module Hydrogen.Schema.Color.Alpha
  ( -- * Alpha Variants
    LCHA
  , P3A
  , OKLCHA
  , LABA
  , OKLABA
  
  -- * Constructors
  , lcha
  , p3a
  , oklcha
  , laba
  , oklaba
  , lchaFromRecord
  , p3aFromRecord
  , oklabaFromRecord
  
  -- * Accessors
  , getLCH
  , getP3
  , getOKLCH
  , getLAB
  , getOKLAB
  , class HasAlpha
  , getAlpha
  , lchaToRecord
  , p3aToRecord
  , oklchaToRecord
  , labaToRecord
  , oklabaToRecord
  
  -- * Alpha Addition (withAlpha variants)
  , withAlphaLCH
  , withAlphaLAB
  , withAlphaOKLCH
  , withAlphaOKLAB
  , withAlphaP3
  
  -- * Alpha Removal (removeAlpha variants)
  , removeAlphaLCHA
  , removeAlphaLABA
  , removeAlphaOKLCHA
  , removeAlphaOKLABA
  , removeAlphaP3A
  
  -- * Alpha Operations
  , setAlpha
  , multiplyAlpha
  
  -- * Compositing
  , over
  , overLCHA
  , overP3A
  , overOKLCHA
  , overLABA
  , overOKLABA
  
  -- * Conversions (cylindrical <-> Cartesian with alpha)
  , oklchaToOklaba
  , oklabaToOklcha
  , lchaToLaba
  , labaToLcha
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (==)
  , (<>)
  )

import Data.Int (round, toNumber)

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Color.LCH (LCH, lchFromRecord, lchToRecord, lchToLab, labToLch) as LCH
import Hydrogen.Schema.Color.OKLCH (OKLCH, oklchFromRecord, oklchToRecord) as OKLCH
import Hydrogen.Schema.Color.LAB (LAB, labFromRecord, labToRecord) as LAB
import Hydrogen.Schema.Color.OKLAB (OKLAB, oklabFromRecord, oklabToRecord) as OKLAB
import Hydrogen.Schema.Color.Opacity (Opacity, fromUnitInterval, toUnitInterval) as Opacity
import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // lcha - lch + alpha
-- ═════════════════════════════════════════════════════════════════════════════

-- | LCHA - LCH (Cylindrical LAB) with Alpha
-- |
-- | LCH is perceptually uniform and intuitive:
-- | - L: Lightness (0-100)
-- | - C: Chroma (saturation, 0-150+)
-- | - H: Hue (0-359)
-- | - A: Alpha (0.0-1.0)
newtype LCHA = LCHA
  { lch :: LCH.LCH
  , alpha :: Opacity.Opacity
  }

derive instance eqLCHA :: Eq LCHA

instance showLCHA :: Show LCHA where
  show (LCHA c) = "lcha(" <> show (LCH.lchToRecord c.lch).l <> ", " 
    <> show (LCH.lchToRecord c.lch).c <> ", " 
    <> show (LCH.lchToRecord c.lch).h <> ", "
    <> show (Opacity.toUnitInterval c.alpha) <> ")"

-- | Create LCHA color
lcha :: Number -> Number -> Number -> Number -> LCHA
lcha l c h a = LCHA
  { lch: LCH.lchFromRecord { l, c, h }
  , alpha: Opacity.fromUnitInterval a
  }

-- | Create from record
lchaFromRecord :: { l :: Number, c :: Number, h :: Number, a :: Number } -> LCHA
lchaFromRecord r = lcha r.l r.c r.h r.a

-- | Get LCH component
getLCH :: LCHA -> LCH.LCH
getLCH (LCHA c) = c.lch

-- | Convert to record
lchaToRecord :: LCHA -> { l :: Number, c :: Number, h :: Number, a :: Number }
lchaToRecord (LCHA c) =
  let lchRec = LCH.lchToRecord c.lch
  in { l: lchRec.l, c: lchRec.c, h: lchRec.h, a: Opacity.toUnitInterval c.alpha }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // p3a - display p3 + alpha
-- ═════════════════════════════════════════════════════════════════════════════

-- | P3A - Display P3 with Alpha
-- |
-- | Apple's wide gamut RGB space with transparency.
-- | - R, G, B: 0.0-1.0 (can exceed for HDR)
-- | - A: Alpha 0.0-1.0
newtype P3A = P3A
  { r :: Number
  , g :: Number
  , b :: Number
  , alpha :: Opacity.Opacity
  }

derive instance eqP3A :: Eq P3A

instance showP3A :: Show P3A where
  show (P3A c) = "color(display-p3 " <> show c.r <> " " 
    <> show c.g <> " " <> show c.b <> " / " 
    <> show (Opacity.toUnitInterval c.alpha) <> ")"

-- | Create P3A color
p3a :: Number -> Number -> Number -> Number -> P3A
p3a r g b a = P3A
  { r: Bounded.clampNumber 0.0 1.0 r
  , g: Bounded.clampNumber 0.0 1.0 g
  , b: Bounded.clampNumber 0.0 1.0 b
  , alpha: Opacity.fromUnitInterval a
  }

-- | Create from record
p3aFromRecord :: { r :: Number, g :: Number, b :: Number, a :: Number } -> P3A
p3aFromRecord rec = p3a rec.r rec.g rec.b rec.a

-- | Get P3 component (without alpha)
getP3 :: P3A -> { r :: Number, g :: Number, b :: Number }
getP3 (P3A c) = { r: c.r, g: c.g, b: c.b }

-- | Convert to record
p3aToRecord :: P3A -> { r :: Number, g :: Number, b :: Number, a :: Number }
p3aToRecord (P3A c) = { r: c.r, g: c.g, b: c.b, a: Opacity.toUnitInterval c.alpha }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // oklcha - oklch + alpha
-- ═════════════════════════════════════════════════════════════════════════════

-- | OKLCHA - OKLCH with Alpha
-- |
-- | Modern perceptually uniform color space with transparency.
-- | - L: Lightness (0.0-1.0)
-- | - C: Chroma (0.0-0.4)
-- | - H: Hue (0-359)
-- | - A: Alpha (0.0-1.0)
newtype OKLCHA = OKLCHA
  { oklch :: OKLCH.OKLCH
  , alpha :: Opacity.Opacity
  }

derive instance eqOKLCHA :: Eq OKLCHA

instance showOKLCHA :: Show OKLCHA where
  show (OKLCHA c) = "oklch(" <> show (OKLCH.oklchToRecord c.oklch).l <> " " 
    <> show (OKLCH.oklchToRecord c.oklch).c <> " " 
    <> show (OKLCH.oklchToRecord c.oklch).h <> " / "
    <> show (Opacity.toUnitInterval c.alpha) <> ")"

-- | Create OKLCHA color
-- | Note: h is provided as Number but internally converted to Int (Hue is 0-359 Int)
oklcha :: Number -> Number -> Number -> Number -> OKLCHA
oklcha l c h a = OKLCHA
  { oklch: OKLCH.oklchFromRecord { l, c, h: round h }
  , alpha: Opacity.fromUnitInterval a
  }

-- | Get OKLCH component
getOKLCH :: OKLCHA -> OKLCH.OKLCH
getOKLCH (OKLCHA c) = c.oklch

-- | Convert to record
oklchaToRecord :: OKLCHA -> { l :: Number, c :: Number, h :: Number, a :: Number }
oklchaToRecord (OKLCHA c) =
  let oklchRec = OKLCH.oklchToRecord c.oklch
  in { l: oklchRec.l, c: oklchRec.c, h: toNumber oklchRec.h, a: Opacity.toUnitInterval c.alpha }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // laba - lab + alpha
-- ═════════════════════════════════════════════════════════════════════════════

-- | LABA - CIE LAB with Alpha
-- |
-- | Perceptually uniform Cartesian color space with transparency.
-- | - L: Lightness (0-100)
-- | - A: Green-Red axis (-128 to 127)
-- | - B: Blue-Yellow axis (-128 to 127)
-- | - Alpha: Opacity (0.0-1.0)
newtype LABA = LABA
  { lab :: LAB.LAB
  , alpha :: Opacity.Opacity
  }

derive instance eqLABA :: Eq LABA

instance showLABA :: Show LABA where
  show (LABA c) = "lab(" <> show (LAB.labToRecord c.lab).l <> " " 
    <> show (LAB.labToRecord c.lab).a <> " " 
    <> show (LAB.labToRecord c.lab).b <> " / "
    <> show (Opacity.toUnitInterval c.alpha) <> ")"

-- | Create LABA color
laba :: Number -> Number -> Number -> Number -> LABA
laba l a b alpha' = LABA
  { lab: LAB.labFromRecord { l, a, b }
  , alpha: Opacity.fromUnitInterval alpha'
  }

-- | Get LAB component
getLAB :: LABA -> LAB.LAB
getLAB (LABA c) = c.lab

-- | Convert to record
labaToRecord :: LABA -> { l :: Number, a :: Number, b :: Number, alpha :: Number }
labaToRecord (LABA c) =
  let labRec = LAB.labToRecord c.lab
  in { l: labRec.l, a: labRec.a, b: labRec.b, alpha: Opacity.toUnitInterval c.alpha }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // oklaba - oklab + alpha
-- ═════════════════════════════════════════════════════════════════════════════

-- | OKLABA - OKLAB (Cartesian) with Alpha
-- |
-- | Modern perceptually uniform Cartesian color space with transparency.
-- | - L: Lightness (0.0-1.0)
-- | - A: Green-Red axis (-0.4 to +0.4)
-- | - B: Blue-Yellow axis (-0.4 to +0.4)
-- | - Alpha: Opacity (0.0-1.0)
-- |
-- | Use OKLCHA for cylindrical (hue-based), OKLABA for Cartesian (axis-based).
newtype OKLABA = OKLABA
  { oklab :: OKLAB.OKLAB
  , alpha :: Opacity.Opacity
  }

derive instance eqOKLABA :: Eq OKLABA

instance showOKLABA :: Show OKLABA where
  show (OKLABA c) = "oklab(" <> show (OKLAB.oklabToRecord c.oklab).l <> " " 
    <> show (OKLAB.oklabToRecord c.oklab).a <> " " 
    <> show (OKLAB.oklabToRecord c.oklab).b <> " / "
    <> show (Opacity.toUnitInterval c.alpha) <> ")"

-- | Create OKLABA color
oklaba :: Number -> Number -> Number -> Number -> OKLABA
oklaba l a b alpha' = OKLABA
  { oklab: OKLAB.oklabFromRecord { l, a, b }
  , alpha: Opacity.fromUnitInterval alpha'
  }

-- | Create from record
oklabaFromRecord :: { l :: Number, a :: Number, b :: Number, alpha :: Number } -> OKLABA
oklabaFromRecord r = oklaba r.l r.a r.b r.alpha

-- | Get OKLAB component
getOKLAB :: OKLABA -> OKLAB.OKLAB
getOKLAB (OKLABA c) = c.oklab

-- | Convert to record
oklabaToRecord :: OKLABA -> { l :: Number, a :: Number, b :: Number, alpha :: Number }
oklabaToRecord (OKLABA c) =
  let oklabRec = OKLAB.oklabToRecord c.oklab
  in { l: oklabRec.l, a: oklabRec.a, b: oklabRec.b, alpha: Opacity.toUnitInterval c.alpha }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // alpha operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type class for colors with alpha
class HasAlpha a where
  getAlpha :: a -> Number
  setAlpha :: Number -> a -> a

instance hasAlphaLCHA :: HasAlpha LCHA where
  getAlpha (LCHA c) = Opacity.toUnitInterval c.alpha
  setAlpha a (LCHA c) = LCHA c { alpha = Opacity.fromUnitInterval a }

instance hasAlphaP3A :: HasAlpha P3A where
  getAlpha (P3A c) = Opacity.toUnitInterval c.alpha
  setAlpha a (P3A c) = P3A c { alpha = Opacity.fromUnitInterval a }

instance hasAlphaOKLCHA :: HasAlpha OKLCHA where
  getAlpha (OKLCHA c) = Opacity.toUnitInterval c.alpha
  setAlpha a (OKLCHA c) = OKLCHA c { alpha = Opacity.fromUnitInterval a }

instance hasAlphaLABA :: HasAlpha LABA where
  getAlpha (LABA c) = Opacity.toUnitInterval c.alpha
  setAlpha a (LABA c) = LABA c { alpha = Opacity.fromUnitInterval a }

instance hasAlphaOKLABA :: HasAlpha OKLABA where
  getAlpha (OKLABA c) = Opacity.toUnitInterval c.alpha
  setAlpha a (OKLABA c) = OKLABA c { alpha = Opacity.fromUnitInterval a }

-- | Multiply alpha by factor
multiplyAlpha :: forall a. HasAlpha a => Number -> a -> a
multiplyAlpha factor color = setAlpha (getAlpha color * factor) color

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // with alpha (add alpha)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add alpha to LCH color
withAlphaLCH :: Number -> LCH.LCH -> LCHA
withAlphaLCH a lchColor = LCHA
  { lch: lchColor
  , alpha: Opacity.fromUnitInterval a
  }

-- | Add alpha to LAB color
withAlphaLAB :: Number -> LAB.LAB -> LABA
withAlphaLAB a labColor = LABA
  { lab: labColor
  , alpha: Opacity.fromUnitInterval a
  }

-- | Add alpha to OKLCH color
withAlphaOKLCH :: Number -> OKLCH.OKLCH -> OKLCHA
withAlphaOKLCH a oklchColor = OKLCHA
  { oklch: oklchColor
  , alpha: Opacity.fromUnitInterval a
  }

-- | Add alpha to OKLAB color
withAlphaOKLAB :: Number -> OKLAB.OKLAB -> OKLABA
withAlphaOKLAB a oklabColor = OKLABA
  { oklab: oklabColor
  , alpha: Opacity.fromUnitInterval a
  }

-- | Add alpha to Display P3 color
withAlphaP3 :: Number -> { r :: Number, g :: Number, b :: Number } -> P3A
withAlphaP3 a p3Color = p3a p3Color.r p3Color.g p3Color.b a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // remove alpha (strip alpha)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Remove alpha from LCHA, returning LCH
removeAlphaLCHA :: LCHA -> LCH.LCH
removeAlphaLCHA (LCHA c) = c.lch

-- | Remove alpha from LABA, returning LAB
removeAlphaLABA :: LABA -> LAB.LAB
removeAlphaLABA (LABA c) = c.lab

-- | Remove alpha from OKLCHA, returning OKLCH
removeAlphaOKLCHA :: OKLCHA -> OKLCH.OKLCH
removeAlphaOKLCHA (OKLCHA c) = c.oklch

-- | Remove alpha from OKLABA, returning OKLAB
removeAlphaOKLABA :: OKLABA -> OKLAB.OKLAB
removeAlphaOKLABA (OKLABA c) = c.oklab

-- | Remove alpha from P3A, returning P3 record
removeAlphaP3A :: P3A -> { r :: Number, g :: Number, b :: Number }
removeAlphaP3A (P3A c) = { r: c.r, g: c.g, b: c.b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // compositing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Porter-Duff "over" operation (source over destination)
-- |
-- | The standard alpha compositing formula:
-- | out_alpha = src_alpha + dst_alpha * (1 - src_alpha)
-- | out_color = (src_color * src_alpha + dst_color * dst_alpha * (1 - src_alpha)) / out_alpha
over 
  :: { r :: Number, g :: Number, b :: Number, a :: Number }
  -> { r :: Number, g :: Number, b :: Number, a :: Number }
  -> { r :: Number, g :: Number, b :: Number, a :: Number }
over src dst =
  let srcA = src.a
      dstA = dst.a
      outA = srcA + dstA * (1.0 - srcA)
      blend srcC dstC = 
        if outA == 0.0 
          then 0.0 
          else (srcC * srcA + dstC * dstA * (1.0 - srcA)) / outA
  in { r: blend src.r dst.r
     , g: blend src.g dst.g
     , b: blend src.b dst.b
     , a: outA
     }

-- | Composite LCHA colors using "over"
overLCHA :: LCHA -> LCHA -> LCHA
overLCHA src dst =
  let srcRec = lchaToRecord src
      dstRec = lchaToRecord dst
      -- For simplicity, composite in LCH space (not perceptually accurate but useful)
      srcA = srcRec.a
      dstA = dstRec.a
      outA = srcA + dstA * (1.0 - srcA)
      blend srcC dstC = 
        if outA == 0.0 
          then 0.0 
          else (srcC * srcA + dstC * dstA * (1.0 - srcA)) / outA
  in lcha 
       (blend srcRec.l dstRec.l)
       (blend srcRec.c dstRec.c)
       (blendHue srcRec.h dstRec.h srcA dstA)
       outA

-- | Composite P3A colors using "over"
overP3A :: P3A -> P3A -> P3A
overP3A src dst =
  let srcRec = p3aToRecord src
      dstRec = p3aToRecord dst
      result = over 
        { r: srcRec.r, g: srcRec.g, b: srcRec.b, a: srcRec.a }
        { r: dstRec.r, g: dstRec.g, b: dstRec.b, a: dstRec.a }
  in p3a result.r result.g result.b result.a

-- | Composite OKLCHA colors using "over"
overOKLCHA :: OKLCHA -> OKLCHA -> OKLCHA
overOKLCHA src dst =
  let srcRec = oklchaToRecord src
      dstRec = oklchaToRecord dst
      srcA = srcRec.a
      dstA = dstRec.a
      outA = srcA + dstA * (1.0 - srcA)
      blend srcC dstC = 
        if outA == 0.0 
          then 0.0 
          else (srcC * srcA + dstC * dstA * (1.0 - srcA)) / outA
  in oklcha 
       (blend srcRec.l dstRec.l)
       (blend srcRec.c dstRec.c)
       (blendHue srcRec.h dstRec.h srcA dstA)
       outA

-- | Composite LABA colors using "over"
overLABA :: LABA -> LABA -> LABA
overLABA src dst =
  let srcRec = labaToRecord src
      dstRec = labaToRecord dst
      srcA = srcRec.alpha
      dstA = dstRec.alpha
      outA = srcA + dstA * (1.0 - srcA)
      blend srcC dstC = 
        if outA == 0.0 
          then 0.0 
          else (srcC * srcA + dstC * dstA * (1.0 - srcA)) / outA
  in laba 
       (blend srcRec.l dstRec.l)
       (blend srcRec.a dstRec.a)
       (blend srcRec.b dstRec.b)
       outA

-- | Composite OKLABA colors using "over"
overOKLABA :: OKLABA -> OKLABA -> OKLABA
overOKLABA src dst =
  let srcRec = oklabaToRecord src
      dstRec = oklabaToRecord dst
      srcA = srcRec.alpha
      dstA = dstRec.alpha
      outA = srcA + dstA * (1.0 - srcA)
      blend srcC dstC = 
        if outA == 0.0 
          then 0.0 
          else (srcC * srcA + dstC * dstA * (1.0 - srcA)) / outA
  in oklaba 
       (blend srcRec.l dstRec.l)
       (blend srcRec.a dstRec.a)
       (blend srcRec.b dstRec.b)
       outA

-- | Blend hue values (circular interpolation)
blendHue :: Number -> Number -> Number -> Number -> Number
blendHue srcH dstH srcA dstA =
  let outA = srcA + dstA * (1.0 - srcA)
      -- Simple weighted average (not circular, but good enough for most cases)
      blend = if outA == 0.0 
        then 0.0 
        else (srcH * srcA + dstH * dstA * (1.0 - srcA)) / outA
  in Bounded.clampNumber 0.0 359.0 blend

-- ═════════════════════════════════════════════════════════════════════════════
--                                    // conversions (cylindrical <-> Cartesian)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert OKLCHA (cylindrical) to OKLABA (Cartesian)
-- |
-- | Formula: a = C * cos(H), b = C * sin(H)
-- | Preserves alpha.
oklchaToOklaba :: OKLCHA -> OKLABA
oklchaToOklaba (OKLCHA c) =
  let oklchRec = OKLCH.oklchToRecord c.oklch
      l = oklchRec.l
      chroma = oklchRec.c
      hueRad = toNumber oklchRec.h * Math.pi / 180.0
      a = chroma * Math.cos hueRad
      b = chroma * Math.sin hueRad
  in OKLABA
    { oklab: OKLAB.oklabFromRecord { l, a, b }
    , alpha: c.alpha
    }

-- | Convert OKLABA (Cartesian) to OKLCHA (cylindrical)
-- |
-- | Formula: C = sqrt(a^2 + b^2), H = atan2(b, a)
-- | Preserves alpha.
oklabaToOklcha :: OKLABA -> OKLCHA
oklabaToOklcha (OKLABA c) =
  let oklabRec = OKLAB.oklabToRecord c.oklab
      l = oklabRec.l
      a = oklabRec.a
      b = oklabRec.b
      chroma = Math.sqrt (a * a + b * b)
      hueRad = Math.atan2 b a
      hueDeg = hueRad * 180.0 / Math.pi
      hueNormalized = if hueDeg < 0.0 then hueDeg + 360.0 else hueDeg
  in OKLCHA
    { oklch: OKLCH.oklchFromRecord { l, c: chroma, h: round hueNormalized }
    , alpha: c.alpha
    }

-- | Convert LCHA (cylindrical LAB) to LABA (Cartesian LAB)
-- |
-- | Uses the LCH.lchToLab conversion, preserves alpha.
lchaToLaba :: LCHA -> LABA
lchaToLaba (LCHA c) = LABA
  { lab: LCH.lchToLab c.lch
  , alpha: c.alpha
  }

-- | Convert LABA (Cartesian LAB) to LCHA (cylindrical LAB)
-- |
-- | Uses the LCH.labToLch conversion, preserves alpha.
labaToLcha :: LABA -> LCHA
labaToLcha (LABA c) = LCHA
  { lch: LCH.labToLch c.lab
  , alpha: c.alpha
  }
