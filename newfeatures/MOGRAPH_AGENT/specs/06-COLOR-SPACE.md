# Specification 06: Color Space
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-06  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Internal Technical  

---

## 1. Overview

This specification defines color handling with:

1. **Multiple color spaces** (RGB, HSL, HSV, LAB, LCH)
2. **Perceptual interpolation** for smooth gradients
3. **Bounded values** with deterministic conversion
4. **Accessibility** (contrast ratios, color blindness)

---

## 2. Core Color Types

### 2.1 Lean4 Definitions

```lean4
/-- RGB color with bounded components [0,1] -/
structure RGB where
  r : Float
  g : Float
  b : Float
  h_r : 0 ≤ r ∧ r ≤ 1
  h_g : 0 ≤ g ∧ g ≤ 1
  h_b : 0 ≤ b ∧ b ≤ 1
  deriving Repr

/-- RGBA with alpha channel -/
structure RGBA where
  rgb : RGB
  a : Float
  h_a : 0 ≤ a ∧ a ≤ 1
  deriving Repr

/-- HSL color space -/
structure HSL where
  h : Float  -- Hue [0, 360)
  s : Float  -- Saturation [0, 1]
  l : Float  -- Lightness [0, 1]
  h_h : 0 ≤ h ∧ h < 360
  h_s : 0 ≤ s ∧ s ≤ 1
  h_l : 0 ≤ l ∧ l ≤ 1
  deriving Repr

/-- HSV color space -/
structure HSV where
  h : Float  -- Hue [0, 360)
  s : Float  -- Saturation [0, 1]
  v : Float  -- Value [0, 1]
  h_h : 0 ≤ h ∧ h < 360
  h_s : 0 ≤ s ∧ s ≤ 1
  h_v : 0 ≤ v ∧ v ≤ 1
  deriving Repr

/-- CIELAB color space (perceptually uniform) -/
structure LAB where
  l : Float  -- Lightness [0, 100]
  a : Float  -- Green-Red [-128, 127]
  b : Float  -- Blue-Yellow [-128, 127]
  h_l : 0 ≤ l ∧ l ≤ 100
  h_a : -128 ≤ a ∧ a ≤ 127
  h_b : -128 ≤ b ∧ b ≤ 127
  deriving Repr

/-- LCH color space (polar LAB) -/
structure LCH where
  l : Float  -- Lightness [0, 100]
  c : Float  -- Chroma [0, ~230]
  h : Float  -- Hue [0, 360)
  h_l : 0 ≤ l ∧ l ≤ 100
  h_c : 0 ≤ c
  h_h : 0 ≤ h ∧ h < 360
  deriving Repr
```

### 2.2 Haskell Implementation

```haskell
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}

module Lattice.Color.Types where

import Lattice.Core.Bounded
import GHC.Generics (Generic)
import Data.Ratio (Rational)

-- | RGB color with bounded components
data RGB = RGB
  { rgbR :: !(Bounded Double)  -- [0, 1]
  , rgbG :: !(Bounded Double)  -- [0, 1]
  , rgbB :: !(Bounded Double)  -- [0, 1]
  } deriving (Eq, Show, Generic)

-- | RGBA color
data RGBA = RGBA
  { rgbaRGB :: !RGB
  , rgbaA   :: !(Bounded Double)  -- [0, 1]
  } deriving (Eq, Show, Generic)

-- | RGB constraints
rgbConstraint :: (Double, Double, Double)
rgbConstraint = (0, 1, 0)

-- | Smart constructor for RGB
mkRGB :: Double -> Double -> Double -> Either String RGB
mkRGB r g b = RGB
  <$> mkBounded r 0 1 0
  <*> mkBounded g 0 1 0
  <*> mkBounded b 0 1 0

-- | Smart constructor for RGBA
mkRGBA :: Double -> Double -> Double -> Double -> Either String RGBA
mkRGBA r g b a = RGBA
  <$> mkRGB r g b
  <*> mkBounded a 0 1 1

-- | HSL color
data HSL = HSL
  { hslH :: !(Bounded Double)  -- [0, 360)
  , hslS :: !(Bounded Double)  -- [0, 1]
  , hslL :: !(Bounded Double)  -- [0, 1]
  } deriving (Eq, Show, Generic)

-- | HSV color
data HSV = HSV
  { hsvH :: !(Bounded Double)  -- [0, 360)
  , hsvS :: !(Bounded Double)  -- [0, 1]
  , hsvV :: !(Bounded Double)  -- [0, 1]
  } deriving (Eq, Show, Generic)

-- | CIELAB color (perceptually uniform)
data LAB = LAB
  { labL :: !(Bounded Double)  -- [0, 100]
  , labA :: !(Bounded Double)  -- [-128, 127]
  , labB :: !(Bounded Double)  -- [-128, 127]
  } deriving (Eq, Show, Generic)

-- | LCH color (cylindrical LAB)
data LCH = LCH
  { lchL :: !(Bounded Double)  -- [0, 100]
  , lchC :: !(Bounded Double)  -- [0, 230]
  , lchH :: !(Bounded Double)  -- [0, 360)
  } deriving (Eq, Show, Generic)

-- | Color with unified representation
data Color
  = ColorRGB !RGB
  | ColorRGBA !RGBA
  | ColorHSL !HSL
  | ColorHSV !HSV
  | ColorLAB !LAB
  | ColorLCH !LCH
  | ColorHex !Text
  | ColorNamed !NamedColor
  deriving (Eq, Show, Generic)

-- | Named colors (CSS standard)
data NamedColor
  = Red | Orange | Yellow | Green | Blue | Purple | Pink
  | Brown | Black | White | Gray | Transparent
  deriving (Eq, Show, Enum, Bounded, Generic)

-- | Convert named color to RGB
namedToRGB :: NamedColor -> RGB
namedToRGB = \case
  Red         -> unsafeRGB 1 0 0
  Orange      -> unsafeRGB 1 0.647 0
  Yellow      -> unsafeRGB 1 1 0
  Green       -> unsafeRGB 0 0.502 0
  Blue        -> unsafeRGB 0 0 1
  Purple      -> unsafeRGB 0.502 0 0.502
  Pink        -> unsafeRGB 1 0.753 0.796
  Brown       -> unsafeRGB 0.647 0.165 0.165
  Black       -> unsafeRGB 0 0 0
  White       -> unsafeRGB 1 1 1
  Gray        -> unsafeRGB 0.502 0.502 0.502
  Transparent -> unsafeRGB 0 0 0  -- Alpha handled separately
  where
    unsafeRGB r g b = RGB 
      (unsafeMkBounded r 0 1 0)
      (unsafeMkBounded g 0 1 0)
      (unsafeMkBounded b 0 1 0)
```

---

## 3. Color Conversions

### 3.1 RGB ↔ HSL

```haskell
-- | Convert RGB to HSL (exact rational arithmetic)
rgbToHSL :: RGB -> HSL
rgbToHSL (RGB br bg bb) =
  let r = toRational $ bValue br
      g = toRational $ bValue bg
      b = toRational $ bValue bb
      
      cmax = maximum [r, g, b]
      cmin = minimum [r, g, b]
      delta = cmax - cmin
      
      l = (cmax + cmin) / 2
      
      s = if delta == 0 then 0
          else delta / (1 - abs (2 * l - 1))
      
      h' = if delta == 0 then 0
           else if cmax == r then mod' ((g - b) / delta) 6
           else if cmax == g then (b - r) / delta + 2
           else (r - g) / delta + 4
      
      h = h' * 60
      hNorm = if h < 0 then h + 360 else h
      
  in HSL
       (unsafeMkBounded (fromRational hNorm) 0 360 0)
       (unsafeMkBounded (fromRational $ max 0 $ min 1 s) 0 1 0)
       (unsafeMkBounded (fromRational $ max 0 $ min 1 l) 0 1 0.5)
  where
    mod' x m = x - m * fromIntegral (floor (x / m))

-- | Convert HSL to RGB
hslToRGB :: HSL -> RGB
hslToRGB (HSL bh bs bl) =
  let h = toRational $ bValue bh
      s = toRational $ bValue bs
      l = toRational $ bValue bl
      
      c = (1 - abs (2 * l - 1)) * s
      x = c * (1 - abs (mod' (h / 60) 2 - 1))
      m = l - c / 2
      
      (r', g', b') = case floor (h / 60) `mod` 6 of
        0 -> (c, x, 0)
        1 -> (x, c, 0)
        2 -> (0, c, x)
        3 -> (0, x, c)
        4 -> (x, 0, c)
        5 -> (c, 0, x)
        _ -> (0, 0, 0)
      
  in RGB
       (unsafeMkBounded (fromRational $ r' + m) 0 1 0)
       (unsafeMkBounded (fromRational $ g' + m) 0 1 0)
       (unsafeMkBounded (fromRational $ b' + m) 0 1 0)
  where
    mod' x m = x - m * fromIntegral (floor (x / m))
```

### 3.2 RGB ↔ LAB (via XYZ)

```haskell
-- | D65 white point
d65White :: (Rational, Rational, Rational)
d65White = (95047 % 100000, 100000 % 100000, 108883 % 100000)

-- | Convert RGB to XYZ (sRGB with D65 white point)
rgbToXYZ :: RGB -> (Rational, Rational, Rational)
rgbToXYZ (RGB br bg bb) =
  let r = linearize $ toRational $ bValue br
      g = linearize $ toRational $ bValue bg
      b = linearize $ toRational $ bValue bb
      
      -- sRGB to XYZ matrix (D65)
      x = r * (4124564 % 10000000) + g * (3575761 % 10000000) + b * (1804375 % 10000000)
      y = r * (2126729 % 10000000) + g * (7151522 % 10000000) + b * (721750  % 10000000)
      z = r * (193339  % 10000000) + g * (1191920 % 10000000) + b * (9503041 % 10000000)
  in (x, y, z)
  where
    linearize v = if v > (4045 % 100000)
                  then ((v + (55 % 1000)) / (1055 % 1000)) ^^ 24 / 10
                  else v / (1292 % 100)

-- | Convert XYZ to RGB
xyzToRGB :: (Rational, Rational, Rational) -> RGB
xyzToRGB (x, y, z) =
  let -- XYZ to sRGB matrix
      r' = x * (32406255 % 10000000) + y * (-15372080 % 10000000) + z * (-4986286 % 10000000)
      g' = x * (-9689307 % 10000000) + y * (18760108 % 10000000)  + z * (415560  % 10000000)
      b' = x * (556434   % 10000000) + y * (-2040259 % 10000000)  + z * (10572252 % 10000000)
      
      r = gammaCompress r'
      g = gammaCompress g'
      b = gammaCompress b'
  in RGB
       (unsafeMkBounded (fromRational $ clamp r) 0 1 0)
       (unsafeMkBounded (fromRational $ clamp g) 0 1 0)
       (unsafeMkBounded (fromRational $ clamp b) 0 1 0)
  where
    gammaCompress v = if v > (313 % 100000)
                      then (1055 % 1000) * (v ^^ (1 % 24)) - (55 % 1000)
                      else (1292 % 100) * v
    clamp v = max 0 (min 1 v)

-- | Convert XYZ to LAB
xyzToLAB :: (Rational, Rational, Rational) -> LAB
xyzToLAB (x, y, z) =
  let (xn, yn, zn) = d65White
      
      fx = labF (x / xn)
      fy = labF (y / yn)
      fz = labF (z / zn)
      
      l = 116 * fy - 16
      a = 500 * (fx - fy)
      b = 200 * (fy - fz)
  in LAB
       (unsafeMkBounded (fromRational $ max 0 $ min 100 l) 0 100 50)
       (unsafeMkBounded (fromRational $ max (-128) $ min 127 a) (-128) 127 0)
       (unsafeMkBounded (fromRational $ max (-128) $ min 127 b) (-128) 127 0)
  where
    labF t = if t > (216 % 24389)
             then t ^^ (1 % 3)
             else (24389 % 3132) * t + (16 % 116)

-- | Convert LAB to XYZ
labToXYZ :: LAB -> (Rational, Rational, Rational)
labToXYZ (LAB bl ba bb) =
  let l = toRational $ bValue bl
      a = toRational $ bValue ba
      b = toRational $ bValue bb
      
      (xn, yn, zn) = d65White
      
      fy = (l + 16) / 116
      fx = a / 500 + fy
      fz = fy - b / 200
      
      x = xn * labFInv fx
      y = yn * labFInv fy
      z = zn * labFInv fz
  in (x, y, z)
  where
    labFInv t = let t3 = t * t * t
                in if t3 > (216 % 24389)
                   then t3
                   else (t - 16 % 116) * (3132 % 24389)

-- | Convert RGB to LAB
rgbToLAB :: RGB -> LAB
rgbToLAB = xyzToLAB . rgbToXYZ

-- | Convert LAB to RGB
labToRGB :: LAB -> RGB
labToRGB = xyzToRGB . labToXYZ
```

### 3.3 LAB ↔ LCH

```haskell
-- | Convert LAB to LCH (polar form)
labToLCH :: LAB -> LCH
labToLCH (LAB bl ba bb) =
  let l = toRational $ bValue bl
      a = toRational $ bValue ba
      b = toRational $ bValue bb
      
      c = sqrt $ fromRational (a * a + b * b)
      h' = atan2 (fromRational b) (fromRational a) * 180 / pi
      h = if h' < 0 then h' + 360 else h'
  in LCH
       (unsafeMkBounded (bValue bl) 0 100 50)
       (unsafeMkBounded (max 0 c) 0 230 0)
       (unsafeMkBounded (max 0 $ min 360 h) 0 360 0)

-- | Convert LCH to LAB
lchToLAB :: LCH -> LAB
lchToLAB (LCH bl bc bh) =
  let l = bValue bl
      c = bValue bc
      h = bValue bh * pi / 180  -- Convert to radians
      
      a = c * cos h
      b = c * sin h
  in LAB
       (unsafeMkBounded l 0 100 50)
       (unsafeMkBounded (max (-128) $ min 127 a) (-128) 127 0)
       (unsafeMkBounded (max (-128) $ min 127 b) (-128) 127 0)
```

---

## 4. Color Interpolation

### 4.1 Perceptual Interpolation

```haskell
-- | Interpolation mode
data InterpolationMode
  = InterpRGB      -- Linear RGB (fast but not perceptual)
  | InterpHSL      -- HSL interpolation (hue-aware)
  | InterpLAB      -- LAB interpolation (perceptually uniform)
  | InterpLCH      -- LCH interpolation (perceptual with hue)
  deriving (Eq, Show, Enum, Bounded)

-- | Interpolate colors
interpolateColor :: InterpolationMode -> Rational -> RGB -> RGB -> RGB
interpolateColor mode t c1 c2 =
  let t' = max 0 (min 1 t)
  in case mode of
       InterpRGB -> interpolateRGB t' c1 c2
       InterpHSL -> interpolateHSL t' c1 c2
       InterpLAB -> interpolateLAB t' c1 c2
       InterpLCH -> interpolateLCH t' c1 c2

-- | RGB interpolation
interpolateRGB :: Rational -> RGB -> RGB -> RGB
interpolateRGB t (RGB r1 g1 b1) (RGB r2 g2 b2) =
  let lerp a b = fromRational $ toRational (bValue a) + t * (toRational (bValue b) - toRational (bValue a))
  in RGB
       (unsafeMkBounded (lerp r1 r2) 0 1 0)
       (unsafeMkBounded (lerp g1 g2) 0 1 0)
       (unsafeMkBounded (lerp b1 b2) 0 1 0)

-- | HSL interpolation (shortest hue path)
interpolateHSL :: Rational -> RGB -> RGB -> RGB
interpolateHSL t c1 c2 =
  let hsl1 = rgbToHSL c1
      hsl2 = rgbToHSL c2
      
      h1 = toRational $ bValue $ hslH hsl1
      h2 = toRational $ bValue $ hslH hsl2
      
      -- Shortest path around hue circle
      dh = h2 - h1
      dh' = if dh > 180 then dh - 360
            else if dh < -180 then dh + 360
            else dh
      
      h = mod' (h1 + t * dh') 360
      s = lerp (hslS hsl1) (hslS hsl2)
      l = lerp (hslL hsl1) (hslL hsl2)
      
      hsl = HSL
              (unsafeMkBounded (fromRational h) 0 360 0)
              (unsafeMkBounded s 0 1 0)
              (unsafeMkBounded l 0 1 0.5)
  in hslToRGB hsl
  where
    lerp a b = bValue a + fromRational t * (bValue b - bValue a)
    mod' x m = x - m * fromIntegral (floor (x / m))

-- | LAB interpolation (perceptually uniform)
interpolateLAB :: Rational -> RGB -> RGB -> RGB
interpolateLAB t c1 c2 =
  let lab1 = rgbToLAB c1
      lab2 = rgbToLAB c2
      
      l = lerp (labL lab1) (labL lab2)
      a = lerp (labA lab1) (labA lab2)
      b = lerp (labB lab1) (labB lab2)
      
      lab = LAB
              (unsafeMkBounded l 0 100 50)
              (unsafeMkBounded a (-128) 127 0)
              (unsafeMkBounded b (-128) 127 0)
  in labToRGB lab
  where
    lerp x y = bValue x + fromRational t * (bValue y - bValue x)

-- | LCH interpolation (perceptual with hue)
interpolateLCH :: Rational -> RGB -> RGB -> RGB
interpolateLCH t c1 c2 =
  let lch1 = labToLCH $ rgbToLAB c1
      lch2 = labToLCH $ rgbToLAB c2
      
      h1 = toRational $ bValue $ lchH lch1
      h2 = toRational $ bValue $ lchH lch2
      
      -- Shortest hue path
      dh = h2 - h1
      dh' = if dh > 180 then dh - 360
            else if dh < -180 then dh + 360
            else dh
      
      l = lerp (lchL lch1) (lchL lch2)
      c = lerp (lchC lch1) (lchC lch2)
      h = mod' (h1 + t * dh') 360
      
      lch = LCH
              (unsafeMkBounded l 0 100 50)
              (unsafeMkBounded (max 0 c) 0 230 0)
              (unsafeMkBounded (fromRational h) 0 360 0)
  in labToRGB $ lchToLAB lch
  where
    lerp x y = bValue x + fromRational t * (bValue y - bValue x)
    mod' x m = x - m * fromIntegral (floor (x / m))
```

---

## 5. Gradients

### 5.1 Gradient Types

```haskell
-- | Gradient stop
data GradientStop = GradientStop
  { gsOffset :: !(Bounded Double)  -- [0, 1]
  , gsColor  :: !RGB
  } deriving (Eq, Show, Generic)

-- | Gradient definition
data Gradient = Gradient
  { gradStops :: ![GradientStop]      -- At least 2 stops
  , gradType  :: !GradientType
  , gradInterp :: !InterpolationMode
  } deriving (Eq, Show, Generic)

data GradientType
  = GradientLinear !Point !Point           -- Start, end
  | GradientRadial !Point !Point !Double   -- Center, focus, radius
  deriving (Eq, Show, Generic)

-- | Validate gradient
validateGradient :: Gradient -> Either String Gradient
validateGradient g
  | length (gradStops g) < 2 = Left "Gradient must have at least 2 stops"
  | not (hasBoundaryStops g) = Left "Gradient must have stops at 0 and 1"
  | not (sorted g) = Left "Gradient stops must be sorted"
  | otherwise = Right g
  where
    hasBoundaryStops g' = 
      any ((== 0) . bValue . gsOffset) (gradStops g') &&
      any ((== 1) . bValue . gsOffset) (gradStops g')
    sorted g' = 
      let offsets = map (bValue . gsOffset) (gradStops g')
      in offsets == sort offsets

-- | Evaluate gradient at position
evalGradient :: Gradient -> Rational -> RGB
evalGradient g t =
  let stops = gradStops g
      t' = max 0 (min 1 t)
  in case findStopPair stops t' of
       (stop1, stop2) ->
         let o1 = toRational $ bValue $ gsOffset stop1
             o2 = toRational $ bValue $ gsOffset stop2
             localT = if o2 == o1 then 0 else (t' - o1) / (o2 - o1)
         in interpolateColor (gradInterp g) localT (gsColor stop1) (gsColor stop2)
  where
    findStopPair stops t' =
      let pairs = zip stops (tail stops)
      in case find (\(s1, s2) -> toRational (bValue $ gsOffset s1) <= t' && 
                                  t' <= toRational (bValue $ gsOffset s2)) pairs of
           Just pair -> pair
           Nothing -> (last stops, last stops)  -- Fallback
```

---

## 6. Accessibility

### 6.1 Contrast Ratio (WCAG)

```haskell
-- | Calculate relative luminance (WCAG 2.1)
relativeLuminance :: RGB -> Rational
relativeLuminance (RGB br bg bb) =
  let r = linearize $ toRational $ bValue br
      g = linearize $ toRational $ bValue bg
      b = linearize $ toRational $ bValue bb
  in (2126 % 10000) * r + (7152 % 10000) * g + (722 % 10000) * b
  where
    linearize v = if v <= (4045 % 100000)
                  then v / (1292 % 100)
                  else ((v + (55 % 1000)) / (1055 % 1000)) ^^ (24 % 10)

-- | Calculate contrast ratio (WCAG 2.1)
contrastRatio :: RGB -> RGB -> Rational
contrastRatio c1 c2 =
  let l1 = relativeLuminance c1
      l2 = relativeLuminance c2
      lighter = max l1 l2
      darker = min l1 l2
  in (lighter + (5 % 100)) / (darker + (5 % 100))

-- | WCAG conformance levels
data WCAGLevel = WCAGFail | WCAGAA | WCAGAAA
  deriving (Eq, Show, Ord, Enum, Bounded)

-- | Check WCAG text contrast
wcagTextContrast :: RGB -> RGB -> Bool -> WCAGLevel
wcagTextContrast fg bg isLargeText =
  let ratio = fromRational $ contrastRatio fg bg :: Double
  in if isLargeText
     then if ratio >= 4.5 then WCAGAAA
          else if ratio >= 3.0 then WCAGAA
          else WCAGFail
     else if ratio >= 7.0 then WCAGAAA
          else if ratio >= 4.5 then WCAGAA
          else WCAGFail

-- | Suggest accessible color
suggestAccessible :: RGB -> RGB -> Bool -> RGB
suggestAccessible fg bg isLargeText =
  let targetRatio = if isLargeText then 3.0 else 4.5
      currentRatio = fromRational $ contrastRatio fg bg
  in if currentRatio >= targetRatio
     then fg
     else adjustLuminance fg bg targetRatio
  where
    adjustLuminance fg' bg' target =
      let bgLum = fromRational $ relativeLuminance bg'
          -- Calculate required foreground luminance
          -- (L1 + 0.05) / (L2 + 0.05) = ratio
          needed = if bgLum > 0.5
                   then (bgLum + 0.05) / target - 0.05  -- Darken
                   else target * (bgLum + 0.05) - 0.05  -- Lighten
      in adjustToLuminance fg' (toRational needed)
    
    adjustToLuminance c targetLum =
      let lab = rgbToLAB c
          -- Adjust L* to achieve target luminance
          newL = max 0 $ min 100 $ fromRational targetLum * 100
      in labToRGB $ lab { labL = unsafeMkBounded newL 0 100 50 }
```

### 6.2 Color Blindness Simulation

```haskell
-- | Color blindness types
data ColorBlindness
  = Protanopia    -- Red-blind
  | Deuteranopia  -- Green-blind
  | Tritanopia    -- Blue-blind
  | Achromatopsia -- Total color blindness
  deriving (Eq, Show, Enum, Bounded)

-- | Simulate color blindness
simulateColorBlindness :: ColorBlindness -> RGB -> RGB
simulateColorBlindness cb (RGB br bg bb) =
  let r = toRational $ bValue br
      g = toRational $ bValue bg
      b = toRational $ bValue bb
      
      (r', g', b') = case cb of
        Protanopia -> 
          ( (567 % 1000) * r + (433 % 1000) * g
          , (558 % 1000) * g + (442 % 1000) * r
          , (242 % 1000) * r + (757 % 1000) * b + (1 % 1000) * g
          )
        Deuteranopia ->
          ( (625 % 1000) * r + (375 % 1000) * g
          , (7 % 10) * g + (3 % 10) * r
          , (3 % 10) * g + (7 % 10) * b
          )
        Tritanopia ->
          ( (95 % 100) * r + (5 % 100) * g
          , (433 % 1000) * g + (567 % 1000) * b
          , (475 % 1000) * g + (525 % 1000) * b
          )
        Achromatopsia ->
          let gray = (299 % 1000) * r + (587 % 1000) * g + (114 % 1000) * b
          in (gray, gray, gray)
  in RGB
       (unsafeMkBounded (fromRational $ clamp r') 0 1 0)
       (unsafeMkBounded (fromRational $ clamp g') 0 1 0)
       (unsafeMkBounded (fromRational $ clamp b') 0 1 0)
  where
    clamp x = max 0 (min 1 x)
```

---

## 7. Lottie Serialization

```haskell
-- | Convert RGB to Lottie format [r, g, b]
rgbToLottie :: RGB -> Value
rgbToLottie (RGB r g b) = Array $ V.fromList
  [ Number $ fromFloatDigits $ bValue r
  , Number $ fromFloatDigits $ bValue g
  , Number $ fromFloatDigits $ bValue b
  ]

-- | Convert RGBA to Lottie format [r, g, b, a]
rgbaToLottie :: RGBA -> Value
rgbaToLottie (RGBA rgb a) = Array $ V.fromList
  [ Number $ fromFloatDigits $ bValue $ rgbR rgb
  , Number $ fromFloatDigits $ bValue $ rgbG rgb
  , Number $ fromFloatDigits $ bValue $ rgbB rgb
  , Number $ fromFloatDigits $ bValue a
  ]

-- | Parse hex color
parseHex :: Text -> Either String RGB
parseHex hex =
  let stripped = T.dropWhile (== '#') hex
  in case T.length stripped of
       6 -> parseHex6 stripped
       3 -> parseHex3 stripped
       8 -> fst <$> parseHex8 stripped  -- Ignore alpha
       _ -> Left "Invalid hex color"
  where
    parseHex6 s = do
      r <- parseHexByte (T.take 2 s)
      g <- parseHexByte (T.take 2 $ T.drop 2 s)
      b <- parseHexByte (T.drop 4 s)
      mkRGB (fromIntegral r / 255) (fromIntegral g / 255) (fromIntegral b / 255)
    
    parseHex3 s = 
      let expand c = T.pack [c, c]
      in parseHex6 $ T.concatMap expand s
    
    parseHex8 s = do
      rgb <- parseHex6 (T.take 6 s)
      a <- parseHexByte (T.drop 6 s)
      pure (rgb, fromIntegral a / 255)
    
    parseHexByte t = case readHex (T.unpack t) of
      [(n, "")] | n >= 0 && n <= 255 -> Right n
      _ -> Left $ "Invalid hex byte: " ++ T.unpack t

-- | Format as hex
rgbToHex :: RGB -> Text
rgbToHex (RGB r g b) =
  let toHex v = T.pack $ printf "%02x" (round (bValue v * 255) :: Int)
  in "#" <> toHex r <> toHex g <> toHex b
```

---

## 8. Lean4 Proofs

```lean4
namespace ColorProofs

/-- RGB to HSL to RGB is identity (within precision) -/
theorem rgb_hsl_roundtrip (c : RGB) :
    ∀ ε > 0, colorDistance c (hslToRGB (rgbToHSL c)) < ε := by
  sorry

/-- LAB interpolation midpoint is perceptually equidistant -/
theorem lab_midpoint_equidistant (c1 c2 : RGB) :
    let mid = interpolateLAB (1/2) c1 c2
    let lab1 = rgbToLAB c1
    let lab2 = rgbToLAB c2
    let labMid = rgbToLAB mid
    labDistance lab1 labMid = labDistance labMid lab2 := by
  sorry

/-- Contrast ratio is symmetric -/
theorem contrast_symmetric (c1 c2 : RGB) :
    contrastRatio c1 c2 = contrastRatio c2 c1 := by
  simp [contrastRatio]
  -- max and min are symmetric when swapped
  sorry

/-- Relative luminance is in [0, 1] -/
theorem luminance_bounded (c : RGB) :
    0 ≤ relativeLuminance c ∧ relativeLuminance c ≤ 1 := by
  sorry

end ColorProofs
```

---

## 9. Constraint Summary

| Type | Property | Min | Max | Default | Unit |
|------|----------|-----|-----|---------|------|
| RGB | r, g, b | 0 | 1 | 0 | normalized |
| RGBA | a | 0 | 1 | 1 | normalized |
| HSL | h | 0 | 360 | 0 | degrees |
| HSL | s, l | 0 | 1 | 0.5 | normalized |
| LAB | L | 0 | 100 | 50 | L* |
| LAB | a, b | -128 | 127 | 0 | a*, b* |
| LCH | L | 0 | 100 | 50 | L* |
| LCH | C | 0 | 230 | 0 | chroma |
| LCH | H | 0 | 360 | 0 | degrees |
| Gradient | offset | 0 | 1 | - | normalized |
| Gradient | stops | 2 | 256 | 2 | count |

---

## 10. Test Matrix

| Test | Input | Expected |
|------|-------|----------|
| RGB identity | mkRGB 0.5 0.5 0.5 | Valid gray |
| Hex parse | "#ff0000" | Red RGB |
| HSL roundtrip | red → HSL → RGB | red |
| LAB midpoint | black, white | L*=50 |
| Contrast white/black | white, black | 21:1 |
| WCAG AA | 4.5:1 ratio | Pass |
| Gradient eval | t=0.5 on 2-stop | Midpoint color |

---

*End of Specification 06*
