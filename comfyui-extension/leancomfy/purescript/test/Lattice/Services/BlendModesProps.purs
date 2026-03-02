-- | Port of ui/src/__tests__/services/blendModes.property.test.ts
-- |
-- | Property tests for blend mode color mathematics.
-- | Tests RGB<->HSL conversion roundtrips, luminance, blend invariants, clamping.
-- | Self-contained: defines its own blend functions (no external blend module needed).

module Test.Lattice.Services.BlendModesProps (spec) where

import Prelude

import Data.Foldable (for_)
import Data.Int (round, toNumber) as Int
import Data.Number (abs) as Math
import Math (round, min, max) as Math
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Lattice.TestHelpers (assertCloseTo)

--------------------------------------------------------------------------------
-- Color math helpers (self-contained for testing)
--------------------------------------------------------------------------------

-- | RGB to HSL conversion. Inputs [0, 255], outputs h [0, 1], s [0, 1], l [0, 1]
rgbToHsl :: Int -> Int -> Int -> { h :: Number, s :: Number, l :: Number }
rgbToHsl ri gi bi =
  let r = Int.toNumber ri / 255.0
      g = Int.toNumber gi / 255.0
      b = Int.toNumber bi / 255.0
      mx = Math.max r (Math.max g b)
      mn = Math.min r (Math.min g b)
      l = (mx + mn) / 2.0
  in if mx == mn
     then { h: 0.0, s: 0.0, l }
     else
       let d = mx - mn
           s = if l > 0.5 then d / (2.0 - mx - mn) else d / (mx + mn)
           h' = if mx == r then ((g - b) / d + (if g < b then 6.0 else 0.0)) / 6.0
                else if mx == g then ((b - r) / d + 2.0) / 6.0
                else ((r - g) / d + 4.0) / 6.0
       in { h: h', s, l }

-- | HSL to RGB conversion. Inputs [0, 1], outputs [0, 255]
hslToRgb :: Number -> Number -> Number -> { r :: Int, g :: Int, b :: Int }
hslToRgb h s l =
  if s == 0.0
  then
    let v = Int.round (l * 255.0)
    in { r: v, g: v, b: v }
  else
    let q = if l < 0.5 then l * (1.0 + s) else l + s - l * s
        p = 2.0 * l - q
        hue2rgb pp qq t' =
          let t = if t' < 0.0 then t' + 1.0
                  else if t' > 1.0 then t' - 1.0
                  else t'
          in if t < 1.0 / 6.0 then pp + (qq - pp) * 6.0 * t
             else if t < 1.0 / 2.0 then qq
             else if t < 2.0 / 3.0 then pp + (qq - pp) * (2.0 / 3.0 - t) * 6.0
             else pp
        r = hue2rgb p q (h + 1.0 / 3.0)
        g = hue2rgb p q h
        b = hue2rgb p q (h - 1.0 / 3.0)
    in { r: Int.round (r * 255.0), g: Int.round (g * 255.0), b: Int.round (b * 255.0) }

-- | Luminance (BT.601 luma weights)
getLuminance :: Int -> Int -> Int -> Number
getLuminance r g b = 0.299 * Int.toNumber r + 0.587 * Int.toNumber g + 0.114 * Int.toNumber b

-- | Simple blend modes
blendNormal :: Int -> Int -> Number -> Int
blendNormal base blend opacity =
  Int.round (Int.toNumber base * (1.0 - opacity) + Int.toNumber blend * opacity)

blendMultiply :: Int -> Int -> Int
blendMultiply base blend =
  Int.round (Int.toNumber base * Int.toNumber blend / 255.0)

blendScreen :: Int -> Int -> Int
blendScreen base blend =
  Int.round (255.0 - (255.0 - Int.toNumber base) * (255.0 - Int.toNumber blend) / 255.0)

blendAdd :: Int -> Int -> Int
blendAdd a b = min 255 (a + b)

-- | Clamp to [0, 255]
clamp :: Number -> Int
clamp v = max 0 (min 255 (Int.round v))

--------------------------------------------------------------------------------
-- Test channel values
--------------------------------------------------------------------------------

channels :: Array Int
channels = [0, 1, 32, 64, 100, 127, 128, 200, 254, 255]

hueSamples :: Array Number
hueSamples = [0.0, 0.1, 0.25, 0.33, 0.5, 0.67, 0.75, 0.9, 1.0]

normalizedSamples :: Array Number
normalizedSamples = [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0]

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "BLEND MODE Properties" do
    rgbHslRoundtrip
    luminanceCalculation
    basicBlendInvariants
    clampFunction

rgbHslRoundtrip :: Spec Unit
rgbHslRoundtrip = do
  describe "RGB <-> HSL conversion roundtrip" do
    it "RGB -> HSL -> RGB preserves color (within rounding)" do
      for_ channels \r ->
        for_ channels \g ->
          for_ channels \b -> do
            let hsl = rgbToHsl r g b
                rgb = hslToRgb hsl.h hsl.s hsl.l
            if Math.abs (Int.toNumber (r - rgb.r)) <= 1.0
               && Math.abs (Int.toNumber (g - rgb.g)) <= 1.0
               && Math.abs (Int.toNumber (b - rgb.b)) <= 1.0
              then pure unit
              else fail ("Roundtrip failed for (" <> show r <> "," <> show g <> "," <> show b
                <> ") -> (" <> show rgb.r <> "," <> show rgb.g <> "," <> show rgb.b <> ")")

    it "grayscale colors have saturation = 0" do
      for_ channels \gray -> do
        let hsl = rgbToHsl gray gray gray
        hsl.s `shouldEqual` 0.0

    it "pure white has L = 1" do
      let hsl = rgbToHsl 255 255 255
      hsl.l `shouldEqual` 1.0

    it "pure black has L = 0" do
      let hsl = rgbToHsl 0 0 0
      hsl.l `shouldEqual` 0.0

    it "HSL with S=0 produces grayscale" do
      for_ hueSamples \h ->
        for_ normalizedSamples \l -> do
          let rgb = hslToRgb h 0.0 l
          rgb.r `shouldEqual` rgb.g
          rgb.g `shouldEqual` rgb.b

luminanceCalculation :: Spec Unit
luminanceCalculation = do
  describe "luminance calculation" do
    it "luminance is bounded 0-255" do
      for_ channels \r ->
        for_ channels \g ->
          for_ channels \b -> do
            let lum = getLuminance r g b
            if lum >= 0.0 && lum <= 255.0
              then pure unit
              else fail ("Luminance out of bounds: " <> show lum)

    it "grayscale luminance equals the gray value" do
      for_ channels \gray -> do
        let lum = getLuminance gray gray gray
        assertCloseTo 1.0e-6 (Int.toNumber gray) lum

    it "pure white has maximum luminance" do
      let lum = getLuminance 255 255 255
      lum `shouldEqual` 255.0

    it "pure black has minimum luminance" do
      let lum = getLuminance 0 0 0
      lum `shouldEqual` 0.0

    it "green has higher luminance weight than red or blue" do
      let redLum = getLuminance 255 0 0
          greenLum = getLuminance 0 255 0
          blueLum = getLuminance 0 0 255
      if greenLum > redLum && greenLum > blueLum
        then pure unit
        else fail "Green does not have highest luminance weight"

basicBlendInvariants :: Spec Unit
basicBlendInvariants = do
  describe "basic blend invariants" do
    it "normal blend at opacity 0 returns base" do
      for_ channels \base ->
        for_ channels \blend ->
          blendNormal base blend 0.0 `shouldEqual` base

    it "normal blend at opacity 1 returns blend" do
      for_ channels \base ->
        for_ channels \blend ->
          blendNormal base blend 1.0 `shouldEqual` blend

    it "multiply is commutative" do
      for_ channels \a ->
        for_ channels \b ->
          blendMultiply a b `shouldEqual` blendMultiply b a

    it "screen is commutative" do
      for_ channels \a ->
        for_ channels \b ->
          blendScreen a b `shouldEqual` blendScreen b a

    it "add is commutative" do
      for_ channels \a ->
        for_ channels \b ->
          blendAdd a b `shouldEqual` blendAdd b a

    it "multiply with white returns original" do
      for_ channels \base ->
        blendMultiply base 255 `shouldEqual` base

    it "multiply with black returns black" do
      for_ channels \base ->
        blendMultiply base 0 `shouldEqual` 0

    it "screen with black returns original" do
      for_ channels \base ->
        blendScreen base 0 `shouldEqual` base

    it "screen with white returns white" do
      for_ channels \base ->
        blendScreen base 255 `shouldEqual` 255

    it "add result is bounded by 255" do
      for_ channels \a ->
        for_ channels \b -> do
          let result = blendAdd a b
          if result >= 0 && result <= 255
            then pure unit
            else fail ("add result out of bounds: " <> show result)

clampFunction :: Spec Unit
clampFunction = do
  describe "clamp function" do
    it "clamp always returns value in [0, 255]" do
      for_ [-1000.0, -1.0, 0.0, 127.5, 255.0, 256.0, 1000.0] \v -> do
        let result = clamp v
        if result >= 0 && result <= 255
          then pure unit
          else fail ("Clamp out of bounds: " <> show result)

    it "clamp preserves values already in range" do
      for_ channels \v ->
        clamp (Int.toNumber v) `shouldEqual` v

    it "clamp caps values > 255 to 255" do
      for_ [256.0, 300.0, 1000.0] \v ->
        clamp v `shouldEqual` 255

    it "clamp floors values < 0 to 0" do
      for_ [-1.0, -100.0, -1000.0] \v ->
        clamp v `shouldEqual` 0
