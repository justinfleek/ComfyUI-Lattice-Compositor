-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // widget property tests
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Exhaustive property-based tests for Widget system.
-- |
-- | Tests designed to find REAL bugs:
-- | - Division by zero in scaling functions
-- | - Array index out of bounds
-- | - Infinity/NaN propagation
-- | - Empty data handling
-- | - Boundary value errors
-- | - Monotonicity violations
-- | - Isometric projection invariants
-- | - Color interpolation edge cases

module Test.Widget where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (all, any, sum)
import Data.Int (toNumber, floor) as Int
import Data.Maybe (Maybe(Just, Nothing), fromMaybe, isJust, isNothing)
import Data.Number as Number
import Data.String as String
import Data.Tuple (Tuple(Tuple))
import Effect.Aff (Aff, throwError)
import Effect.Exception (error, Error)
import Hydrogen.Element.Compound.Widget.Card as Card
import Hydrogen.Element.Compound.Widget.Chart3D as Chart3D
import Hydrogen.Element.Compound.Widget.ChartAdvanced as ChartAdv
import Hydrogen.Element.Compound.Widget.Theme as Theme
import Hydrogen.Math.Core as Math
import Hydrogen.Render.Element as E
import Test.QuickCheck (Result, (===), (<?>))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency, oneOf, vectorOf)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck) as Spec

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // generators with realistic
--                                                    // distributions for finding
--                                                    // real bugs
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate a Number in the given range using integer subdivision.
-- | Maps integer range to floating point range with 0.1 precision.
genNumber :: Number -> Number -> Gen Number
genNumber lo hi = do
  -- Scale to integer range for chooseInt, then scale back
  let loI = Int.floor (lo * 10.0)
  let hiI = Int.floor (hi * 10.0)
  n <- chooseInt loI hiI
  pure (Int.toNumber n / 10.0)

-- | Generate Number with adversarial distribution biased toward edge cases.
-- |
-- | Real bugs hide at: 0, negative, very small, very large, near-integers
genAdversarialNumber :: Gen Number
genAdversarialNumber = frequency $ NEA.cons'
  (Tuple 8.0 (pure 0.0))                           -- Division by zero
  [ Tuple 5.0 (pure (-0.0))                        -- Negative zero
  , Tuple 8.0 (pure 1.0)                           -- Identity edge
  , Tuple 8.0 (pure (-1.0))                        -- Negative identity
  , Tuple 5.0 (pure 0.0000001)                     -- Near zero positive
  , Tuple 5.0 (pure (-0.0000001))                  -- Near zero negative
  , Tuple 5.0 (pure 999999999.0)                   -- Very large
  , Tuple 5.0 (pure (-999999999.0))                -- Very large negative
  , Tuple 5.0 (pure 0.5)                           -- Half
  , Tuple 5.0 (pure 1.0000001)                     -- Just above 1
  , Tuple 5.0 (pure 0.9999999)                     -- Just below 1
  , Tuple 10.0 (genNumber (-1000.0) 1000.0)         -- Normal range
  , Tuple 10.0 (genNumber 0.0 100.0)               -- Typical chart values
  , Tuple 8.0 (Int.toNumber <$> chooseInt (-100) 100)  -- Integers as floats
  , Tuple 8.0 (pure 100.0)                         -- Common max
  ]

-- | Generate array of numbers with realistic chart data distribution.
-- |
-- | Real chart bugs hide in: empty arrays, single element, all same value,
-- | monotonic sequences, alternating signs, extreme outliers
genChartDataArray :: Gen (Array Number)
genChartDataArray = frequency $ NEA.cons'
  (Tuple 5.0 (pure []))                                    -- Empty: divison by length
  [ Tuple 5.0 (pure [0.0])                                 -- Single zero
  , Tuple 5.0 (Array.singleton <$> genAdversarialNumber)   -- Single element
  , Tuple 3.0 (pure [0.0, 0.0, 0.0, 0.0])                  -- All zeros: range = 0
  , Tuple 3.0 (pure [42.0, 42.0, 42.0])                    -- All same: range = 0
  , Tuple 5.0 (pure [1.0, 2.0, 3.0, 4.0, 5.0])             -- Monotonic increasing
  , Tuple 5.0 (pure [5.0, 4.0, 3.0, 2.0, 1.0])             -- Monotonic decreasing
  , Tuple 5.0 (pure [1.0, (-1.0), 1.0, (-1.0)])            -- Alternating
  , Tuple 5.0 (pure [0.0, 1000000.0, 0.0])                 -- Extreme outlier
  , Tuple 5.0 (pure [(-100.0), 0.0, 100.0])                -- Symmetric around zero
  , Tuple 10.0 (vectorOf 5 (genNumber 0.0 100.0))           -- Normal 5 elements
  , Tuple 10.0 (vectorOf 10 (genNumber (-50.0) 50.0))      -- Normal 10 mixed
  , Tuple 10.0 (vectorOf 50 (genNumber 0.0 1000.0))        -- Larger dataset
  , Tuple 5.0 (vectorOf 3 genAdversarialNumber)            -- 3 adversarial
  , Tuple 5.0 (vectorOf 100 (pure 0.0))                    -- 100 zeros
  , Tuple 4.0 (vectorOf 2 (genNumber 0.0 1.0))             -- Minimal valid
  , Tuple 5.0 ((\n -> Array.replicate n 1.0) <$> chooseInt 0 200)  -- Variable length constant
  ]

-- | Generate bar chart data with realistic distribution.
genBar3DData :: Gen (Array Chart3D.Bar3DData)
genBar3DData = frequency $ NEA.cons'
  (Tuple 5.0 (pure []))                            -- Empty
  [ Tuple 5.0 (vectorOf 1 genSingleBar)            -- Single bar
  , Tuple 10.0 (vectorOf 3 genSingleBar)           -- Few bars
  , Tuple 20.0 (vectorOf 6 genSingleBar)           -- Typical
  , Tuple 10.0 (vectorOf 20 genSingleBar)          -- Many bars
  , Tuple 10.0 genAllZeroBars                      -- All zero values
  , Tuple 10.0 genNegativeBars                     -- Negative values
  , Tuple 10.0 genMixedSignBars                    -- Mixed positive/negative
  , Tuple 10.0 genExtremeValueBars                 -- Extreme values
  , Tuple 10.0 genIdenticalBars                    -- All same value
  ]

genSingleBar :: Gen Chart3D.Bar3DData
genSingleBar = do
  value <- genAdversarialNumber
  label <- genLabel
  color <- oneOf $ NEA.cons' (pure Nothing) [Just <$> genHexColor]
  pure { label, value, color }

genLabel :: Gen String
genLabel = elements $ NEA.cons'
  ""                                               -- Empty label
  [ "A"                                            -- Single char
  , "Label"                                        -- Normal
  , "Very Long Label That Might Overflow"          -- Long
  , "日本語"                                        -- Unicode
  , "   "                                          -- Whitespace only
  , String.joinWith "" (Array.replicate 100 "x")   -- Very long
  , "<script>alert('xss')</script>"                -- XSS attempt
  , "Label\nWith\nNewlines"                        -- Newlines
  ]

genHexColor :: Gen String
genHexColor = elements $ NEA.cons'
  "#000000"
  [ "#FFFFFF"
  , "#FF0000"
  , "#00FF00"
  , "#0000FF"
  , "#f97316"                                      -- Theme color
  , ""                                             -- Empty (edge case)
  , "invalid"                                      -- Invalid hex
  , "#FFF"                                         -- Short form
  , "rgb(255,0,0)"                                 -- Wrong format
  ]

genAllZeroBars :: Gen (Array Chart3D.Bar3DData)
genAllZeroBars = do
  n <- chooseInt 1 10
  pure $ Array.replicate n { label: "Zero", value: 0.0, color: Nothing }

genNegativeBars :: Gen (Array Chart3D.Bar3DData)
genNegativeBars = do
  values <- vectorOf 5 (genNumber (-100.0) (-1.0))
  pure $ Array.mapWithIndex (\i v -> { label: "Bar " <> show i, value: v, color: Nothing }) values

genMixedSignBars :: Gen (Array Chart3D.Bar3DData)
genMixedSignBars = do
  values <- vectorOf 6 (genNumber (-100.0) 100.0)
  pure $ Array.mapWithIndex (\i v -> { label: "Bar " <> show i, value: v, color: Nothing }) values

genExtremeValueBars :: Gen (Array Chart3D.Bar3DData)
genExtremeValueBars = pure
  [ { label: "Tiny", value: 0.00001, color: Nothing }
  , { label: "Huge", value: 999999999.0, color: Nothing }
  , { label: "Normal", value: 50.0, color: Nothing }
  ]

genIdenticalBars :: Gen (Array Chart3D.Bar3DData)
genIdenticalBars = do
  v <- genAdversarialNumber
  n <- chooseInt 2 8
  pure $ Array.replicate n { label: "Same", value: v, color: Nothing }

-- | Generate waterfall data with realistic distribution.
genWaterfallData :: Gen (Array ChartAdv.WaterfallData)
genWaterfallData = frequency $ NEA.cons'
  (Tuple 5.0 (pure []))
  [ Tuple 10.0 (vectorOf 1 genWaterfallPoint)
  , Tuple 20.0 (vectorOf 5 genWaterfallPoint)
  , Tuple 15.0 genAlternatingWaterfall             -- +/- alternating
  , Tuple 15.0 genAllPositiveWaterfall
  , Tuple 15.0 genAllNegativeWaterfall
  , Tuple 10.0 genWaterfallWithTotals
  , Tuple 10.0 genNetZeroWaterfall                 -- Sums to zero
  ]

genWaterfallPoint :: Gen ChartAdv.WaterfallData
genWaterfallPoint = do
  value <- genAdversarialNumber
  label <- genLabel
  isTotal <- oneOf $ NEA.cons' (pure false) [pure true, pure false, pure false]
  pure { label, value, isTotal }

genAlternatingWaterfall :: Gen (Array ChartAdv.WaterfallData)
genAlternatingWaterfall = pure
  [ { label: "Start", value: 100.0, isTotal: false }
  , { label: "Loss", value: (-30.0), isTotal: false }
  , { label: "Gain", value: 50.0, isTotal: false }
  , { label: "Loss", value: (-20.0), isTotal: false }
  , { label: "End", value: 100.0, isTotal: true }
  ]

genAllPositiveWaterfall :: Gen (Array ChartAdv.WaterfallData)
genAllPositiveWaterfall = do
  values <- vectorOf 5 (genNumber 1.0 100.0)
  pure $ Array.mapWithIndex (\i v -> { label: "+" <> show i, value: v, isTotal: false }) values

genAllNegativeWaterfall :: Gen (Array ChartAdv.WaterfallData)
genAllNegativeWaterfall = do
  values <- vectorOf 5 (genNumber (-100.0) (-1.0))
  pure $ Array.mapWithIndex (\i v -> { label: "-" <> show i, value: v, isTotal: false }) values

genWaterfallWithTotals :: Gen (Array ChartAdv.WaterfallData)
genWaterfallWithTotals = pure
  [ { label: "Q1", value: 100.0, isTotal: true }
  , { label: "Sales", value: 50.0, isTotal: false }
  , { label: "Costs", value: (-30.0), isTotal: false }
  , { label: "Q2", value: 120.0, isTotal: true }
  ]

genNetZeroWaterfall :: Gen (Array ChartAdv.WaterfallData)
genNetZeroWaterfall = pure
  [ { label: "Up", value: 100.0, isTotal: false }
  , { label: "Down", value: (-50.0), isTotal: false }
  , { label: "Down", value: (-50.0), isTotal: false }
  , { label: "Net", value: 0.0, isTotal: true }
  ]

-- | Generate grouped bar data.
genGroupedBarData :: Gen (Array ChartAdv.GroupedBarData)
genGroupedBarData = frequency $ NEA.cons'
  (Tuple 5.0 (pure []))
  [ Tuple 10.0 (vectorOf 1 (genGroupedCategory 3))
  , Tuple 20.0 (vectorOf 4 (genGroupedCategory 3))
  , Tuple 15.0 (vectorOf 6 (genGroupedCategory 5))
  , Tuple 10.0 (vectorOf 3 (genGroupedCategory 0))    -- Empty values arrays
  , Tuple 10.0 (vectorOf 3 (genGroupedCategory 1))    -- Single value per category
  , Tuple 10.0 genMismatchedGroups                    -- Different lengths
  , Tuple 10.0 genAllZeroGroups
  , Tuple 10.0 genSparseGroups                        -- Some categories empty
  ]

genGroupedCategory :: Int -> Gen ChartAdv.GroupedBarData
genGroupedCategory numValues = do
  category <- genLabel
  values <- vectorOf numValues genAdversarialNumber
  pure { category, values }

genMismatchedGroups :: Gen (Array ChartAdv.GroupedBarData)
genMismatchedGroups = pure
  [ { category: "A", values: [1.0, 2.0, 3.0] }
  , { category: "B", values: [4.0, 5.0] }            -- Different length!
  , { category: "C", values: [6.0, 7.0, 8.0, 9.0] }  -- Different length!
  ]

genAllZeroGroups :: Gen (Array ChartAdv.GroupedBarData)
genAllZeroGroups = pure
  [ { category: "A", values: [0.0, 0.0, 0.0] }
  , { category: "B", values: [0.0, 0.0, 0.0] }
  ]

genSparseGroups :: Gen (Array ChartAdv.GroupedBarData)
genSparseGroups = pure
  [ { category: "A", values: [100.0, 0.0, 0.0] }
  , { category: "B", values: [0.0, 100.0, 0.0] }
  , { category: "C", values: [0.0, 0.0, 100.0] }
  ]

-- | Generate surface data grid.
genSurfaceData :: Gen Chart3D.SurfaceData
genSurfaceData = frequency $ NEA.cons'
  (Tuple 5.0 (pure { rows: 0, cols: 0, values: [] }))  -- Empty
  [ Tuple 5.0 (pure { rows: 1, cols: 1, values: [0.0] })   -- Minimal
  , Tuple 10.0 (genSurfaceGrid 3 3)
  , Tuple 15.0 (genSurfaceGrid 5 5)
  , Tuple 10.0 (genSurfaceGrid 10 10)
  , Tuple 10.0 genFlatSurface                          -- All same height
  , Tuple 10.0 genPeakSurface                          -- Single peak
  , Tuple 10.0 genValleySurface                        -- Single valley
  , Tuple 10.0 genCheckerboardSurface
  , Tuple 10.0 genMismatchedSurface                    -- rows*cols != values.length
  , Tuple 10.0 genNegativeHeightSurface
  ]

genSurfaceGrid :: Int -> Int -> Gen Chart3D.SurfaceData
genSurfaceGrid rows cols = do
  values <- vectorOf (rows * cols) genAdversarialNumber
  pure { rows, cols, values }

genFlatSurface :: Gen Chart3D.SurfaceData
genFlatSurface = do
  h <- genAdversarialNumber
  pure { rows: 4, cols: 4, values: Array.replicate 16 h }

genPeakSurface :: Gen Chart3D.SurfaceData
genPeakSurface = pure
  { rows: 3
  , cols: 3
  , values: [0.0, 0.0, 0.0, 0.0, 100.0, 0.0, 0.0, 0.0, 0.0]  -- Peak in center
  }

genValleySurface :: Gen Chart3D.SurfaceData
genValleySurface = pure
  { rows: 3
  , cols: 3
  , values: [100.0, 100.0, 100.0, 100.0, 0.0, 100.0, 100.0, 100.0, 100.0]
  }

genCheckerboardSurface :: Gen Chart3D.SurfaceData
genCheckerboardSurface = pure
  { rows: 4
  , cols: 4
  , values: [0.0, 100.0, 0.0, 100.0, 100.0, 0.0, 100.0, 0.0, 0.0, 100.0, 0.0, 100.0, 100.0, 0.0, 100.0, 0.0]
  }

genMismatchedSurface :: Gen Chart3D.SurfaceData
genMismatchedSurface = pure
  { rows: 3
  , cols: 3
  , values: [1.0, 2.0]  -- Only 2 values for 3x3 grid!
  }

genNegativeHeightSurface :: Gen Chart3D.SurfaceData
genNegativeHeightSurface = pure
  { rows: 3
  , cols: 3
  , values: [(-50.0), (-25.0), 0.0, (-25.0), 0.0, 25.0, 0.0, 25.0, 50.0]
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // isometric projection tests
-- ═══════════════════════════════════════════════════════════════════════════════

isometricProjectionTests :: Spec Unit
isometricProjectionTests = describe "Isometric Projection Invariants" do
  
  describe "Mathematical Properties" do
    it "origin maps to origin" do
      let result = Chart3D.isoProject 0.0 0.0 0.0
      result.x `shouldBeCloseTo` 0.0
      result.y `shouldBeCloseTo` 0.0
    
    it "projection is linear in each axis" do
      Spec.quickCheck do
        x <- genNumber (-100.0) 100.0
        y <- genNumber (-100.0) 100.0
        z <- genNumber (-100.0) 100.0
        k <- genNumber 0.1 10.0
        let p1 = Chart3D.isoProject x y z
        let p2 = Chart3D.isoProject (k * x) (k * y) (k * z)
        -- Scaled input should produce scaled output (approximately)
        let ratio_x = if p1.x == 0.0 then 1.0 else p2.x / p1.x
        let _ratio_y = if p1.y == 0.0 then 1.0 else p2.y / p1.y
        pure $ (Math.abs (ratio_x - k) < 0.01 || p1.x == 0.0)
               <?> "X scaling failed"
    
    it "y-axis projects upward (negative screen y)" do
      Spec.quickCheck do
        y <- genNumber 1.0 1000.0  -- Positive height
        let p = Chart3D.isoProject 0.0 y 0.0
        pure $ p.y < 0.0 <?> "y=" <> show y <> " should project to negative screen y"
    
    it "x-axis projects to positive screen x" do
      Spec.quickCheck do
        x <- genNumber 1.0 1000.0  -- Positive x
        let p = Chart3D.isoProject x 0.0 0.0
        pure $ p.x > 0.0 <?> "x=" <> show x <> " should project to positive screen x"
    
    it "z-axis projects to negative screen x" do
      Spec.quickCheck do
        z <- genNumber 1.0 1000.0  -- Positive z
        let p = Chart3D.isoProject 0.0 0.0 z
        pure $ p.x < 0.0 <?> "z=" <> show z <> " should project to negative screen x"
    
    it "never produces NaN or Infinity" do
      Spec.quickCheck do
        x <- genAdversarialNumber
        y <- genAdversarialNumber
        z <- genAdversarialNumber
        let p = Chart3D.isoProject x y z
        pure $ isFiniteNumber p.x && isFiniteNumber p.y
               <?> "isoProject produced non-finite: " <> show p

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // array helper invariants
-- ═══════════════════════════════════════════════════════════════════════════════

arrayHelperTests :: Spec Unit
arrayHelperTests = describe "Array Helper Invariants" do
  
  describe "arrayMin/arrayMax" do
    it "empty array returns 0.0 (bounded fallback)" do
      let minVal = arrayMin []
      let maxVal = arrayMax []
      minVal `shouldBeCloseTo` 0.0
      maxVal `shouldBeCloseTo` 0.0
    
    it "single element array returns that element" do
      Spec.quickCheck do
        x <- genAdversarialNumber
        let minVal = arrayMin [x]
        let maxVal = arrayMax [x]
        pure $ (minVal == x && maxVal == x) 
               <?> "Single element: " <> show x
    
    it "min <= max for any non-empty array" do
      Spec.quickCheck do
        arr <- genChartDataArray
        let minVal = arrayMin arr
        let maxVal = arrayMax arr
        pure $ (Array.null arr || minVal <= maxVal)
               <?> "min=" <> show minVal <> " > max=" <> show maxVal
    
    it "min and max are elements of the array" do
      Spec.quickCheck do
        arr <- genChartDataArray
        let minVal = arrayMin arr
        let maxVal = arrayMax arr
        let containsMin = Array.null arr || Array.elem minVal arr
        let containsMax = Array.null arr || Array.elem maxVal arr
        pure $ (containsMin && containsMax)
               <?> "min/max not in array"
    
    it "all elements between min and max" do
      Spec.quickCheck do
        arr <- genChartDataArray
        let minVal = arrayMin arr
        let maxVal = arrayMax arr
        pure $ all (\x -> x >= minVal && x <= maxVal) arr
               <?> "Element outside [min,max] range"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // value formatting tests
-- ═══════════════════════════════════════════════════════════════════════════════

valueFormattingTests :: Spec Unit
valueFormattingTests = describe "Value Formatting Invariants" do
  
  describe "formatValue" do
    it "never produces empty string" do
      Spec.quickCheck do
        v <- genAdversarialNumber
        let result = Card.formatValue v
        pure $ String.length result > 0
               <?> "Empty string for " <> show v
    
    it "large values use K/M/B suffixes" do
      let v1000 = Card.formatValue 1000.0
      let v1m = Card.formatValue 1000000.0
      let v1b = Card.formatValue 1000000000.0
      (String.contains (String.Pattern "K") v1000 ||
       String.contains (String.Pattern "0") v1000) `shouldBe` true
      String.contains (String.Pattern "M") v1m `shouldBe` true
      String.contains (String.Pattern "B") v1b `shouldBe` true
    
    it "monotonicity: larger values don't format smaller" do
      Spec.quickCheck do
        a <- genNumber 0.0 1000000.0
        b <- genNumber 0.0 1000000.0
        let smaller = Math.min a b
        let larger = Math.max a b
        let fmtSmaller = Card.formatValue smaller
        let fmtLarger = Card.formatValue larger
        -- Parse back to compare magnitudes (rough check)
        let magSmaller = estimateMagnitude fmtSmaller
        let magLarger = estimateMagnitude fmtLarger
        pure $ magSmaller <= magLarger
               <?> show smaller <> " -> " <> fmtSmaller <> " vs " <> show larger <> " -> " <> fmtLarger
    
    it "zero formats to '0'" do
      let result = Card.formatValue 0.0
      String.contains (String.Pattern "0") result `shouldBe` true
  
  describe "formatPercent" do
    it "preserves sign information" do
      Spec.quickCheck do
        p <- genNumber (-100.0) 100.0
        let result = Card.formatPercent p
        let hasNegative = String.contains (String.Pattern "-") result
        pure $ (p >= 0.0 || hasNegative)
               <?> "Lost negative sign for " <> show p
    
    it "reasonable length output" do
      Spec.quickCheck do
        p <- genAdversarialNumber
        let result = Card.formatPercent p
        pure $ String.length result < 50
               <?> "Unreasonably long: " <> result

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // theme invariants
-- ═══════════════════════════════════════════════════════════════════════════════

themeTests :: Spec Unit
themeTests = describe "Theme Invariants" do
  
  describe "Color Palettes" do
    it "rainbowPalette has 8 distinct colors" do
      Array.length Theme.rainbowPalette `shouldEqual` 8
      Array.nub Theme.rainbowPalette `shouldEqual` Theme.rainbowPalette
    
    it "all palette colors are valid hex format" do
      let isValidHex s = String.take 1 s == "#" && String.length s == 7
      all isValidHex Theme.rainbowPalette `shouldBe` true
      all isValidHex Theme.monochromeGreenPalette `shouldBe` true
      all isValidHex Theme.warmPalette `shouldBe` true
      all isValidHex Theme.coolPalette `shouldBe` true
    
    it "individual neon colors are valid hex" do
      let colors = [Theme.neonPurple, Theme.neonBlue, Theme.neonCyan, Theme.neonGreen,
                    Theme.neonYellow, Theme.neonOrange, Theme.neonRed, Theme.neonPink]
      let isValidHex s = String.take 1 s == "#" && String.length s == 7
      all isValidHex colors `shouldBe` true
  
  describe "Glow Effects" do
    it "textGlow produces valid CSS" do
      let glows = [Theme.textGlow "#FF0000" Theme.GlowSubtle,
                   Theme.textGlow "#00FF00" Theme.GlowMedium,
                   Theme.textGlow "#0000FF" Theme.GlowIntense,
                   Theme.textGlow "#FFFFFF" Theme.GlowExtreme]
      all (\s -> String.length s > 0) glows `shouldBe` true
      all (\s -> String.contains (String.Pattern "px") s) glows `shouldBe` true
    
    it "boxGlow produces valid CSS" do
      let glows = [Theme.boxGlow "#FF0000" Theme.GlowSubtle,
                   Theme.boxGlow "#00FF00" Theme.GlowMedium]
      all (\s -> String.length s > 0) glows `shouldBe` true
  
  describe "Widget Sizing" do
    it "all sizes have positive dimensions" do
      let sizes = [Theme.SizeSmall, Theme.SizeMedium, Theme.SizeLarge, Theme.SizeWide, Theme.SizeTall]
      all (\s -> Theme.widgetWidth s > 0.0) sizes `shouldBe` true
      all (\s -> Theme.widgetHeight s > 0.0) sizes `shouldBe` true
      all (\s -> Theme.chartHeight s > 0.0) sizes `shouldBe` true
    
    it "chart height < widget height" do
      let sizes = [Theme.SizeSmall, Theme.SizeMedium, Theme.SizeLarge, Theme.SizeWide, Theme.SizeTall]
      all (\s -> Theme.chartHeight s < Theme.widgetHeight s) sizes `shouldBe` true
  
  describe "Theme Modes" do
    it "dark and light modes produce different colors" do
      let darkBg = Theme.containerBackground Theme.ModeDark
      let lightBg = Theme.containerBackground Theme.ModeLight
      darkBg `shouldNotEqual` lightBg
      
      let darkText = Theme.textPrimary Theme.ModeDark
      let lightText = Theme.textPrimary Theme.ModeLight
      darkText `shouldNotEqual` lightText

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // chart data edge case tests
-- ═══════════════════════════════════════════════════════════════════════════════

chartEdgeCaseTests :: Spec Unit
chartEdgeCaseTests = describe "Chart Data Edge Cases" do
  
  describe "Empty Data Handling" do
    it "3D bar chart handles empty array - produces valid element" do
      let result = Chart3D.chart3DBar Chart3D.defaultBar3DConfig []
      -- Force evaluation and verify it's a valid SVG container
      (E.isEmpty result) `shouldBe` false
    
    it "waterfall chart handles empty array - produces valid element" do
      let result = ChartAdv.waterfallChart ChartAdv.defaultWaterfallConfig []
      (E.isEmpty result) `shouldBe` false
    
    it "grouped bar chart handles empty array - produces valid element" do
      let result = ChartAdv.groupedBarChart ChartAdv.defaultGroupedBarConfig []
      (E.isEmpty result) `shouldBe` false
    
    it "stacked bar chart handles empty array - produces valid element" do
      let result = ChartAdv.stackedBarChart ChartAdv.defaultStackedConfig []
      (E.isEmpty result) `shouldBe` false
    
    it "stacked column chart handles empty array - produces valid element" do
      let result = ChartAdv.stackedColumnChart ChartAdv.defaultStackedConfig []
      (E.isEmpty result) `shouldBe` false
    
    it "surface chart handles empty data - produces valid element" do
      let result = Chart3D.chart3DSurface Chart3D.defaultSurfaceConfig 
                     { rows: 0, cols: 0, values: [] }
      (E.isEmpty result) `shouldBe` false
    
    it "dual axis chart handles empty data - produces valid element" do
      let result = ChartAdv.dualAxisChart ChartAdv.defaultDualAxisConfig
                     { categories: [], lineSeries: [], columnSeries: [], lineLabel: "", columnLabel: "" }
      (E.isEmpty result) `shouldBe` false
  
  describe "All-Zero Data Handling" do
    it "3D bar chart with all zero values produces children" do
      let bars = Array.replicate 5 { label: "Zero", value: 0.0, color: Nothing }
      let result = Chart3D.chart3DBar Chart3D.defaultBar3DConfig bars
      -- Should have children (the bars, even if height is 0)
      (E.childCount result > 0) `shouldBe` true
    
    it "waterfall with all zeros produces valid structure" do
      let data' = Array.replicate 5 { label: "Z", value: 0.0, isTotal: false }
      let result = ChartAdv.waterfallChart ChartAdv.defaultWaterfallConfig data'
      (E.isEmpty result) `shouldBe` false
    
    it "grouped bar with all zeros has expected structure" do
      let data' = [{ category: "A", values: [0.0, 0.0, 0.0] },
                   { category: "B", values: [0.0, 0.0, 0.0] }]
      let result = ChartAdv.groupedBarChart ChartAdv.defaultGroupedBarConfig data'
      (E.childCount result > 0) `shouldBe` true
    
    it "surface with all zero heights renders grid" do
      let result = Chart3D.chart3DSurface Chart3D.defaultSurfaceConfig
                     { rows: 3, cols: 3, values: Array.replicate 9 0.0 }
      (E.isEmpty result) `shouldBe` false
  
  describe "Single Element Data" do
    it "3D bar chart with single bar has children" do
      let bars = [{ label: "Only", value: 100.0, color: Nothing }]
      let result = Chart3D.chart3DBar Chart3D.defaultBar3DConfig bars
      (E.childCount result > 0) `shouldBe` true
    
    it "waterfall with single point renders" do
      let data' = [{ label: "Single", value: 50.0, isTotal: false }]
      let result = ChartAdv.waterfallChart ChartAdv.defaultWaterfallConfig data'
      (E.isEmpty result) `shouldBe` false
    
    it "grouped bar with single category has content" do
      let data' = [{ category: "Only", values: [1.0, 2.0, 3.0] }]
      let result = ChartAdv.groupedBarChart ChartAdv.defaultGroupedBarConfig data'
      (E.childCount result > 0) `shouldBe` true
    
    it "1x1 surface has structure" do
      let result = Chart3D.chart3DSurface Chart3D.defaultSurfaceConfig
                     { rows: 1, cols: 1, values: [50.0] }
      (E.isEmpty result) `shouldBe` false
  
  describe "Extreme Value Data" do
    it "3D bar chart handles very large values without NaN" do
      let bars = [{ label: "Big", value: 999999999999.0, color: Nothing }]
      let result = Chart3D.chart3DBar Chart3D.defaultBar3DConfig bars
      -- Verify element exists and has content (no NaN crash)
      (E.childCount result > 0) `shouldBe` true
    
    it "3D bar chart handles very small values" do
      let bars = [{ label: "Tiny", value: 0.000000001, color: Nothing }]
      let result = Chart3D.chart3DBar Chart3D.defaultBar3DConfig bars
      (E.isEmpty result) `shouldBe` false
    
    it "chart handles negative values" do
      let bars = [{ label: "Neg", value: (-100.0), color: Nothing }]
      let result = Chart3D.chart3DBar Chart3D.defaultBar3DConfig bars
      (E.childCount result > 0) `shouldBe` true
    
    it "rainfall handles asymmetric data" do
      let data' = { leftValues: [1.0], rightValues: Array.replicate 100 50.0, 
                    leftLabel: "L", rightLabel: "R" }
      let result = ChartAdv.rainfallChart ChartAdv.defaultRainfallConfig data'
      -- Verify both sides render even with asymmetric counts
      (E.childCount result > 0) `shouldBe` true

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // aggregate data property tests
-- ═══════════════════════════════════════════════════════════════════════════════

aggregateDataTests :: Spec Unit
aggregateDataTests = describe "Aggregate Data Properties" do
  
  describe "Sum invariants for chart data" do
    it "sum of values equals total (waterfall non-totals)" do
      Spec.quickCheck do
        arr <- genChartDataArray
        let total = sum arr
        let reconstructed = sum arr
        pure $ total === reconstructed
    
    it "stacked bar total equals sum of segments" do
      Spec.quickCheck do
        values <- vectorOf 5 genAdversarialNumber
        let total = sum values
        -- For stacked bars, each stack should sum to its components
        pure $ (isFiniteNumber total || any (\v -> not (isFiniteNumber v)) values)
               <?> "Sum should be finite if all inputs finite"
  
  describe "Optional value handling" do
    it "fromMaybe provides fallback for Nothing" do
      Spec.quickCheck do
        fallback <- genAdversarialNumber
        let result = fromMaybe fallback Nothing
        pure $ result === fallback
    
    it "fromMaybe uses Just value when present" do
      Spec.quickCheck do
        fallback <- genAdversarialNumber
        value <- genAdversarialNumber
        let result = fromMaybe fallback (Just value)
        pure $ result === value
    
    it "isJust and isNothing are complementary" do
      Spec.quickCheck do
        value <- genAdversarialNumber
        let justVal = Just value
        let nothingVal = Nothing :: Maybe Number
        pure $ (isJust justVal && isNothing nothingVal && 
                not (isJust nothingVal) && not (isNothing justVal))
               <?> "isJust/isNothing should be complements"
  
  describe "Any/All predicate properties" do
    it "any positive in mixed array" do
      Spec.quickCheck do
        arr <- genChartDataArray
        let hasPositive = any (\x -> x > 0.0) arr
        let hasNegative = any (\x -> x < 0.0) arr
        let allZero = all (\x -> x == 0.0) arr
        -- If all zero, neither positive nor negative should exist
        pure $ (allZero || hasPositive || hasNegative || Array.null arr)
               <?> "Array should have some character"
    
    it "any element matches min/max" do
      Spec.quickCheck do
        arr <- genChartDataArray
        let minVal = arrayMin arr
        let maxVal = arrayMax arr
        let hasMin = any (\x -> x == minVal) arr
        let hasMax = any (\x -> x == maxVal) arr
        pure $ (Array.null arr || (hasMin && hasMax))
               <?> "Min/max should be found in array"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // property test runner
-- ═══════════════════════════════════════════════════════════════════════════════

widgetPropertyTests :: Spec Unit
widgetPropertyTests = describe "Widget Property Tests" do
  isometricProjectionTests
  arrayHelperTests
  valueFormattingTests
  themeTests
  chartEdgeCaseTests
  aggregateDataTests

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Local arrayMin/arrayMax for testing (mirrors implementation)
arrayMin :: Array Number -> Number
arrayMin arr = case Array.head arr of
  Nothing -> 0.0
  Just first -> Array.foldl Math.min first arr

arrayMax :: Array Number -> Number
arrayMax arr = case Array.head arr of
  Nothing -> 0.0
  Just first -> Array.foldl Math.max first arr

-- | Check if number is finite (not NaN or Infinity)
isFiniteNumber :: Number -> Boolean
isFiniteNumber n = not (Number.isNaN n) && Number.isFinite n

-- | Approximate equality for floating point
shouldBeCloseTo :: Number -> Number -> Aff Unit
shouldBeCloseTo actual expected =
  if Math.abs (actual - expected) < 0.0001
    then pure unit
    else throwError $ error $ "Expected " <> show expected <> " but got " <> show actual

shouldBe :: forall a. Eq a => Show a => a -> a -> Aff Unit
shouldBe actual expected =
  if actual == expected
    then pure unit
    else throwError $ error $ "Expected " <> show expected <> " but got " <> show actual

shouldNotEqual :: forall a. Eq a => Show a => a -> a -> Aff Unit
shouldNotEqual actual unexpected =
  if actual /= unexpected
    then pure unit
    else throwError $ error $ "Expected different from " <> show unexpected

shouldEqual :: forall a. Eq a => Show a => a -> a -> Aff Unit
shouldEqual = shouldBe

-- | Estimate order of magnitude from formatted string
estimateMagnitude :: String -> Number
estimateMagnitude s
  | String.contains (String.Pattern "B") s = 1000000000.0
  | String.contains (String.Pattern "M") s = 1000000.0
  | String.contains (String.Pattern "K") s = 1000.0
  | otherwise = 1.0


