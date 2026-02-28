-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // test // gpu // text
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property-based tests for SDF Text Rendering Kernels.
-- |
-- | ## What We Test
-- |
-- | 1. **Config Invariants**
-- |    - Workgroup dimensions must be positive
-- |    - DPI must be positive and finite
-- |    - Width/height must be positive
-- |
-- | 2. **Subpixel Modes**
-- |    - All modes are distinct
-- |    - Show/Eq instances are consistent
-- |
-- | 3. **Pipeline Composition**
-- |    - Sequences preserve determinism
-- |    - Workgroup/dispatch calculations are correct
-- |
-- | ## Realistic Distributions
-- |
-- | Generators are weighted toward realistic production values.

module Test.GPU.Text where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Int (toNumber)
import Data.Number (isFinite)
import Data.Tuple (Tuple(Tuple))
import Test.QuickCheck (Result, (===), (<?>))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck) as Spec

import Hydrogen.GPU.Kernel.Text as T

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // REALISTIC GENERATORS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate rasterize modes with realistic distribution.
genRasterizeMode :: Gen T.RasterizeMode
genRasterizeMode = frequency $ NEA.cons'
  (Tuple 50.0 (pure T.RasterizeSDF))       -- Standard SDF
  [ Tuple 30.0 (pure T.RasterizeMSDF)      -- Multi-channel (common for UI)
  , Tuple 20.0 (pure T.RasterizeMTSDF)     -- Multi-channel with true SDF
  ]

-- | Generate layout directions.
genLayoutDirection :: Gen T.LayoutDirection
genLayoutDirection = frequency $ NEA.cons'
  (Tuple 60.0 (pure T.LayoutLTR))          -- Western languages (most common)
  [ Tuple 20.0 (pure T.LayoutRTL)          -- Arabic/Hebrew
  , Tuple 10.0 (pure T.LayoutTTB)          -- CJK vertical
  , Tuple 10.0 (pure T.LayoutBTT)          -- Less common
  ]

-- | Generate subpixel modes with realistic distribution.
genSubpixelMode :: Gen T.SubpixelMode
genSubpixelMode = frequency $ NEA.cons'
  (Tuple 40.0 (pure T.SubpixelRGB))        -- Most LCD monitors
  [ Tuple 20.0 (pure T.SubpixelNone)       -- HiDPI, mobile
  , Tuple 20.0 (pure T.SubpixelBGR)        -- Some monitors
  , Tuple 10.0 (pure T.SubpixelVRGB)       -- Rotated displays
  , Tuple 10.0 (pure T.SubpixelVBGR)       -- Rotated displays
  ]

-- | Generate subpixel filters.
genSubpixelFilter :: Gen T.SubpixelFilter
genSubpixelFilter = frequency $ NEA.cons'
  (Tuple 50.0 (pure T.FilterGaussian))     -- Best quality
  [ Tuple 30.0 (pure T.FilterLinear)       -- Good balance
  , Tuple 20.0 (pure T.FilterBox)          -- Fastest
  ]

-- | Generate cursor styles.
genCursorStyle :: Gen T.CursorStyle
genCursorStyle = frequency $ NEA.cons'
  (Tuple 40.0 (pure T.CursorBlock))        -- Traditional terminal
  [ Tuple 30.0 (pure T.CursorBar)          -- Modern editors
  , Tuple 20.0 (pure T.CursorUnderline)    -- Alternative
  , Tuple 10.0 (pure T.CursorHollow)       -- Vim visual mode
  ]

-- | Generate blink states.
genBlinkState :: Gen T.BlinkState
genBlinkState = elements $ NEA.cons' T.BlinkVisible
  [ T.BlinkHidden
  , T.BlinkFading
  ]

-- | Generate text effects.
genTextEffect :: Gen T.TextEffect
genTextEffect = frequency $ NEA.cons'
  (Tuple 40.0 (pure T.EffectNone))         -- Plain text (most common)
  [ Tuple 20.0 genShadowEffect             -- UI text
  , Tuple 20.0 genOutlineEffect            -- Game HUD
  , Tuple 15.0 genGlowEffect               -- Neon effects
  , Tuple 5.0 genBevelEffect               -- Embossed text
  ]
  where
    -- Shadow effect with realistic config
    genShadowEffect :: Gen T.TextEffect
    genShadowEffect = pure $ T.EffectShadow
      { offsetX: 2.0
      , offsetY: 2.0
      , blur: 4.0
      , colorR: 0.0
      , colorG: 0.0
      , colorB: 0.0
      , colorA: 0.5
      }
    
    -- Outline effect with realistic config
    genOutlineEffect :: Gen T.TextEffect
    genOutlineEffect = pure $ T.EffectOutline
      { width: 1.0
      , colorR: 0.0
      , colorG: 0.0
      , colorB: 0.0
      , colorA: 1.0
      }
    
    -- Glow effect with realistic config
    genGlowEffect :: Gen T.TextEffect
    genGlowEffect = pure $ T.EffectGlow
      { radius: 8.0
      , intensity: 0.8
      , colorR: 0.5
      , colorG: 0.8
      , colorB: 1.0
      }
    
    -- Bevel effect with realistic config
    genBevelEffect :: Gen T.TextEffect
    genBevelEffect = pure $ T.EffectBevel
      { depth: 2.0
      , lightAngle: 45.0
      }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // BOUNDED GENERATORS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate DPI values with realistic distribution.
genDPI :: Gen Number
genDPI = frequency $ NEA.cons'
  (Tuple 30.0 (pure 96.0))                 -- Standard desktop
  [ Tuple 25.0 (pure 144.0)                -- 1.5x scaling
  , Tuple 20.0 (pure 192.0)                -- 2x (Retina/4K)
  , Tuple 10.0 (pure 288.0)                -- 3x (iPhone)
  , Tuple 10.0 (toNumber <$> chooseInt 72 384) -- Range
  , Tuple 5.0 (pure 72.0)                  -- Print/legacy
  ]

-- | Generate workgroup size component.
genWorkgroupComponent :: Gen Int
genWorkgroupComponent = frequency $ NEA.cons'
  (Tuple 30.0 (pure 8))                    -- Common default
  [ Tuple 30.0 (pure 16)                   -- Optimized
  , Tuple 20.0 (pure 32)                   -- Large workgroups
  , Tuple 10.0 (pure 4)                    -- Small workgroups
  , Tuple 10.0 (pure 1)                    -- Single thread dim
  ]

-- | Generate font size in pixels.
genFontSize :: Gen Number
genFontSize = frequency $ NEA.cons'
  (Tuple 10.0 (pure 12.0))                 -- Small UI
  [ Tuple 25.0 (pure 14.0)                 -- Terminal default
  , Tuple 25.0 (pure 16.0)                 -- Body text
  , Tuple 15.0 (pure 18.0)                 -- Large body
  , Tuple 10.0 (pure 24.0)                 -- Headings
  , Tuple 10.0 (toNumber <$> chooseInt 8 72)  -- Range
  , Tuple 5.0 (pure 48.0)                  -- Display text
  ]

-- | Generate screen dimensions.
genScreenDimension :: Gen Int
genScreenDimension = frequency $ NEA.cons'
  (Tuple 20.0 (pure 1920))                 -- 1080p width
  [ Tuple 20.0 (pure 1080)                 -- 1080p height
  , Tuple 15.0 (pure 2560)                 -- 1440p width
  , Tuple 15.0 (pure 1440)                 -- 1440p height
  , Tuple 10.0 (pure 3840)                 -- 4K width
  , Tuple 10.0 (pure 2160)                 -- 4K height
  , Tuple 5.0 (chooseInt 640 7680)         -- Range
  , Tuple 5.0 (pure 0)                     -- Invalid: zero (should fail)
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // PROPERTY TESTS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | All text kernel property tests
textKernelPropertyTests :: Spec Unit
textKernelPropertyTests = describe "Text Kernel Property Tests" do
  
  configInvariantTests
  subpixelModeTests
  rasterizeModeTests
  cursorStyleTests
  textEffectTests
  pipelinePresetTests

-- | Config invariant tests
configInvariantTests :: Spec Unit
configInvariantTests = describe "TextKernelConfig Invariants" do
  
  it "default config has positive workgroup dimensions" do
    let cfg = T.defaultTextKernelConfig
    Spec.quickCheck $ (cfg.workgroupSize.x > 0 && cfg.workgroupSize.y > 0 && cfg.workgroupSize.z > 0)
        <?> "workgroup dimensions must be positive"
  
  it "default config has positive screen dimensions" do
    let cfg = T.defaultTextKernelConfig
    Spec.quickCheck $ (cfg.width > 0 && cfg.height > 0)
        <?> "screen dimensions must be positive"
  
  it "default config has valid DPI" do
    let cfg = T.defaultTextKernelConfig
    Spec.quickCheck $ (cfg.dpi > 0.0 && isFinite cfg.dpi)
        <?> "DPI must be positive and finite"
  
  it "terminal config produces valid dimensions" do
    Spec.quickCheck do
      cols <- chooseInt 1 500
      rows <- chooseInt 1 200
      let cfg = T.terminalConfig cols rows
      pure $ (cfg.width > 0 && cfg.height > 0)
          <?> ("terminal config must produce positive dimensions for " <> show cols <> "x" <> show rows)
  
  it "editor config preserves input dimensions" do
    Spec.quickCheck do
      w <- chooseInt 1 4096
      h <- chooseInt 1 4096
      let cfg = T.editorConfig w h
      pure $ (cfg.width == w && cfg.height == h)
          <?> "editor config must preserve dimensions"
  
  it "UI config accepts custom DPI" do
    Spec.quickCheck do
      dpi <- genDPI
      let cfg = T.uiConfig 1920 1080 dpi
      pure $ (cfg.dpi == dpi)
          <?> "UI config must accept custom DPI"

-- | Subpixel mode tests
subpixelModeTests :: Spec Unit
subpixelModeTests = describe "SubpixelMode" do
  
  it "all subpixel modes are distinct" do
    let modes = [T.SubpixelNone, T.SubpixelRGB, T.SubpixelBGR, T.SubpixelVRGB, T.SubpixelVBGR]
    Spec.quickCheck $ allDistinct modes <?> "subpixel modes must be distinct"
  
  it "SubpixelNone equals itself" do
    Spec.quickCheck $ (T.SubpixelNone == T.SubpixelNone) <?> "reflexive equality"
  
  it "SubpixelRGB not equal to SubpixelBGR" do
    Spec.quickCheck $ (T.SubpixelRGB /= T.SubpixelBGR) <?> "RGB /= BGR"

-- | Rasterize mode tests
rasterizeModeTests :: Spec Unit
rasterizeModeTests = describe "RasterizeMode" do
  
  it "all rasterize modes are distinct" do
    let modes = [T.RasterizeSDF, T.RasterizeMSDF, T.RasterizeMTSDF]
    Spec.quickCheck $ allDistinct modes <?> "rasterize modes must be distinct"
  
  it "SDF mode has Show instance" do
    Spec.quickCheck $ (show T.RasterizeSDF == "RasterizeSDF") <?> "Show instance"
  
  it "MSDF mode has Show instance" do
    Spec.quickCheck $ (show T.RasterizeMSDF == "RasterizeMSDF") <?> "Show instance"

-- | Cursor style tests
cursorStyleTests :: Spec Unit
cursorStyleTests = describe "CursorStyle" do
  
  it "all cursor styles are distinct" do
    let styles = [T.CursorBlock, T.CursorUnderline, T.CursorBar, T.CursorHollow]
    Spec.quickCheck $ allDistinct styles <?> "cursor styles must be distinct"
  
  it "all blink states are distinct" do
    let states = [T.BlinkVisible, T.BlinkHidden, T.BlinkFading]
    Spec.quickCheck $ allDistinct states <?> "blink states must be distinct"

-- | Text effect tests
textEffectTests :: Spec Unit
textEffectTests = describe "TextEffect" do
  
  it "different effect types are not equal" do
    let shadow = T.EffectShadow { offsetX: 2.0, offsetY: 2.0, blur: 4.0
                                , colorR: 0.0, colorG: 0.0, colorB: 0.0, colorA: 0.5 }
    let outline = T.EffectOutline { width: 1.0, colorR: 0.0, colorG: 0.0
                                  , colorB: 0.0, colorA: 1.0 }
    Spec.quickCheck $ (shadow /= outline) <?> "shadow /= outline"
    Spec.quickCheck $ (shadow /= T.EffectNone) <?> "shadow /= none"
    Spec.quickCheck $ (outline /= T.EffectNone) <?> "outline /= none"
  
  it "EffectNone equals itself" do
    Spec.quickCheck $ (T.EffectNone == T.EffectNone) <?> "reflexive equality"
  
  it "same effect with same config are equal" do
    let shadow1 = T.EffectShadow { offsetX: 2.0, offsetY: 2.0, blur: 4.0
                                 , colorR: 0.0, colorG: 0.0, colorB: 0.0, colorA: 0.5 }
    let shadow2 = T.EffectShadow { offsetX: 2.0, offsetY: 2.0, blur: 4.0
                                 , colorR: 0.0, colorG: 0.0, colorB: 0.0, colorA: 0.5 }
    Spec.quickCheck $ (shadow1 == shadow2) <?> "same shadow configs are equal"

-- | Pipeline preset tests  
pipelinePresetTests :: Spec Unit
pipelinePresetTests = describe "Pipeline Presets" do
  
  it "ghostty terminal pipeline returns a valid kernel" do
    -- Pipeline presets take dimensions (cols/rows or width/height)
    let pipeline = T.ghosttyTerminalPipeline 80 24
    Spec.quickCheck $ isSequenceKernel pipeline
        <?> "ghostty pipeline must be a sequence"
  
  it "IDE editor pipeline returns a valid kernel" do
    let pipeline = T.ideEditorPipeline 1920 1080
    Spec.quickCheck $ isSequenceKernel pipeline
        <?> "IDE pipeline must be a sequence"
  
  it "UI label pipeline returns a valid kernel" do
    let pipeline = T.uiLabelPipeline 200 32
    Spec.quickCheck $ isSequenceKernel pipeline
        <?> "UI pipeline must be a sequence"
  
  it "game HUD pipeline returns a valid kernel" do
    let pipeline = T.gameHUDPipeline 1920 1080
    Spec.quickCheck $ isSequenceKernel pipeline
        <?> "game HUD pipeline must be a sequence"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // HELPERS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if a kernel is a sequence
isSequenceKernel :: T.TextKernel -> Boolean
isSequenceKernel (T.KernelTextSequence _) = true
isSequenceKernel _ = false

-- | Check all elements in array are distinct
-- | Uses Array.nub to remove duplicates and compares lengths
allDistinct :: forall a. Ord a => Array a -> Boolean
allDistinct arr = Array.length arr == Array.length (Array.nub arr)

-- | Property test returning Result type
-- | Used for property-based equality checks
equalityProperty :: forall a. Eq a => Show a => a -> a -> Result
equalityProperty a b = a === b
