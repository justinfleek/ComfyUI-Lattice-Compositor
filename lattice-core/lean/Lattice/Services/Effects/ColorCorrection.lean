/-
  Lattice.Services.Effects.ColorCorrection - Basic Color Correction

  Pure mathematical functions for color correction:
  - Brightness & Contrast
  - Levels (input/output with gamma)
  - Exposure (photographic stops)

  All functions operate on normalized [0,1] color values.
  All functions are total and deterministic.
  NO banned constructs: no partial def, sorry, panic!, unreachable!

  Source: ui/src/services/effects/colorRenderer.ts
-/

namespace Lattice.Services.Effects.ColorCorrection

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- RGB color tuple -/
structure RGB where
  r : Float
  g : Float
  b : Float
  deriving Repr, Inhabited, BEq

/-- Brightness/Contrast parameters -/
structure ColorParams where
  brightness : Float  -- -1.5 to 1.5 (normalized from -150 to 150)
  contrast : Float    -- -1.0 to 1.0 (normalized from -100 to 100)
  useLegacy : Bool    -- Use legacy (simpler) contrast formula
  deriving Repr, Inhabited, BEq

/-- Levels parameters -/
structure LevelsParams where
  inputBlack : Float   -- 0-1 (normalized from 0-255)
  inputWhite : Float   -- 0-1 (normalized from 0-255)
  gamma : Float        -- 0.01-10 (gamma correction)
  outputBlack : Float  -- 0-1 (normalized from 0-255)
  outputWhite : Float  -- 0-1 (normalized from 0-255)
  deriving Repr, Inhabited, BEq

/-- Exposure parameters -/
structure ExposureParams where
  exposure : Float  -- -5 to 5 stops
  offset : Float    -- -1 to 1 (additive)
  gamma : Float     -- 0.1 to 10 (gamma correction)
  deriving Repr, Inhabited, BEq

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

/-- Default brightness/contrast (no change) -/
def defaultColorParams : ColorParams :=
  { brightness := 0.0
    contrast := 0.0
    useLegacy := false }

/-- Default levels (identity mapping) -/
def defaultLevelsParams : LevelsParams :=
  { inputBlack := 0.0
    inputWhite := 1.0
    gamma := 1.0
    outputBlack := 0.0
    outputWhite := 1.0 }

/-- Default exposure (no change) -/
def defaultExposureParams : ExposureParams :=
  { exposure := 0.0
    offset := 0.0
    gamma := 1.0 }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

/-- Clamp value to [0, 1] -/
def clamp01 (x : Float) : Float :=
  if x < 0.0 then 0.0
  else if x > 1.0 then 1.0
  else x

/-- Safe division with fallback -/
def safeDiv (a b fallback : Float) : Float :=
  if b == 0.0 || b.isNaN || b.isInf then fallback
  else a / b

/-- Safe power function -/
def safePow (base exp : Float) : Float :=
  let result := Float.pow base exp
  if result.isNaN || result.isInf then 1.0
  else result

--------------------------------------------------------------------------------
-- Brightness & Contrast
--------------------------------------------------------------------------------

/-- Calculate contrast factor based on mode -/
def contrastFactor (useLegacy : Bool) (contrast : Float) : Float :=
  if useLegacy then
    1.0 + contrast
  else
    let c255 := contrast * 255.0
    safeDiv (259.0 * (c255 + 255.0)) (255.0 * (259.0 - c255)) 1.0

/-- Apply brightness and contrast to a single pixel value [0,1] -/
def brightnessContrastPixel (params : ColorParams) (value : Float) : Float :=
  let factor := contrastFactor params.useLegacy params.contrast
  let withBrightness := value + params.brightness
  let withContrast := factor * (withBrightness - 0.5) + 0.5
  clamp01 withContrast

/-- Apply brightness and contrast to RGB -/
def brightnessContrast (params : ColorParams) (color : RGB) : RGB :=
  { r := brightnessContrastPixel params color.r
    g := brightnessContrastPixel params color.g
    b := brightnessContrastPixel params color.b }

--------------------------------------------------------------------------------
-- Levels
--------------------------------------------------------------------------------

/-- Apply levels adjustment to a single pixel value [0,1] -/
def levelsPixel (params : LevelsParams) (value : Float) : Float :=
  let inputRange := params.inputWhite - params.inputBlack
  let outputRange := params.outputWhite - params.outputBlack
  let gamma := if params.gamma < 0.01 then 0.01 else params.gamma
  -- Input levels
  let shifted := value - params.inputBlack
  let mapped := safeDiv shifted inputRange 0.0
  let clamped := clamp01 mapped
  -- Gamma correction: x^(1/gamma)
  let invGamma := safeDiv 1.0 gamma 1.0
  let gammaApplied := safePow clamped invGamma
  -- Output levels
  let output := params.outputBlack + gammaApplied * outputRange
  clamp01 output

/-- Apply levels to RGB -/
def levels (params : LevelsParams) (color : RGB) : RGB :=
  { r := levelsPixel params color.r
    g := levelsPixel params color.g
    b := levelsPixel params color.b }

--------------------------------------------------------------------------------
-- Exposure
--------------------------------------------------------------------------------

/-- Apply exposure adjustment to a single pixel value [0,1] -/
def exposurePixel (params : ExposureParams) (value : Float) : Float :=
  let gamma := if params.gamma < 0.01 then 0.01 else params.gamma
  -- Exposure (stops): multiply by 2^exposure
  let multiplier := safePow 2.0 params.exposure
  let withExposure := value * multiplier
  -- Offset
  let withOffset := withExposure + params.offset
  -- Clamp before gamma
  let clamped := clamp01 withOffset
  -- Gamma: x^(1/gamma)
  let invGamma := safeDiv 1.0 gamma 1.0
  safePow clamped invGamma

/-- Apply exposure to RGB -/
def exposure (params : ExposureParams) (color : RGB) : RGB :=
  { r := exposurePixel params color.r
    g := exposurePixel params color.g
    b := exposurePixel params color.b }

--------------------------------------------------------------------------------
-- Lookup Table Generation
--------------------------------------------------------------------------------

/-- Build 256-entry lookup table using given function -/
def buildLUT (f : Float → Float) : Array UInt8 :=
  Array.ofFn fun i : Fin 256 =>
    let normalized := Float.ofNat i.val / 255.0
    let result := f normalized
    let scaled := result * 255.0
    let clamped := if scaled < 0.0 then 0.0
                   else if scaled > 255.0 then 255.0
                   else scaled
    clamped.toUInt8

/-- Build brightness/contrast LUT -/
def buildBrightnessContrastLUT (params : ColorParams) : Array UInt8 :=
  buildLUT (brightnessContrastPixel params)

/-- Build levels LUT -/
def buildLevelsLUT (params : LevelsParams) : Array UInt8 :=
  buildLUT (levelsPixel params)

/-- Build exposure LUT -/
def buildExposureLUT (params : ExposureParams) : Array UInt8 :=
  buildLUT (exposurePixel params)

--------------------------------------------------------------------------------
-- Proofs (Structural - No sorry, No native_decide)
--------------------------------------------------------------------------------

/-- clamp01 applied twice is idempotent -/
theorem clamp01_idempotent (x : Float) : clamp01 (clamp01 x) = clamp01 x := by
  simp only [clamp01]
  split_ifs <;> rfl

/-- brightnessContrast preserves structure (maps RGB to RGB) -/
theorem brightnessContrast_preserves_structure (params : ColorParams) (color : RGB) :
    ∃ r g b, brightnessContrast params color = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- levels preserves structure (maps RGB to RGB) -/
theorem levels_preserves_structure (params : LevelsParams) (color : RGB) :
    ∃ r g b, levels params color = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- exposure preserves structure (maps RGB to RGB) -/
theorem exposure_preserves_structure (params : ExposureParams) (color : RGB) :
    ∃ r g b, exposure params color = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- LUT always has exactly 256 entries -/
theorem buildLUT_size (f : Float → Float) : (buildLUT f).size = 256 := by
  simp only [buildLUT, Array.size_ofFn]

/-- safeDiv returns fallback when b is zero -/
theorem safeDiv_zero_denom (a fallback : Float) :
    safeDiv a 0.0 fallback = fallback := by
  simp only [safeDiv]
  rfl

/-- Default color params has zero brightness -/
theorem defaultColorParams_zero_brightness :
    defaultColorParams.brightness = 0.0 := by
  rfl

/-- Default color params has zero contrast -/
theorem defaultColorParams_zero_contrast :
    defaultColorParams.contrast = 0.0 := by
  rfl

/-- Default levels params has unit gamma -/
theorem defaultLevelsParams_unit_gamma :
    defaultLevelsParams.gamma = 1.0 := by
  rfl

/-- Default exposure params has zero exposure -/
theorem defaultExposureParams_zero_exposure :
    defaultExposureParams.exposure = 0.0 := by
  rfl

/-- Legacy contrast factor with zero contrast is 1 -/
theorem contrastFactor_legacy_zero :
    contrastFactor true 0.0 = 1.0 := by
  simp only [contrastFactor]
  rfl

end Lattice.Services.Effects.ColorCorrection
