/-
  Lattice.Services.Color.Conversion - Color Space Conversions

  Pure mathematical functions for color space conversion:
  - RGB ↔ HSV conversion
  - BT.709 luminance (brightness)
  - Color sample creation with derived values

  Source: ui/src/services/colorDepthReactivity.ts
-/

namespace Lattice.Services.Color.Conversion

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- RGB color with components in 0-1 range -/
structure RGB where
  r : Float  -- 0-1
  g : Float  -- 0-1
  b : Float  -- 0-1
  deriving Repr, Inhabited

/-- RGBA color with alpha -/
structure RGBA where
  r : Float  -- 0-1
  g : Float  -- 0-1
  b : Float  -- 0-1
  a : Float  -- 0-1
  deriving Repr, Inhabited

/-- HSV color with components in 0-1 range -/
structure HSV where
  h : Float  -- 0-1 (0 = red, 0.33 = green, 0.67 = blue)
  s : Float  -- 0-1
  v : Float  -- 0-1
  deriving Repr, Inhabited

/-- Complete color sample with all derived values -/
structure ColorSample where
  r : Float          -- 0-1
  g : Float          -- 0-1
  b : Float          -- 0-1
  a : Float          -- 0-1
  brightness : Float -- 0-1 (BT.709 luminance)
  hue : Float        -- 0-1
  saturation : Float -- 0-1
  value : Float      -- 0-1 (HSV V)
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- RGB to HSV Conversion
--------------------------------------------------------------------------------

/-- Convert RGB to HSV.

    Algorithm:
    - V = max(R, G, B)
    - S = (V - min) / V (0 if V = 0)
    - H based on which channel is max -/
def rgbToHsv (rgb : RGB) : HSV :=
  let r := rgb.r
  let g := rgb.g
  let b := rgb.b

  let maxVal := Float.max r (Float.max g b)
  let minVal := Float.min r (Float.min g b)
  let d := maxVal - minVal

  -- Value is max
  let v := maxVal

  -- Saturation
  let s := if maxVal == 0.0 then 0.0 else d / maxVal

  -- Hue calculation
  let h :=
    if maxVal == minVal then 0.0  -- Achromatic
    else if maxVal == r then
      let hRaw := (g - b) / d
      let hAdj := if g < b then hRaw + 6.0 else hRaw
      hAdj / 6.0
    else if maxVal == g then
      ((b - r) / d + 2.0) / 6.0
    else  -- maxVal == b
      ((r - g) / d + 4.0) / 6.0

  ⟨h, s, v⟩

/-- Convert HSV to RGB.

    Standard HSV to RGB conversion algorithm. -/
def hsvToRgb (hsv : HSV) : RGB :=
  let h := hsv.h
  let s := hsv.s
  let v := hsv.v

  if s == 0.0 then
    -- Achromatic (gray)
    ⟨v, v, v⟩
  else
    let h6 := h * 6.0
    let i := h6.toUInt64.toNat % 6
    let f := h6 - Float.floor h6
    let p := v * (1.0 - s)
    let q := v * (1.0 - s * f)
    let t := v * (1.0 - s * (1.0 - f))

    match i with
    | 0 => ⟨v, t, p⟩
    | 1 => ⟨q, v, p⟩
    | 2 => ⟨p, v, t⟩
    | 3 => ⟨p, q, v⟩
    | 4 => ⟨t, p, v⟩
    | _ => ⟨v, p, q⟩  -- i == 5

--------------------------------------------------------------------------------
-- Brightness (Luminance)
--------------------------------------------------------------------------------

/-- Calculate brightness using ITU-R BT.709 luminance coefficients.

    Y = 0.2126 * R + 0.7152 * G + 0.0722 * B

    This is the standard formula for perceived brightness. -/
def calculateBrightness (r g b : Float) : Float :=
  0.2126 * r + 0.7152 * g + 0.0722 * b

/-- Calculate brightness from RGB structure. -/
def rgbBrightness (rgb : RGB) : Float :=
  calculateBrightness rgb.r rgb.g rgb.b

--------------------------------------------------------------------------------
-- Color Sample Creation
--------------------------------------------------------------------------------

/-- Create a complete color sample from RGBA values.

    Derives all color properties:
    - HSV components
    - BT.709 brightness -/
def createColorSample (r g b a : Float) : ColorSample :=
  let hsv := rgbToHsv ⟨r, g, b⟩
  let brightness := calculateBrightness r g b
  { r := r
  , g := g
  , b := b
  , a := a
  , brightness := brightness
  , hue := hsv.h
  , saturation := hsv.s
  , value := hsv.v }

/-- Create color sample from RGB. -/
def colorSampleFromRGB (rgb : RGB) (a : Float := 1.0) : ColorSample :=
  createColorSample rgb.r rgb.g rgb.b a

/-- Create color sample from RGBA. -/
def colorSampleFromRGBA (rgba : RGBA) : ColorSample :=
  createColorSample rgba.r rgba.g rgba.b rgba.a

/-- Empty/black color sample. -/
def emptyColorSample : ColorSample :=
  createColorSample 0.0 0.0 0.0 0.0

--------------------------------------------------------------------------------
-- Feature Extraction
--------------------------------------------------------------------------------

/-- Color feature type for sampling. -/
inductive ColorFeature where
  | brightness
  | hue
  | saturation
  | value
  | red
  | green
  | blue
  | alpha
  deriving Repr, DecidableEq, Inhabited

/-- Extract a specific feature value from a color sample. -/
def getFeatureValue (sample : ColorSample) (feature : ColorFeature) : Float :=
  match feature with
  | .brightness => sample.brightness
  | .hue => sample.hue
  | .saturation => sample.saturation
  | .value => sample.value
  | .red => sample.r
  | .green => sample.g
  | .blue => sample.b
  | .alpha => sample.a

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

/-- Clamp a value to 0-1 range. -/
def clamp01 (x : Float) : Float :=
  Float.max 0.0 (Float.min 1.0 x)

/-- Clamp RGB to valid range. -/
def clampRGB (rgb : RGB) : RGB :=
  ⟨clamp01 rgb.r, clamp01 rgb.g, clamp01 rgb.b⟩

/-- Clamp RGBA to valid range. -/
def clampRGBA (rgba : RGBA) : RGBA :=
  ⟨clamp01 rgba.r, clamp01 rgba.g, clamp01 rgba.b, clamp01 rgba.a⟩

/-- Linear interpolation between two colors. -/
def lerpRGB (a b : RGB) (t : Float) : RGB :=
  let tc := clamp01 t
  ⟨a.r + (b.r - a.r) * tc,
   a.g + (b.g - a.g) * tc,
   a.b + (b.b - a.b) * tc⟩

/-- Linear interpolation between two RGBA colors. -/
def lerpRGBA (a b : RGBA) (t : Float) : RGBA :=
  let tc := clamp01 t
  ⟨a.r + (b.r - a.r) * tc,
   a.g + (b.g - a.g) * tc,
   a.b + (b.b - a.b) * tc,
   a.a + (b.a - a.a) * tc⟩

end Lattice.Services.Color.Conversion
