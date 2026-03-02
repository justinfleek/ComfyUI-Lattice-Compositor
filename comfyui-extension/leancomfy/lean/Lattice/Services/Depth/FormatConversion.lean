/-
  Lattice.Services.Depth.FormatConversion - Depth Format Conversion

  Pure functions for converting depth buffers between formats:
  - Bit depth conversion (8/16/32-bit)
  - Normalization and inversion
  - Image data generation (RGBA)
  - Colormap application for visualization

  Source: ui/src/services/export/depthRenderer.ts (lines 600-997)
-/

namespace Lattice.Services.Depth.FormatConversion

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Supported depth map formats. -/
inductive DepthMapFormat
  | raw           -- Float32 raw depth
  | midas         -- MiDaS format (16-bit, inverted, normalized)
  | depthAnything -- Depth Anything format (16-bit, inverted, normalized)
  | zoeDepth      -- ZoeDepth format (16-bit, metric)
  | marigold      -- Marigold format (16-bit, normalized)
  | grayscale8    -- 8-bit grayscale
  | grayscale16   -- 16-bit grayscale
  deriving Repr, DecidableEq

/-- Depth format specification. -/
structure DepthFormatSpec where
  bitDepth : Nat         -- 8, 16, or 32
  nearClip : Float       -- Near clipping plane
  farClip : Float        -- Far clipping plane
  normalize : Bool       -- Normalize to [0, 1] range
  invert : Bool          -- Invert (near=bright, far=dark)
  deriving Repr

/-- RGB color tuple. -/
structure RGB where
  r : UInt8
  g : UInt8
  b : UInt8
  deriving Repr

/-- RGBA pixel. -/
structure RGBA where
  r : UInt8
  g : UInt8
  b : UInt8
  a : UInt8
  deriving Repr

/-- Depth render result. -/
structure DepthRenderResult where
  width : Nat
  height : Nat
  minDepth : Float
  maxDepth : Float
  deriving Repr

--------------------------------------------------------------------------------
-- Format Specifications
--------------------------------------------------------------------------------

/-- Get format specification for depth format. -/
def getFormatSpec (format : DepthMapFormat) : DepthFormatSpec :=
  match format with
  | DepthMapFormat.raw =>
    { bitDepth := 32, nearClip := 0.1, farClip := 100.0, normalize := false, invert := false }
  | DepthMapFormat.midas =>
    { bitDepth := 16, nearClip := 0.1, farClip := 100.0, normalize := true, invert := true }
  | DepthMapFormat.depthAnything =>
    { bitDepth := 16, nearClip := 0.1, farClip := 100.0, normalize := true, invert := true }
  | DepthMapFormat.zoeDepth =>
    { bitDepth := 16, nearClip := 0.001, farClip := 80.0, normalize := false, invert := false }
  | DepthMapFormat.marigold =>
    { bitDepth := 16, nearClip := 0.1, farClip := 100.0, normalize := true, invert := false }
  | DepthMapFormat.grayscale8 =>
    { bitDepth := 8, nearClip := 0.1, farClip := 100.0, normalize := true, invert := false }
  | DepthMapFormat.grayscale16 =>
    { bitDepth := 16, nearClip := 0.1, farClip := 100.0, normalize := true, invert := false }

--------------------------------------------------------------------------------
-- Normalization
--------------------------------------------------------------------------------

/-- Clamp value to [0, 1] range. -/
def clamp01 (value : Float) : Float :=
  Float.max 0.0 (Float.min 1.0 value)

/-- Normalize depth value to [0, 1] range based on min/max. -/
def normalizeDepth (depth minDepth maxDepth : Float) : Float :=
  let range := maxDepth - minDepth
  let safeRange := if range > 0.0 then range else 1.0
  clamp01 ((depth - minDepth) / safeRange)

/-- Normalize depth for metric format (scale to far clip). -/
def normalizeMetricDepth (depth farClip : Float) : Float :=
  clamp01 (depth / farClip)

/-- Invert normalized depth value. -/
def invertDepth (normalized : Float) : Float :=
  1.0 - normalized

--------------------------------------------------------------------------------
-- Bit Depth Conversion
--------------------------------------------------------------------------------

/-- Convert normalized [0, 1] to 8-bit [0, 255]. -/
def to8bit (normalized : Float) : UInt8 :=
  let scaled := normalized * 255.0
  let clamped := Float.max 0.0 (Float.min 255.0 scaled)
  clamped.toUInt8

/-- Convert normalized [0, 1] to 16-bit [0, 65535]. -/
def to16bit (normalized : Float) : UInt16 :=
  let scaled := normalized * 65535.0
  let clamped := Float.max 0.0 (Float.min 65535.0 scaled)
  clamped.toUInt32.toUInt16

/-- Convert 16-bit to 8-bit (for display). -/
def uint16To8bit (value : UInt16) : UInt8 :=
  (value.toNat / 256).toUInt8

/-- Convert Float32 depth (assumed 0-1) to 8-bit. -/
def float32To8bit (value : Float) : UInt8 :=
  to8bit (clamp01 value)

--------------------------------------------------------------------------------
-- Depth to Format Conversion
--------------------------------------------------------------------------------

/-- Convert single depth value based on format specification. -/
def convertDepthValue (depth minDepth maxDepth : Float)
                      (spec : DepthFormatSpec) : Float :=
  let normalized := if spec.normalize then
    normalizeDepth depth minDepth maxDepth
  else
    normalizeMetricDepth depth spec.farClip
  if spec.invert then invertDepth normalized else normalized

/-- Convert depth value to 8-bit output. -/
def depthTo8bit (depth minDepth maxDepth : Float) (spec : DepthFormatSpec) : UInt8 :=
  let normalized := convertDepthValue depth minDepth maxDepth spec
  to8bit normalized

/-- Convert depth value to 16-bit output. -/
def depthTo16bit (depth minDepth maxDepth : Float) (spec : DepthFormatSpec) : UInt16 :=
  let normalized := convertDepthValue depth minDepth maxDepth spec
  to16bit normalized

--------------------------------------------------------------------------------
-- Image Data Generation
--------------------------------------------------------------------------------

/-- Create grayscale RGBA pixel from depth value. -/
def depthToGrayscalePixel (value : UInt8) : RGBA :=
  { r := value, g := value, b := value, a := 255 }

/-- Create RGBA pixel from RGB and alpha. -/
def rgbToRGBA (rgb : RGB) (alpha : UInt8 := 255) : RGBA :=
  { r := rgb.r, g := rgb.g, b := rgb.b, a := alpha }

/-- Calculate pixel index in RGBA image data. -/
def pixelIndex (i : Nat) : Nat :=
  i * 4

--------------------------------------------------------------------------------
-- Colormap Colors
--------------------------------------------------------------------------------

/-- Viridis colormap lookup table (10 colors). -/
def viridisColors : Array RGB := #[
  { r := 68,  g := 1,   b := 84  },
  { r := 72,  g := 40,  b := 120 },
  { r := 62,  g := 74,  b := 137 },
  { r := 49,  g := 104, b := 142 },
  { r := 38,  g := 130, b := 142 },
  { r := 31,  g := 158, b := 137 },
  { r := 53,  g := 183, b := 121 },
  { r := 109, g := 205, b := 89  },
  { r := 180, g := 222, b := 44  },
  { r := 253, g := 231, b := 37  }
]

/-- Magma colormap lookup table (9 colors). -/
def magmaColors : Array RGB := #[
  { r := 0,   g := 0,   b := 4   },
  { r := 28,  g := 16,  b := 68  },
  { r := 79,  g := 18,  b := 123 },
  { r := 129, g := 37,  b := 129 },
  { r := 181, g := 54,  b := 122 },
  { r := 229, g := 80,  b := 100 },
  { r := 251, g := 135, b := 97  },
  { r := 254, g := 194, b := 135 },
  { r := 252, g := 253, b := 191 }
]

/-- Plasma colormap lookup table (9 colors). -/
def plasmaColors : Array RGB := #[
  { r := 13,  g := 8,   b := 135 },
  { r := 75,  g := 3,   b := 161 },
  { r := 125, g := 3,   b := 168 },
  { r := 168, g := 34,  b := 150 },
  { r := 203, g := 70,  b := 121 },
  { r := 229, g := 107, b := 93  },
  { r := 248, g := 148, b := 65  },
  { r := 253, g := 195, b := 40  },
  { r := 240, g := 249, b := 33  }
]

/-- Inferno colormap lookup table (11 colors). -/
def infernoColors : Array RGB := #[
  { r := 0,   g := 0,   b := 4   },
  { r := 22,  g := 11,  b := 57  },
  { r := 66,  g := 10,  b := 104 },
  { r := 106, g := 23,  b := 110 },
  { r := 147, g := 38,  b := 103 },
  { r := 188, g := 55,  b := 84  },
  { r := 221, g := 81,  b := 58  },
  { r := 243, g := 118, b := 27  },
  { r := 252, g := 165, b := 10  },
  { r := 246, g := 215, b := 70  },
  { r := 252, g := 255, b := 164 }
]

/-- Turbo colormap lookup table (13 colors). -/
def turboColors : Array RGB := #[
  { r := 48,  g := 18,  b := 59  },
  { r := 70,  g := 68,  b := 172 },
  { r := 62,  g := 121, b := 229 },
  { r := 38,  g := 170, b := 225 },
  { r := 31,  g := 212, b := 182 },
  { r := 76,  g := 237, b := 123 },
  { r := 149, g := 249, b := 67  },
  { r := 212, g := 241, b := 31  },
  { r := 253, g := 207, b := 37  },
  { r := 252, g := 150, b := 38  },
  { r := 239, g := 85,  b := 33  },
  { r := 205, g := 33,  b := 28  },
  { r := 122, g := 4,   b := 3   }
]

--------------------------------------------------------------------------------
-- Colormap Interpolation
--------------------------------------------------------------------------------

/-- Linearly interpolate between two UInt8 values. -/
def lerpUInt8 (a b : UInt8) (t : Float) : UInt8 :=
  let result := a.toFloat + (b.toFloat - a.toFloat) * t
  Float.max 0.0 (Float.min 255.0 result) |>.toUInt8

/-- Linearly interpolate between two RGB colors. -/
def lerpRGB (c1 c2 : RGB) (t : Float) : RGB :=
  { r := lerpUInt8 c1.r c2.r t
  , g := lerpUInt8 c1.g c2.g t
  , b := lerpUInt8 c1.b c2.b t
  }

/-- Sample color from colormap array with interpolation. -/
def sampleColormap (colors : Array RGB) (t : Float) : RGB :=
  if colors.size == 0 then { r := 0, g := 0, b := 0 }
  else
    let clamped := clamp01 t
    let n := colors.size
    let idx := clamped * (n - 1).toFloat
    let i := idx.toUInt32.toNat
    let f := idx - i.toFloat

    if i >= n - 1 then colors[n - 1]!
    else lerpRGB colors[i]! colors[i + 1]! f

--------------------------------------------------------------------------------
-- Colormap Selection
--------------------------------------------------------------------------------

/-- Supported colormaps. -/
inductive Colormap
  | grayscale
  | viridis
  | magma
  | plasma
  | inferno
  | turbo
  deriving Repr, DecidableEq

/-- Get color from colormap at normalized position. -/
def getColormapColor (t : Float) (cmap : Colormap) : RGB :=
  match cmap with
  | Colormap.grayscale =>
    let v := to8bit (clamp01 t)
    { r := v, g := v, b := v }
  | Colormap.viridis => sampleColormap viridisColors t
  | Colormap.magma => sampleColormap magmaColors t
  | Colormap.plasma => sampleColormap plasmaColors t
  | Colormap.inferno => sampleColormap infernoColors t
  | Colormap.turbo => sampleColormap turboColors t

/-- Parse colormap from string. -/
def parseColormap (s : String) : Colormap :=
  match s with
  | "viridis" => Colormap.viridis
  | "magma" => Colormap.magma
  | "plasma" => Colormap.plasma
  | "inferno" => Colormap.inferno
  | "turbo" => Colormap.turbo
  | _ => Colormap.grayscale

--------------------------------------------------------------------------------
-- AI Model Depth Convention
--------------------------------------------------------------------------------

/-- AI models (MiDaS, Depth-Anything) expect near=bright, far=dark.
    This inverts the normalized depth for proper visualization. -/
def invertForAIVisualization (normalized : Float) : Float :=
  1.0 - clamp01 normalized

end Lattice.Services.Depth.FormatConversion
