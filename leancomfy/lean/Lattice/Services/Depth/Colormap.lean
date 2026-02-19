/-
  Lattice.Services.Depth.Colormap - Scientific Colormaps

  Pure mathematical functions for depth visualization colormaps:
  - Viridis (default matplotlib, perceptually uniform)
  - Magma (perceptually uniform, warm)
  - Plasma (perceptually uniform, bright)
  - Inferno (perceptually uniform, high contrast)
  - Turbo (Google's rainbow alternative)

  Source: ui/src/services/export/depthRenderer.ts (lines 826-997)
-/

namespace Lattice.Services.Depth.Colormap

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- RGB color as triple of values in [0, 255]. -/
abbrev RGB := Nat × Nat × Nat

/-- Colormap enum. -/
inductive ColormapType
  | grayscale
  | viridis
  | magma
  | plasma
  | inferno
  | turbo
  deriving Repr, DecidableEq

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

/-- Clamp value to [0, 1]. -/
def clamp01 (t : Float) : Float :=
  if t < 0.0 then 0.0
  else if t > 1.0 then 1.0
  else t

/-- Linear interpolation between two integers. -/
def lerpInt (a b : Nat) (t : Float) : Nat :=
  let result := a.toFloat + (b.toFloat - a.toFloat) * t
  result.toUInt32.toNat

/-- Interpolate between two RGB colors. -/
def lerpRGB (c1 c2 : RGB) (t : Float) : RGB :=
  (lerpInt c1.1 c2.1 t, lerpInt c1.2.1 c2.2.1 t, lerpInt c1.2.2 c2.2.2 t)

/-- Sample from color array with interpolation.
    t in [0, 1], colors is the lookup table. -/
def sampleColorArray (colors : Array RGB) (t : Float) : RGB :=
  if colors.size == 0 then (0, 0, 0)
  else
    let clamped := clamp01 t
    let idx := clamped * (colors.size - 1).toFloat
    let i := idx.toUInt32.toNat
    let f := idx - i.toFloat
    if i >= colors.size - 1 then
      colors[colors.size - 1]!
    else
      lerpRGB colors[i]! colors[i + 1]! f

--------------------------------------------------------------------------------
-- Grayscale
--------------------------------------------------------------------------------

/-- Grayscale colormap: t → (v, v, v) where v = t * 255. -/
def grayscale (t : Float) : RGB :=
  let v := (clamp01 t * 255.0).toUInt32.toNat
  (v, v, v)

--------------------------------------------------------------------------------
-- Viridis Colormap
--------------------------------------------------------------------------------

/-- Viridis colormap lookup table (10 control points). -/
def viridisColors : Array RGB := #[
  (68, 1, 84),
  (72, 40, 120),
  (62, 74, 137),
  (49, 104, 142),
  (38, 130, 142),
  (31, 158, 137),
  (53, 183, 121),
  (109, 205, 89),
  (180, 222, 44),
  (253, 231, 37)
]

/-- Viridis colormap: perceptually uniform, blue-green-yellow. -/
def viridis (t : Float) : RGB := sampleColorArray viridisColors t

--------------------------------------------------------------------------------
-- Magma Colormap
--------------------------------------------------------------------------------

/-- Magma colormap lookup table (9 control points). -/
def magmaColors : Array RGB := #[
  (0, 0, 4),
  (28, 16, 68),
  (79, 18, 123),
  (129, 37, 129),
  (181, 54, 122),
  (229, 80, 100),
  (251, 135, 97),
  (254, 194, 135),
  (252, 253, 191)
]

/-- Magma colormap: perceptually uniform, black-red-yellow-white. -/
def magma (t : Float) : RGB := sampleColorArray magmaColors t

--------------------------------------------------------------------------------
-- Plasma Colormap
--------------------------------------------------------------------------------

/-- Plasma colormap lookup table (9 control points). -/
def plasmaColors : Array RGB := #[
  (13, 8, 135),
  (75, 3, 161),
  (125, 3, 168),
  (168, 34, 150),
  (203, 70, 121),
  (229, 107, 93),
  (248, 148, 65),
  (253, 195, 40),
  (240, 249, 33)
]

/-- Plasma colormap: perceptually uniform, purple-orange-yellow. -/
def plasma (t : Float) : RGB := sampleColorArray plasmaColors t

--------------------------------------------------------------------------------
-- Inferno Colormap
--------------------------------------------------------------------------------

/-- Inferno colormap lookup table (11 control points). -/
def infernoColors : Array RGB := #[
  (0, 0, 4),
  (22, 11, 57),
  (66, 10, 104),
  (106, 23, 110),
  (147, 38, 103),
  (188, 55, 84),
  (221, 81, 58),
  (243, 118, 27),
  (252, 165, 10),
  (246, 215, 70),
  (252, 255, 164)
]

/-- Inferno colormap: perceptually uniform, black-purple-red-yellow-white. -/
def inferno (t : Float) : RGB := sampleColorArray infernoColors t

--------------------------------------------------------------------------------
-- Turbo Colormap
--------------------------------------------------------------------------------

/-- Turbo colormap lookup table (13 control points). -/
def turboColors : Array RGB := #[
  (48, 18, 59),
  (70, 68, 172),
  (62, 121, 229),
  (38, 170, 225),
  (31, 212, 182),
  (76, 237, 123),
  (149, 249, 67),
  (212, 241, 31),
  (253, 207, 37),
  (252, 150, 38),
  (239, 85, 33),
  (205, 33, 28),
  (122, 4, 3)
]

/-- Turbo colormap: Google's improved rainbow, perceptually smoother. -/
def turbo (t : Float) : RGB := sampleColorArray turboColors t

--------------------------------------------------------------------------------
-- Colormap Dispatcher
--------------------------------------------------------------------------------

/-- Get color from specified colormap at position t ∈ [0, 1]. -/
def getColor (colormap : ColormapType) (t : Float) : RGB :=
  match colormap with
  | ColormapType.grayscale => grayscale t
  | ColormapType.viridis => viridis t
  | ColormapType.magma => magma t
  | ColormapType.plasma => plasma t
  | ColormapType.inferno => inferno t
  | ColormapType.turbo => turbo t

end Lattice.Services.Depth.Colormap
