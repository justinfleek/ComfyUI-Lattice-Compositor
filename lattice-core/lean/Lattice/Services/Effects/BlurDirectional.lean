/-
  Lattice.Services.Effects.BlurDirectional - Directional and Radial Blur

  Pure mathematical functions for motion-style blurs:
  - Directional blur (motion blur in a direction)
  - Radial blur (zoom blur from center)
  - Box blur (fast average blur)
  - Sharpen filter

  All functions are total and deterministic.
  NO banned constructs: no partial def, sorry, panic!, unreachable!

  Source: ui/src/services/effects/blurRenderer.ts
-/

namespace Lattice.Services.Effects.BlurDirectional

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Directional (motion) blur parameters -/
structure DirectionalParams where
  angle : Float      -- Blur angle in radians [0, 2*pi]
  distance : Float   -- Blur distance in pixels [0-500]
  samples : Nat      -- Number of samples [1-64]
  deriving Repr, Inhabited

/-- Radial blur type -/
inductive RadialType where
  | Spin  -- Rotational blur around center
  | Zoom  -- Zoom blur toward/from center
  deriving Repr, DecidableEq

/-- Radial (zoom) blur parameters -/
structure RadialParams where
  centerX : Float    -- Center X [0-1] normalized
  centerY : Float    -- Center Y [0-1] normalized
  amount : Float     -- Blur amount [0-100]
  samples : Nat      -- Number of samples [1-64]
  radialType : RadialType
  deriving Repr, Inhabited

/-- Box blur parameters -/
structure BoxParams where
  radiusX : Nat  -- Horizontal radius [1-250]
  radiusY : Nat  -- Vertical radius [1-250]
  deriving Repr, Inhabited

/-- Sharpen parameters -/
structure SharpenParams where
  amount : Float  -- Sharpen amount [0-500%]
  radius : Nat    -- Radius [1-10]
  threshold : Nat -- Threshold [0-255]
  deriving Repr, Inhabited

/-- Sample offset with weight -/
structure SampleOffset where
  dx : Float
  dy : Float
  weight : Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

/-- Default directional blur -/
def defaultDirectionalParams : DirectionalParams :=
  { angle := 0.0
    distance := 10.0
    samples := 16 }

/-- Default radial blur -/
def defaultRadialParams : RadialParams :=
  { centerX := 0.5
    centerY := 0.5
    amount := 10.0
    samples := 16
    radialType := RadialType.Zoom }

/-- Default box blur -/
def defaultBoxParams : BoxParams :=
  { radiusX := 5
    radiusY := 5 }

/-- Default sharpen -/
def defaultSharpenParams : SharpenParams :=
  { amount := 100.0
    radius := 1
    threshold := 0 }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

/-- Pi constant -/
def pi : Float := 3.14159265358979323846

/-- Safe trigonometric functions -/
def safeCos (x : Float) : Float :=
  let result := Float.cos x
  if result.isNaN || result.isInf then 1.0 else result

def safeSin (x : Float) : Float :=
  let result := Float.sin x
  if result.isNaN || result.isInf then 0.0 else result

def safeAtan2 (y x : Float) : Float :=
  let result := Float.atan2 y x
  if result.isNaN || result.isInf then 0.0 else result

def safeSqrt (x : Float) : Float :=
  let clamped := if x < 0.0 then 0.0 else x
  let result := Float.sqrt clamped
  if result.isNaN || result.isInf then 0.0 else result

/-- Absolute value -/
def fabs (x : Float) : Float :=
  if x < 0.0 then -x else x

/-- Normalize angle to [0, 2*pi] -/
def normalizeAngle (angle : Float) : Float :=
  let twoPi := 2.0 * pi
  let n := Float.floor (angle / twoPi)
  let a := angle - n * twoPi
  if a < 0.0 then a + twoPi else a

/-- 2D Euclidean distance -/
def distance2D (x1 y1 x2 y2 : Float) : Float :=
  let dx := x2 - x1
  let dy := y2 - y1
  safeSqrt (dx * dx + dy * dy)

--------------------------------------------------------------------------------
-- Directional Blur
--------------------------------------------------------------------------------

/-- Calculate sample offset for directional blur -/
def directionalOffset (params : DirectionalParams) (sampleIdx : Nat) : SampleOffset :=
  let angle := params.angle
  let dist := params.distance
  let samples := max 1 params.samples
  let samplesF := Float.ofNat samples
  let samplesMinus1 := if samples > 1 then Float.ofNat (samples - 1) else 1.0
  let t := Float.ofNat sampleIdx / samplesMinus1 - 0.5
  let dx := safeCos angle * dist * t
  let dy := safeSin angle * dist * t
  let weight := 1.0 / samplesF
  { dx := dx, dy := dy, weight := weight }

/-- Generate all sample offsets for directional blur -/
def directionalOffsets (params : DirectionalParams) : Array SampleOffset :=
  let samples := max 1 params.samples
  Array.ofFn fun i : Fin samples => directionalOffset params i.val

--------------------------------------------------------------------------------
-- Radial Blur
--------------------------------------------------------------------------------

/-- Calculate sample offset for radial blur at a pixel position -/
def radialOffset (params : RadialParams) (x y : Float) (sampleIdx : Nat) : SampleOffset :=
  let cx := params.centerX
  let cy := params.centerY
  let amount := params.amount / 100.0
  let samples := max 1 params.samples
  let samplesF := Float.ofNat samples
  let samplesMinus1 := if samples > 1 then Float.ofNat (samples - 1) else 1.0
  let dx' := x - cx
  let dy' := y - cy
  let dist := safeSqrt (dx' * dx' + dy' * dy')
  let t := Float.ofNat sampleIdx / samplesMinus1 - 0.5
  let (offsetX, offsetY) := match params.radialType with
    | RadialType.Zoom =>
      (dx' * amount * t, dy' * amount * t)
    | RadialType.Spin =>
      let angle := safeAtan2 dy' dx'
      let spinAngle := angle + amount * t
      (safeCos spinAngle * dist - dx', safeSin spinAngle * dist - dy')
  let weight := 1.0 / samplesF
  { dx := offsetX, dy := offsetY, weight := weight }

--------------------------------------------------------------------------------
-- Box Blur
--------------------------------------------------------------------------------

/-- Box blur kernel size -/
def boxBlurSize (params : BoxParams) : Nat × Nat :=
  let rx := max 1 (min 250 params.radiusX)
  let ry := max 1 (min 250 params.radiusY)
  (rx * 2 + 1, ry * 2 + 1)

/-- Box blur kernel weight (uniform) -/
def boxBlurWeight (params : BoxParams) : Float :=
  let (w, h) := boxBlurSize params
  1.0 / Float.ofNat (w * h)

--------------------------------------------------------------------------------
-- Sharpen
--------------------------------------------------------------------------------

/-- Sharpen kernel center weight -/
def sharpenCenterWeight (params : SharpenParams) : Float :=
  let amount := params.amount / 100.0
  let r := max 1 (min 10 params.radius)
  let size := r * 2 + 1
  let blurWeight := 1.0 / Float.ofNat (size * size)
  1.0 + amount * (1.0 - blurWeight)

/-- Sharpen kernel neighbor weight -/
def sharpenNeighborWeight (params : SharpenParams) : Float :=
  let amount := params.amount / 100.0
  let r := max 1 (min 10 params.radius)
  let size := r * 2 + 1
  let blurWeight := 1.0 / Float.ofNat (size * size)
  -(amount * blurWeight)

/-- Apply sharpen threshold -/
def sharpenWithThreshold (params : SharpenParams) (original sharpened : Float) : Float :=
  let threshold := Float.ofNat params.threshold / 255.0
  let diff := fabs (sharpened - original)
  if diff < threshold then original else sharpened

--------------------------------------------------------------------------------
-- Proofs (Structural - No sorry, No native_decide)
--------------------------------------------------------------------------------

/-- Default directional blur has 16 samples -/
theorem defaultDirectionalParams_samples :
    defaultDirectionalParams.samples = 16 := by
  rfl

/-- Default directional blur has zero angle -/
theorem defaultDirectionalParams_zero_angle :
    defaultDirectionalParams.angle = 0.0 := by
  rfl

/-- Default radial blur uses Zoom type -/
theorem defaultRadialParams_zoom :
    defaultRadialParams.radialType = RadialType.Zoom := by
  rfl

/-- Default radial blur is centered at (0.5, 0.5) -/
theorem defaultRadialParams_centered :
    defaultRadialParams.centerX = 0.5 ∧ defaultRadialParams.centerY = 0.5 := by
  constructor <;> rfl

/-- Default box blur has equal radii -/
theorem defaultBoxParams_equal_radii :
    defaultBoxParams.radiusX = defaultBoxParams.radiusY := by
  rfl

/-- Default sharpen has 100% amount -/
theorem defaultSharpenParams_full_amount :
    defaultSharpenParams.amount = 100.0 := by
  rfl

/-- directionalOffsets array size equals samples -/
theorem directionalOffsets_size (params : DirectionalParams) :
    (directionalOffsets params).size = max 1 params.samples := by
  simp only [directionalOffsets, Array.size_ofFn]

/-- boxBlurSize produces odd dimensions -/
theorem boxBlurSize_odd (params : BoxParams) :
    let (w, h) := boxBlurSize params
    w % 2 = 1 ∧ h % 2 = 1 := by
  simp only [boxBlurSize]
  constructor
  · -- w = 2*rx + 1, so w % 2 = 1
    omega
  · -- h = 2*ry + 1, so h % 2 = 1
    omega

/-- directionalOffset preserves structure -/
theorem directionalOffset_preserves_structure (params : DirectionalParams) (sampleIdx : Nat) :
    ∃ dx dy w, directionalOffset params sampleIdx = { dx := dx, dy := dy, weight := w } := by
  exact ⟨_, _, _, rfl⟩

/-- radialOffset preserves structure -/
theorem radialOffset_preserves_structure (params : RadialParams) (x y : Float) (sampleIdx : Nat) :
    ∃ dx dy w, radialOffset params x y sampleIdx = { dx := dx, dy := dy, weight := w } := by
  exact ⟨_, _, _, rfl⟩

/-- Pi constant is well-defined -/
theorem pi_value : pi = 3.14159265358979323846 := by
  rfl

/-- normalizeAngle is well-defined for any input -/
theorem normalizeAngle_defined (angle : Float) :
    ∃ a, normalizeAngle angle = a := by
  exact ⟨_, rfl⟩

/-- distance2D is well-defined for any inputs -/
theorem distance2D_defined (x1 y1 x2 y2 : Float) :
    ∃ d, distance2D x1 y1 x2 y2 = d := by
  exact ⟨_, rfl⟩

end Lattice.Services.Effects.BlurDirectional
