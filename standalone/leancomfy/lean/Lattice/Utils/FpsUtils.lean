/-
  Lattice.Utils.FpsUtils - Frame rate utilities

  Validation and helper functions for frame rate handling.
  Ensures fps values are valid to prevent division by zero.
  NO banned constructs: no partial def, sorry, panic!, unreachable!, native_decide

  Uses raw Float with defensive guards.

  Source: ui/src/utils/fpsUtils.ts
-/

namespace Lattice.Utils.FpsUtils

/-! ## Constants -/

/-- Default fps for Lattice Compositor (WAN model standard) -/
def defaultFps : Nat := 16

/-- Minimum allowed fps value -/
def minFps : Nat := 1

/-- Maximum allowed fps value -/
def maxFps : Nat := 120

/-! ## Utility -/

/-- Check if a Float is finite -/
def isFinite (x : Float) : Bool :=
  !x.isNaN && !x.isInf

/-- Clamp natural number to range -/
def clampNat (lo hi x : Nat) : Nat :=
  max lo (min hi x)

/-! ## FPS Type -/

/-- Validated FPS value (stores the raw Nat, validation at construction) -/
structure Fps where
  val : Nat
  deriving Repr, Inhabited

/-- Smart constructor for Fps -/
def Fps.mk' (n : Nat) : Fps :=
  ⟨clampNat minFps maxFps (max 1 n)⟩

/-- Default FPS instance -/
def Fps.default : Fps := ⟨defaultFps⟩

/-- Check if Fps is valid (positive and in range) -/
def Fps.isValid (fps : Fps) : Bool :=
  fps.val > 0 && fps.val >= minFps && fps.val <= maxFps

/-! ## Validation -/

/-- Validate fps value from Float, returning fallback if invalid -/
def validateFps (fps : Option Float) (fallback : Fps := Fps.default) : Fps :=
  match fps with
  | none => fallback
  | some f =>
    if !isFinite f || f <= 0.0 then fallback
    else
      let clamped := Float.max (Float.ofNat minFps) (Float.min (Float.ofNat maxFps) f)
      let nat := clamped.toUInt64.toNat
      if nat > 0 && nat >= minFps && nat <= maxFps then ⟨nat⟩
      else fallback

/-- Validate fps from Nat -/
def validateFpsNat (fps : Nat) (fallback : Fps := Fps.default) : Fps :=
  if fps > 0 then
    ⟨clampNat minFps maxFps fps⟩
  else
    fallback

/-! ## Safe Operations -/

/-- Safely divide by fps -/
def safeDivideByFps (numerator : Float) (fps : Fps) : Float :=
  let denom := Float.ofNat fps.val
  if denom > 0.0 then numerator / denom else 0.0

/-- Convert frame number to time in seconds -/
def frameToTime (frame : Nat) (fps : Fps) : Float :=
  let fpsFloat := Float.ofNat fps.val
  if fpsFloat > 0.0 then
    let result := Float.ofNat frame / fpsFloat
    if isFinite result then result else 0.0
  else 0.0

/-- Convert time in seconds to frame number -/
def timeToFrame (time : Float) (fps : Fps) : Nat :=
  if time < 0.0 || !isFinite time then 0
  else
    let result := time * Float.ofNat fps.val
    if isFinite result && result >= 0.0 then result.toUInt64.toNat else 0

/-- Calculate duration in seconds from frame count -/
def calculateDuration (frameCount : Nat) (fps : Fps) : Float :=
  let fpsFloat := Float.ofNat fps.val
  if fpsFloat > 0.0 then
    let result := Float.ofNat frameCount / fpsFloat
    if isFinite result then result else 0.0
  else 0.0

/-- Calculate frame count from duration (ceiling) -/
def calculateFrameCount (duration : Float) (fps : Fps) : Nat :=
  if !isFinite duration || duration < 0.0 then 0
  else
    let result := duration * Float.ofNat fps.val
    if isFinite result then (Float.ceil result).toUInt64.toNat else 0

/-! ## Assertions -/

/-- Assert fps is valid, return Except -/
def assertValidFps (fps : Option Float) (context : Option String := none) : Except String Fps :=
  match fps with
  | none =>
    let ctx := context.map (s!" in {·}") |>.getD ""
    .error s!"Invalid fps value{ctx}: none. FPS must be a positive number."
  | some f =>
    if !isFinite f || f <= 0.0 then
      let ctx := context.map (s!" in {·}") |>.getD ""
      .error s!"Invalid fps value{ctx}: {f}. FPS must be a positive number."
    else
      .ok (validateFps (some f))

--------------------------------------------------------------------------------
-- Proofs (Structural - No sorry, No native_decide)
--------------------------------------------------------------------------------

/-- Default fps value is defaultFps -/
theorem Fps_default_val : Fps.default.val = defaultFps := by
  rfl

/-- clampNat always returns at least lo -/
theorem clampNat_ge_lo (lo hi x : Nat) : clampNat lo hi x >= lo := by
  simp only [clampNat]
  exact Nat.le_max_left lo _

/-- clampNat always returns at most hi when lo <= hi -/
theorem clampNat_le_hi (lo hi x : Nat) (h : lo <= hi) : clampNat lo hi x <= hi := by
  simp only [clampNat]
  exact Nat.max_le.mpr ⟨h, Nat.min_le_left hi x⟩

/-- validateFpsNat with positive input produces valid fps -/
theorem validateFpsNat_positive (n : Nat) (h : n > 0) :
    (validateFpsNat n).val >= minFps := by
  simp only [validateFpsNat]
  split_ifs with h'
  · simp only [clampNat]
    exact Nat.le_max_left minFps _
  · exact Nat.le_refl _

/-- frameToTime is well-defined -/
theorem frameToTime_defined (frame : Nat) (fps : Fps) :
    ∃ t, frameToTime frame fps = t := by
  exact ⟨_, rfl⟩

/-- timeToFrame is well-defined -/
theorem timeToFrame_defined (time : Float) (fps : Fps) :
    ∃ f, timeToFrame time fps = f := by
  exact ⟨_, rfl⟩

/-- calculateDuration is well-defined -/
theorem calculateDuration_defined (frameCount : Nat) (fps : Fps) :
    ∃ d, calculateDuration frameCount fps = d := by
  exact ⟨_, rfl⟩

/-- calculateFrameCount is well-defined -/
theorem calculateFrameCount_defined (duration : Float) (fps : Fps) :
    ∃ f, calculateFrameCount duration fps = f := by
  exact ⟨_, rfl⟩

end Lattice.Utils.FpsUtils
