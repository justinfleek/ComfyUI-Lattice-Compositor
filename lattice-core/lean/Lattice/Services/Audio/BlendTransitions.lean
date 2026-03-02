/-
  Lattice.Services.Audio.BlendTransitions - IPAdapter Blend Transitions

  Pure mathematical functions for blending between values/images:
  - Step blend (hard cut)
  - Linear blend (crossfade)
  - Smooth blend (smoothstep crossfade)

  Used for IPAdapter weight scheduling and general audio-reactive transitions.

  Source: ui/src/services/audioReactiveMapping.ts (createIPAdapterSchedule)
-/

namespace Lattice.Services.Audio.BlendTransitions

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Blend mode for transitions -/
inductive BlendMode where
  | step     -- Hard cut at 50%
  | linear   -- Linear crossfade
  | smooth   -- Smoothstep crossfade
  deriving Repr, DecidableEq, Inhabited

--------------------------------------------------------------------------------
-- Core Blend Functions
--------------------------------------------------------------------------------

/-- Step blend: hard cut at 50%.

    progress < 0.5: returns 0
    progress >= 0.5: returns 1

    Use for instant transitions on beat. -/
def stepBlend (progress : Float) : Float :=
  if progress >= 0.5 then 1.0 else 0.0

/-- Linear blend: direct crossfade.

    Returns progress clamped to [0, 1].

    Use for smooth, constant-rate transitions. -/
def linearBlend (progress : Float) : Float :=
  Float.max 0.0 (Float.min 1.0 progress)

/-- Smooth blend: smoothstep crossfade.

    Uses 3t² - 2t³ curve for natural-feeling transitions
    with smooth acceleration and deceleration.

    Use for organic, pleasing transitions. -/
def smoothBlend (progress : Float) : Float :=
  let t := Float.max 0.0 (Float.min 1.0 progress)
  t * t * (3.0 - 2.0 * t)

/-- Apply blend mode to get blend factor.

    progress: Transition progress [0, 1]
    mode: Blend algorithm to use

    Returns: Blend factor [0, 1] for mixing -/
def applyBlendMode (progress : Float) (mode : BlendMode) : Float :=
  match mode with
  | .step => stepBlend progress
  | .linear => linearBlend progress
  | .smooth => smoothBlend progress

--------------------------------------------------------------------------------
-- Weight Calculation
--------------------------------------------------------------------------------

/-- Calculate weights for two-image transition.

    blend: Blend factor from applyBlendMode [0, 1]
    minWeight: Minimum weight floor (for IPAdapter stability)

    Returns: (currentWeight, nextWeight) -/
def twoImageWeights (blend : Float) (minWeight : Float) : Float × Float :=
  let current := Float.max minWeight (1.0 - blend)
  let next := Float.max minWeight blend
  (current, next)

/-- Calculate blend factor for N-image cycling.

    imageCount: Total number of images in cycle
    progress: Overall progress through all images [0, N]

    Returns: (currentIndex, nextIndex, blendFactor) -/
def cycleBlendIndices (imageCount : Nat) (progress : Float) : Nat × Nat × Float :=
  if imageCount == 0 then (0, 0, 0.0)
  else
    let current := (Float.floor progress).toUInt64.toNat % imageCount
    let next := (current + 1) % imageCount
    let blend := progress - Float.floor progress
    (current, next, blend)

--------------------------------------------------------------------------------
-- Transition Progress
--------------------------------------------------------------------------------

/-- Calculate transition progress.

    currentFrame: Current frame number
    transitionStartFrame: Frame when transition started
    transitionLength: Total transition length in frames

    Returns: Progress [0, 1] clamped -/
def transitionProgress (currentFrame : Nat) (transitionStartFrame : Nat)
    (transitionLength : Nat) : Float :=
  if transitionLength == 0 then 1.0  -- Instant transition
  else
    let elapsed := currentFrame - transitionStartFrame
    let progress := elapsed.toFloat / transitionLength.toFloat
    Float.max 0.0 (Float.min 1.0 progress)

/-- Check if transition is complete.

    progress: Current transition progress
    Returns: true if progress >= 1.0 -/
def isTransitionComplete (progress : Float) : Bool :=
  progress >= 1.0

--------------------------------------------------------------------------------
-- Full Transition Calculation
--------------------------------------------------------------------------------

/-- Calculate IPAdapter-style weights for frame.

    currentFrame: Current frame number
    transitionStartFrame: Frame when transition started
    transitionLength: Duration in frames
    currentIndex: Current image index
    imageCount: Total images
    blendMode: Transition blend mode
    minWeight: Minimum weight floor

    Returns: (weights array as function, newCurrentIndex, isComplete) -/
def calculateIPAdapterWeights (currentFrame : Nat) (transitionStartFrame : Nat)
    (transitionLength : Nat) (currentIndex : Nat) (imageCount : Nat)
    (blendMode : BlendMode) (minWeight : Float) : (Nat → Float) × Nat × Bool :=
  if imageCount == 0 then
    (fun _ => 0.0, 0, true)
  else
    let progress := transitionProgress currentFrame transitionStartFrame transitionLength
    let complete := isTransitionComplete progress
    let blend := applyBlendMode progress blendMode
    let nextIndex := (currentIndex + 1) % imageCount
    let (currentWeight, nextWeight) := twoImageWeights blend minWeight

    let weights := fun i =>
      if i == currentIndex then currentWeight
      else if i == nextIndex then nextWeight
      else minWeight

    let newIndex := if complete then nextIndex else currentIndex
    (weights, newIndex, complete)

end Lattice.Services.Audio.BlendTransitions
