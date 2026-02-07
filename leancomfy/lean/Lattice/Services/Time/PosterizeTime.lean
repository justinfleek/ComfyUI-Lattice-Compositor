/-
  Lattice.Services.Time.PosterizeTime - Frame Rate Reduction

  Pure functions for posterize time effect:
  - Target frame rate conversion
  - Posterized frame calculation
  - Frame holding logic

  Source: ui/src/services/effects/timeRenderer.ts (lines 390-449)
-/

namespace Lattice.Services.Time.PosterizeTime

--------------------------------------------------------------------------------
-- Parameter Validation
--------------------------------------------------------------------------------

/-- Default target frame rate for posterize effect. -/
def defaultTargetFps : Float := 12.0

/-- Validate and clamp target fps to [1, 60]. -/
def validateTargetFps (fps : Float) : Float :=
  Float.max 1.0 (Float.min 60.0 fps)

--------------------------------------------------------------------------------
-- Posterize Calculation
--------------------------------------------------------------------------------

/-- Calculate frame ratio: source fps / target fps. -/
def calculateFrameRatio (sourceFps targetFps : Float) : Float :=
  sourceFps / targetFps

/-- Calculate the "posterized" frame number.
    Rounds down to nearest posterized frame boundary. -/
def calculatePosterizedFrame (currentFrame : Nat) (frameRatio : Float) : Nat :=
  let current := currentFrame.toFloat
  let posterized := (current / frameRatio).floor * frameRatio
  posterized.toUInt32.toNat

/-- Threshold for determining if current frame is "close enough" to posterized. -/
def nearFrameThreshold : Float := 0.5

/-- Check if current frame should be used (vs held frame).
    Returns true if current frame is within threshold of posterized frame. -/
def shouldUseCurrent (currentFrame posterizedFrame : Nat) : Bool :=
  let diff := if currentFrame > posterizedFrame
              then currentFrame - posterizedFrame
              else posterizedFrame - currentFrame
  diff.toFloat < nearFrameThreshold

end Lattice.Services.Time.PosterizeTime
