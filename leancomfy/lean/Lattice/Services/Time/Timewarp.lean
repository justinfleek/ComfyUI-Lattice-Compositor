/-
  Lattice.Services.Time.Timewarp - Frame Blending for Timewarp

  Pure functions for timewarp frame interpolation:
  - Interpolation method selection
  - Blend factor calculations
  - Motion blur adjustment

  Source: ui/src/services/effects/timeRenderer.ts (lines 724-807)
-/

namespace Lattice.Services.Time.Timewarp

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Timewarp interpolation methods. -/
inductive TimewarpMethod
  | wholeFrames    -- Nearest frame, no interpolation
  | frameMix       -- Simple cross-fade between frames
  | pixelMotion    -- Optical flow-based interpolation
  deriving Repr, DecidableEq

/-- Parse timewarp method from string. -/
def parseTimewarpMethod (s : String) : TimewarpMethod :=
  match s with
  | "whole-frames" => TimewarpMethod.wholeFrames
  | "frame-mix" => TimewarpMethod.frameMix
  | "pixel-motion" => TimewarpMethod.pixelMotion
  | _ => TimewarpMethod.wholeFrames  -- Default

--------------------------------------------------------------------------------
-- Blend Calculations
--------------------------------------------------------------------------------

/-- Check if blend factor indicates exact frame (no interpolation needed). -/
def isExactFrame (blend : Float) : Bool :=
  blend == 0.0 || blend == 1.0

/-- Select nearest frame for whole-frames mode.
    Returns 1 if blend >= 0.5 (use frame2), 0 otherwise (use frame1). -/
def selectNearestFrame (blend : Float) : Nat :=
  if blend < 0.5 then 0 else 1

--------------------------------------------------------------------------------
-- Frame Mix (Cross-fade)
--------------------------------------------------------------------------------

/-- Mix single pixel channel between two frames.
    result = src1 * (1 - blend) + src2 * blend -/
def frameMixPixel (src1 src2 blend : Float) : Float :=
  src1 * (1.0 - blend) + src2 * blend

--------------------------------------------------------------------------------
-- Motion Blur Adjustment
--------------------------------------------------------------------------------

/-- Default motion blur amount. -/
def defaultMotionBlur : Float := 0.5

/-- Calculate adjusted blend factor considering motion blur.
    Reduces blend near motion vector areas. -/
def calculateAdjustedBlend (blend motionBlurAmount mvX mvY : Float) : Float :=
  let magnitude := Float.sqrt (mvX * mvX + mvY * mvY)
  let blurFactor := Float.min 1.0 (motionBlurAmount * magnitude / 10.0)
  blend * (1.0 - blurFactor * 0.5)

end Lattice.Services.Time.Timewarp
