/-
  Lattice.Services.Time.FrameBlending - Frame Interpolation Math

  Pure mathematical functions for time-based frame blending:
  - Whole-frame selection (nearest)
  - Frame mix (cross-fade)
  - Echo intensity decay

  Source: ui/src/services/effects/timeRenderer.ts (lines 746-808, 313-316)
-/

namespace Lattice.Services.Time.FrameBlending

--------------------------------------------------------------------------------
-- Timewarp Methods
--------------------------------------------------------------------------------

/-- Timewarp interpolation method. -/
inductive TimewarpMethod
  | wholeFrames  -- Nearest frame, no interpolation
  | frameMix     -- Cross-fade between frames
  | pixelMotion  -- Optical flow-based
  deriving Repr, DecidableEq

--------------------------------------------------------------------------------
-- Whole Frame Selection
--------------------------------------------------------------------------------

/-- Select which frame to use based on blend factor.
    Returns true if frame1 should be used, false for frame2. -/
def selectWholeFrame (blendFactor : Float) : Bool :=
  blendFactor < 0.5

--------------------------------------------------------------------------------
-- Frame Mix (Cross-fade)
--------------------------------------------------------------------------------

/-- Calculate blended pixel value using linear interpolation.
    frame1Value * (1 - blend) + frame2Value * blend -/
def mixPixelValue (frame1Value frame2Value blend : Float) : Float :=
  frame1Value * (1.0 - blend) + frame2Value * blend

/-- Blend RGBA pixel values.
    Returns (r, g, b, a) blended result. -/
def mixPixelRGBA (r1 g1 b1 a1 r2 g2 b2 a2 blend : Float) : Float × Float × Float × Float :=
  ( mixPixelValue r1 r2 blend
  , mixPixelValue g1 g2 blend
  , mixPixelValue b1 b2 blend
  , mixPixelValue a1 a2 blend
  )

--------------------------------------------------------------------------------
-- Echo Intensity Decay
--------------------------------------------------------------------------------

/-- Calculate echo intensity at a given echo index.
    Uses exponential decay: startingIntensity * (1 - decay)^echoIndex -/
def echoIntensity (startingIntensity decay : Float) (echoIndex : Nat) : Float :=
  startingIntensity * Float.pow (1.0 - decay) echoIndex.toFloat

/-- Check if echo intensity is significant enough to render.
    Returns true if intensity > 0.001 -/
def isSignificantEcho (intensity : Float) : Bool :=
  intensity > 0.001

--------------------------------------------------------------------------------
-- Posterize Time
--------------------------------------------------------------------------------

/-- Calculate the posterized frame number.
    Quantizes time to target frame rate. -/
def posterizedFrame (currentFrame : Nat) (sourceFps targetFps : Float) : Nat :=
  if targetFps <= 0.0 || sourceFps <= 0.0 then currentFrame
  else
    let frameRatio := sourceFps / targetFps
    let quantized := Float.floor (currentFrame.toFloat / frameRatio) * frameRatio
    quantized.toUInt32.toNat

/-- Check if current frame is a "new" posterized frame.
    Returns true if frame is close to its posterized value. -/
def isNewPosterizedFrame (currentFrame : Nat) (sourceFps targetFps : Float) : Bool :=
  let posterized := posterizedFrame currentFrame sourceFps targetFps
  let diff := if currentFrame >= posterized
              then currentFrame - posterized
              else posterized - currentFrame
  diff.toFloat < 0.5

--------------------------------------------------------------------------------
-- Motion Blur Adjustment
--------------------------------------------------------------------------------

/-- Calculate motion blur factor from motion vector magnitude.
    motionBlurAmount: base blur amount (0-1)
    motionMagnitude: length of motion vector -/
def motionBlurFactor (motionBlurAmount motionMagnitude : Float) : Float :=
  let raw := motionBlurAmount * motionMagnitude / 10.0
  if raw > 1.0 then 1.0 else raw

/-- Adjust blend factor for motion blur.
    Reduces blend when there's significant motion. -/
def adjustedBlendForMotion (blend blurFactor : Float) : Float :=
  blend * (1.0 - blurFactor * 0.5)

--------------------------------------------------------------------------------
-- Frame Blending Decision
--------------------------------------------------------------------------------

/-- Determine if blending is needed based on blend factor.
    Returns None if exact frame (0 or 1), Some blend otherwise. -/
def needsBlending (blendFactor : Float) : Option Float :=
  if blendFactor == 0.0 || blendFactor == 1.0 then
    none
  else
    some blendFactor

end Lattice.Services.Time.FrameBlending
