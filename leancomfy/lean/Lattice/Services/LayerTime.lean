/-
  Lattice.Services.LayerTime - Layer time calculations

  Pure functions for time remapping:
  - Time stretch (percentage-based speed)
  - Reversed playback (negative stretch)
  - Loop and ping-pong modes
  - Source time from composition time

  Source: ui/src/services/layerTime.ts
-/

namespace Lattice.Services.LayerTime

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Result of source time calculation -/
structure SourceTimeResult where
  /-- Source time in seconds -/
  sourceTime : Float
  /-- Source frame number -/
  sourceFrame : Nat
  /-- Effective playback speed (1 = normal, 0.5 = half, -1 = reversed) -/
  effectiveSpeed : Float
  /-- Whether playback is reversed -/
  isReversed : Bool
  /-- Whether source time was clamped/looped -/
  wasAdjusted : Bool
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- Normal time stretch (100%) -/
def normalStretch : Float := 100.0

/-- Default FPS -/
def defaultFps : Float := 30.0

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

/-- Ensure time stretch is valid -/
def safeTimeStretch (stretch : Float) : Float :=
  if stretch.isFinite then stretch else normalStretch

/-- Ensure FPS is valid -/
def safeFps (fps : Float) : Float :=
  if fps.isFinite && fps > 0 then fps else defaultFps

/-- Safe modulo for floats -/
def safeMod (a b : Float) : Float :=
  if b == 0 then a
  else a - b * Float.floor (a / b)

--------------------------------------------------------------------------------
-- Core Functions
--------------------------------------------------------------------------------

/-- Calculate effective speed from time stretch percentage.
    100% = 1x speed, 200% = 0.5x speed (slower), 50% = 2x speed (faster)
    Formula: effectiveSpeed = 100 / timeStretch -/
def effectiveSpeedFromStretch (timeStretch : Float) : Float :=
  let safe := safeTimeStretch timeStretch
  if safe == 0 then 0 else normalStretch / safe

/-- Check if time stretch indicates reversed playback -/
def isStretchReversed (timeStretch : Float) : Bool :=
  safeTimeStretch timeStretch < 0

/-- Reverse a time stretch value (toggle playback direction) -/
def reverseStretch (timeStretch : Float) : Float :=
  -(safeTimeStretch timeStretch)

/-- Calculate stretched duration from source duration and time stretch.
    100% stretch = same duration, 200% = 2x duration, 50% = 0.5x duration -/
def getStretchedDuration (sourceDuration : Float) (timeStretch : Float) : Float :=
  let safe := safeTimeStretch timeStretch
  if safe == 0 then sourceDuration
  else (sourceDuration * Float.abs safe) / normalStretch

/-- Calculate original source duration from stretched duration -/
def getSourceDuration (stretchedDuration : Float) (timeStretch : Float) : Float :=
  let safe := safeTimeStretch timeStretch
  if safe == 0 then stretchedDuration
  else (stretchedDuration * normalStretch) / Float.abs safe

--------------------------------------------------------------------------------
-- Loop/Clamp Functions
--------------------------------------------------------------------------------

/-- Apply simple loop to source frame -/
def loopFrame (sourceFrame : Float) (sourceDuration : Float) : Float × Bool :=
  if sourceDuration <= 0 then (sourceFrame, false)
  else
    let adjusted := safeMod (safeMod sourceFrame sourceDuration + sourceDuration) sourceDuration
    (adjusted, adjusted != sourceFrame)

/-- Apply ping-pong loop to source frame -/
def pingPongFrame (sourceFrame : Float) (sourceDuration : Float) : Float × Bool :=
  if sourceDuration <= 0 then (sourceFrame, false)
  else
    let cycles := Float.floor (sourceFrame / sourceDuration)
    let phase := safeMod sourceFrame sourceDuration
    let adjusted :=
      if phase < 0 then sourceDuration + phase
      else if cycles.toUInt64.toNat % 2 == 1 then sourceDuration - 1 - phase
      else phase
    (adjusted, cycles != 0)

/-- Clamp source frame to valid range -/
def clampFrame (sourceFrame : Float) (sourceDuration : Float) : Float × Bool :=
  if sourceDuration <= 0 then (sourceFrame, false)
  else
    let adjusted := Float.max 0 (Float.min sourceFrame (sourceDuration - 1))
    (adjusted, adjusted != sourceFrame)

--------------------------------------------------------------------------------
-- Source Time Calculation
--------------------------------------------------------------------------------

/-- Options for source time calculation -/
structure SourceTimeOptions where
  /-- Composition frame rate -/
  fps : Float := defaultFps
  /-- Source duration in frames (for clamping/looping) -/
  sourceDuration : Option Float := none
  /-- Loop playback when source time exceeds duration -/
  loop : Bool := false
  /-- Ping-pong loop (reverse at end instead of restart) -/
  pingPong : Bool := false
  deriving Repr, Inhabited

/-- Calculate source time from composition frame (simplified version).

    compFrame: Current composition frame (0-based)
    layerStartFrame: Frame where layer starts in composition
    timeStretch: Time stretch percentage (100 = normal, negative = reversed)
    options: Additional options for looping/clamping -/
def getSourceTime (compFrame : Float) (layerStartFrame : Float) (timeStretch : Float)
    (options : SourceTimeOptions := {}) : SourceTimeResult :=
  let fps := safeFps options.fps
  let stretch := safeTimeStretch timeStretch
  let effectiveSpeed := effectiveSpeedFromStretch stretch
  let isReversed := stretch < 0
  let absSpeed := Float.abs effectiveSpeed

  -- Calculate time relative to layer start
  let layerFrame := compFrame - layerStartFrame

  -- Apply time stretch to get source frame
  let sourceFrameBase := layerFrame * absSpeed

  -- Handle reversed playback
  let sourceFrameReversed := match options.sourceDuration with
    | some dur =>
      if isReversed then dur - 1 - sourceFrameBase
      else sourceFrameBase
    | none => sourceFrameBase

  -- Handle looping/clamping
  let (sourceFrame, wasAdjusted) := match options.sourceDuration with
    | some dur =>
      if dur > 0 then
        if options.loop then
          if options.pingPong then pingPongFrame sourceFrameReversed dur
          else loopFrame sourceFrameReversed dur
        else clampFrame sourceFrameReversed dur
      else (sourceFrameReversed, false)
    | none => (sourceFrameReversed, false)

  -- Ensure non-negative
  let finalFrame := Float.max 0 sourceFrame

  {
    sourceTime := finalFrame / fps
    sourceFrame := finalFrame.toUInt64.toNat
    effectiveSpeed := effectiveSpeed
    isReversed := isReversed
    wasAdjusted := wasAdjusted
  }

/-- Check if layer is visible at a given composition frame -/
def isLayerVisibleAtFrame (compFrame : Float) (startFrame endFrame : Float) : Bool :=
  compFrame >= startFrame && compFrame <= endFrame

/-- Get just the source frame number (convenience function) -/
def getSourceFrame (compFrame : Float) (layerStartFrame : Float) (timeStretch : Float)
    (fps : Float) (sourceDuration : Option Float := none) : Nat :=
  let result := getSourceTime compFrame layerStartFrame timeStretch
    { fps := fps, sourceDuration := sourceDuration }
  result.sourceFrame

--------------------------------------------------------------------------------
-- Stretch Anchor Calculations
--------------------------------------------------------------------------------

/-- Calculate new endpoints after time stretch, anchored at start -/
def stretchFromStart (startFrame : Float) (currentDuration : Float)
    (currentStretch newStretch : Float) : Float × Float :=
  let sourceDuration := getSourceDuration currentDuration currentStretch
  let newDuration := getStretchedDuration sourceDuration newStretch
  (startFrame, startFrame + newDuration)

/-- Calculate new endpoints after time stretch, anchored at end -/
def stretchFromEnd (endFrame : Float) (currentDuration : Float)
    (currentStretch newStretch : Float) : Float × Float :=
  let sourceDuration := getSourceDuration currentDuration currentStretch
  let newDuration := getStretchedDuration sourceDuration newStretch
  (endFrame - newDuration, endFrame)

/-- Calculate new endpoints after time stretch, anchored at center -/
def stretchFromCenter (startFrame endFrame : Float) (currentDuration : Float)
    (currentStretch newStretch : Float) : Float × Float :=
  let center := (startFrame + endFrame) / 2
  let sourceDuration := getSourceDuration currentDuration currentStretch
  let newDuration := getStretchedDuration sourceDuration newStretch
  let newStart := Float.floor (center - newDuration / 2)
  (newStart, newStart + newDuration)

/-- Calculate new endpoints after time stretch, anchored at specific frame -/
def stretchFromFrame (startFrame : Float) (currentDuration : Float)
    (currentStretch newStretch : Float) (anchorFrame : Float) : Float × Float :=
  let sourceDuration := getSourceDuration currentDuration currentStretch
  let newDuration := getStretchedDuration sourceDuration newStretch
  let ratio := if currentDuration == 0 then 0 else (anchorFrame - startFrame) / currentDuration
  let newStart := Float.floor (anchorFrame - ratio * newDuration)
  (newStart, newStart + newDuration)

end Lattice.Services.LayerTime
