/-
  Lattice.Services.Time.FrameBuffer - Temporal Frame Storage

  Frame buffer management for time-based effects:
  - Ring buffer of previous frames
  - Frame-based (deterministic) timestamps
  - Echo frame retrieval
  - Buffer statistics

  Source: ui/src/services/effects/timeRenderer.ts (lines 23-182)
-/

namespace Lattice.Services.Time.FrameBuffer

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Frame buffer entry - stores frame image data with metadata. -/
structure FrameBufferEntry (α : Type) where
  imageData : α        -- Generic to support different image formats
  frame : Nat          -- Frame number
  storedAtFrame : Nat  -- Frame-based timestamp for deterministic cleanup
  deriving Repr

/-- Buffer statistics. -/
structure FrameBufferStats where
  frameCount : Nat
  oldestFrame : Int
  newestFrame : Int
  deriving Repr

/-- Echo frame result with echo index. -/
structure EchoFrameResult (α : Type) where
  imageData : α
  frame : Nat
  echoIndex : Nat
  deriving Repr

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- Maximum number of frames to store in buffer. -/
def maxBufferFrames : Nat := 64

/-- Maximum frame distance for cleanup. -/
def defaultMaxFrameDistance : Nat := maxBufferFrames * 2

--------------------------------------------------------------------------------
-- Buffer Operations (pure)
--------------------------------------------------------------------------------

/-- Check if buffer needs trimming. -/
def shouldTrimBuffer (bufferLength : Nat) : Bool :=
  bufferLength > maxBufferFrames

/-- Check if a frame is within acceptable range of current frame. -/
def isFrameInRange (frameNum currentFrame maxDistance : Nat) : Bool :=
  let diff := if frameNum > currentFrame
              then frameNum - currentFrame
              else currentFrame - frameNum
  diff < maxDistance

/-- Check frame distance is within range (for cleanup). -/
def frameDistanceInRange (storedAtFrame currentFrame : Nat) : Bool :=
  isFrameInRange storedAtFrame currentFrame defaultMaxFrameDistance

/-- Calculate absolute distance between two frame numbers. -/
def frameDist (a b : Nat) : Nat :=
  if a > b then a - b else b - a

/-- Find the closest frame to target in a list of entries.
    Returns index of closest entry. -/
def findClosestFrameIndex {α : Type} (entries : Array (FrameBufferEntry α))
                          (targetFrame : Nat) : Option Nat :=
  if entries.size == 0 then none
  else
    let indexed := entries.mapIdx fun idx entry => (idx, frameDist entry.frame targetFrame)
    let sorted := indexed.qsort (fun a b => a.2 < b.2)
    match sorted[0]? with
    | some (idx, _) => some idx
    | none => none

/-- Calculate target frames for echo effect.
    Returns array of (targetFrame, echoIndex) pairs. -/
def calculateEchoTargetFrames (currentFrame : Nat) (echoTimeFrames : Float)
                               (numEchoes : Nat) : Array (Nat × Nat) :=
  let indices := Array.range numEchoes |>.map (· + 1)
  indices.map fun i =>
    let target := (currentFrame.toFloat + echoTimeFrames * i.toFloat).toUInt32.toNat
    (target, i)

/-- Calculate echo intensity using exponential decay.
    intensity = startingIntensity * (1 - decay)^echoIndex -/
def calculateEchoIntensity (startingIntensity decay : Float) (echoIndex : Nat) : Float :=
  let base := 1.0 - decay
  let power := base ^ echoIndex.toFloat
  startingIntensity * power

--------------------------------------------------------------------------------
-- Statistics
--------------------------------------------------------------------------------

/-- Calculate buffer statistics from entries. -/
def calculateBufferStats {α : Type} (entries : Array (FrameBufferEntry α))
                         : FrameBufferStats :=
  if entries.size == 0 then emptyBufferStats
  else
    let frames := entries.map (·.frame)
    let minFrame := frames.foldl min frames[0]!
    let maxFrame := frames.foldl max frames[0]!
    { frameCount := entries.size
    , oldestFrame := minFrame.toInt
    , newestFrame := maxFrame.toInt
    }

/-- Empty buffer statistics. -/
def emptyBufferStats : FrameBufferStats :=
  { frameCount := 0
  , oldestFrame := -1
  , newestFrame := -1
  }

end Lattice.Services.Time.FrameBuffer
