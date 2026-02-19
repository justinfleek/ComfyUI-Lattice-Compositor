/-
  Lattice.Schemas.Exports.WorkflowParamsSchema

  WorkflowParams export format types.
  These define the EXACT property names that workflow templates expect.

  Source: ui/src/schemas/exports/workflow-params-schema.ts
-/

namespace Lattice.Schemas.Exports.WorkflowParamsSchema

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_TRACKS : Nat := 10000
def MAX_POINTS_PER_TRACK : Nat := 100000
def ATI_FIXED_FRAMES : Nat := 121
def MAX_COORDINATE : Float := 16384.0

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- Track point format used by WanMove and ATI exports -/
structure TrackPoint where
  x : Float
  y : Float
  deriving Repr, Inhabited, DecidableEq

/-- WanMove motionData structure -/
structure WanMoveMotionData where
  tracks : Array (Array TrackPoint)
  deriving Repr, Inhabited

/-- ATI motionData structure -/
structure ATIMotionData where
  trajectories : Array (Array TrackPoint)
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

/-- Check if track point is valid -/
def TrackPoint.isValid (p : TrackPoint) : Bool :=
  p.x >= 0 && p.x <= MAX_COORDINATE &&
  p.y >= 0 && p.y <= MAX_COORDINATE

/-- Check if WanMove motion data is valid -/
def WanMoveMotionData.isValid (d : WanMoveMotionData) : Bool :=
  d.tracks.size <= MAX_TRACKS &&
  d.tracks.all (fun track => track.size <= MAX_POINTS_PER_TRACK)

/-- Check if ATI motion data is valid -/
def ATIMotionData.isValid (d : ATIMotionData) : Bool :=
  d.trajectories.size <= MAX_TRACKS &&
  d.trajectories.all (fun traj => traj.size == ATI_FIXED_FRAMES)

end Lattice.Schemas.Exports.WorkflowParamsSchema
