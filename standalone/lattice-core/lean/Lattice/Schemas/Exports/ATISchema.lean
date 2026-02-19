/-
  Lattice.Schemas.Exports.ATISchema

  ATI (Attention-based Temporal Interpolation) export format types and constants.
  ATI format uses exactly 121 frames with pixel coordinate trajectories.

  Source: ui/src/schemas/exports/ati-schema.ts
-/

namespace Lattice.Schemas.Exports.ATISchema

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- ATI format requires exactly 121 frames -/
def ATI_FIXED_FRAMES : Nat := 121

/-- Maximum supported resolution -/
def ATI_MAX_DIMENSION : Nat := 8192

/-- Minimum supported resolution -/
def ATI_MIN_DIMENSION : Nat := 1

/-- Maximum number of tracks -/
def MAX_TRACKS : Nat := 10000

/-- Maximum original frame count before resampling -/
def MAX_ORIGINAL_FRAMES : Nat := 100000

/-- Maximum FPS -/
def MAX_FPS : Float := 120.0

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- A single 2D point in pixel coordinates for ATI tracking -/
structure ATITrackPoint where
  x : Float
  y : Float
  deriving Repr, Inhabited, DecidableEq

/-- A single 2D point tuple -/
abbrev ATIPointTuple := Float × Float

/-- Result of an ATI export operation -/
structure ATIExportResult where
  /-- JSON-serialized track data -/
  tracks : String
  /-- Width of the composition in pixels -/
  width : Nat
  /-- Height of the composition in pixels -/
  height : Nat
  /-- Number of tracks exported -/
  numTracks : Nat
  /-- Original frame count before resampling to 121 -/
  originalFrames : Nat
  deriving Repr, Inhabited

/-- Configuration options for ATI export -/
structure ATIExportConfig where
  /-- Composition ID to export -/
  compositionId : String
  /-- Whether to include visibility data -/
  includeVisibility : Bool := true
  /-- Frame range start (will be resampled to 121 frames) -/
  startFrame : Option Nat := Option.none
  /-- Frame range end (will be resampled to 121 frames) -/
  endFrame : Option Nat := Option.none
  deriving Repr, Inhabited

/-- ATI metadata -/
structure ATIMetadata where
  version : String
  width : Nat
  height : Nat
  fps : Float
  frameCount : Nat
  numTracks : Nat
  exportedAt : Option String := Option.none
  deriving Repr, Inhabited

/-- Full ATI data structure for import/export operations -/
structure ATIData where
  /-- Track coordinate data: array of tracks, each with 121 frames of (x, y) points -/
  tracks : Array (Array ATIPointTuple)
  /-- Optional visibility data -/
  visibility : Option (Array (Array Bool)) := Option.none
  /-- Metadata -/
  metadata : ATIMetadata
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Validation Helpers
--------------------------------------------------------------------------------

/-- Check if export result dimensions are valid -/
def ATIExportResult.isValid (r : ATIExportResult) : Bool :=
  r.width >= ATI_MIN_DIMENSION && r.width <= ATI_MAX_DIMENSION &&
  r.height >= ATI_MIN_DIMENSION && r.height <= ATI_MAX_DIMENSION &&
  r.numTracks <= MAX_TRACKS &&
  r.originalFrames <= MAX_ORIGINAL_FRAMES

/-- Check if config has valid frame range -/
def ATIExportConfig.isValid (c : ATIExportConfig) : Bool :=
  match c.startFrame, c.endFrame with
  | some start, some end_ => end_ >= start && end_ <= MAX_ORIGINAL_FRAMES
  | some start, none => start <= MAX_ORIGINAL_FRAMES
  | none, some end_ => end_ <= MAX_ORIGINAL_FRAMES
  | none, none => true

/-- Check if metadata is valid -/
def ATIMetadata.isValid (m : ATIMetadata) : Bool :=
  m.width >= ATI_MIN_DIMENSION && m.width <= ATI_MAX_DIMENSION &&
  m.height >= ATI_MIN_DIMENSION && m.height <= ATI_MAX_DIMENSION &&
  m.fps > 0 && m.fps <= MAX_FPS &&
  m.frameCount == ATI_FIXED_FRAMES &&
  m.numTracks <= MAX_TRACKS

/-- Check if ATI data is valid -/
def ATIData.isValid (d : ATIData) : Bool :=
  d.metadata.isValid &&
  d.tracks.size == d.metadata.numTracks &&
  d.tracks.all (fun track => track.size == ATI_FIXED_FRAMES) &&
  match d.visibility with
  | some vis =>
      vis.size == d.tracks.size &&
      vis.all (fun v => v.size == ATI_FIXED_FRAMES)
  | none => true

end Lattice.Schemas.Exports.ATISchema
