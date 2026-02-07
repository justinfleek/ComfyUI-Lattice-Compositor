/-
  Lattice.Schemas.Exports.SCAILSchema

  SCAIL (Pose-Driven Video) export format types.
  SCAIL uses reference image (identity/appearance) + pose video/sequence for motion guidance.

  Source: ui/src/schemas/exports/scail-schema.ts
-/

namespace Lattice.Schemas.Exports.SCAILSchema

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_DIMENSION : Nat := 16384
def MAX_FRAMES : Nat := 100000
def MAX_FPS : Float := 120.0

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- SCAIL export configuration -/
structure SCAILExportConfig where
  referenceImage : String      -- Reference image filename (identity/appearance source)
  poseVideo : Option String := Option.none    -- Pose video filename or path
  poseDirectory : Option String := Option.none -- Directory of pose frame images
  width : Nat
  height : Nat
  frameCount : Nat
  fps : Float
  prompt : String
  negativePrompt : Option String := Option.none
  deriving Repr, Inhabited

/-- SCAIL export result -/
structure SCAILExportResult where
  referenceImage : String      -- Uploaded reference image filename
  poseInput : String           -- Uploaded pose video or image sequence
  poseWidth : Nat
  poseHeight : Nat
  generationWidth : Nat
  generationHeight : Nat
  frameCount : Nat
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

/-- Check if export config is valid -/
def SCAILExportConfig.isValid (c : SCAILExportConfig) : Bool :=
  c.width > 0 && c.width <= MAX_DIMENSION &&
  c.height > 0 && c.height <= MAX_DIMENSION &&
  c.frameCount > 0 && c.frameCount <= MAX_FRAMES &&
  c.fps > 0 && c.fps <= MAX_FPS

/-- Check if export result is valid -/
def SCAILExportResult.isValid (r : SCAILExportResult) : Bool :=
  r.poseWidth > 0 && r.poseWidth <= MAX_DIMENSION &&
  r.poseHeight > 0 && r.poseHeight <= MAX_DIMENSION &&
  r.generationWidth > 0 && r.generationWidth <= MAX_DIMENSION &&
  r.generationHeight > 0 && r.generationHeight <= MAX_DIMENSION &&
  r.frameCount > 0 && r.frameCount <= MAX_FRAMES

end Lattice.Schemas.Exports.SCAILSchema
