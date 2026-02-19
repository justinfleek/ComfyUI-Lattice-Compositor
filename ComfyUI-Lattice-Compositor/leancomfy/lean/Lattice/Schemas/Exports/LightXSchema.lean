/-
  Lattice.Schemas.Exports.LightXSchema

  Light-X export format enums and types.

  Source: ui/src/schemas/exports/lightx-schema.ts
-/

namespace Lattice.Schemas.Exports.LightXSchema

--------------------------------------------------------------------------------
-- Light-X Motion Style
--------------------------------------------------------------------------------

/-- Light-X motion style options -/
inductive LightXMotionStyle where
  | gradual
  | bullet
  | direct
  | dollyZoom
  deriving Repr, DecidableEq, Inhabited

def lightXMotionStyleFromString : String → Option LightXMotionStyle
  | "gradual" => some .gradual
  | "bullet" => some .bullet
  | "direct" => some .direct
  | "dolly-zoom" => some .dollyZoom
  | _ => Option.none

def lightXMotionStyleToString : LightXMotionStyle → String
  | .gradual => "gradual"
  | .bullet => "bullet"
  | .direct => "direct"
  | .dollyZoom => "dolly-zoom"

--------------------------------------------------------------------------------
-- Light-X Relight Source
--------------------------------------------------------------------------------

/-- Light-X relighting source options -/
inductive LightXRelightSource where
  | text
  | reference
  | hdr
  | background
  deriving Repr, DecidableEq, Inhabited

def lightXRelightSourceFromString : String → Option LightXRelightSource
  | "text" => some .text
  | "reference" => some .reference
  | "hdr" => some .hdr
  | "background" => some .background
  | _ => Option.none

def lightXRelightSourceToString : LightXRelightSource → String
  | .text => "text"
  | .reference => "reference"
  | .hdr => "hdr"
  | .background => "background"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_FRAMES : Nat := 100000
def MAX_FPS : Float := 120.0
def MAX_FOV : Float := 180.0
def MAX_CLIP : Float := 100000.0
def MAX_DIMENSION : Nat := 16384

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- Camera trajectory metadata -/
structure CameraTrajectoryMetadata where
  frameCount : Nat
  fps : Float
  fov : Float
  nearClip : Float
  farClip : Float
  width : Nat
  height : Nat
  deriving Repr, Inhabited

/-- Camera trajectory export with 4x4 matrices -/
structure CameraTrajectoryExport where
  /-- Array of 4x4 transformation matrices, one per frame -/
  matrices : Array (Array (Array Float))
  metadata : CameraTrajectoryMetadata
  deriving Repr, Inhabited

/-- Light-X relighting configuration -/
structure LightXRelightingConfig where
  source : LightXRelightSource
  textPrompt : Option String := Option.none
  referenceImage : Option String := Option.none  -- Base64
  hdrMap : Option String := Option.none          -- Base64 or path
  backgroundColor : Option String := Option.none -- Hex color
  deriving Repr, Inhabited

/-- Light-X export format -/
structure LightXExport where
  cameraTrajectory : CameraTrajectoryExport
  motionStyle : LightXMotionStyle
  relighting : LightXRelightingConfig
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

/-- Check if camera trajectory metadata is valid -/
def CameraTrajectoryMetadata.isValid (m : CameraTrajectoryMetadata) : Bool :=
  m.frameCount > 0 && m.frameCount <= MAX_FRAMES &&
  m.fps > 0 && m.fps <= MAX_FPS &&
  m.fov > 0 && m.fov <= MAX_FOV &&
  m.nearClip > 0 && m.nearClip <= MAX_CLIP &&
  m.farClip > m.nearClip && m.farClip <= MAX_CLIP &&
  m.width > 0 && m.width <= MAX_DIMENSION &&
  m.height > 0 && m.height <= MAX_DIMENSION

/-- Check if camera trajectory export is valid -/
def CameraTrajectoryExport.isValid (e : CameraTrajectoryExport) : Bool :=
  e.metadata.isValid &&
  e.matrices.size == e.metadata.frameCount &&
  e.matrices.all (fun mat => mat.size == 4 && mat.all (fun row => row.size == 4))

end Lattice.Schemas.Exports.LightXSchema
