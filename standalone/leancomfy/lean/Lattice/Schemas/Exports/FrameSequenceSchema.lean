/-
  Lattice.Schemas.Exports.FrameSequenceSchema

  Frame sequence export format enums and types.

  Source: ui/src/schemas/exports/framesequence-schema.ts
-/

namespace Lattice.Schemas.Exports.FrameSequenceSchema

--------------------------------------------------------------------------------
-- Frame Format
--------------------------------------------------------------------------------

/-- Frame export format options -/
inductive FrameFormat where
  | png      -- Lossless, 8-bit RGBA
  | jpeg     -- Lossy, 8-bit RGB
  | webp     -- Modern, supports lossless
  | tiff     -- Via backend - 8/16-bit
  | exr      -- Via backend - HDR 32-bit float
  | dpx      -- Via backend - 10/16-bit film format
  deriving Repr, DecidableEq, Inhabited

def frameFormatFromString : String → Option FrameFormat
  | "png" => some .png
  | "jpeg" => some .jpeg
  | "webp" => some .webp
  | "tiff" => some .tiff
  | "exr" => some .exr
  | "dpx" => some .dpx
  | _ => Option.none

def frameFormatToString : FrameFormat → String
  | .png => "png"
  | .jpeg => "jpeg"
  | .webp => "webp"
  | .tiff => "tiff"
  | .exr => "exr"
  | .dpx => "dpx"

--------------------------------------------------------------------------------
-- Color Space
--------------------------------------------------------------------------------

/-- Color space options -/
inductive ColorSpace where
  | sRGB
  | linear
  | ACEScg
  | Rec709
  deriving Repr, DecidableEq, Inhabited

def colorSpaceFromString : String → Option ColorSpace
  | "sRGB" => some .sRGB
  | "Linear" => some .linear
  | "ACEScg" => some .ACEScg
  | "Rec709" => some .Rec709
  | _ => Option.none

def colorSpaceToString : ColorSpace → String
  | .sRGB => "sRGB"
  | .linear => "Linear"
  | .ACEScg => "ACEScg"
  | .Rec709 => "Rec709"

--------------------------------------------------------------------------------
-- Bit Depth
--------------------------------------------------------------------------------

/-- Bit depth options -/
inductive BitDepth where
  | bits8
  | bits10
  | bits16
  | bits32
  deriving Repr, DecidableEq, Inhabited

def bitDepthFromNat : Nat → Option BitDepth
  | 8 => some .bits8
  | 10 => some .bits10
  | 16 => some .bits16
  | 32 => some .bits32
  | _ => Option.none

def bitDepthToNat : BitDepth → Nat
  | .bits8 => 8
  | .bits10 => 10
  | .bits16 => 16
  | .bits32 => 32

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_FRAMES : Nat := 100000
def MAX_DIMENSION : Nat := 16384
def MAX_FPS : Float := 120.0
def MAX_QUALITY : Nat := 100
def MAX_FILE_SIZE : Nat := 2147483647  -- 2GB

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- Frame export options -/
structure FrameExportOptions where
  format : FrameFormat
  quality : Nat  -- 0-100 for lossy formats
  filenamePattern : String  -- e.g., "frame_{frame:04d}"
  outputDir : String
  startFrame : Nat
  endFrame : Nat
  bitDepth : Option BitDepth := Option.none
  colorSpace : Option ColorSpace := Option.none
  deriving Repr, Inhabited

/-- Exported frame info -/
structure ExportedFrame where
  frameNumber : Nat
  filename : String
  size : Nat
  deriving Repr, Inhabited

/-- Frame sequence export result -/
structure FrameSequenceResult where
  success : Bool
  frames : Array ExportedFrame
  totalSize : Nat
  errors : Array String
  warnings : Array String
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

/-- Check if export options are valid -/
def FrameExportOptions.isValid (o : FrameExportOptions) : Bool :=
  o.quality <= MAX_QUALITY &&
  o.startFrame <= MAX_FRAMES &&
  o.endFrame <= MAX_FRAMES &&
  o.endFrame >= o.startFrame

/-- Check if exported frame is valid -/
def ExportedFrame.isValid (f : ExportedFrame) : Bool :=
  f.frameNumber <= MAX_FRAMES &&
  f.size <= MAX_FILE_SIZE

end Lattice.Schemas.Exports.FrameSequenceSchema
