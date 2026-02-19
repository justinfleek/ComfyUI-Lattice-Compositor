/-
  Lattice.Services.Depth.ExportSequence - Depth Export Sequence

  Pure functions for depth sequence export:
  - Frame sequence generation
  - Filename generation
  - Depth metadata structure
  - Export progress tracking

  Source: ui/src/services/export/depthRenderer.ts (lines 1006-1115)
-/

namespace Lattice.Services.Depth.ExportSequence

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Depth map format enumeration (mirrors FormatConversion). -/
inductive DepthMapFormat
  | raw
  | midas
  | depthAnything
  | zoeDepth
  | marigold
  | grayscale8
  | grayscale16
  deriving Repr, DecidableEq

/-- Export options for depth sequence. -/
structure DepthExportOptions where
  startFrame : Nat
  endFrame : Nat
  width : Nat
  height : Nat
  format : DepthMapFormat
  outputDir : String
  deriving Repr

/-- Depth metadata for export. -/
structure DepthMetadata where
  format : DepthMapFormat
  bitDepth : Nat
  nearClip : Float
  farClip : Float
  inverted : Bool
  normalized : Bool
  frameCount : Nat
  width : Nat
  height : Nat
  actualRangeMin : Float
  actualRangeMax : Float
  generatedAt : String  -- ISO 8601 timestamp
  generator : String
  deriving Repr

/-- Export progress event. -/
structure ExportProgress where
  currentFrame : Nat
  totalFrames : Nat
  deriving Repr

/-- Frame export result. -/
structure FrameExportResult where
  frameIndex : Nat
  outputPath : String
  deriving Repr

--------------------------------------------------------------------------------
-- Frame Calculations
--------------------------------------------------------------------------------

/-- Calculate total frame count in sequence. -/
def totalFrames (startFrame endFrame : Nat) : Nat :=
  if endFrame >= startFrame then endFrame - startFrame + 1 else 0

/-- Calculate frame number from index. -/
def frameFromIndex (startFrame index : Nat) : Nat :=
  startFrame + index

/-- Generate frame indices for sequence. -/
def frameIndices (startFrame endFrame : Nat) : Array Nat :=
  let total := totalFrames startFrame endFrame
  Array.range total

--------------------------------------------------------------------------------
-- Filename Generation
--------------------------------------------------------------------------------

/-- Pad number with leading zeros. -/
def padNumber (n : Nat) (width : Nat) : String :=
  let s := toString n
  let padding := String.mk (List.replicate (width - s.length) '0')
  padding ++ s

/-- Generate depth frame filename.
    Format: depth_XXXXX.png (5-digit padding) -/
def depthFilename (frameIndex : Nat) : String :=
  s!"depth_{padNumber frameIndex 5}.png"

/-- Generate full output path for depth frame. -/
def depthOutputPath (outputDir : String) (frameIndex : Nat) : String :=
  s!"{outputDir}/depth/{depthFilename frameIndex}"

/-- Generate all output paths for sequence. -/
def allOutputPaths (options : DepthExportOptions) : Array String :=
  let total := totalFrames options.startFrame options.endFrame
  Array.range total |>.map fun i => depthOutputPath options.outputDir i

--------------------------------------------------------------------------------
-- Format Specification Lookup
--------------------------------------------------------------------------------

/-- Get bit depth for format. -/
def formatBitDepth (format : DepthMapFormat) : Nat :=
  match format with
  | DepthMapFormat.raw => 32
  | DepthMapFormat.grayscale8 => 8
  | _ => 16

/-- Get near clip for format. -/
def formatNearClip (format : DepthMapFormat) : Float :=
  match format with
  | DepthMapFormat.zoeDepth => 0.001
  | _ => 0.1

/-- Get far clip for format. -/
def formatFarClip (format : DepthMapFormat) : Float :=
  match format with
  | DepthMapFormat.zoeDepth => 80.0
  | _ => 100.0

/-- Check if format uses normalization. -/
def formatNormalized (format : DepthMapFormat) : Bool :=
  match format with
  | DepthMapFormat.raw => false
  | DepthMapFormat.zoeDepth => false
  | _ => true

/-- Check if format uses inversion. -/
def formatInverted (format : DepthMapFormat) : Bool :=
  match format with
  | DepthMapFormat.midas => true
  | DepthMapFormat.depthAnything => true
  | _ => false

--------------------------------------------------------------------------------
-- Metadata Generation
--------------------------------------------------------------------------------

/-- Generator name constant. -/
def generatorName : String := "Lattice Compositor"

/-- Create depth metadata from export results. -/
def createDepthMetadata (format : DepthMapFormat)
                        (frameCount width height : Nat)
                        (minDepth maxDepth : Float)
                        (timestamp : String) : DepthMetadata :=
  { format := format
  , bitDepth := formatBitDepth format
  , nearClip := formatNearClip format
  , farClip := formatFarClip format
  , inverted := formatInverted format
  , normalized := formatNormalized format
  , frameCount := frameCount
  , width := width
  , height := height
  , actualRangeMin := minDepth
  , actualRangeMax := maxDepth
  , generatedAt := timestamp
  , generator := generatorName
  }

/-- Calculate metadata from export options. -/
def metadataFromOptions (options : DepthExportOptions)
                        (minDepth maxDepth : Float)
                        (timestamp : String) : DepthMetadata :=
  createDepthMetadata
    options.format
    (totalFrames options.startFrame options.endFrame)
    options.width
    options.height
    minDepth
    maxDepth
    timestamp

--------------------------------------------------------------------------------
-- Progress Tracking
--------------------------------------------------------------------------------

/-- Create progress event. -/
def createProgress (currentFrame totalFrames : Nat) : ExportProgress :=
  { currentFrame := currentFrame, totalFrames := totalFrames }

/-- Calculate progress percentage. -/
def progressPercent (progress : ExportProgress) : Float :=
  if progress.totalFrames == 0 then 100.0
  else (progress.currentFrame.toFloat / progress.totalFrames.toFloat) * 100.0

/-- Check if export is complete. -/
def isComplete (progress : ExportProgress) : Bool :=
  progress.currentFrame >= progress.totalFrames

--------------------------------------------------------------------------------
-- Export Validation
--------------------------------------------------------------------------------

/-- Validate export options. -/
def validateOptions (options : DepthExportOptions) : Bool :=
  options.width > 0 &&
  options.height > 0 &&
  options.endFrame >= options.startFrame

/-- Check if output directory path is valid. -/
def isValidOutputDir (path : String) : Bool :=
  path.length > 0 && !path.startsWith " "

end Lattice.Services.Depth.ExportSequence
