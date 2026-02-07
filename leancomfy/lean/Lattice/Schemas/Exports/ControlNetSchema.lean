/-
  Lattice.Schemas.Exports.ControlNetSchema

  ControlNet export format enums and types.

  Source: ui/src/schemas/exports/controlnet-schema.ts
-/

namespace Lattice.Schemas.Exports.ControlNetSchema

--------------------------------------------------------------------------------
-- ControlNet Type
--------------------------------------------------------------------------------

/-- ControlNet type options -/
inductive ControlNetType where
  | depth     -- Depth map
  | canny     -- Canny edge detection
  | lineart   -- Line art extraction
  | softedge  -- Soft edge detection (HED/PIDI)
  | normal    -- Normal map
  | scribble  -- Scribble/sketch input
  | seg       -- Semantic segmentation
  | pose      -- OpenPose skeleton
  deriving Repr, DecidableEq, Inhabited

def controlNetTypeFromString : String → Option ControlNetType
  | "depth" => some .depth
  | "canny" => some .canny
  | "lineart" => some .lineart
  | "softedge" => some .softedge
  | "normal" => some .normal
  | "scribble" => some .scribble
  | "seg" => some .seg
  | "pose" => some .pose
  | _ => Option.none

def controlNetTypeToString : ControlNetType → String
  | .depth => "depth"
  | .canny => "canny"
  | .lineart => "lineart"
  | .softedge => "softedge"
  | .normal => "normal"
  | .scribble => "scribble"
  | .seg => "seg"
  | .pose => "pose"

--------------------------------------------------------------------------------
-- Pose Output Format
--------------------------------------------------------------------------------

/-- Pose output format options -/
inductive PoseOutputFormat where
  | images
  | json
  | both
  deriving Repr, DecidableEq, Inhabited

def poseOutputFormatFromString : String → Option PoseOutputFormat
  | "images" => some .images
  | "json" => some .json
  | "both" => some .both
  | _ => Option.none

def poseOutputFormatToString : PoseOutputFormat → String
  | .images => "images"
  | .json => "json"
  | .both => "both"

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- ControlNet export configuration -/
structure ControlNetExportConfig where
  controlNetType : ControlNetType
  resolution : Nat
  thresholdLow : Option Float
  thresholdHigh : Option Float
  detectResolution : Option Nat
  deriving Repr, Inhabited

/-- Pose export configuration -/
structure PoseExportConfig where
  width : Nat
  height : Nat
  startFrame : Nat
  endFrame : Nat
  boneWidth : Float
  keypointRadius : Float
  showKeypoints : Bool
  showBones : Bool
  useOpenPoseColors : Bool
  outputFormat : PoseOutputFormat
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_THRESHOLD : Float := 255.0
def MAX_POSE_KEYPOINTS : Nat := 1000
def MAX_FACE_KEYPOINTS : Nat := 1000
def MAX_HAND_KEYPOINTS : Nat := 500
def MAX_PEOPLE_PER_FRAME : Nat := 1000
def MAX_BONE_WIDTH : Float := 100.0
def MAX_KEYPOINT_RADIUS : Float := 100.0
def MAX_OPENPOSE_VERSION : Nat := 100

end Lattice.Schemas.Exports.ControlNetSchema
