/-
  Lattice.Schemas.ComfyUI.Targets

  Export targets and format enums for ComfyUI integration.

  Source: ui/src/schemas/comfyui-schema.ts
-/

namespace Lattice.Schemas.ComfyUI.Targets

--------------------------------------------------------------------------------
-- Export Target
--------------------------------------------------------------------------------

/-- Export target options -/
inductive ExportTarget where
  | wan22_i2v
  | wan22_t2v
  | wan22_fun_camera
  | wan22_first_last
  | uni3c_camera
  | uni3c_motion
  | motionctrl
  | motionctrl_svd
  | cogvideox
  | controlnet_depth
  | controlnet_canny
  | controlnet_lineart
  | controlnet_pose
  | animatediff_cameractrl
  | custom_workflow
  | light_x
  | wan_move
  | ati
  | ttm
  | ttm_wan
  | ttm_cogvideox
  | ttm_svd
  | scail
  | camera_comfyui
  deriving Repr, DecidableEq, Inhabited

def exportTargetFromString : String → Option ExportTarget
  | "wan22-i2v" => some .wan22_i2v
  | "wan22-t2v" => some .wan22_t2v
  | "wan22-fun-camera" => some .wan22_fun_camera
  | "wan22-first-last" => some .wan22_first_last
  | "uni3c-camera" => some .uni3c_camera
  | "uni3c-motion" => some .uni3c_motion
  | "motionctrl" => some .motionctrl
  | "motionctrl-svd" => some .motionctrl_svd
  | "cogvideox" => some .cogvideox
  | "controlnet-depth" => some .controlnet_depth
  | "controlnet-canny" => some .controlnet_canny
  | "controlnet-lineart" => some .controlnet_lineart
  | "controlnet-pose" => some .controlnet_pose
  | "animatediff-cameractrl" => some .animatediff_cameractrl
  | "custom-workflow" => some .custom_workflow
  | "light-x" => some .light_x
  | "wan-move" => some .wan_move
  | "ati" => some .ati
  | "ttm" => some .ttm
  | "ttm-wan" => some .ttm_wan
  | "ttm-cogvideox" => some .ttm_cogvideox
  | "ttm-svd" => some .ttm_svd
  | "scail" => some .scail
  | "camera-comfyui" => some .camera_comfyui
  | _ => none

def exportTargetToString : ExportTarget → String
  | .wan22_i2v => "wan22-i2v"
  | .wan22_t2v => "wan22-t2v"
  | .wan22_fun_camera => "wan22-fun-camera"
  | .wan22_first_last => "wan22-first-last"
  | .uni3c_camera => "uni3c-camera"
  | .uni3c_motion => "uni3c-motion"
  | .motionctrl => "motionctrl"
  | .motionctrl_svd => "motionctrl-svd"
  | .cogvideox => "cogvideox"
  | .controlnet_depth => "controlnet-depth"
  | .controlnet_canny => "controlnet-canny"
  | .controlnet_lineart => "controlnet-lineart"
  | .controlnet_pose => "controlnet-pose"
  | .animatediff_cameractrl => "animatediff-cameractrl"
  | .custom_workflow => "custom-workflow"
  | .light_x => "light-x"
  | .wan_move => "wan-move"
  | .ati => "ati"
  | .ttm => "ttm"
  | .ttm_wan => "ttm-wan"
  | .ttm_cogvideox => "ttm-cogvideox"
  | .ttm_svd => "ttm-svd"
  | .scail => "scail"
  | .camera_comfyui => "camera-comfyui"

--------------------------------------------------------------------------------
-- Depth Map Format
--------------------------------------------------------------------------------

/-- Depth map format options -/
inductive DepthMapFormat where
  | raw
  | midas
  | zoe
  | depth_pro
  | depth_anything
  | marigold
  | normalized
  deriving Repr, DecidableEq, Inhabited

def depthMapFormatFromString : String → Option DepthMapFormat
  | "raw" => some .raw
  | "midas" => some .midas
  | "zoe" => some .zoe
  | "depth-pro" => some .depth_pro
  | "depth-anything" => some .depth_anything
  | "marigold" => some .marigold
  | "normalized" => some .normalized
  | _ => none

def depthMapFormatToString : DepthMapFormat → String
  | .raw => "raw"
  | .midas => "midas"
  | .zoe => "zoe"
  | .depth_pro => "depth-pro"
  | .depth_anything => "depth-anything"
  | .marigold => "marigold"
  | .normalized => "normalized"

--------------------------------------------------------------------------------
-- Control Type
--------------------------------------------------------------------------------

/-- Control type options -/
inductive ControlType where
  | depth
  | canny
  | lineart
  | softedge
  | normal
  | scribble
  | seg
  | pose
  deriving Repr, DecidableEq, Inhabited

def controlTypeFromString : String → Option ControlType
  | "depth" => some .depth
  | "canny" => some .canny
  | "lineart" => some .lineart
  | "softedge" => some .softedge
  | "normal" => some .normal
  | "scribble" => some .scribble
  | "seg" => some .seg
  | "pose" => some .pose
  | _ => none

def controlTypeToString : ControlType → String
  | .depth => "depth"
  | .canny => "canny"
  | .lineart => "lineart"
  | .softedge => "softedge"
  | .normal => "normal"
  | .scribble => "scribble"
  | .seg => "seg"
  | .pose => "pose"

--------------------------------------------------------------------------------
-- Video Format
--------------------------------------------------------------------------------

/-- Video format options -/
inductive VideoFormat where
  | mp4
  | webm
  | gif
  | webp
  | image_sequence
  deriving Repr, DecidableEq, Inhabited

def videoFormatFromString : String → Option VideoFormat
  | "mp4" => some .mp4
  | "webm" => some .webm
  | "gif" => some .gif
  | "webp" => some .webp
  | "image_sequence" => some .image_sequence
  | _ => none

def videoFormatToString : VideoFormat → String
  | .mp4 => "mp4"
  | .webm => "webm"
  | .gif => "gif"
  | .webp => "webp"
  | .image_sequence => "image_sequence"

--------------------------------------------------------------------------------
-- Video Codec
--------------------------------------------------------------------------------

/-- Video codec options -/
inductive VideoCodec where
  | h264
  | h265
  | vp9
  | av1
  deriving Repr, DecidableEq, Inhabited

def videoCodecFromString : String → Option VideoCodec
  | "h264" => some .h264
  | "h265" => some .h265
  | "vp9" => some .vp9
  | "av1" => some .av1
  | _ => none

def videoCodecToString : VideoCodec → String
  | .h264 => "h264"
  | .h265 => "h265"
  | .vp9 => "vp9"
  | .av1 => "av1"

--------------------------------------------------------------------------------
-- Frame Sequence Format
--------------------------------------------------------------------------------

/-- Frame sequence format options -/
inductive FrameSequenceFormat where
  | png
  | jpeg
  | webp
  | tiff
  | exr
  | dpx
  deriving Repr, DecidableEq, Inhabited

def frameSequenceFormatFromString : String → Option FrameSequenceFormat
  | "png" => some .png
  | "jpeg" => some .jpeg
  | "webp" => some .webp
  | "tiff" => some .tiff
  | "exr" => some .exr
  | "dpx" => some .dpx
  | _ => none

def frameSequenceFormatToString : FrameSequenceFormat → String
  | .png => "png"
  | .jpeg => "jpeg"
  | .webp => "webp"
  | .tiff => "tiff"
  | .exr => "exr"
  | .dpx => "dpx"

--------------------------------------------------------------------------------
-- Depth Colormap
--------------------------------------------------------------------------------

/-- Depth colormap options -/
inductive DepthColormap where
  | grayscale
  | viridis
  | magma
  | plasma
  | inferno
  | turbo
  deriving Repr, DecidableEq, Inhabited

def depthColormapFromString : String → Option DepthColormap
  | "grayscale" => some .grayscale
  | "viridis" => some .viridis
  | "magma" => some .magma
  | "plasma" => some .plasma
  | "inferno" => some .inferno
  | "turbo" => some .turbo
  | _ => none

def depthColormapToString : DepthColormap → String
  | .grayscale => "grayscale"
  | .viridis => "viridis"
  | .magma => "magma"
  | .plasma => "plasma"
  | .inferno => "inferno"
  | .turbo => "turbo"

--------------------------------------------------------------------------------
-- Export Stage
--------------------------------------------------------------------------------

/-- Export progress stage -/
inductive ExportStage where
  | preparing
  | rendering_frames
  | rendering_depth
  | rendering_control
  | exporting_camera
  | generating_workflow
  | uploading
  | queuing
  | generating
  | downloading
  | complete
  | error
  deriving Repr, DecidableEq, Inhabited

def exportStageFromString : String → Option ExportStage
  | "preparing" => some .preparing
  | "rendering_frames" => some .rendering_frames
  | "rendering_depth" => some .rendering_depth
  | "rendering_control" => some .rendering_control
  | "exporting_camera" => some .exporting_camera
  | "generating_workflow" => some .generating_workflow
  | "uploading" => some .uploading
  | "queuing" => some .queuing
  | "generating" => some .generating
  | "downloading" => some .downloading
  | "complete" => some .complete
  | "error" => some .error
  | _ => none

def exportStageToString : ExportStage → String
  | .preparing => "preparing"
  | .rendering_frames => "rendering_frames"
  | .rendering_depth => "rendering_depth"
  | .rendering_control => "rendering_control"
  | .exporting_camera => "exporting_camera"
  | .generating_workflow => "generating_workflow"
  | .uploading => "uploading"
  | .queuing => "queuing"
  | .generating => "generating"
  | .downloading => "downloading"
  | .complete => "complete"
  | .error => "error"

--------------------------------------------------------------------------------
-- Generation Status
--------------------------------------------------------------------------------

/-- Generation status options -/
inductive GenerationStatus where
  | queued
  | executing
  | completed
  | error
  deriving Repr, DecidableEq, Inhabited

def generationStatusFromString : String → Option GenerationStatus
  | "queued" => some .queued
  | "executing" => some .executing
  | "completed" => some .completed
  | "error" => some .error
  | _ => none

def generationStatusToString : GenerationStatus → String
  | .queued => "queued"
  | .executing => "executing"
  | .completed => "completed"
  | .error => "error"

end Lattice.Schemas.ComfyUI.Targets
