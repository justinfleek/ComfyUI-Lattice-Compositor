/-
  Lattice.Export - Export types and ComfyUI integration

  Max 500 lines.

  Source: ui/src/types/export.ts (404 lines)

  Key concepts:
  - ExportTarget: Video generation models (Wan 2.2, CogVideoX, etc.)
  - ExportConfig: Settings for each export target
  - CameraMotion: Camera data formats for different targets
  - ComfyUINode: Node structure for workflow generation
-/

import Lattice.Primitives

namespace Lattice.Export

open Lattice.Primitives

/-! ## Export Target -/

/-- Export target types (video generation models) -/
inductive ExportTarget where
  | wan22           -- Wan 2.2 video generation
  | uni3c           -- Uni3C camera control
  | motionctrl      -- MotionCtrl pose-based
  | cogvideox       -- CogVideoX
  | controlnet      -- ControlNet preprocessors
  | depthAnything   -- Depth Anything export
  | normalMap       -- Normal map export
  | poseSequence    -- OpenPose sequence
  | opticalFlow     -- Optical flow maps
  | segmentation    -- Segmentation masks
  | custom          -- Custom workflow
  deriving Repr, BEq, DecidableEq

/-! ## Video Format -/

/-- Output video format -/
inductive VideoFormat where
  | mp4   -- H.264/H.265
  | webm  -- VP9
  | gif   -- Animated GIF
  | png   -- PNG sequence
  | exr   -- EXR sequence (HDR)
  deriving Repr, BEq, DecidableEq

/-! ## Video Codec -/

/-- Video codec -/
inductive VideoCodec where
  | h264
  | h265
  | vp9
  | prores
  deriving Repr, BEq, DecidableEq

/-! ## Pixel Format -/

/-- Pixel format -/
inductive PixelFormat where
  | yuv420p
  | yuv444p
  | rgb24
  | rgba
  deriving Repr, BEq, DecidableEq

/-! ## Depth Format -/

/-- Depth map format -/
inductive DepthFormat where
  | grayscale16   -- 16-bit grayscale PNG
  | grayscale8    -- 8-bit grayscale PNG
  | exr32         -- 32-bit EXR
  | disparity     -- Inverse depth (disparity)
  deriving Repr, BEq, DecidableEq

/-! ## Normal Format -/

/-- Normal map format -/
inductive NormalFormat where
  | opengl    -- Y+ up
  | directx   -- Y- up
  | worldSpace
  | viewSpace
  deriving Repr, BEq, DecidableEq

/-! ## Pose Format -/

/-- Pose estimation format -/
inductive PoseFormat where
  | openpose18    -- COCO 18 keypoints
  | openpose25    -- Body25
  | mediapipe     -- MediaPipe pose
  | dwpose       -- DWPose (133 keypoints)
  deriving Repr, BEq, DecidableEq

/-! ## Flow Format -/

/-- Optical flow format -/
inductive FlowFormat where
  | flo     -- Middlebury .flo
  | png     -- PNG with color coding
  | exr     -- EXR with raw values
  deriving Repr, BEq, DecidableEq

/-! ## Video Encoder Options -/

/-- Video encoder configuration -/
structure VideoEncoderOptions where
  format : VideoFormat
  codec : VideoCodec
  quality : Nat              -- 0-51 for H.264 (lower = better)
  bitrate : Option Nat       -- kbps
  pixelFormat : PixelFormat
  fps : Float
  quality_le_51 : quality ≤ 51
  fps_positive : fps > 0
  fps_finite : fps.isFinite
  deriving Repr

/-! ## Depth Export Options -/

/-- Depth export configuration -/
structure DepthExportOptions where
  format : DepthFormat
  minDepth : Float
  maxDepth : Float
  invertDepth : Bool
  normalizeToRange : Bool
  minDepth_finite : minDepth.isFinite
  maxDepth_finite : maxDepth.isFinite
  minDepth_lt_maxDepth : minDepth < maxDepth
  deriving Repr

/-! ## Normal Export Options -/

/-- Normal map export configuration -/
structure NormalExportOptions where
  format : NormalFormat
  flipY : Bool
  flipX : Bool
  deriving Repr

/-! ## Pose Export Options -/

/-- Pose export configuration -/
structure PoseExportOptions where
  format : PoseFormat
  drawSkeleton : Bool
  drawKeypoints : Bool
  keypointRadius : Nat
  lineThickness : Nat
  backgroundColor : RGBA
  keypointRadius_positive : keypointRadius > 0
  lineThickness_positive : lineThickness > 0
  deriving Repr

/-! ## MotionCtrl Pose -/

/-- Single pose for MotionCtrl (18 keypoints) -/
structure MotionCtrlPose where
  keypoints : Array (Float × Float × Float)  -- (x, y, confidence) * 18
  keypoints_size : keypoints.size = 18
  deriving Repr

/-- MotionCtrl export data -/
structure MotionCtrlExportData where
  poses : Array MotionCtrlPose
  width : Nat
  height : Nat
  fps : Float
  width_positive : width > 0
  height_positive : height > 0
  fps_positive : fps > 0
  fps_finite : fps.isFinite
  deriving Repr

/-! ## Wan 2.2 Camera Motion -/

/-- Wan 2.2 camera motion keyframe -/
structure Wan22CameraKeyframe where
  frame : FrameNumber
  pan : Float       -- -1 to 1
  tilt : Float      -- -1 to 1
  roll : Float      -- -180 to 180
  zoom : Float      -- 0.5 to 2.0
  pan_finite : pan.isFinite
  tilt_finite : tilt.isFinite
  roll_finite : roll.isFinite
  zoom_finite : zoom.isFinite
  deriving Repr

/-- Wan 2.2 camera motion data -/
structure Wan22CameraMotion where
  keyframes : Array Wan22CameraKeyframe
  frameCount : FrameNumber
  deriving Repr

/-! ## Uni3C Camera Data -/

/-- Uni3C camera intrinsics -/
structure Uni3CIntrinsics where
  fx : Float
  fy : Float
  cx : Float
  cy : Float
  fx_positive : fx > 0
  fx_finite : fx.isFinite
  fy_positive : fy > 0
  fy_finite : fy.isFinite
  cx_finite : cx.isFinite
  cy_finite : cy.isFinite
  deriving Repr

/-- Uni3C camera pose (4x4 matrix, row-major) -/
structure Uni3CCameraPose where
  frame : FrameNumber
  matrix : Array Float  -- 16 elements
  matrix_size : matrix.size = 16
  deriving Repr

/-- Uni3C export data -/
structure Uni3CCameraData where
  intrinsics : Uni3CIntrinsics
  poses : Array Uni3CCameraPose
  width : Nat
  height : Nat
  fps : Float
  width_positive : width > 0
  height_positive : height > 0
  fps_positive : fps > 0
  fps_finite : fps.isFinite
  deriving Repr

/-! ## ComfyUI Types -/

/-- ComfyUI node input type -/
inductive ComfyUIInputType where
  | int
  | float
  | string
  | boolean
  | image
  | latent
  | model
  | clip
  | vae
  | conditioning
  | mask
  | controlNet
  deriving Repr, BEq, DecidableEq

/-- ComfyUI node input value -/
inductive ComfyUIInputValue where
  | intValue : Int → ComfyUIInputValue
  | floatValue : Float → ComfyUIInputValue
  | stringValue : String → ComfyUIInputValue
  | boolValue : Bool → ComfyUIInputValue
  | nodeRef : String → Nat → ComfyUIInputValue  -- node_id, output_index
  deriving Repr

/-- ComfyUI node input -/
structure ComfyUIInput where
  name : NonEmptyString
  inputType : ComfyUIInputType
  value : ComfyUIInputValue
  deriving Repr

/-- ComfyUI node -/
structure ComfyUINode where
  id : NonEmptyString
  classType : NonEmptyString
  inputs : Array ComfyUIInput
  deriving Repr

/-- ComfyUI workflow -/
structure ComfyUIWorkflow where
  nodes : Array ComfyUINode
  outputNodeId : NonEmptyString
  deriving Repr

/-! ## Export Config -/

/-- Main export configuration -/
structure ExportConfig where
  target : ExportTarget
  outputPath : NonEmptyString
  width : Nat
  height : Nat
  fps : Float
  frameStart : FrameNumber
  frameEnd : FrameNumber
  -- Video options
  videoOptions : Option VideoEncoderOptions
  -- Depth options
  depthOptions : Option DepthExportOptions
  -- Normal options
  normalOptions : Option NormalExportOptions
  -- Pose options
  poseOptions : Option PoseExportOptions
  -- ComfyUI workflow
  workflow : Option ComfyUIWorkflow
  -- Proofs
  width_positive : width > 0
  height_positive : height > 0
  fps_positive : fps > 0
  fps_finite : fps.isFinite
  deriving Repr

/-! ## Export Result -/

/-- Export result status -/
inductive ExportStatus where
  | success
  | failed
  | cancelled
  deriving Repr, BEq, DecidableEq

/-- Export result -/
structure ExportResult where
  status : ExportStatus
  outputPath : Option NonEmptyString
  frameCount : Nat
  duration : Float  -- Seconds
  fileSize : Nat    -- Bytes
  errorMessage : Option String
  duration_ge_0 : duration ≥ 0
  duration_finite : duration.isFinite
  deriving Repr

/-! ## Default Values -/

/-- Default video encoder options -/
def defaultVideoOptions (fps : Float) (h : fps > 0) (hf : fps.isFinite) : VideoEncoderOptions :=
  { format := VideoFormat.mp4
  , codec := VideoCodec.h264
  , quality := 23
  , bitrate := none
  , pixelFormat := PixelFormat.yuv420p
  , fps := fps
  , quality_le_51 := by decide
  , fps_positive := h
  , fps_finite := hf
  }

end Lattice.Export
