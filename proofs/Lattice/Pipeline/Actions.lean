-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // lattice // pipeline // actions
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- LATTICE PIPELINE ACTIONS — The ACTUAL operations agents perform.
--
-- This is NOT generic "ButtonPurpose" — these are the REAL pipeline operations:
-- - Generate (diffusion model inference)
-- - Render (frame composition)
-- - Import (asset ingestion)
-- - Export (video generation)
-- - DepthMap (depth estimation)
-- - Enhance (prompt enhancement)
-- - Segment (AI segmentation)
-- - Vectorize (image to vector)
--
-- Each action has:
-- - Required capabilities (what agent permissions are needed)
-- - Resource requirements (GPU, memory, time bounds)
-- - State preconditions (what must be true before action)
-- - State postconditions (what becomes true after action)
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import Mathlib.Data.Finset.Basic

namespace Lattice.Pipeline

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // layer operations
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Layer types in Lattice composition. -/
inductive LayerType where
  | Solid         -- Solid color layer
  | Text          -- Text layer with typography
  | Shape         -- Vector shape layer
  | Spline        -- Bezier spline path
  | Image         -- Raster image
  | Video         -- Video footage
  | Audio         -- Audio track
  | Camera        -- 3D camera
  | Light         -- Light source
  | Particles     -- Particle system
  | Group         -- Layer group/folder
  | Control       -- Control null (no render)
  | Nested        -- Nested composition
  | Depth         -- Depth map layer
  | Normal        -- Normal map layer
  | Generated     -- AI-generated content
  | DepthFlow     -- DepthFlow animated depth
  | Adjustment    -- Adjustment layer
  | Matte         -- Matte/mask layer
  deriving DecidableEq, Repr

/-- Layer action: operations on composition layers. -/
inductive LayerAction where
  | Create (layerType : LayerType)
  | Delete
  | Duplicate
  | Move (newIndex : Nat)
  | SetVisibility (visible : Bool)
  | SetOpacity (opacity : Float)  -- 0.0 to 1.0
  | SetParent (parentId : Option Nat)
  | Rename (newName : String)
  deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // keyframe operations
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Interpolation types for keyframe animation. -/
inductive Interpolation where
  | Linear
  | Bezier
  | Hold
  | EaseIn
  | EaseOut
  | EaseInOut
  | EaseInQuad | EaseOutQuad | EaseInOutQuad
  | EaseInCubic | EaseOutCubic | EaseInOutCubic
  | EaseInElastic | EaseOutElastic
  | EaseOutBounce
  deriving DecidableEq, Repr

/-- Keyframe action: animation operations. -/
inductive KeyframeAction where
  | Add (frame : Nat) (value : Float) (interp : Interpolation)
  | Remove (frame : Nat)
  | Modify (frame : Nat) (newValue : Float)
  | SetInterpolation (frame : Nat) (interp : Interpolation)
  | ScaleTiming (factor : Float)  -- Scale all keyframes
  | Copy (startFrame endFrame : Nat)
  | Paste (targetFrame : Nat)
  deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // effect operations
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Effect categories in Lattice. -/
inductive EffectCategory where
  | BlurSharpen      -- Blur and sharpen effects
  | ColorCorrection  -- Color grading, curves, levels
  | Distort          -- Warp, bulge, twirl, wave
  | Generate         -- Noise, gradients, patterns
  | Keying           -- Chroma key, luma key
  | Matte            -- Matte operations
  | NoiseGrain       -- Add/remove noise
  | Perspective      -- 3D perspective transforms
  | Stylize          -- Glow, emboss, posterize
  | Time             -- Time-based effects (echo, trails)
  | Transition       -- Transition effects
  | Utility          -- Utility effects
  deriving DecidableEq, Repr

/-- Specific effects available. -/
inductive EffectType where
  -- Blur
  | GaussianBlur | MotionBlur | RadialBlur | ZoomBlur
  -- Color
  | BrightnessContrast | HueSaturation | ColorBalance | Tint | Curves | Levels
  -- Stylize
  | Glow | DropShadow | Stroke | Emboss | Posterize
  -- Distort
  | Bulge | Twirl | Wave | Displacement | Liquify
  -- Generate
  | Gradient | FractalNoise | Checkerboard | Grid
  deriving DecidableEq, Repr

/-- Effect action: adding/modifying effects. -/
inductive EffectAction where
  | Add (effectType : EffectType)
  | Remove (effectIndex : Nat)
  | Modify (effectIndex : Nat) (paramName : String) (value : Float)
  | Enable (effectIndex : Nat)
  | Disable (effectIndex : Nat)
  | Reorder (fromIndex toIndex : Nat)
  deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // ai processing actions
-- ═══════════════════════════════════════════════════════════════════════════════

/-- AI processing actions — the heavy compute operations.

These are the operations that:
- Require GPU resources
- Take significant time
- May fail due to resource constraints
- Need progress tracking -/
inductive AIProcessingAction where
  -- Image Analysis
  | SegmentImage        -- SAM/DINO segmentation
  | VectorizeImage      -- Trace to vector paths
  | DecomposeImage      -- AI layer decomposition (Qwen-Image-Layered)
  -- Depth Estimation
  | GenerateDepth       -- Depth-Anything, MiDaS, Zoe, DepthPro, Marigold
  | EstimateNormals     -- Surface normal estimation
  -- Enhancement
  | EnhancePrompt       -- Prompt enhancement for generation
  | Upscale            -- AI upscaling (Real-ESRGAN, etc.)
  -- Generation
  | GenerateImage       -- Image generation from prompt
  | InpaintImage        -- Fill masked regions
  deriving DecidableEq, Repr

/-- Depth map formats (from various models). -/
inductive DepthFormat where
  | Raw           -- Raw Float32 values
  | MiDaS         -- 0=far, 255=near
  | Zoe           -- 16-bit linear
  | DepthPro      -- Metric depth
  | DepthAnything -- Depth-Anything format
  | Marigold      -- Affine-invariant
  | Normalized    -- 0-1 normalized
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // camera actions
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Camera trajectory presets (from LATTICE camera system). -/
inductive CameraTrajectory where
  | Orbit | OrbitReverse
  | Swing1 | Swing2
  | DollyIn | DollyOut
  | PanLeft | PanRight | TiltUp | TiltDown
  | ZoomIn | ZoomOut
  | Circle | Figure8 | SpiralIn | SpiralOut
  | CraneUp | CraneDown | TruckLeft | TruckRight
  | ArcLeft | ArcRight
  deriving DecidableEq, Repr

/-- Camera shake types. -/
inductive CameraShake where
  | Handheld
  | Impact
  | Earthquake
  | Subtle
  deriving DecidableEq, Repr

/-- Camera action: 3D camera control. -/
inductive CameraAction where
  | SetPosition (x y z : Float)
  | SetRotation (rx ry rz : Float)
  | SetFOV (fov : Float)
  | ApplyTrajectory (trajectory : CameraTrajectory)
  | AddShake (shake : CameraShake) (intensity : Float)
  | ApplyRackFocus (startDepth endDepth : Float)
  | SetPathFollowing (splineId : Nat)
  | EnableAutoFocus (targetLayerId : Nat)
  deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // export targets
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Video generation model targets.

Each target has different:
- Input requirements (depth, camera, pose, etc.)
- Output characteristics
- Processing time
- Quality/style -/
inductive ExportTarget where
  -- Wan models
  | Wan22_I2V         -- Wan 2.2 Image-to-Video
  | Wan22_T2V         -- Wan 2.2 Text-to-Video
  | Wan22_FunCamera   -- Wan 2.2 Fun Camera Control
  | Wan22_FirstLast   -- Wan 2.2 First+Last Frame
  -- Uni3C models
  | Uni3C_Camera      -- Uni3C Camera Control
  | Uni3C_Motion      -- Uni3C Human Motion + Camera
  -- MotionCtrl
  | MotionCtrl        -- MotionCtrl camera poses
  | MotionCtrl_SVD    -- MotionCtrl for SVD
  -- CogVideoX
  | CogVideoX_I2V     -- CogVideoX Image-to-Video
  -- ControlNet variants
  | ControlNet_Depth  -- Depth map for ControlNet
  | ControlNet_Canny  -- Canny edge for ControlNet
  | ControlNet_Lineart -- Line art for ControlNet
  | ControlNet_Pose   -- Pose skeleton for ControlNet
  -- AnimateDiff
  | AnimateDiff_CameraCtrl
  -- Specialized
  | LightX            -- Light-X relighting + camera
  | WanMove           -- Wan-Move point trajectories
  | ATI               -- ATI Any Trajectory Instruction
  | TTM               -- TTM Time-to-Move cut-and-drag
  | TTM_Wan           -- TTM with Wan backend
  | TTM_CogVideoX     -- TTM with CogVideoX backend
  | TTM_SVD           -- TTM with SVD backend
  | SCAIL             -- SCAIL pose-driven video
  -- Generic
  | CustomWorkflow    -- User's custom ComfyUI workflow
  deriving DecidableEq, Repr

/-- Control image types for export. -/
inductive ControlImageType where
  | Depth
  | Canny
  | Lineart
  | SoftEdge
  | Normal
  | Scribble
  | Segmentation
  | Pose
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // export pipeline stages
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Export pipeline stages — the actual rendering/generation flow. -/
inductive ExportStage where
  | Preparing         -- Initial setup
  | RenderingFrames   -- Rendering reference/last frames
  | RenderingDepth    -- Rendering depth sequence
  | RenderingControl  -- Rendering control images (canny, etc.)
  | ExportingCamera   -- Exporting camera trajectory data
  | GeneratingWorkflow -- Building ComfyUI workflow JSON
  | Uploading         -- Uploading to ComfyUI server
  | Queuing           -- Queuing workflow for execution
  | Generating        -- AI generation in progress
  | Downloading       -- Downloading generated results
  | Complete          -- Export complete
  | Error             -- Error occurred
  deriving DecidableEq, Repr

/-- Export stage is terminal (no more stages after). -/
def ExportStage.isTerminal : ExportStage → Bool
  | .Complete | .Error => true
  | _ => false

/-- Valid stage transitions. -/
def ExportStage.canTransitionTo : ExportStage → ExportStage → Bool
  | .Preparing, .RenderingFrames => true
  | .RenderingFrames, .RenderingDepth => true
  | .RenderingDepth, .RenderingControl => true
  | .RenderingControl, .ExportingCamera => true
  | .ExportingCamera, .GeneratingWorkflow => true
  | .GeneratingWorkflow, .Uploading => true
  | .Uploading, .Queuing => true
  | .Queuing, .Generating => true
  | .Generating, .Downloading => true
  | .Downloading, .Complete => true
  -- Any stage can transition to Error
  | _, .Error => true
  | _, _ => false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // composite pipeline action
-- ═══════════════════════════════════════════════════════════════════════════════

/-- All pipeline actions an agent can perform. -/
inductive PipelineAction where
  | Layer (layerId : Nat) (action : LayerAction)
  | Keyframe (layerId propertyId : Nat) (action : KeyframeAction)
  | Effect (layerId : Nat) (action : EffectAction)
  | AIProcessing (layerId : Nat) (action : AIProcessingAction)
  | Camera (action : CameraAction)
  | Export (target : ExportTarget) (controlTypes : List ControlImageType)
  | System (action : SystemAction)
  deriving Repr

/-- System-level actions. -/
inductive SystemAction where
  | SaveProject
  | LoadProject (path : String)
  | Undo
  | Redo
  | ClearCache
  | OptimizeMemory
  deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // resource requirements
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Resource requirements for an action. -/
structure ResourceRequirements where
  gpuMemoryMB : Nat        -- GPU memory required
  cpuCores : Nat           -- CPU cores used
  estimatedTimeMs : Nat    -- Estimated completion time
  requiresNetwork : Bool   -- Needs network (ComfyUI server)
  deriving Repr

/-- Estimate resources for AI processing action. -/
def AIProcessingAction.resourceRequirements : AIProcessingAction → ResourceRequirements
  | .SegmentImage => ⟨2048, 4, 5000, false⟩
  | .VectorizeImage => ⟨512, 2, 2000, false⟩
  | .DecomposeImage => ⟨4096, 4, 10000, false⟩
  | .GenerateDepth => ⟨2048, 2, 3000, false⟩
  | .EstimateNormals => ⟨1024, 2, 2000, false⟩
  | .EnhancePrompt => ⟨512, 1, 1000, true⟩
  | .Upscale => ⟨4096, 4, 8000, false⟩
  | .GenerateImage => ⟨8192, 4, 30000, true⟩
  | .InpaintImage => ⟨6144, 4, 20000, true⟩

/-- Export target resource requirements. -/
def ExportTarget.resourceRequirements : ExportTarget → ResourceRequirements
  | .Wan22_I2V | .Wan22_T2V | .Wan22_FunCamera | .Wan22_FirstLast =>
      ⟨12288, 4, 120000, true⟩  -- 12GB VRAM, ~2 min
  | .CogVideoX_I2V => ⟨16384, 4, 180000, true⟩  -- 16GB VRAM, ~3 min
  | .ControlNet_Depth | .ControlNet_Canny | .ControlNet_Lineart | .ControlNet_Pose =>
      ⟨8192, 4, 60000, true⟩   -- 8GB VRAM, ~1 min
  | .CustomWorkflow => ⟨8192, 4, 60000, true⟩  -- Estimate
  | _ => ⟨10240, 4, 90000, true⟩  -- Default: 10GB, 1.5 min

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // capability tokens
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Capabilities required to perform pipeline actions.

At billion-agent scale, agents have LIMITED capabilities:
- ViewOnly agents can read but not modify
- EditBasic agents can modify layers/keyframes
- AIProcessing agents can run AI operations
- Export agents can send to generation servers
- Admin agents can do everything -/
inductive PipelineCapability where
  | ViewOnly          -- Read-only access
  | EditLayers        -- Create/modify layers
  | EditKeyframes     -- Animate properties
  | EditEffects       -- Add/modify effects
  | RunAIProcessing   -- Execute AI operations (GPU-heavy)
  | ExportToComfyUI   -- Send to generation server
  | SystemAdmin       -- System operations
  deriving DecidableEq, Repr

/-- Required capability for each action type. -/
def PipelineAction.requiredCapability : PipelineAction → PipelineCapability
  | .Layer _ _ => .EditLayers
  | .Keyframe _ _ _ => .EditKeyframes
  | .Effect _ _ => .EditEffects
  | .AIProcessing _ _ => .RunAIProcessing
  | .Camera _ => .EditLayers  -- Camera is a layer
  | .Export _ _ => .ExportToComfyUI
  | .System _ => .SystemAdmin

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // proofs
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Export stages follow a valid progression. -/
theorem export_stage_progression
  (stage : ExportStage)
  (h_not_terminal : stage.isTerminal = false)
  : ∃ next, stage.canTransitionTo next ∧ next ≠ .Error := by
  cases stage with
  | Preparing => exact ⟨.RenderingFrames, rfl, by intro h; cases h⟩
  | RenderingFrames => exact ⟨.RenderingDepth, rfl, by intro h; cases h⟩
  | RenderingDepth => exact ⟨.RenderingControl, rfl, by intro h; cases h⟩
  | RenderingControl => exact ⟨.ExportingCamera, rfl, by intro h; cases h⟩
  | ExportingCamera => exact ⟨.GeneratingWorkflow, rfl, by intro h; cases h⟩
  | GeneratingWorkflow => exact ⟨.Uploading, rfl, by intro h; cases h⟩
  | Uploading => exact ⟨.Queuing, rfl, by intro h; cases h⟩
  | Queuing => exact ⟨.Generating, rfl, by intro h; cases h⟩
  | Generating => exact ⟨.Downloading, rfl, by intro h; cases h⟩
  | Downloading => exact ⟨.Complete, rfl, by intro h; cases h⟩
  | Complete => simp [ExportStage.isTerminal] at h_not_terminal
  | Error => simp [ExportStage.isTerminal] at h_not_terminal

/-- Terminal stages have no valid non-error transitions. -/
theorem terminal_no_forward_progress
  (stage : ExportStage)
  (h_terminal : stage.isTerminal = true)
  (next : ExportStage)
  (h_not_error : next ≠ .Error)
  : stage.canTransitionTo next = false := by
  cases stage with
  | Complete => cases next <;> simp [ExportStage.canTransitionTo] at * <;> trivial
  | Error => cases next <;> simp [ExportStage.canTransitionTo] at * <;> trivial
  | _ => simp [ExportStage.isTerminal] at h_terminal

/-- AI processing actions always have bounded resource requirements. -/
theorem ai_processing_resources_bounded (action : AIProcessingAction) :
    action.resourceRequirements.gpuMemoryMB ≤ 8192 ∧
    action.resourceRequirements.estimatedTimeMs ≤ 30000 := by
  cases action <;> simp [AIProcessingAction.resourceRequirements] <;> norm_num

/-- Layer creation is capability-gated. -/
theorem layer_create_requires_edit
  (layerId : Nat) (layerType : LayerType)
  : (PipelineAction.Layer layerId (.Create layerType)).requiredCapability = .EditLayers := by
  rfl

/-- Export always requires ExportToComfyUI capability. -/
theorem export_requires_capability
  (target : ExportTarget) (controls : List ControlImageType)
  : (PipelineAction.Export target controls).requiredCapability = .ExportToComfyUI := by
  rfl

/-- Interpolation types are finite (16 types). -/
theorem interpolation_finite : Fintype Interpolation := by
  constructor
  · exact ⟨[.Linear, .Bezier, .Hold, .EaseIn, .EaseOut, .EaseInOut,
           .EaseInQuad, .EaseOutQuad, .EaseInOutQuad,
           .EaseInCubic, .EaseOutCubic, .EaseInOutCubic,
           .EaseInElastic, .EaseOutElastic, .EaseOutBounce],
          by simp⟩
  · intro a
    cases a <;> simp

end Lattice.Pipeline
