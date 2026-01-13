/**
 * Vision-Guided Authoring Types
 *
 * Types for AI-assisted trajectory and path suggestion.
 * Based on docs/14_VISION_AUTHORING.md specification.
 *
 * PRINCIPLE: AI suggests, user accepts, MotionEngine evaluates.
 * AI is NEVER involved in frame evaluation.
 */

import type {
  Keyframe,
  ControlPoint as ProjectControlPoint,
  Vec3,
} from "@/types/project";

// Re-export for use in this module
export type ControlPoint = ProjectControlPoint;

// ============================================================================
// SCENE CONTEXT (Input to AI)
// ============================================================================

export interface SceneContext {
  readonly compositionId: string;
  readonly width: number;
  readonly height: number;
  readonly frameCount: number;
  readonly fps: number;
  readonly selectedLayerIds: readonly string[];
  readonly currentFrame: number;
  readonly frameImage?: ImageData; // Current frame for VLM analysis
  readonly depthMap?: Float32Array; // Pre-computed depth map
  readonly segmentationMasks?: SegmentationMask[];
}

export interface SegmentationMask {
  readonly id: string;
  readonly label: string;
  readonly mask: Uint8Array; // Binary mask
  readonly boundingBox: { x: number; y: number; width: number; height: number };
  readonly centroid: { x: number; y: number };
  readonly confidence: number;
}

// ============================================================================
// MOTION INTENT TYPES (AI Output)
// ============================================================================

export type CameraMotionType =
  | "dolly" // Forward/backward
  | "truck" // Left/right
  | "pedestal" // Up/down
  | "pan" // Rotate horizontally
  | "tilt" // Rotate vertically
  | "roll" // Rotate around view axis
  | "orbit" // Around a point
  | "drift" // Slow random movement
  | "handheld" // Organic shake
  | "crane" // Vertical arc
  | "zoom" // FOV change
  | "follow_path"; // Follow spline trajectory

export type MotionIntensity =
  | "very_subtle"
  | "subtle"
  | "medium"
  | "strong"
  | "dramatic";

export type EasingType =
  | "linear"
  | "easeIn"
  | "easeOut"
  | "easeInOut"
  | "bounce"
  | "elastic";

export interface CameraMotionIntent {
  readonly type: CameraMotionType;
  readonly intensity: MotionIntensity;
  readonly axis?: "x" | "y" | "z" | "all";
  readonly durationFrames?: number;
  readonly suggestedEasing?: EasingType;
  readonly noiseAmount?: number; // For handheld
  readonly orbitCenter?: Vec3; // For orbit
  readonly suggestedPath?: ControlPoint[]; // For follow_path
}

export type SplineUsage =
  | "camera_path" // Camera follows spline
  | "emitter_path" // Particles emit along spline
  | "text_path" // Text follows spline
  | "layer_path"; // Layer follows spline

export interface SplineMotionIntent {
  readonly usage: SplineUsage;
  readonly smoothness: number; // 0-1, curve smoothness
  readonly complexity: number; // Number of control points
  readonly worldSpace: boolean; // World or local coords
  readonly suggestedPoints: ControlPoint[]; // AI-suggested path points
  readonly closed: boolean; // Closed loop?
}

export type ParticleBehavior =
  | "flow" // Directional stream
  | "drift" // Floating particles
  | "spray" // Fan-out emission
  | "turbulence" // Chaotic movement
  | "explosion" // Burst from point
  | "vortex" // Spiral motion
  | "rain" // Downward fall
  | "snow" // Slow fall with drift
  | "fireflies" // Random glowing
  | "dust" // Ambient particles
  | "along_path"; // Emit along suggested path

export interface ParticleMotionIntent {
  readonly behavior: ParticleBehavior;
  readonly direction?: Vec3;
  readonly intensity: number;
  readonly spread?: number;
  readonly lifetime?: number;
  readonly colorScheme?: "warm" | "cool" | "neutral" | "custom";
  readonly suggestedEmitPath?: ControlPoint[]; // For along_path
}

export type LayerMotionType =
  | "parallax" // Depth-based offset
  | "float" // Gentle up/down
  | "sway" // Side-to-side
  | "breathe" // Scale oscillation
  | "drift" // Slow random
  | "noise" // Turbulent movement
  | "pulse" // Opacity oscillation
  | "rotate" // Continuous rotation
  | "follow_path"; // Follow spline

export interface LayerMotionIntent {
  readonly targetLayerId?: string; // Specific layer or all selected
  readonly motionType: LayerMotionType;
  readonly amplitude: number; // Scale of motion
  readonly frequency?: number; // For oscillating motions
  readonly phase?: number; // Offset in cycle
  readonly axis?: "x" | "y" | "z" | "scale" | "rotation";
  readonly suggestedPath?: ControlPoint[]; // For follow_path
}

// ============================================================================
// MOTION INTENT RESULT (Full AI Response)
// ============================================================================

export interface MotionIntentResult {
  readonly description: string; // Human-readable summary
  readonly confidence: number; // 0-1
  readonly cameraIntents?: readonly CameraMotionIntent[];
  readonly layerIntents?: readonly LayerMotionIntent[];
  readonly particleIntents?: readonly ParticleMotionIntent[];
  readonly splineIntents?: readonly SplineMotionIntent[];
  readonly rawResponse?: string; // Original AI response for debugging
}

// ============================================================================
// POINT SUGGESTION (Specific to trajectory/path suggestion)
// ============================================================================

export interface PointSuggestion {
  readonly x: number; // Pixel X
  readonly y: number; // Pixel Y
  readonly depth?: number; // Estimated depth at point
  readonly reason: string; // Why this point was suggested
  readonly confidence: number; // 0-1
}

export interface TrajectorySuggestion {
  readonly id: string;
  readonly name: string; // e.g., "Around subject", "Depth dive"
  readonly description: string;
  readonly points: ControlPoint[];
  readonly usage: SplineUsage;
  readonly durationFrames: number;
  readonly confidence: number;
}

export interface PathSuggestionResult {
  readonly trajectories: TrajectorySuggestion[];
  readonly keyPoints: PointSuggestion[]; // Important points in the scene
  readonly depthLayers: DepthLayer[]; // Depth-based layer suggestions
}

export interface DepthLayer {
  readonly name: string; // e.g., "Foreground", "Subject", "Background"
  readonly depthRange: { min: number; max: number };
  readonly mask: Uint8Array;
  readonly suggestedParallax: number; // Suggested parallax amount
}

// ============================================================================
// KEYFRAME BATCH (Translation Output)
// ============================================================================

export interface KeyframeBatch {
  readonly layerId: string;
  readonly propertyPath: string; // e.g., 'transform.position.x'
  readonly keyframes: Keyframe<unknown>[];
}

export interface TranslationResult {
  readonly keyframeBatches: KeyframeBatch[];
  readonly newLayers?: NewLayerSpec[]; // Suggested new layers to create
  readonly newSplines?: NewSplineSpec[]; // Suggested splines to create
}

export interface NewLayerSpec {
  readonly type: "spline" | "particles" | "camera";
  readonly name: string;
  readonly config: Record<string, unknown>;
}

export interface NewSplineSpec {
  readonly name: string;
  readonly points: ControlPoint[];
  readonly closed: boolean;
}

// ============================================================================
// VISION MODEL CONFIGURATION
// ============================================================================

export type VisionModelId =
  | "qwen-vl"
  | "qwen2-vl"
  | "gpt-4v"
  | "gpt-4o"
  | "claude-vision"
  | "llava"
  | "local-vlm"
  | "rule-based"; // Fallback when AI unavailable

export interface VisionModelConfig {
  readonly modelId: VisionModelId;
  readonly apiEndpoint?: string;
  /** @deprecated API keys are now handled server-side via environment variables */
  readonly apiKey?: string;
  readonly maxTokens?: number;
  readonly temperature?: number;
}

// ============================================================================
// DEPTH ESTIMATION
// ============================================================================

export type DepthModelId =
  | "depth-anything-v2"
  | "midas"
  | "zoe-depth"
  | "marigold";

export interface DepthEstimationResult {
  readonly depthMap: Float32Array; // Normalized depth [0,1]
  readonly width: number;
  readonly height: number;
  readonly model: DepthModelId;
  readonly confidence: number;
}

// ============================================================================
// SEGMENTATION
// ============================================================================

export type SegmentationModelId =
  | "sam"
  | "sam2"
  | "grounding-dino"
  | "yolo-world";

export interface SegmentationRequest {
  readonly image: ImageData;
  readonly prompt?: string; // Text prompt for grounded segmentation
  readonly points?: Array<{ x: number; y: number; label: 0 | 1 }>; // Point prompts
  readonly boxes?: Array<{
    x: number;
    y: number;
    width: number;
    height: number;
  }>;
}

export interface SegmentationResult {
  readonly masks: SegmentationMask[];
  readonly model: SegmentationModelId;
}
