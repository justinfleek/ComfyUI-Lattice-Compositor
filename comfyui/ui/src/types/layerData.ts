/**
 * Layer Data Types - Layer-specific data interfaces
 *
 * Extracted from project.ts for better modularity.
 * Each layer type has its own data interface defining type-specific properties.
 */

import type { AnimatableProperty } from "./animation";
import type { JSONValue } from "./dataAsset";

// ============================================================
// IMAGE LAYER DATA
// ============================================================

export interface ImageLayerData {
  // Asset reference - empty string if using inline source
  assetId: string;

  // Inline data URL - empty string if using assetId
  // Used for temporary/generated images before asset creation
  source: string;

  // Display options
  fit: "none" | "contain" | "cover" | "fill";

  // Cropping (for segmented regions)
  cropEnabled: boolean;
  cropRect: {
    x: number;
    y: number;
    width: number;
    height: number;
  };

  // Source info (for regeneration/editing)
  sourceType: "file" | "generated" | "segmented" | "inline";
  segmentationMaskId: string; // Empty string if not from segmentation
}

// ============================================================
// DEPTH LAYER DATA
// ============================================================

export interface DepthLayerData {
  /** Source asset ID (depth map image) */
  assetId: string | null;

  /** Visualization mode */
  visualizationMode: "grayscale" | "colormap" | "contour" | "3d-mesh";

  /** Color map preset for visualization */
  colorMap: "turbo" | "viridis" | "plasma" | "inferno" | "magma" | "grayscale";

  /** Invert depth values (near <-> far) */
  invert: boolean;

  /** Depth range normalization */
  minDepth: number;
  maxDepth: number;
  autoNormalize: boolean;

  /** Contour settings (when visualizationMode = 'contour') */
  contourLevels: number;
  contourColor: string;
  contourWidth: number;

  /** 3D mesh settings (when visualizationMode = '3d-mesh') */
  meshDisplacement: AnimatableProperty<number>;
  meshResolution: number;
  wireframe: boolean;
}

// ============================================================
// NORMAL LAYER DATA
// ============================================================

export interface NormalLayerData {
  /** Source asset ID (normal map image) */
  assetId: string | null;

  /** Visualization mode */
  visualizationMode: "rgb" | "hemisphere" | "arrows" | "lit";

  /** Normal map format */
  format: "opengl" | "directx";

  /** Flip channels */
  flipX: boolean;
  flipY: boolean;
  flipZ: boolean;

  /** Arrow visualization settings */
  arrowDensity: number;
  arrowScale: number;
  arrowColor: string;

  /** Lit visualization settings (fake lighting preview) */
  lightDirection: { x: number; y: number; z: number };
  lightIntensity: number;
  ambientIntensity: number;
}

// ============================================================
// AUDIO LAYER DATA
// ============================================================

export interface AudioLayerData {
  /** Source asset ID (audio file) */
  assetId: string | null;

  /** Audio level (dB, 0 = unity) */
  level: AnimatableProperty<number>;

  /** Mute toggle */
  muted: boolean;

  /** Solo this audio track */
  solo: boolean;

  /** Panning (-1 = left, 0 = center, 1 = right) */
  pan: AnimatableProperty<number>;

  /** Playback settings */
  startTime: number;
  loop: boolean;
  speed: number;

  /** Waveform visualization in timeline */
  showWaveform: boolean;
  waveformColor: string;

  /** Audio reactivity - expose audio features for linking */
  exposeFeatures: boolean;
}

// ============================================================
// VIDEO DATA
// ============================================================

export interface VideoData {
  assetId: string | null;

  // Playback control
  loop: boolean; // Loop when reaching end
  pingPong: boolean; // Reverse at end instead of restart
  startTime: number; // Start offset in source video (seconds)
  endTime?: number; // End time in source (undefined = full duration)
  speed: number; // Playback speed (1 = normal, 2 = 2x, 0.5 = half)

  // Speed mapping (professional feature for time manipulation)
  speedMapEnabled: boolean;
  speedMap?: AnimatableProperty<number>; // Maps comp time to video time
  /** @deprecated Use 'speedMapEnabled' instead */
  timeRemapEnabled?: boolean;
  /** @deprecated Use 'speedMap' instead */
  timeRemap?: AnimatableProperty<number>;

  // Timewarp - animatable speed with integration for smooth ramps
  timewarpEnabled?: boolean;
  timewarpSpeed?: AnimatableProperty<number>; // Speed % (100 = normal, 200 = 2x, 50 = 0.5x)
  timewarpMethod?: "whole-frames" | "frame-mix" | "pixel-motion";

  // Frame blending for speed changes
  frameBlending: "none" | "frame-mix" | "pixel-motion";

  // Audio
  audioEnabled: boolean;
  audioLevel: number; // 0-100

  // Poster frame (for thumbnails)
  posterFrame: number; // Frame to show when paused at start
}

// ============================================================
// NESTED COMP DATA
// ============================================================

export interface NestedCompData {
  compositionId: string; // Reference to composition in project.compositions

  // Speed mapping (time manipulation)
  speedMapEnabled: boolean;
  speedMap?: AnimatableProperty<number>; // Maps parent time to nested comp time
  /** @deprecated Use 'speedMapEnabled' instead */
  timeRemapEnabled?: boolean;
  /** @deprecated Use 'speedMap' instead */
  timeRemap?: AnimatableProperty<number>;

  // Timewarp - animatable speed with integration for smooth ramps
  timewarpEnabled?: boolean;
  timewarpSpeed?: AnimatableProperty<number>; // Speed % (100 = normal, 200 = 2x, 50 = 0.5x)
  timewarpMethod?: "whole-frames" | "frame-mix" | "pixel-motion";

  // Flatten transform (render nested layers in parent's 3D space)
  flattenTransform: boolean;

  // Override nested comp settings
  overrideFrameRate: boolean;
  frameRate?: number;
}

// ============================================================
// GENERATED MAP DATA
// ============================================================

export type GeneratedMapType =
  | "depth" // DepthAnything V3
  | "normal" // NormalCrafter
  | "edge" // Canny/HED
  | "pose" // DWPose/OpenPose
  | "segment" // SAM2/MatSeg
  | "lineart" // Lineart extraction
  | "softedge"; // Soft edge detection

export interface GeneratedMapData {
  sourceLayerId: string; // Which layer to generate from
  mapType: GeneratedMapType;
  modelId: string; // Which model to use
  parameters: Record<string, JSONValue>;
  cachedResult?: string; // Base64 cached output
  lastGenerated?: string; // ISO timestamp
}

// ============================================================
// GENERATED LAYER DATA (AI-generated content)
// ============================================================

export interface GeneratedLayerData {
  /** Generated content type */
  generationType:
    | "depth"
    | "normal"
    | "edge"
    | "segment"
    | "inpaint"
    | "custom";

  /** Source layer ID (input to generation) */
  sourceLayerId: string | null;

  /** Model used for generation */
  model: string;

  /** Generation parameters (model-specific) */
  parameters: Record<string, JSONValue>;

  /** Generated asset ID (output) */
  generatedAssetId: string | null;

  /** Generation status */
  status: "pending" | "generating" | "complete" | "error";
  errorMessage?: string;

  /** Auto-regenerate when source changes */
  autoRegenerate: boolean;

  /** Last generation timestamp */
  lastGenerated?: string;
}

// ============================================================
// MATTE LAYER DATA
// ============================================================

export interface MatteLayerData {
  /** Matte extraction method */
  matteType:
    | "luminance"
    | "alpha"
    | "red"
    | "green"
    | "blue"
    | "hue"
    | "saturation";

  /** Invert the matte */
  invert: boolean;

  /** Threshold for matte cutoff */
  threshold: number;

  /** Feather/blur amount */
  feather: number;

  /** Expand/contract matte edges */
  expansion: number;

  /** Source layer ID (if extracting matte from another layer) */
  sourceLayerId: string | null;

  /** Preview mode */
  previewMode: "matte" | "composite" | "overlay";
}

// ============================================================
// CONTROL LAYER DATA (formerly Null Object)
// ============================================================

export interface ControlLayerData {
  /** Visual size of control icon in editor */
  size: number;

  /** Show XYZ axis indicators */
  showAxes: boolean;

  /** Show control layer icon/gizmo */
  showIcon: boolean;

  /** Icon shape */
  iconShape: "crosshair" | "diamond" | "circle" | "square";

  /** Icon color */
  iconColor: string;
}

// ============================================================
// SOLID LAYER DATA
// ============================================================

export interface SolidLayerData {
  /** Solid color */
  color: string;

  /** Width in pixels */
  width: number;

  /** Height in pixels */
  height: number;

  /** Shadow catcher mode (Three.js ShadowMaterial) */
  shadowCatcher?: boolean;
  shadowOpacity?: number;
  shadowColor?: string;
  receiveShadow?: boolean;
}

// ============================================================
// NULL LAYER DATA (deprecated - use ControlLayerData)
// ============================================================

/** @deprecated Use ControlLayerData instead */
export interface NullLayerData {
  /** Visual size of null icon in editor */
  size: number;
}

// ============================================================
// GROUP LAYER DATA
// ============================================================

export interface GroupLayerData {
  /** Collapsed state in timeline */
  collapsed: boolean;

  /** Group color label */
  color: string | null;

  /** Pass-through mode (group doesn't create intermediate composite) */
  passThrough: boolean;

  /** Isolate group (only show group contents when selected) */
  isolate: boolean;
}

// ============================================================
// EFFECT LAYER DATA (formerly Adjustment Layer)
// ============================================================

export interface EffectLayerData {
  /** Effect layer flag (always true for effect layers) */
  effectLayer: boolean;

  /** @deprecated Use effectLayer - backwards compatibility */
  adjustmentLayer: boolean;

  /** Layer label color for organization */
  color: string;
}

// ============================================================
// MODEL LAYER DATA (3D Models)
// ============================================================

export interface ModelLayerData {
  /** Asset ID for the 3D model */
  assetId: string | null;

  /** Current animation clip (if model has animations) */
  animationClip?: string;

  /** Animation playback */
  animationSpeed: number;
  animationLoop: boolean;
  animationTime: AnimatableProperty<number>;

  /** Material overrides */
  materialOverride?: {
    albedo?: string; // Asset ID
    normal?: string;
    roughness?: string;
    metalness?: string;
    emissive?: string;
    emissiveIntensity?: number;
  };

  /** Rendering options */
  castShadows: boolean;
  receiveShadows: boolean;
  wireframe: boolean;

  /** LOD settings */
  lodBias: number;

  /** Instance count (for instancing) */
  instanceCount?: number;
  instanceData?: ModelInstanceData[];
}

export interface ModelInstanceData {
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  scale: { x: number; y: number; z: number };
  color?: string;
}

// ============================================================
// POINT CLOUD LAYER DATA
// ============================================================

export interface PointCloudLayerData {
  /** Asset ID for the point cloud */
  assetId: string | null;

  /** Point size */
  pointSize: AnimatableProperty<number>;

  /** Point size attenuation (smaller at distance) */
  sizeAttenuation: boolean;

  /** Color mode */
  colorMode: "vertex" | "height" | "intensity" | "solid";
  solidColor?: string;

  /** Height-based coloring */
  heightColormap?: "turbo" | "viridis" | "plasma" | "grayscale";
  heightMin?: number;
  heightMax?: number;

  /** Intensity range (for intensity coloring) */
  intensityMin?: number;
  intensityMax?: number;

  /** Point decimation (show every Nth point) */
  decimation: number;

  /** Clipping box */
  clipEnabled: boolean;
  clipBox?: {
    minX: number;
    maxX: number;
    minY: number;
    maxY: number;
    minZ: number;
    maxZ: number;
  };
}

// ============================================================
// POSE LAYER DATA (OpenPose skeleton)
// ============================================================

export interface PoseKeypoint {
  x: number; // Normalized 0-1
  y: number; // Normalized 0-1
  confidence: number; // 0-1
}

export interface PoseLayerData {
  /** Keypoints for the skeleton */
  keypoints: PoseKeypoint[];

  /** Pose format */
  format: "openpose" | "coco" | "dwpose";

  /** Rendering options */
  lineWidth: number;
  jointRadius: number;
  lineColor: string;
  jointColor: string;

  /** Show confidence (opacity based on confidence) */
  showConfidence: boolean;

  /** Mirror pose */
  mirror: boolean;
}

// OpenPose keypoint indices
export const OPENPOSE_KEYPOINTS = {
  NOSE: 0,
  NECK: 1,
  RIGHT_SHOULDER: 2,
  RIGHT_ELBOW: 3,
  RIGHT_WRIST: 4,
  LEFT_SHOULDER: 5,
  LEFT_ELBOW: 6,
  LEFT_WRIST: 7,
  RIGHT_HIP: 8,
  RIGHT_KNEE: 9,
  RIGHT_ANKLE: 10,
  LEFT_HIP: 11,
  LEFT_KNEE: 12,
  LEFT_ANKLE: 13,
  RIGHT_EYE: 14,
  LEFT_EYE: 15,
  RIGHT_EAR: 16,
  LEFT_EAR: 17,
} as const;

// Skeleton connections for rendering
export const OPENPOSE_CONNECTIONS: [number, number][] = [
  [0, 1], // Nose to Neck
  [1, 2], // Neck to Right Shoulder
  [2, 3], // Right Shoulder to Elbow
  [3, 4], // Right Elbow to Wrist
  [1, 5], // Neck to Left Shoulder
  [5, 6], // Left Shoulder to Elbow
  [6, 7], // Left Elbow to Wrist
  [1, 8], // Neck to Right Hip
  [8, 9], // Right Hip to Knee
  [9, 10], // Right Knee to Ankle
  [1, 11], // Neck to Left Hip
  [11, 12], // Left Hip to Knee
  [12, 13], // Left Knee to Ankle
  [0, 14], // Nose to Right Eye
  [14, 16], // Right Eye to Ear
  [0, 15], // Nose to Left Eye
  [15, 17], // Left Eye to Ear
];

/**
 * Create default pose keypoints (T-pose)
 */
export function createDefaultPoseKeypoints(): PoseKeypoint[] {
  return [
    { x: 0.5, y: 0.1, confidence: 1 }, // 0: nose
    { x: 0.5, y: 0.2, confidence: 1 }, // 1: neck
    { x: 0.35, y: 0.25, confidence: 1 }, // 2: right_shoulder
    { x: 0.2, y: 0.25, confidence: 1 }, // 3: right_elbow
    { x: 0.05, y: 0.25, confidence: 1 }, // 4: right_wrist
    { x: 0.65, y: 0.25, confidence: 1 }, // 5: left_shoulder
    { x: 0.8, y: 0.25, confidence: 1 }, // 6: left_elbow
    { x: 0.95, y: 0.25, confidence: 1 }, // 7: left_wrist
    { x: 0.4, y: 0.5, confidence: 1 }, // 8: right_hip
    { x: 0.4, y: 0.7, confidence: 1 }, // 9: right_knee
    { x: 0.4, y: 0.85, confidence: 1 }, // 10: right_ankle
    { x: 0.6, y: 0.5, confidence: 1 }, // 11: left_hip
    { x: 0.6, y: 0.7, confidence: 1 }, // 12: left_knee
    { x: 0.6, y: 0.85, confidence: 1 }, // 13: left_ankle
    { x: 0.45, y: 0.08, confidence: 1 }, // 14: right_eye
    { x: 0.55, y: 0.08, confidence: 1 }, // 15: left_eye
    { x: 0.4, y: 0.1, confidence: 1 }, // 16: right_ear
    { x: 0.6, y: 0.1, confidence: 1 }, // 17: left_ear
  ];
}
