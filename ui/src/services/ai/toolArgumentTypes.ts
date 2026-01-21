/**
 * Tool Argument Types
 *
 * Proper TypeScript types for all AI tool call arguments.
 * Replaces Record<string, any> with type-safe discriminated unions.
 */

import type { InterpolationType, LayerType } from "@/types/project";
import type { TrajectoryType } from "@/services/cameraTrajectory";
import type { RackFocusConfig } from "@/services/cameraEnhancements";

// ============================================================================
// COMMON TYPES
// ============================================================================

export interface Vec2 {
  x: number;
  y: number;
}

export interface Vec3 {
  x: number;
  y: number;
  z: number;
}

export interface RGBA {
  r: number;
  g: number;
  b: number;
  a?: number;
}

export interface ControlPointInput {
  x: number;
  y: number;
  handleIn?: { x: number; y: number } | null;
  handleOut?: { x: number; y: number } | null;
}

// ============================================================================
// LAYER MANAGEMENT ARGUMENTS
// ============================================================================

export interface CreateLayerArgs {
  type: string;
  name?: string;
  properties?: Record<string, string | number | boolean | Vec2 | Vec3>;
  position?: Vec2;
  inPoint?: number;
  outPoint?: number;
}

export interface DeleteLayerArgs {
  layerId: string;
}

export interface DuplicateLayerArgs {
  layerId: string;
  newName?: string;
}

export interface RenameLayerArgs {
  layerId: string;
  name: string;
}

export interface SetLayerParentArgs {
  layerId: string;
  parentId?: string | null;
}

export interface ReorderLayersArgs {
  layerId: string;
  newIndex: number;
}

// ============================================================================
// PROPERTY MODIFICATION ARGUMENTS
// ============================================================================

export interface SetLayerPropertyArgs {
  layerId: string;
  propertyPath: string;
  value: string | number | boolean | Vec2 | Vec3 | null;
}

export interface SetLayerTransformArgs {
  layerId: string;
  position?: Vec2;
  scale?: Vec2;
  rotation?: number;
  opacity?: number;
  anchorPoint?: Vec2;
}

// ============================================================================
// KEYFRAME ANIMATION ARGUMENTS
// ============================================================================

export interface AddKeyframeArgs {
  layerId: string;
  propertyPath: string;
  frame: number;
  value: string | number | boolean | Vec2 | Vec3;
  interpolation?: InterpolationType;
}

export interface RemoveKeyframeArgs {
  layerId: string;
  propertyPath: string;
  frame: number;
}

export interface SetKeyframeEasingArgs {
  layerId: string;
  propertyPath: string;
  frame: number;
  interpolation: InterpolationType;
}

export interface ScaleKeyframeTimingArgs {
  layerId: string;
  scaleFactor: number;
  propertyPath?: string;
}

// ============================================================================
// EXPRESSION ARGUMENTS
// ============================================================================

export type ExpressionType =
  | "jitter"
  | "repeatAfter"
  | "repeatBefore"
  | "inertia"
  | "bounce"
  | "elastic";

export interface SetExpressionArgs {
  layerId: string;
  propertyPath: string;
  expressionType: ExpressionType;
  params?: Record<string, number | string | boolean>;
}

export interface RemoveExpressionArgs {
  layerId: string;
  propertyPath: string;
}

// ============================================================================
// EFFECT ARGUMENTS
// ============================================================================

export type EffectType =
  | "gaussianBlur"
  | "motionBlur"
  | "radialBlur"
  | "zoomBlur"
  | "brightnessContrast"
  | "hueSaturation"
  | "colorBalance"
  | "tint"
  | "glow"
  | "dropShadow"
  | "stroke"
  | "bulge"
  | "twirl"
  | "wave"
  | "displacement"
  | "gradient"
  | "fractalNoise"
  | "checkerboard";

export interface AddEffectArgs {
  layerId: string;
  effectType: EffectType;
  params?: Record<string, number | string | boolean | Vec2 | Vec3>;
}

export interface UpdateEffectArgs {
  layerId: string;
  effectId: string;
  params: Record<string, number | string | boolean | Vec2 | Vec3>;
}

export interface RemoveEffectArgs {
  layerId: string;
  effectId: string;
}

// ============================================================================
// PARTICLE SYSTEM ARGUMENTS
// ============================================================================

export interface ParticleEmitterConfig {
  type?: "point" | "line" | "box" | "circle" | "path";
  position?: Vec2;
  size?: { width: number; height: number };
  pathReference?: string;
}

export interface ParticleConfig {
  count?: number;
  lifetime?: number;
  size?: number;
  color?: RGBA;
  velocity?: Vec2;
  spread?: number;
}

export interface ParticlePhysicsConfig {
  gravity?: { x: number; y: number };
  wind?: Vec2;
  turbulence?: number;
}

export interface ConfigureParticlesArgs {
  layerId: string;
  emitter?: ParticleEmitterConfig;
  particles?: ParticleConfig;
  physics?: ParticlePhysicsConfig;
}

// ============================================================================
// CAMERA SYSTEM ARGUMENTS
// ============================================================================

export interface ApplyCameraTrajectoryArgs {
  cameraLayerId: string;
  trajectoryType: TrajectoryType;
  startFrame?: number;
  duration?: number;
  amplitude?: number;
  loops?: number;
  easing?: "linear" | "ease-in" | "ease-out" | "ease-in-out" | "bounce";
  center?: Vec3;
}

export type CameraShakeType = "handheld" | "impact" | "earthquake" | "subtle" | "custom";

export interface AddCameraShakeArgs {
  cameraLayerId: string;
  shakeType: CameraShakeType;
  intensity: number;
  frequency: number;
  startFrame?: number;
  duration?: number;
  decay?: number;
  rotationEnabled?: boolean;
  seed?: number;
}

export interface ApplyRackFocusArgs {
  cameraLayerId: string;
  startDistance: number;
  endDistance: number;
  startFrame?: number;
  duration?: number;
  easing?: RackFocusConfig["easing"];
  holdStart?: number;
  holdEnd?: number;
}

export interface SetCameraPathFollowingArgs {
  cameraLayerId: string;
  splineLayerId?: string | null;
  lookMode?: "tangent" | "target" | "fixed";
  lookTarget?: Vec3 | null;
  startOffset?: number;
  speed?: number;
  bankAmount?: number;
  smoothing?: number;
}

export interface SetCameraAutoFocusArgs {
  cameraLayerId: string;
  enabled?: boolean;
  mode?: "center" | "point" | "nearest" | "farthest" | "face";
  focusPoint?: Vec2;
  smoothing?: number;
}

// ============================================================================
// TEXT ARGUMENTS
// ============================================================================

export interface SetTextContentArgs {
  layerId: string;
  text?: string;
  fontSize?: number;
  fontFamily?: string;
  fontWeight?: string | number;
  color?: RGBA;
  alignment?: "left" | "center" | "right" | "justify";
}

export interface SetTextPathArgs {
  textLayerId: string;
  splineLayerId?: string | null;
  startOffset?: number;
}

// ============================================================================
// SPLINE ARGUMENTS
// ============================================================================

export interface SetSplinePointsArgs {
  layerId: string;
  points: ControlPointInput[];
  closed?: boolean;
}

// ============================================================================
// SPEED MAP ARGUMENTS
// ============================================================================

export interface SpeedMapKeyframe {
  frame: number;
  value: number;
}

export interface SetSpeedMapArgs {
  layerId: string;
  enabled?: boolean;
  keyframes?: SpeedMapKeyframe[];
}

// ============================================================================
// PLAYBACK ARGUMENTS
// ============================================================================

export interface SetCurrentFrameArgs {
  frame: number;
}

export interface PlayPreviewArgs {
  play: boolean;
}

// ============================================================================
// AI IMAGE PROCESSING ARGUMENTS
// ============================================================================

export interface DecomposeImageArgs {
  sourceLayerId: string;
  numLayers?: number;
}

export interface VectorizeImageTraceOptions {
  colorMode?: "color" | "grayscale" | "blackAndWhite";
  filterSpeckle?: number;
  cornerThreshold?: number;
  colorPrecision?: number;
  layerDifference?: number;
}

export interface VectorizeImageArgs {
  sourceLayerId: string;
  mode?: "trace" | "ai";
  separateLayers?: boolean;
  groupByPath?: boolean;
  autoGroupByRegion?: boolean;
  enableAnimation?: boolean;
  traceOptions?: VectorizeImageTraceOptions;
}

// ============================================================================
// UTILITY ARGUMENTS
// ============================================================================

export interface GetLayerInfoArgs {
  layerId: string;
}

export interface FindLayersArgs {
  name?: string;
  type?: LayerType;
}

export interface GetProjectStateArgs {
  // No arguments
}

// ============================================================================
// DISCRIMINATED UNION OF ALL TOOL ARGUMENTS
// ============================================================================

/**
 * Discriminated union of all tool arguments
 * Each variant includes the tool name for type-safe narrowing
 */
export type ToolArguments =
  | ({ name: "createLayer" } & CreateLayerArgs)
  | ({ name: "deleteLayer" } & DeleteLayerArgs)
  | ({ name: "duplicateLayer" } & DuplicateLayerArgs)
  | ({ name: "renameLayer" } & RenameLayerArgs)
  | ({ name: "setLayerParent" } & SetLayerParentArgs)
  | ({ name: "reorderLayers" } & ReorderLayersArgs)
  | ({ name: "setLayerProperty" } & SetLayerPropertyArgs)
  | ({ name: "setLayerTransform" } & SetLayerTransformArgs)
  | ({ name: "addKeyframe" } & AddKeyframeArgs)
  | ({ name: "removeKeyframe" } & RemoveKeyframeArgs)
  | ({ name: "setKeyframeEasing" } & SetKeyframeEasingArgs)
  | ({ name: "scaleKeyframeTiming" } & ScaleKeyframeTimingArgs)
  | ({ name: "setExpression" } & SetExpressionArgs)
  | ({ name: "removeExpression" } & RemoveExpressionArgs)
  | ({ name: "addEffect" } & AddEffectArgs)
  | ({ name: "updateEffect" } & UpdateEffectArgs)
  | ({ name: "removeEffect" } & RemoveEffectArgs)
  | ({ name: "configureParticles" } & ConfigureParticlesArgs)
  | ({ name: "applyCameraTrajectory" } & ApplyCameraTrajectoryArgs)
  | ({ name: "addCameraShake" } & AddCameraShakeArgs)
  | ({ name: "applyRackFocus" } & ApplyRackFocusArgs)
  | ({ name: "setCameraPathFollowing" } & SetCameraPathFollowingArgs)
  | ({ name: "setCameraAutoFocus" } & SetCameraAutoFocusArgs)
  | ({ name: "setTextContent" } & SetTextContentArgs)
  | ({ name: "setTextPath" } & SetTextPathArgs)
  | ({ name: "setSplinePoints" } & SetSplinePointsArgs)
  | ({ name: "setSpeedMap" } & SetSpeedMapArgs)
  | ({ name: "setTimeRemap" } & SetSpeedMapArgs)
  | ({ name: "setCurrentFrame" } & SetCurrentFrameArgs)
  | ({ name: "playPreview" } & PlayPreviewArgs)
  | ({ name: "decomposeImage" } & DecomposeImageArgs)
  | ({ name: "vectorizeImage" } & VectorizeImageArgs)
  | ({ name: "getLayerInfo" } & GetLayerInfoArgs)
  | ({ name: "findLayers" } & FindLayersArgs)
  | ({ name: "getProjectState" } & GetProjectStateArgs);

/**
 * Extract arguments type from ToolArguments based on tool name
 * This allows type-safe access to arguments without type assertions
 */
export type ToolArgumentsFor<T extends ToolArguments["name"]> = Extract<
  ToolArguments,
  { name: T }
> extends infer U
  ? U extends { name: T }
    ? Omit<U, "name">
    : never
  : never;
