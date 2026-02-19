/**
 * Lattice Engine Type Definitions
 *
 * Core types for the Three.js-based rendering engine.
 * These types bridge the gap between the project schema and the rendering layer.
 */

import type * as THREE from "three";
import type { AnimatableProperty, Layer } from "@/types/project";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Engine Configuration
// ═══════════════════════════════════════════════════════════════════════════

export interface LatticeEngineConfig {
  /** Target canvas element for WebGL rendering */
  canvas: HTMLCanvasElement;

  /** Viewport width in pixels (canvas size) */
  width: number;

  /** Viewport height in pixels (canvas size) */
  height: number;

  /** Composition width in pixels (project size) */
  compositionWidth?: number;

  /** Composition height in pixels (project size) */
  compositionHeight?: number;

  /** Device pixel ratio (default: min(devicePixelRatio, 2)) */
  pixelRatio?: number;

  /** Enable antialiasing (default: true) */
  antialias?: boolean;

  /** Enable alpha/transparency (default: true) */
  alpha?: boolean;

  /** Background color (default: transparent) */
  backgroundColor?: string | null;

  /** Enable debug mode */
  debug?: boolean;

  /** Power preference for WebGL context */
  powerPreference?: "default" | "high-performance" | "low-power";
}

// ═══════════════════════════════════════════════════════════════════════════
// Render State
// ═══════════════════════════════════════════════════════════════════════════

export interface RenderState {
  /** Current frame being rendered */
  currentFrame: number;

  /** Whether the engine is actively rendering */
  isRendering: boolean;

  /** Whether the engine is disposed */
  isDisposed: boolean;

  /** Current viewport dimensions */
  viewport: {
    width: number;
    height: number;
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// Layer Instance Types
// ═══════════════════════════════════════════════════════════════════════════

export interface LayerInstance {
  /** Unique layer identifier */
  readonly id: string;

  /** Layer type */
  readonly type: string;

  /** Three.js object representing this layer */
  readonly object: THREE.Object3D;

  /** Update layer properties */
  update(properties: Partial<Layer>): void;

  /** Evaluate animated properties at frame */
  evaluateFrame(frame: number): void;

  /** Dispose layer resources */
  dispose(): void;
}

// ═══════════════════════════════════════════════════════════════════════════
// Transform Types
// ═══════════════════════════════════════════════════════════════════════════

export interface Transform3D {
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  scale: { x: number; y: number; z: number };
  origin: { x: number; y: number; z: number };
  /** @deprecated Use 'origin' instead */
  anchorPoint?: { x: number; y: number; z: number };
}

export interface EvaluatedTransform {
  position: THREE.Vector3;
  rotation: THREE.Euler;
  scale: THREE.Vector3;
  origin: THREE.Vector3;
  /** @deprecated Use 'origin' instead */
  anchorPoint?: THREE.Vector3;
}

// ═══════════════════════════════════════════════════════════════════════════
// Camera Types
// ═══════════════════════════════════════════════════════════════════════════

export interface CameraState {
  position: { x: number; y: number; z: number };
  target: { x: number; y: number; z: number };
  fov: number;
  near: number;
  far: number;
}

export interface CameraAnimationProps {
  position?: AnimatableProperty<{ x: number; y: number; z: number }>;
  target?: AnimatableProperty<{ x: number; y: number; z: number }>;
  fov?: AnimatableProperty<number>;
}

// ═══════════════════════════════════════════════════════════════════════════
// Render Target Types
// ═══════════════════════════════════════════════════════════════════════════

export interface RenderTargetConfig {
  width: number;
  height: number;
  format?: "rgba" | "rgb" | "depth" | "normal";
  type?: "uint8" | "float16" | "float32";
  samples?: number;
}

export interface CaptureResult {
  imageData: ImageData;
  width: number;
  height: number;
  format: string;
}

export interface DepthCaptureResult {
  depthBuffer: Float32Array;
  width: number;
  height: number;
  near: number;
  far: number;
}

// ═══════════════════════════════════════════════════════════════════════════
// Effect Types
// ═══════════════════════════════════════════════════════════════════════════

import type { PropertyValue } from "@/types/project";

export interface EffectConfig {
  type: string;
  enabled: boolean;
  order: number;
  parameters: Record<string, PropertyValue>;
}

export interface BlurEffectConfig extends EffectConfig {
  type: "blur";
  parameters: {
    radius: number;
    quality: "low" | "medium" | "high";
  };
}

export interface GlowEffectConfig extends EffectConfig {
  type: "glow";
  parameters: {
    intensity: number;
    radius: number;
    threshold: number;
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// Animation Types
// ═══════════════════════════════════════════════════════════════════════════

export interface KeyframeEvaluation<T> {
  value: T;
  isAnimated: boolean;
  currentKeyframe?: number;
  nextKeyframe?: number;
  progress?: number;
}

export type InterpolationFn = (t: number) => number;

// ═══════════════════════════════════════════════════════════════════════════
// Text Types
// ═══════════════════════════════════════════════════════════════════════════

export interface TextRenderConfig {
  text: string;
  fontFamily?: string;
  fontSize?: number;
  fontWeight?: string | number;
  fontStyle?: "normal" | "italic";
  color?: string | number;
  outlineWidth?: number;
  outlineColor?: string | number;
  letterSpacing?: number;
  lineHeight?: number;
  textAlign?: "left" | "center" | "right";
  maxWidth?: number;
}

export interface CharacterTransform {
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  scale: { x: number; y: number };
  opacity: number;
}

// ═══════════════════════════════════════════════════════════════════════════
// Particle Types
// ═══════════════════════════════════════════════════════════════════════════

export interface ParticleState {
  position: Float32Array; // x, y, z per particle
  velocity: Float32Array; // vx, vy, vz per particle
  color: Float32Array; // r, g, b, a per particle
  size: Float32Array; // size per particle
  age: Float32Array; // age per particle
  lifetime: Float32Array; // max lifetime per particle
}

export interface EmissionConfig {
  position: { x: number; y: number; z: number };
  direction: number;
  spread: number;
  speed: number;
  speedVariance: number;
  size: number;
  sizeVariance: number;
  color: [number, number, number];
  lifetime: number;
  lifetimeVariance: number;
}

// ═══════════════════════════════════════════════════════════════════════════
// Path Types
// ═══════════════════════════════════════════════════════════════════════════

export interface PathPoint {
  position: THREE.Vector3;
  tangent: THREE.Vector3;
  normal: THREE.Vector3;
  distance: number;
  t: number;
}

export interface PathConfig {
  points: Array<{ x: number; y: number; z: number }>;
  closed: boolean;
  tension?: number;
}

// ═══════════════════════════════════════════════════════════════════════════
// Export Types
// ═══════════════════════════════════════════════════════════════════════════

export interface ExportFrameOptions {
  frame: number;
  width?: number;
  height?: number;
  format?: "png" | "jpeg" | "webp";
  quality?: number;
  includeDepth?: boolean;
  includeNormal?: boolean;
}

export interface ExportSequenceOptions {
  startFrame: number;
  endFrame: number;
  width?: number;
  height?: number;
  format?: "png" | "jpeg" | "webp";
  quality?: number;
  onProgress?: (current: number, total: number) => void;
}

// ═══════════════════════════════════════════════════════════════════════════
// Performance Types
// ═══════════════════════════════════════════════════════════════════════════

export interface PerformanceStats {
  fps: number;
  frameTime: number;
  drawCalls: number;
  triangles: number;
  textures: number;
  geometries: number;
  memoryUsed: number;
}

export interface PerformanceConfig {
  targetFps?: number;
  maxPixelRatio?: number;
  enableFrustumCulling?: boolean;
  enableObjectPooling?: boolean;
  enableTextureCompression?: boolean;
}

// ═══════════════════════════════════════════════════════════════════════════
// Event Types
// ═══════════════════════════════════════════════════════════════════════════

export type EngineEventType =
  | "frameStart"
  | "frameEnd"
  | "layerAdded"
  | "layerRemoved"
  | "layerUpdated"
  | "resize"
  | "resolutionChange"
  | "dispose"
  | "contextLost"
  | "contextRestored"
  | "transform-dragging"
  | "transform-end";

import type { JSONValue } from "@/types/dataAsset";

export interface EngineEvent {
  type: EngineEventType;
  timestamp: number;
  data?: JSONValue;
}

export type EngineEventHandler = (event: EngineEvent) => void;

// ═══════════════════════════════════════════════════════════════════════════
// Utility Types
// ═══════════════════════════════════════════════════════════════════════════

export type Vector2Like = { x: number; y: number };
export type Vector3Like = { x: number; y: number; z?: number };
export type ColorLike = string | number | { r: number; g: number; b: number };

export interface BoundingBox2D {
  x: number;
  y: number;
  width: number;
  height: number;
}

export interface BoundingBox3D {
  min: { x: number; y: number; z: number };
  max: { x: number; y: number; z: number };
}
