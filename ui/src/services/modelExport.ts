/**
 * Model Export Service
 *
 * Exports compositor data in formats compatible with:
 * - Light-X (relighting + camera)
 * - TTM (Time-to-Move - cut-and-drag motion)
 * - Wan-Move (point trajectories)
 * - ATI (Any Trajectory Instruction)
 * - camera-comfyUI (4x4 matrices)
 */

import * as THREE from 'three';
import type { Camera3D } from '@/types/camera';
import type { Layer, ControlPoint, SplineData } from '@/types/project';
import { interpolateProperty } from './interpolation';

// ============================================================================
// CAMERA MATRIX EXPORT (camera-comfyUI compatible)
// ============================================================================

/**
 * Camera pose as 4x4 transformation matrix
 * Format: [R|t] where R is 3x3 rotation, t is 3x1 translation
 */
export interface CameraMatrix4x4 {
  frame: number;
  matrix: number[][]; // 4x4 row-major
}

/**
 * Convert Camera3D to 4x4 transformation matrix
 * Uses Three.js for proper matrix computation
 */
export function camera3DToMatrix4x4(camera: Camera3D): number[][] {
  // Create Three.js objects for proper matrix computation
  const position = new THREE.Vector3(
    camera.position.x,
    camera.position.y,
    camera.position.z
  );

  // Combine all rotations (orientation + individual axes)
  const euler = new THREE.Euler(
    THREE.MathUtils.degToRad(camera.orientation.x + camera.xRotation),
    THREE.MathUtils.degToRad(camera.orientation.y + camera.yRotation),
    THREE.MathUtils.degToRad(camera.orientation.z + camera.zRotation),
    'XYZ'
  );

  const quaternion = new THREE.Quaternion().setFromEuler(euler);
  const scale = new THREE.Vector3(1, 1, 1);

  // Compose the matrix
  const matrix = new THREE.Matrix4();
  matrix.compose(position, quaternion, scale);

  // Convert to 4x4 array (row-major for compatibility)
  const elements = matrix.elements;
  return [
    [elements[0], elements[4], elements[8], elements[12]],
    [elements[1], elements[5], elements[9], elements[13]],
    [elements[2], elements[6], elements[10], elements[14]],
    [elements[3], elements[7], elements[11], elements[15]]
  ];
}

/**
 * Export camera trajectory as sequence of 4x4 matrices
 * Compatible with camera-comfyUI
 */
export interface CameraTrajectoryExport {
  matrices: number[][][]; // [frame][4][4]
  metadata: {
    frameCount: number;
    fps: number;
    fov: number;
    nearClip: number;
    farClip: number;
    width: number;
    height: number;
  };
}

export function exportCameraTrajectory(
  cameras: Camera3D[],  // One per frame (interpolated)
  fps: number,
  width: number,
  height: number
): CameraTrajectoryExport {
  const matrices = cameras.map(cam => camera3DToMatrix4x4(cam));

  return {
    matrices,
    metadata: {
      frameCount: cameras.length,
      fps,
      fov: cameras[0]?.angleOfView ?? 39.6,
      nearClip: cameras[0]?.nearClip ?? 1,
      farClip: cameras[0]?.farClip ?? 10000,
      width,
      height
    }
  };
}

// ============================================================================
// TRAJECTORY EXPORT (Wan-Move / ATI compatible)
// ============================================================================

/**
 * Point trajectory format for Wan-Move
 * Each trajectory is a sequence of (x, y, z) positions over frames
 * Extended with rotation and scale for 3D model compatibility
 */
export interface PointTrajectory {
  id: string;
  points: Array<{ frame: number; x: number; y: number; z?: number }>;
  visibility: boolean[]; // Per-frame visibility
  // Extended properties for 3D exports
  rotation?: Array<{ frame: number; x: number; y: number; z: number }>; // Euler degrees
  scale?: Array<{ frame: number; x: number; y: number }>;
}

/**
 * Full trajectory export for Wan-Move
 * Format matches their expected NumPy array structure
 */
export interface WanMoveTrajectoryExport {
  // Shape: [num_points, num_frames, 2] for 2D coordinates
  // Shape: [num_points, num_frames, 3] for 3D coordinates
  trajectories: number[][][];
  // Shape: [num_points, num_frames] for visibility
  visibility: number[][];
  // Extended: rotation [num_points, num_frames, 3] (optional)
  rotations?: number[][][];
  // Extended: scale [num_points, num_frames, 2] (optional)
  scales?: number[][][];
  metadata: {
    numPoints: number;
    numFrames: number;
    imageWidth: number;
    imageHeight: number;
    is3D: boolean;
    hasRotation: boolean;
    hasScale: boolean;
  };
}

/**
 * Particle trajectory export format
 * Each particle's position over its lifetime
 */
export interface ParticleTrajectoryExport {
  // Per-particle data
  particles: Array<{
    id: number;
    birthFrame: number;
    deathFrame: number;
    // Position at each frame of its lifetime [frame, x, y, z]
    positions: Array<{ frame: number; x: number; y: number; z: number }>;
    // Optional velocity data
    velocities?: Array<{ frame: number; vx: number; vy: number; vz: number }>;
    // Particle properties
    size?: number[];
    opacity?: number[];
    color?: Array<{ r: number; g: number; b: number }>;
  }>;
  // Emitter configuration
  emitterConfig: {
    type: string;
    position: { x: number; y: number; z: number };
    rate: number;
    lifetime: number;
  };
  metadata: {
    totalParticles: number;
    frameCount: number;
    maxActiveParticles: number;
  };
}

/**
 * Extended position getter that includes Z position
 */
export interface Position3D {
  x: number;
  y: number;
  z?: number;
}

/**
 * Extended transform getter for full 3D data
 */
export interface TransformAtFrame {
  position: Position3D;
  rotation?: { x: number; y: number; z: number };
  scale?: { x: number; y: number };
}

/**
 * Extract point trajectories from layer position animation
 * Now includes Z position, rotation, and scale for 3D model compatibility
 */
export function extractLayerTrajectory(
  layer: Layer,
  startFrame: number,
  endFrame: number,
  getPositionAtFrame: (layer: Layer, frame: number) => { x: number; y: number },
  // Optional extended getter for full 3D transform data
  getTransformAtFrame?: (layer: Layer, frame: number) => TransformAtFrame
): PointTrajectory {
  const points: Array<{ frame: number; x: number; y: number; z?: number }> = [];
  const visibility: boolean[] = [];
  const rotation: Array<{ frame: number; x: number; y: number; z: number }> = [];
  const scale: Array<{ frame: number; x: number; y: number }> = [];

  for (let frame = startFrame; frame <= endFrame; frame++) {
    const layerStart = layer.startFrame ?? layer.inPoint ?? 0;
    const layerEnd = layer.endFrame ?? layer.outPoint ?? 80;
    const inRange = frame >= layerStart && frame <= layerEnd;
    visibility.push(inRange && layer.visible);

    if (getTransformAtFrame) {
      // Use extended transform getter for full 3D data
      const transform = getTransformAtFrame(layer, frame);
      points.push({
        frame,
        x: transform.position.x,
        y: transform.position.y,
        z: transform.position.z
      });

      if (transform.rotation) {
        rotation.push({
          frame,
          x: transform.rotation.x,
          y: transform.rotation.y,
          z: transform.rotation.z
        });
      }

      if (transform.scale) {
        scale.push({
          frame,
          x: transform.scale.x,
          y: transform.scale.y
        });
      }
    } else {
      // Fallback to basic 2D position
      const pos = getPositionAtFrame(layer, frame);
      points.push({ frame, x: pos.x, y: pos.y });
    }
  }

  const result: PointTrajectory = {
    id: layer.id,
    points,
    visibility
  };

  // Only include rotation/scale if we have data
  if (rotation.length > 0) {
    result.rotation = rotation;
  }
  if (scale.length > 0) {
    result.scale = scale;
  }

  return result;
}

/**
 * Extract trajectories from spline control points
 * Supports both static and animated control points
 */
export function extractSplineTrajectories(
  splineData: SplineData,
  startFrame: number,
  endFrame: number
): PointTrajectory[] {
  const frameCount = endFrame - startFrame + 1;

  // Check if using animated control points
  if (splineData.animated && splineData.animatedControlPoints?.length) {
    return splineData.animatedControlPoints.map(acp => {
      const points: Array<{ frame: number; x: number; y: number }> = [];

      for (let i = 0; i < frameCount; i++) {
        const frame = startFrame + i;
        // Interpolate x and y at this frame
        const x = interpolateProperty(acp.x, frame);
        const y = interpolateProperty(acp.y, frame);
        points.push({ frame, x, y });
      }

      return {
        id: acp.id,
        points,
        visibility: Array(frameCount).fill(true)
      };
    });
  }

  // Fall back to static control points
  return splineData.controlPoints.map(cp => ({
    id: cp.id,
    points: Array.from({ length: frameCount }, (_, i) => ({
      frame: startFrame + i,
      x: cp.x,
      y: cp.y
    })),
    visibility: Array(frameCount).fill(true)
  }));
}

/**
 * Export trajectories in Wan-Move format
 * Now supports 3D positions, rotation, and scale data
 */
export function exportWanMoveTrajectories(
  trajectories: PointTrajectory[],
  imageWidth: number,
  imageHeight: number,
  options?: { include3D?: boolean; includeRotation?: boolean; includeScale?: boolean }
): WanMoveTrajectoryExport {
  const opts = { include3D: true, includeRotation: true, includeScale: true, ...options };

  if (trajectories.length === 0) {
    return {
      trajectories: [],
      visibility: [],
      metadata: {
        numPoints: 0,
        numFrames: 0,
        imageWidth,
        imageHeight,
        is3D: false,
        hasRotation: false,
        hasScale: false
      }
    };
  }

  const numFrames = trajectories[0].points.length;

  // Check if any trajectory has 3D data
  const has3D = trajectories.some(t => t.points.some(p => p.z !== undefined));
  const hasRotation = trajectories.some(t => t.rotation && t.rotation.length > 0);
  const hasScale = trajectories.some(t => t.scale && t.scale.length > 0);

  // Convert to [num_points, num_frames, 2 or 3] format
  const trajArray = trajectories.map(traj =>
    traj.points.map(pt =>
      (opts.include3D && has3D) ? [pt.x, pt.y, pt.z ?? 0] : [pt.x, pt.y]
    )
  );

  // Convert visibility to [num_points, num_frames] format (1 or 0)
  const visArray = trajectories.map(traj =>
    traj.visibility.map(v => v ? 1 : 0)
  );

  const result: WanMoveTrajectoryExport = {
    trajectories: trajArray,
    visibility: visArray,
    metadata: {
      numPoints: trajectories.length,
      numFrames,
      imageWidth,
      imageHeight,
      is3D: opts.include3D && has3D,
      hasRotation: opts.includeRotation && hasRotation,
      hasScale: opts.includeScale && hasScale
    }
  };

  // Add rotation data if present
  if (opts.includeRotation && hasRotation) {
    result.rotations = trajectories.map(traj =>
      traj.rotation
        ? traj.rotation.map(r => [r.x, r.y, r.z])
        : Array(numFrames).fill([0, 0, 0])
    );
  }

  // Add scale data if present
  if (opts.includeScale && hasScale) {
    result.scales = trajectories.map(traj =>
      traj.scale
        ? traj.scale.map(s => [s.x, s.y])
        : Array(numFrames).fill([1, 1])
    );
  }

  return result;
}

// ============================================================================
// ATI TRAJECTORY EXPORT
// ============================================================================

/**
 * ATI trajectory instruction types
 */
export type ATITrajectoryType = 'free' | 'circular' | 'static' | 'pan';

export interface ATITrajectoryInstruction {
  type: ATITrajectoryType;
  points?: Array<{ x: number; y: number }>; // For free trajectories
  center?: { x: number; y: number }; // For circular
  radius?: number;
  panSpeed?: { x: number; y: number }; // Pixels per frame
}

/**
 * Calculate pan speed from position animation
 */
export function calculatePanSpeed(
  layer: Layer,
  startFrame: number,
  endFrame: number,
  getPositionAtFrame: (layer: Layer, frame: number) => { x: number; y: number }
): { x: number; y: number } {
  if (endFrame <= startFrame) return { x: 0, y: 0 };

  const startPos = getPositionAtFrame(layer, startFrame);
  const endPos = getPositionAtFrame(layer, endFrame);
  const frameCount = endFrame - startFrame;

  return {
    x: (endPos.x - startPos.x) / frameCount,
    y: (endPos.y - startPos.y) / frameCount
  };
}

/**
 * Export trajectory in ATI format
 */
export function exportATITrajectory(
  trajectory: PointTrajectory,
  imageWidth: number,
  imageHeight: number
): ATITrajectoryInstruction {
  const points = trajectory.points;

  if (points.length < 2) {
    return { type: 'static' };
  }

  // Check if it's a linear pan (constant velocity)
  const dx = points[points.length - 1].x - points[0].x;
  const dy = points[points.length - 1].y - points[0].y;
  const frameCount = points.length - 1;

  // Calculate variance to detect linear motion
  let isLinear = true;
  const expectedDxPerFrame = dx / frameCount;
  const expectedDyPerFrame = dy / frameCount;

  for (let i = 1; i < points.length; i++) {
    const actualDx = points[i].x - points[i - 1].x;
    const actualDy = points[i].y - points[i - 1].y;

    if (Math.abs(actualDx - expectedDxPerFrame) > 1 ||
        Math.abs(actualDy - expectedDyPerFrame) > 1) {
      isLinear = false;
      break;
    }
  }

  if (isLinear && (Math.abs(dx) > 5 || Math.abs(dy) > 5)) {
    return {
      type: 'pan',
      panSpeed: {
        x: expectedDxPerFrame,
        y: expectedDyPerFrame
      }
    };
  }

  // Otherwise, export as free trajectory
  return {
    type: 'free',
    points: points.map(p => ({ x: p.x, y: p.y }))
  };
}

// ============================================================================
// TTM (Time-to-Move) EXPORT
// ============================================================================

/**
 * Per-layer TTM export data
 * Each animated layer gets its own mask and trajectory
 */
export interface TTMLayerExport {
  layerId: string;
  layerName: string;
  // Binary motion mask for this layer (white = this layer's region)
  motionMask: string; // Base64 PNG
  // Trajectory for this layer's movement
  trajectory: Array<{ frame: number; x: number; y: number }>;
  // Per-frame visibility
  visibility: boolean[];
}

/**
 * TTM export format - supports multiple animated layers
 * Each layer becomes a separate mask + trajectory pair
 */
export interface TTMExport {
  // Reference image (base64 or path)
  referenceImage: string;

  // Last frame for temporal context
  lastFrame?: string;

  // Per-layer motion data (MULTI-LAYER SUPPORT)
  layers: TTMLayerExport[];

  // Combined motion mask (all layers combined, for single-mask workflows)
  combinedMotionMask: string; // Base64 PNG

  // Model-specific params
  modelConfig: {
    model: 'wan' | 'cogvideox' | 'svd';
    tweakIndex: number;
    tstrongIndex: number;
    inferenceSteps: number;
  };

  // Metadata
  metadata: {
    layerCount: number;
    frameCount: number;
    width: number;
    height: number;
  };
}

/**
 * Legacy single-layer TTM export (backwards compatibility)
 */
export interface TTMSingleLayerExport {
  referenceImage: string;
  motionMask: string;
  trajectory: Array<{ x: number; y: number }>;
  modelConfig: {
    model: 'wan' | 'cogvideox' | 'svd';
    tweakIndex: number;
    tstrongIndex: number;
    inferenceSteps: number;
  };
}

/**
 * Generate motion mask from layer bounds
 * Returns ImageData with white = motion region, black = static
 */
export function generateMotionMask(
  layer: Layer,
  compWidth: number,
  compHeight: number,
  getLayerBounds: (layer: Layer, frame: number) => { x: number; y: number; width: number; height: number }
): ImageData {
  // Create canvas for mask
  const canvas = document.createElement('canvas');
  canvas.width = compWidth;
  canvas.height = compHeight;
  const ctx = canvas.getContext('2d')!;

  // Fill with black (static region)
  ctx.fillStyle = 'black';
  ctx.fillRect(0, 0, compWidth, compHeight);

  // Draw white rectangle for layer bounds (motion region)
  const layerStart = layer.startFrame ?? layer.inPoint ?? 0;
  const bounds = getLayerBounds(layer, layerStart);
  ctx.fillStyle = 'white';
  ctx.fillRect(bounds.x, bounds.y, bounds.width, bounds.height);

  return ctx.getImageData(0, 0, compWidth, compHeight);
}

/**
 * Generate combined motion mask from multiple layers
 * Each layer's region is drawn in white on black background
 */
export function generateCombinedMotionMask(
  layers: Layer[],
  compWidth: number,
  compHeight: number,
  getLayerBounds: (layer: Layer, frame: number) => { x: number; y: number; width: number; height: number }
): ImageData {
  const canvas = document.createElement('canvas');
  canvas.width = compWidth;
  canvas.height = compHeight;
  const ctx = canvas.getContext('2d')!;

  // Fill with black (static region)
  ctx.fillStyle = 'black';
  ctx.fillRect(0, 0, compWidth, compHeight);

  // Draw each layer's bounds in white
  ctx.fillStyle = 'white';
  for (const layer of layers) {
    const layerStartFrame = layer.startFrame ?? layer.inPoint ?? 0;
    const bounds = getLayerBounds(layer, layerStartFrame);
    ctx.fillRect(bounds.x, bounds.y, bounds.width, bounds.height);
  }

  return ctx.getImageData(0, 0, compWidth, compHeight);
}

/**
 * Convert ImageData to base64 PNG
 */
export function imageDataToBase64(imageData: ImageData): string {
  const canvas = document.createElement('canvas');
  canvas.width = imageData.width;
  canvas.height = imageData.height;
  const ctx = canvas.getContext('2d')!;
  ctx.putImageData(imageData, 0, 0);
  return canvas.toDataURL('image/png');
}

/**
 * Export TTM data for a single layer
 */
export function exportTTMLayer(
  layer: Layer,
  startFrame: number,
  endFrame: number,
  compWidth: number,
  compHeight: number,
  getPositionAtFrame: (layer: Layer, frame: number) => { x: number; y: number },
  getLayerBounds: (layer: Layer, frame: number) => { x: number; y: number; width: number; height: number }
): TTMLayerExport {
  // Generate mask for this layer
  const maskData = generateMotionMask(layer, compWidth, compHeight, getLayerBounds);
  const maskBase64 = imageDataToBase64(maskData);

  // Extract trajectory
  const trajectory = extractLayerTrajectory(layer, startFrame, endFrame, getPositionAtFrame);

  return {
    layerId: layer.id,
    layerName: layer.name,
    motionMask: maskBase64,
    trajectory: trajectory.points,
    visibility: trajectory.visibility
  };
}

// ============================================================================
// LIGHT-X EXPORT
// ============================================================================

/**
 * Light-X camera motion types
 */
export type LightXMotionStyle = 'gradual' | 'bullet' | 'direct' | 'dolly-zoom';

/**
 * Light-X relighting source types
 */
export type LightXRelightSource = 'text' | 'reference' | 'hdr' | 'background';

export interface LightXExport {
  // Camera trajectory
  cameraTrajectory: CameraTrajectoryExport;

  // Motion style
  motionStyle: LightXMotionStyle;

  // Relighting configuration
  relighting: {
    source: LightXRelightSource;
    textPrompt?: string;
    referenceImage?: string; // Base64
    hdrMap?: string; // Base64 or path
    backgroundColor?: string; // Hex
  };
}

/**
 * Detect motion style from camera animation
 */
export function detectMotionStyle(
  cameras: Camera3D[]
): LightXMotionStyle {
  if (cameras.length < 2) return 'static' as any;

  const first = cameras[0];
  const last = cameras[cameras.length - 1];

  // Check for dolly zoom (position changes while FOV changes)
  const positionChange = Math.sqrt(
    Math.pow(last.position.z - first.position.z, 2)
  );
  const fovChange = Math.abs(last.angleOfView - first.angleOfView);

  if (positionChange > 100 && fovChange > 5) {
    return 'dolly-zoom';
  }

  // Check for bullet time (orbit around POI)
  const yRotationChange = Math.abs(last.yRotation - first.yRotation);
  if (yRotationChange > 45) {
    return 'bullet';
  }

  // Check for gradual (smooth linear motion)
  let isSmooth = true;
  for (let i = 1; i < cameras.length - 1; i++) {
    const prev = cameras[i - 1];
    const curr = cameras[i];
    const next = cameras[i + 1];

    // Check for acceleration changes
    const vel1 = curr.position.x - prev.position.x;
    const vel2 = next.position.x - curr.position.x;

    if (Math.abs(vel2 - vel1) > 10) {
      isSmooth = false;
      break;
    }
  }

  return isSmooth ? 'gradual' : 'direct';
}

// ============================================================================
// UNIFIED EXPORT FUNCTION
// ============================================================================

export type ModelTarget =
  | 'camera-comfyui'
  | 'wan-move'
  | 'wan-move-3d'
  | 'ati'
  | 'ttm'
  | 'light-x'
  | 'particles';

export interface UnifiedExportOptions {
  target: ModelTarget;
  layers: Layer[];
  cameras: Camera3D[];
  compWidth: number;
  compHeight: number;
  fps: number;
  startFrame: number;
  endFrame: number;

  // Callbacks for getting animated values
  getPositionAtFrame: (layer: Layer, frame: number) => { x: number; y: number };
  getLayerBounds: (layer: Layer, frame: number) => { x: number; y: number; width: number; height: number };

  // Extended callback for full 3D transform data (optional, for 3D exports)
  getTransformAtFrame?: (layer: Layer, frame: number) => TransformAtFrame;

  // TTM-specific options (Time-to-Move)
  ttmModel?: 'wan' | 'cogvideox' | 'svd';
  ttmTweakIndex?: number;       // Dual-clock denoising tweak parameter
  ttmTstrongIndex?: number;     // Dual-clock denoising tstrong parameter
  ttmInferenceSteps?: number;   // Number of inference steps

  // Light-X options
  lightXRelighting?: LightXExport['relighting'];

  // Particle export options
  particleData?: ParticleTrajectoryExport;
}

export interface UnifiedExportResult {
  success: boolean;
  target: ModelTarget;
  data: any;
  files: {
    name: string;
    content: string | Blob;
    type: 'json' | 'npy' | 'png' | 'tensor';
  }[];
  error?: string;  // Error message if success is false
}

/**
 * Export compositor data for a specific model
 */
export async function exportForModel(
  options: UnifiedExportOptions
): Promise<UnifiedExportResult> {
  const { target, layers, cameras, compWidth, compHeight, fps, startFrame, endFrame } = options;

  switch (target) {
    case 'camera-comfyui': {
      const trajectory = exportCameraTrajectory(cameras, fps, compWidth, compHeight);
      return {
        success: true,
        target,
        data: trajectory,
        files: [{
          name: 'camera_trajectory.json',
          content: JSON.stringify(trajectory, null, 2),
          type: 'json'
        }]
      };
    }

    case 'wan-move': {
      // Extract trajectories from animated layers
      const trajectories: PointTrajectory[] = [];
      for (const layer of layers) {
        if (layer.transform.position.animated) {
          trajectories.push(
            extractLayerTrajectory(layer, startFrame, endFrame, options.getPositionAtFrame)
          );
        }
      }

      const wanMoveData = exportWanMoveTrajectories(trajectories, compWidth, compHeight);

      // Convert to pseudo-NPY format (JSON representation)
      // Real NPY export would require a proper binary encoder
      return {
        success: true,
        target,
        data: wanMoveData,
        files: [
          {
            name: 'trajectories.json',
            content: JSON.stringify(wanMoveData.trajectories, null, 2),
            type: 'json'
          },
          {
            name: 'visibility.json',
            content: JSON.stringify(wanMoveData.visibility, null, 2),
            type: 'json'
          },
          {
            name: 'metadata.json',
            content: JSON.stringify(wanMoveData.metadata, null, 2),
            type: 'json'
          }
        ]
      };
    }

    case 'ati': {
      // Export trajectories with pan speed calculation
      const atiInstructions: ATITrajectoryInstruction[] = [];

      for (const layer of layers) {
        if (layer.transform.position.animated) {
          const trajectory = extractLayerTrajectory(
            layer, startFrame, endFrame, options.getPositionAtFrame
          );
          atiInstructions.push(exportATITrajectory(trajectory, compWidth, compHeight));
        }
      }

      // Also export camera as trajectory if animated
      if (cameras.length > 1) {
        const camTrajectory = exportCameraTrajectory(cameras, fps, compWidth, compHeight);
        atiInstructions.push({
          type: 'circular', // Camera motion is typically orbital
          points: cameras.map(c => ({ x: c.position.x, y: c.position.y }))
        });
      }

      return {
        success: true,
        target,
        data: atiInstructions,
        files: [{
          name: 'ati_trajectories.json',
          content: JSON.stringify(atiInstructions, null, 2),
          type: 'json'
        }]
      };
    }

    case 'ttm': {
      // MULTI-LAYER SUPPORT: Find ALL animated layers, not just the first
      const animatedLayers = layers.filter(l => l.transform.position.animated);

      if (animatedLayers.length === 0) {
        return {
          success: false,
          target,
          data: null,
          files: [],
          error: 'No animated layers found for TTM export'
        };
      }

      // Export each layer separately
      const layerExports: TTMLayerExport[] = animatedLayers.map(layer =>
        exportTTMLayer(
          layer,
          startFrame,
          endFrame,
          compWidth,
          compHeight,
          options.getPositionAtFrame,
          options.getLayerBounds
        )
      );

      // Generate combined motion mask (all layers in one image)
      const combinedMaskData = generateCombinedMotionMask(
        animatedLayers, compWidth, compHeight, options.getLayerBounds
      );
      const combinedMaskBase64 = imageDataToBase64(combinedMaskData);

      const frameCount = endFrame - startFrame + 1;

      const ttmExport: TTMExport = {
        referenceImage: '', // Filled by caller/export pipeline
        lastFrame: '', // Filled by caller/export pipeline
        layers: layerExports,
        combinedMotionMask: combinedMaskBase64,
        modelConfig: {
          model: options.ttmModel || 'wan',
          tweakIndex: options.ttmTweakIndex ?? 10,
          tstrongIndex: options.ttmTstrongIndex ?? 20,
          inferenceSteps: options.ttmInferenceSteps ?? 50
        },
        metadata: {
          layerCount: animatedLayers.length,
          frameCount,
          width: compWidth,
          height: compHeight
        }
      };

      // Generate file outputs
      const files: UnifiedExportResult['files'] = [
        {
          name: 'ttm_config.json',
          content: JSON.stringify(ttmExport, null, 2),
          type: 'json' as const
        },
        {
          name: 'combined_motion_mask.png',
          content: combinedMaskBase64,
          type: 'png' as const
        }
      ];

      // Add per-layer mask files
      layerExports.forEach((layerExport, index) => {
        files.push({
          name: `layer_${index}_${layerExport.layerId}_mask.png`,
          content: layerExport.motionMask,
          type: 'png' as const
        });
        files.push({
          name: `layer_${index}_${layerExport.layerId}_trajectory.json`,
          content: JSON.stringify({
            layerId: layerExport.layerId,
            layerName: layerExport.layerName,
            trajectory: layerExport.trajectory,
            visibility: layerExport.visibility
          }, null, 2),
          type: 'json' as const
        });
      });

      return {
        success: true,
        target,
        data: ttmExport,
        files
      };
    }

    case 'light-x': {
      const cameraTrajectory = exportCameraTrajectory(cameras, fps, compWidth, compHeight);
      const motionStyle = detectMotionStyle(cameras);

      const lightXExport: LightXExport = {
        cameraTrajectory,
        motionStyle,
        relighting: options.lightXRelighting || {
          source: 'text',
          textPrompt: 'natural lighting'
        }
      };

      return {
        success: true,
        target,
        data: lightXExport,
        files: [
          {
            name: 'lightx_config.json',
            content: JSON.stringify(lightXExport, null, 2),
            type: 'json'
          },
          {
            name: 'camera_matrices.json',
            content: JSON.stringify(cameraTrajectory.matrices, null, 2),
            type: 'json'
          }
        ]
      };
    }

    case 'wan-move-3d': {
      // Extract trajectories with full 3D transform data
      const trajectories: PointTrajectory[] = [];
      for (const layer of layers) {
        if (layer.transform.position.animated ||
            layer.transform.rotation.animated ||
            layer.transform.scale.animated) {
          trajectories.push(
            extractLayerTrajectory(
              layer,
              startFrame,
              endFrame,
              options.getPositionAtFrame,
              options.getTransformAtFrame
            )
          );
        }
      }

      const wanMove3DData = exportWanMoveTrajectories(
        trajectories,
        compWidth,
        compHeight,
        { include3D: true, includeRotation: true, includeScale: true }
      );

      // Build files including rotation/scale if present
      const files: UnifiedExportResult['files'] = [
        {
          name: 'trajectories_3d.json',
          content: JSON.stringify(wanMove3DData.trajectories, null, 2),
          type: 'json'
        },
        {
          name: 'visibility.json',
          content: JSON.stringify(wanMove3DData.visibility, null, 2),
          type: 'json'
        },
        {
          name: 'metadata.json',
          content: JSON.stringify(wanMove3DData.metadata, null, 2),
          type: 'json'
        }
      ];

      if (wanMove3DData.rotations) {
        files.push({
          name: 'rotations.json',
          content: JSON.stringify(wanMove3DData.rotations, null, 2),
          type: 'json'
        });
      }

      if (wanMove3DData.scales) {
        files.push({
          name: 'scales.json',
          content: JSON.stringify(wanMove3DData.scales, null, 2),
          type: 'json'
        });
      }

      // Also add NPY binary for trajectories
      files.push({
        name: 'trajectories.npy',
        content: trajectoriesToNpy(wanMove3DData.trajectories),
        type: 'npy'
      });

      return {
        success: true,
        target,
        data: wanMove3DData,
        files
      };
    }

    case 'particles': {
      // Export particle trajectory data
      if (!options.particleData) {
        return {
          success: false,
          target,
          data: null,
          files: [],
          error: 'No particle data provided for export'
        };
      }

      const particleData = options.particleData;

      // Create JSON export
      const files: UnifiedExportResult['files'] = [
        {
          name: 'particles.json',
          content: JSON.stringify(particleData, null, 2),
          type: 'json'
        },
        {
          name: 'particle_metadata.json',
          content: JSON.stringify(particleData.metadata, null, 2),
          type: 'json'
        },
        {
          name: 'emitter_config.json',
          content: JSON.stringify(particleData.emitterConfig, null, 2),
          type: 'json'
        }
      ];

      // Create NPY for particle positions (flatten to [total_positions, 4] where 4 = frame, x, y, z)
      const allPositions: number[][] = [];
      for (const particle of particleData.particles) {
        for (const pos of particle.positions) {
          allPositions.push([pos.frame, pos.x, pos.y, pos.z]);
        }
      }

      if (allPositions.length > 0) {
        // Create NPY header for [N, 4] float32 array
        const shape = [allPositions.length, 4];
        const header = createNpyHeader(shape, '<f4');

        // Flatten to Float32Array
        const flat = allPositions.flat();
        const data = new Float32Array(flat);
        const dataBytes = new Uint8Array(data.buffer);

        // Combine
        const result = new Uint8Array(header.length + dataBytes.length);
        result.set(header, 0);
        result.set(dataBytes, header.length);

        files.push({
          name: 'particle_positions.npy',
          content: new Blob([result], { type: 'application/octet-stream' }),
          type: 'npy'
        });
      }

      return {
        success: true,
        target,
        data: particleData,
        files
      };
    }

    default:
      return {
        success: false,
        target,
        data: null,
        files: []
      };
  }
}

// ============================================================================
// NPY BINARY EXPORT (for true Wan-Move compatibility)
// ============================================================================

/**
 * Create NPY file header for float32 array
 * NPY format: https://numpy.org/doc/stable/reference/generated/numpy.lib.format.html
 */
export function createNpyHeader(shape: number[], dtype: string = '<f4'): Uint8Array {
  const header = {
    descr: dtype,
    fortran_order: false,
    shape: shape
  };

  const headerStr = JSON.stringify(header)
    .replace(/"/g, "'")
    .replace(/: /g, ': ')
    .replace(/, /g, ', ');

  // Pad to 64-byte alignment
  const headerBytes = new TextEncoder().encode(headerStr);
  const padLen = 64 - ((10 + headerBytes.length) % 64);
  const paddedHeader = headerStr + ' '.repeat(padLen - 1) + '\n';

  // NPY magic number + version
  const magic = new Uint8Array([0x93, 0x4E, 0x55, 0x4D, 0x50, 0x59, 0x01, 0x00]);
  const headerLenBytes = new Uint8Array(2);
  new DataView(headerLenBytes.buffer).setUint16(0, paddedHeader.length, true);

  const fullHeader = new Uint8Array(magic.length + headerLenBytes.length + paddedHeader.length);
  fullHeader.set(magic, 0);
  fullHeader.set(headerLenBytes, magic.length);
  fullHeader.set(new TextEncoder().encode(paddedHeader), magic.length + 2);

  return fullHeader;
}

/**
 * Export trajectory data as NPY binary
 */
export function trajectoriesToNpy(trajectories: number[][][]): Blob {
  // Flatten the 3D array
  const flat: number[] = [];
  for (const traj of trajectories) {
    for (const point of traj) {
      flat.push(...point);
    }
  }

  const shape = [trajectories.length, trajectories[0]?.length || 0, 2];
  const header = createNpyHeader(shape, '<f4');

  // Create float32 data
  const data = new Float32Array(flat);
  const dataBytes = new Uint8Array(data.buffer);

  // Combine header and data
  const result = new Uint8Array(header.length + dataBytes.length);
  result.set(header, 0);
  result.set(dataBytes, header.length);

  return new Blob([result], { type: 'application/octet-stream' });
}

export default {
  camera3DToMatrix4x4,
  exportCameraTrajectory,
  extractLayerTrajectory,
  exportWanMoveTrajectories,
  exportATITrajectory,
  exportForModel,
  trajectoriesToNpy
};
