/**
 * Mesh Deform Export Service
 *
 * Export functions for mesh deformation data to AI video generation tools:
 * - Wan-Move/ATI: Pin trajectories as point tracks
 * - ControlNet: Overlap pin depth maps
 * - TTM: Motion masks from deformed mesh
 */

import type { WarpPin } from "@/types/meshWarp";
import type { MeshFromAlphaResult } from "../alphaToMesh";
import { _testCalculateTriangleDepths } from "../effects/meshDeformRenderer";
import { interpolateProperty } from "../interpolation";
import type { WanMoveTrajectory } from "./wanMoveExport";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

export type DepthFormat = "uint8" | "uint16" | "float32";

export interface CompositionInfo {
  width: number;
  height: number;
  frameRate: number;
}

// ════════════════════════════════════════════════════════════════════════════
// 1. PIN TRAJECTORY EXPORT (Wan-Move / ATI)
// ════════════════════════════════════════════════════════════════════════════

/**
 * Convert animated mesh deform pins to WanMoveTrajectory format
 * Each pin becomes a trajectory point tracked across frames
 *
 * @param pins - Array of warp pins to export
 * @param frameRange - [startFrame, endFrame] inclusive
 * @param composition - Composition dimensions and frame rate
 * @returns WanMoveTrajectory compatible with Wan-Move/ATI
 */
export function exportPinsAsTrajectory(
  pins: WarpPin[],
  frameRange: [number, number],
  composition: CompositionInfo,
): WanMoveTrajectory {
  const [startFrame, endFrame] = frameRange;
  const numFrames = endFrame - startFrame + 1;
  const { width, height, frameRate } = composition;

  // Filter to pins with meaningful positions (not starch or overlap-only)
  const trackablePins = pins.filter(
    (pin) =>
      pin.type === "position" ||
      pin.type === "advanced" ||
      pin.type === "bend" ||
      pin.type === "rotation",
  );

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  for (const pin of trackablePins) {
    const track: number[][] = [];
    const vis: boolean[] = [];

    for (let f = startFrame; f <= endFrame; f++) {
      // Evaluate animated position at this frame
      const pos = interpolateProperty(pin.position, f, frameRate);

      // Clamp to composition bounds (Wan-Move expects valid pixel coords)
      const x = Math.max(0, Math.min(width - 1, pos.x));
      const y = Math.max(0, Math.min(height - 1, pos.y));

      track.push([x, y]);
      vis.push(true); // Pins are always visible (could extend for pin enable/disable)
    }

    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: {
      numPoints: trackablePins.length,
      numFrames,
      width,
      height,
      fps: frameRate,
    },
  };
}

/**
 * Export pins as trajectory with pin metadata
 * Includes pin names and types for debugging/visualization
 */
export function exportPinsAsTrajectoryWithMetadata(
  pins: WarpPin[],
  frameRange: [number, number],
  composition: CompositionInfo,
): WanMoveTrajectory & {
  pinMetadata: Array<{ id: string; name: string; type: string }>;
} {
  const trajectory = exportPinsAsTrajectory(pins, frameRange, composition);

  const trackablePins = pins.filter(
    (pin) =>
      pin.type === "position" ||
      pin.type === "advanced" ||
      pin.type === "bend" ||
      pin.type === "rotation",
  );

  return {
    ...trajectory,
    pinMetadata: trackablePins.map((pin) => ({
      id: pin.id,
      name: pin.name,
      type: pin.type,
    })),
  };
}

// ════════════════════════════════════════════════════════════════════════════
// 2. OVERLAP DEPTH EXPORT (ControlNet)
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render overlap pin influence as depth map
 * inFront values map to depth: -100 (far/black) to +100 (near/white)
 *
 * @param mesh - The generated mesh from alpha
 * @param deformedVertices - Current deformed vertex positions
 * @param pins - All warp pins (will filter to overlap pins)
 * @param frame - Current frame for animated inFront values
 * @param width - Output width
 * @param height - Output height
 * @param format - Output format: uint8 (0-255), uint16 (0-65535), or float32 (0-1)
 * @returns Depth buffer in requested format
 */
export function exportOverlapAsDepth(
  mesh: MeshFromAlphaResult,
  deformedVertices: Float32Array,
  pins: WarpPin[],
  frame: number,
  width: number,
  height: number,
  format: DepthFormat = "uint8",
): Uint8Array | Uint16Array | Float32Array {
  // Create depth buffer
  let depthBuffer: Uint8Array | Uint16Array | Float32Array;
  const pixelCount = width * height;

  switch (format) {
    case "uint16":
      depthBuffer = new Uint16Array(pixelCount);
      break;
    case "float32":
      depthBuffer = new Float32Array(pixelCount);
      break;
    default:
      depthBuffer = new Uint8Array(pixelCount);
  }

  // Initialize to far (0 depth)
  depthBuffer.fill(0);

  // Check if there are any overlap pins - if not, return empty depth buffer
  const hasOverlapPins = pins.some((p) => p.type === "overlap");
  if (!hasOverlapPins) {
    return depthBuffer;
  }

  // Get triangle depths from overlap pins
  const triangleDepths = _testCalculateTriangleDepths(
    mesh,
    deformedVertices,
    pins,
    frame,
  );

  // Rasterize each triangle with its depth value
  for (const { index: t, depth } of triangleDepths) {
    const i0 = mesh.triangles[t * 3];
    const i1 = mesh.triangles[t * 3 + 1];
    const i2 = mesh.triangles[t * 3 + 2];

    // Get deformed triangle vertices
    const ax = deformedVertices[i0 * 2];
    const ay = deformedVertices[i0 * 2 + 1];
    const bx = deformedVertices[i1 * 2];
    const by = deformedVertices[i1 * 2 + 1];
    const cx = deformedVertices[i2 * 2];
    const cy = deformedVertices[i2 * 2 + 1];

    // Convert inFront (-100..+100) to normalized depth (0..1)
    // Higher inFront = closer = higher depth value (white in MiDaS format)
    const normalizedDepth = (depth + 100) / 200;

    // Convert to output format
    let depthValue: number;
    switch (format) {
      case "uint16":
        depthValue = Math.round(normalizedDepth * 65535);
        break;
      case "float32":
        depthValue = normalizedDepth;
        break;
      default:
        depthValue = Math.round(normalizedDepth * 255);
    }

    // Rasterize triangle
    rasterizeTriangleDepth(
      depthBuffer,
      width,
      height,
      ax,
      ay,
      bx,
      by,
      cx,
      cy,
      depthValue,
    );
  }

  return depthBuffer;
}

/**
 * Rasterize a triangle into a depth buffer
 * Uses scanline algorithm with z-buffer (keep maximum depth = closest)
 */
function rasterizeTriangleDepth(
  buffer: Uint8Array | Uint16Array | Float32Array,
  width: number,
  height: number,
  ax: number,
  ay: number,
  bx: number,
  by: number,
  cx: number,
  cy: number,
  depthValue: number,
): void {
  // Calculate bounding box
  const minX = Math.max(0, Math.floor(Math.min(ax, bx, cx)));
  const maxX = Math.min(width - 1, Math.ceil(Math.max(ax, bx, cx)));
  const minY = Math.max(0, Math.floor(Math.min(ay, by, cy)));
  const maxY = Math.min(height - 1, Math.ceil(Math.max(ay, by, cy)));

  // Precompute barycentric denominator
  const denom = (by - cy) * (ax - cx) + (cx - bx) * (ay - cy);
  if (Math.abs(denom) < 0.0001) return; // Degenerate triangle

  // Scanline rasterization
  for (let y = minY; y <= maxY; y++) {
    for (let x = minX; x <= maxX; x++) {
      // Barycentric coordinates
      const w1 = ((by - cy) * (x - cx) + (cx - bx) * (y - cy)) / denom;
      const w2 = ((cy - ay) * (x - cx) + (ax - cx) * (y - cy)) / denom;
      const w3 = 1 - w1 - w2;

      // Point inside triangle?
      if (w1 >= 0 && w2 >= 0 && w3 >= 0) {
        const idx = y * width + x;
        // Z-buffer: keep maximum (closest to camera)
        if (depthValue > buffer[idx]) {
          buffer[idx] = depthValue;
        }
      }
    }
  }
}

/**
 * Convert depth buffer to ImageData for visualization
 */
export function depthBufferToImageData(
  depthBuffer: Uint8Array | Uint16Array | Float32Array,
  width: number,
  height: number,
): ImageData {
  const imageData = new ImageData(width, height);
  const isUint16 = depthBuffer instanceof Uint16Array;
  const isFloat = depthBuffer instanceof Float32Array;

  for (let i = 0; i < width * height; i++) {
    let value: number;
    if (isFloat) {
      value = Math.round(depthBuffer[i] * 255);
    } else if (isUint16) {
      value = Math.floor(depthBuffer[i] / 256);
    } else {
      value = depthBuffer[i];
    }

    const pixelIdx = i * 4;
    imageData.data[pixelIdx] = value; // R
    imageData.data[pixelIdx + 1] = value; // G
    imageData.data[pixelIdx + 2] = value; // B
    imageData.data[pixelIdx + 3] = 255; // A
  }

  return imageData;
}

// ════════════════════════════════════════════════════════════════════════════
// 3. MOTION MASK EXPORT (TTM)
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render the deformed mesh area as a motion mask
 * White (255) where mesh triangles exist, black (0) elsewhere
 *
 * @param mesh - The generated mesh from alpha
 * @param deformedVertices - Current deformed vertex positions
 * @param width - Output width
 * @param height - Output height
 * @returns ImageData with white mesh area on black background
 */
export function exportDeformedMeshMask(
  mesh: MeshFromAlphaResult,
  deformedVertices: Float32Array,
  width: number,
  height: number,
): ImageData {
  const imageData = new ImageData(width, height);

  // Initialize to black (transparent)
  // ImageData is already initialized to 0, so we just need to set alpha
  for (let i = 3; i < imageData.data.length; i += 4) {
    imageData.data[i] = 255; // Full alpha for black background
  }

  // Rasterize each triangle as white
  for (let t = 0; t < mesh.triangleCount; t++) {
    const i0 = mesh.triangles[t * 3];
    const i1 = mesh.triangles[t * 3 + 1];
    const i2 = mesh.triangles[t * 3 + 2];

    const ax = deformedVertices[i0 * 2];
    const ay = deformedVertices[i0 * 2 + 1];
    const bx = deformedVertices[i1 * 2];
    const by = deformedVertices[i1 * 2 + 1];
    const cx = deformedVertices[i2 * 2];
    const cy = deformedVertices[i2 * 2 + 1];

    rasterizeTriangleMask(imageData, width, height, ax, ay, bx, by, cx, cy);
  }

  return imageData;
}

/**
 * Rasterize a triangle as white pixels in ImageData
 */
function rasterizeTriangleMask(
  imageData: ImageData,
  width: number,
  height: number,
  ax: number,
  ay: number,
  bx: number,
  by: number,
  cx: number,
  cy: number,
): void {
  // Calculate bounding box
  const minX = Math.max(0, Math.floor(Math.min(ax, bx, cx)));
  const maxX = Math.min(width - 1, Math.ceil(Math.max(ax, bx, cx)));
  const minY = Math.max(0, Math.floor(Math.min(ay, by, cy)));
  const maxY = Math.min(height - 1, Math.ceil(Math.max(ay, by, cy)));

  // Precompute barycentric denominator
  const denom = (by - cy) * (ax - cx) + (cx - bx) * (ay - cy);
  if (Math.abs(denom) < 0.0001) return; // Degenerate triangle

  // Scanline rasterization
  for (let y = minY; y <= maxY; y++) {
    for (let x = minX; x <= maxX; x++) {
      // Barycentric coordinates
      const w1 = ((by - cy) * (x - cx) + (cx - bx) * (y - cy)) / denom;
      const w2 = ((cy - ay) * (x - cx) + (ax - cx) * (y - cy)) / denom;
      const w3 = 1 - w1 - w2;

      // Point inside triangle?
      if (w1 >= 0 && w2 >= 0 && w3 >= 0) {
        const pixelIdx = (y * width + x) * 4;
        imageData.data[pixelIdx] = 255; // R = white
        imageData.data[pixelIdx + 1] = 255; // G = white
        imageData.data[pixelIdx + 2] = 255; // B = white
        // Alpha already set to 255
      }
    }
  }
}

/**
 * Export motion mask as raw binary (for efficient transfer)
 * Returns Uint8Array with 1 byte per pixel (0 or 255)
 */
export function exportDeformedMeshMaskBinary(
  mesh: MeshFromAlphaResult,
  deformedVertices: Float32Array,
  width: number,
  height: number,
): Uint8Array {
  const mask = new Uint8Array(width * height);

  for (let t = 0; t < mesh.triangleCount; t++) {
    const i0 = mesh.triangles[t * 3];
    const i1 = mesh.triangles[t * 3 + 1];
    const i2 = mesh.triangles[t * 3 + 2];

    const ax = deformedVertices[i0 * 2];
    const ay = deformedVertices[i0 * 2 + 1];
    const bx = deformedVertices[i1 * 2];
    const by = deformedVertices[i1 * 2 + 1];
    const cx = deformedVertices[i2 * 2];
    const cy = deformedVertices[i2 * 2 + 1];

    rasterizeTriangleBinaryMask(mask, width, height, ax, ay, bx, by, cx, cy);
  }

  return mask;
}

/**
 * Rasterize triangle to binary mask (1 byte per pixel)
 */
function rasterizeTriangleBinaryMask(
  mask: Uint8Array,
  width: number,
  height: number,
  ax: number,
  ay: number,
  bx: number,
  by: number,
  cx: number,
  cy: number,
): void {
  const minX = Math.max(0, Math.floor(Math.min(ax, bx, cx)));
  const maxX = Math.min(width - 1, Math.ceil(Math.max(ax, bx, cx)));
  const minY = Math.max(0, Math.floor(Math.min(ay, by, cy)));
  const maxY = Math.min(height - 1, Math.ceil(Math.max(ay, by, cy)));

  const denom = (by - cy) * (ax - cx) + (cx - bx) * (ay - cy);
  if (Math.abs(denom) < 0.0001) return;

  for (let y = minY; y <= maxY; y++) {
    for (let x = minX; x <= maxX; x++) {
      const w1 = ((by - cy) * (x - cx) + (cx - bx) * (y - cy)) / denom;
      const w2 = ((cy - ay) * (x - cx) + (ax - cx) * (y - cy)) / denom;
      const w3 = 1 - w1 - w2;

      if (w1 >= 0 && w2 >= 0 && w3 >= 0) {
        mask[y * width + x] = 255;
      }
    }
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                              // batch // export // utilities
// ════════════════════════════════════════════════════════════════════════════

/**
 * Export trajectory for a frame range as separate per-frame data
 * Useful for debugging or frame-by-frame export
 */
export function exportPinPositionsPerFrame(
  pins: WarpPin[],
  frameRange: [number, number],
  frameRate: number,
): Array<{
  frame: number;
  positions: Array<{ id: string; x: number; y: number }>;
}> {
  const [startFrame, endFrame] = frameRange;
  const result: Array<{
    frame: number;
    positions: Array<{ id: string; x: number; y: number }>;
  }> = [];

  const trackablePins = pins.filter(
    (pin) =>
      pin.type === "position" ||
      pin.type === "advanced" ||
      pin.type === "bend" ||
      pin.type === "rotation",
  );

  for (let f = startFrame; f <= endFrame; f++) {
    const positions = trackablePins.map((pin) => {
      const pos = interpolateProperty(pin.position, f, frameRate);
      return { id: pin.id, x: pos.x, y: pos.y };
    });
    result.push({ frame: f, positions });
  }

  return result;
}

/**
 * Export depth maps for a frame range
 */
export function exportOverlapDepthSequence(
  mesh: MeshFromAlphaResult,
  deformedVerticesPerFrame: Float32Array[],
  pins: WarpPin[],
  frameRange: [number, number],
  width: number,
  height: number,
  format: DepthFormat = "uint8",
): Array<{ frame: number; depth: Uint8Array | Uint16Array | Float32Array }> {
  const [startFrame, endFrame] = frameRange;
  const result: Array<{
    frame: number;
    depth: Uint8Array | Uint16Array | Float32Array;
  }> = [];

  for (let f = startFrame; f <= endFrame; f++) {
    const frameIndex = f - startFrame;
    const deformedVertices = deformedVerticesPerFrame[frameIndex];

    if (deformedVertices) {
      const depth = exportOverlapAsDepth(
        mesh,
        deformedVertices,
        pins,
        f,
        width,
        height,
        format,
      );
      result.push({ frame: f, depth });
    }
  }

  return result;
}

/**
 * Export motion masks for a frame range
 */
export function exportMeshMaskSequence(
  mesh: MeshFromAlphaResult,
  deformedVerticesPerFrame: Float32Array[],
  frameRange: [number, number],
  width: number,
  height: number,
): Array<{ frame: number; mask: ImageData }> {
  const [startFrame, endFrame] = frameRange;
  const result: Array<{ frame: number; mask: ImageData }> = [];

  for (let f = startFrame; f <= endFrame; f++) {
    const frameIndex = f - startFrame;
    const deformedVertices = deformedVerticesPerFrame[frameIndex];

    if (deformedVertices) {
      const mask = exportDeformedMeshMask(
        mesh,
        deformedVertices,
        width,
        height,
      );
      result.push({ frame: f, mask });
    }
  }

  return result;
}
