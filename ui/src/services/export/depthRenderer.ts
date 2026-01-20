/**
 * Depth Map Renderer
 * Generates depth maps from compositor scene for AI video generation
 */

import { DEPTH_FORMAT_SPECS } from "@/config/exportPresets";
import type { Camera3D } from "@/types/camera";
import type { DepthMapFormat } from "@/types/export";
import type { Layer } from "@/types/project";
import type { LatticeEngine } from "@/engine/LatticeEngine";
import type { BaseLayer } from "@/engine/layers/BaseLayer";
import type { ExportedParticle } from "@/engine/particles/GPUParticleSystem";

// ============================================================================
// Types
// ============================================================================

export interface DepthRenderOptions {
  width: number;
  height: number;
  nearClip: number;
  farClip: number;
  camera: Camera3D;
  layers: Layer[];
  frame: number;
}

export interface DepthRenderResult {
  depthBuffer: Float32Array;
  width: number;
  height: number;
  minDepth: number;
  maxDepth: number;
}

// ============================================================================
// Depth Rendering
// ============================================================================

/**
 * Render depth map from compositor scene
 * Calculates depth based on layer Z positions and camera perspective
 */
export function renderDepthFrame(
  options: DepthRenderOptions,
): DepthRenderResult {
  const { width, height, nearClip, farClip, camera, layers, frame } = options;

  // Use Float32 precision for clip values to match depth buffer storage.
  // This ensures consistent min/max reporting without precision drift.
  const f32NearClip = Math.fround(nearClip);
  const f32FarClip = Math.fround(farClip);
  
  // For the depth buffer fill, we use the Float32 value
  // The returned minDepth/maxDepth will also be Float32 consistent

  // Create depth buffer
  const depthBuffer = new Float32Array(width * height);
  depthBuffer.fill(f32FarClip); // Initialize to far clip (Float32 precision)

  // Initialize min/max to opposite extremes so any real depth value updates them.
  // Handles empty scenes gracefully by keeping these values until validated below.
  let minDepth = Infinity;
  let maxDepth = -Infinity;

  // Sort layers by Z depth (front to back from camera's perspective)
  const sortedLayers = [...layers]
    .filter((l) => l.visible)
    .sort((a, b) => {
      const aZ = getLayerDepth(a, frame);
      const bZ = getLayerDepth(b, frame);
      return aZ - bZ;
    });

  // For each layer, calculate its contribution to the depth buffer
  for (const layer of sortedLayers) {
    const layerDepth = getLayerDepth(layer, frame);
    const layerOpacity = getLayerOpacity(layer, frame);

    if (layerOpacity < 0.01) continue;

    // Get layer bounds in screen space
    const bounds = getLayerScreenBounds(layer, frame, camera, width, height);

    if (!bounds) continue;

    // Calculate depth value for this layer considering camera
    const cameraZ = camera.position.z;
    const relativeDepth = Math.abs(layerDepth - cameraZ);
    // Clamp to clip range with Float32 precision for buffer consistency
    const clampedDepth = Math.fround(Math.max(f32NearClip, Math.min(f32FarClip, relativeDepth)));

    // Update min/max tracking
    minDepth = Math.min(minDepth, clampedDepth);
    maxDepth = Math.max(maxDepth, clampedDepth);

    // Fill depth buffer for layer area
    // For layers with depth maps (depthflow), use their depth data
    if (layer.type === "depthflow" && hasDepthData(layer)) {
      fillDepthFromDepthflow(
        depthBuffer,
        layer,
        bounds,
        width,
        height,
        nearClip,
        farClip,
      );
    } else if (layer.type === "particles") {
      // Particle layers - render each particle as a depth point
      fillDepthFromParticles(
        depthBuffer,
        layer,
        width,
        height,
        camera,
        frame,
        nearClip,
        farClip,
      );
    } else {
      // Solid layers get uniform depth
      fillUniformDepth(
        depthBuffer,
        bounds,
        clampedDepth,
        layerOpacity,
        width,
        height,
      );
    }
  }

  // Handle empty scene: if no layers updated min/max, default to farClip
  if (!Number.isFinite(minDepth) || !Number.isFinite(maxDepth)) {
    minDepth = f32FarClip;
    maxDepth = f32FarClip;
  }
  
  // Ensure invariant: minDepth <= maxDepth
  if (minDepth > maxDepth) {
    const temp = minDepth;
    minDepth = maxDepth;
    maxDepth = temp;
  }

  return {
    depthBuffer,
    width,
    height,
    minDepth,
    maxDepth,
  };
}

/**
 * Get layer Z depth at frame
 */
function getLayerDepth(layer: Layer, frame: number): number {
  const position = layer.transform?.position;
  if (!position) return 0;

  // Check for animated position
  if (position.keyframes && position.keyframes.length > 0) {
    // Interpolate keyframes
    return interpolateValue(position.keyframes, frame, 2) || 0;
  }

  // Static position
  if (position.value) {
    const value = position.value;
    if (typeof value === "object" && "z" in value) {
      return (value as { z?: number }).z ?? 0;
    }
  }

  // Default to 0 (on the focal plane)
  return 0;
}

/**
 * Get layer opacity at frame
 * BUG FIX: Use nullish coalescing (??) instead of || to handle 0 opacity correctly
 */
function getLayerOpacity(layer: Layer, frame: number): number {
  if (
    layer.opacity &&
    "keyframes" in layer.opacity &&
    layer.opacity.keyframes?.length > 0
  ) {
    const interpolated = interpolateValue(layer.opacity.keyframes, frame);
    return (interpolated ?? 100) / 100;
  }

  if (layer.opacity && "value" in layer.opacity) {
    // BUG FIX: 0 is a valid opacity value, don't treat it as falsy
    return (layer.opacity.value ?? 100) / 100;
  }

  return 1;
}

/**
 * Get layer bounds in screen space
 */
function getLayerScreenBounds(
  layer: Layer,
  _frame: number,
  _camera: Camera3D,
  screenWidth: number,
  screenHeight: number,
): { x: number; y: number; width: number; height: number } | null {
  // Get layer position from transform
  let x = 0,
    y = 0;

  const position = layer.transform?.position;
  if (position && "value" in position) {
    const value = position.value;
    if (Array.isArray(value)) {
      x = value[0] || 0;
      y = value[1] || 0;
    }
  }

  // Get layer dimensions (assuming they're stored or can be derived)
  const layerWithDimensions = layer as Layer & { width?: number; height?: number };
  const layerWidth = layerWithDimensions.width ?? screenWidth;
  const layerHeight = layerWithDimensions.height ?? screenHeight;

  // Get scale from transform
  let scaleX = 1,
    scaleY = 1;
  const scale = layer.transform?.scale;
  if (scale && "value" in scale) {
    const value = scale.value;
    if (Array.isArray(value)) {
      scaleX = (value[0] || 100) / 100;
      scaleY = (value[1] || 100) / 100;
    }
  }

  // Calculate screen bounds
  const finalWidth = layerWidth * scaleX;
  const finalHeight = layerHeight * scaleY;

  // Get anchor point from transform
  let anchorX = 0.5,
    anchorY = 0.5;
  const anchorPoint = layer.transform?.anchorPoint;
  if (anchorPoint && "value" in anchorPoint) {
    const value = anchorPoint.value;
    if (Array.isArray(value)) {
      anchorX = (value[0] || 0) / layerWidth + 0.5;
      anchorY = (value[1] || 0) / layerHeight + 0.5;
    }
  }

  // Convert to screen coordinates (compositor origin is center)
  const screenX = x - finalWidth * anchorX + screenWidth / 2;
  const screenY = y - finalHeight * anchorY + screenHeight / 2;

  // Clip to screen
  const clippedX = Math.max(0, Math.min(screenWidth, screenX));
  const clippedY = Math.max(0, Math.min(screenHeight, screenY));
  const clippedWidth = Math.max(
    0,
    Math.min(screenWidth - clippedX, finalWidth - (clippedX - screenX)),
  );
  const clippedHeight = Math.max(
    0,
    Math.min(screenHeight - clippedY, finalHeight - (clippedY - screenY)),
  );

  if (clippedWidth <= 0 || clippedHeight <= 0) return null;

  return {
    x: clippedX,
    y: clippedY,
    width: clippedWidth,
    height: clippedHeight,
  };
}

/**
 * Interface for depthflow layers with runtime depth data
 */
interface DepthflowLayerWithDepthData extends Layer {
  type: "depthflow";
  depthMapData?: Uint8Array | Float32Array;
  depthWidth?: number;
  depthHeight?: number;
}

/**
 * Type guard for depthflow layers with depth data
 */
function hasDepthData(layer: Layer): layer is DepthflowLayerWithDepthData {
  return layer.type === "depthflow" && "depthMapData" in layer && layer.depthMapData !== undefined;
}

/**
 * Fill depth buffer from depthflow layer's depth map
 */
function fillDepthFromDepthflow(
  depthBuffer: Float32Array,
  layer: DepthflowLayerWithDepthData,
  bounds: { x: number; y: number; width: number; height: number },
  screenWidth: number,
  screenHeight: number,
  nearClip: number,
  farClip: number,
): void {
  const depthData = layer.depthMapData;
  if (!depthData) return;
  
  const depthWidth = layer.depthWidth ?? bounds.width;
  const depthHeight = layer.depthHeight ?? bounds.height;

  for (let y = 0; y < bounds.height; y++) {
    for (let x = 0; x < bounds.width; x++) {
      const screenX = Math.floor(bounds.x + x);
      const screenY = Math.floor(bounds.y + y);

      if (
        screenX < 0 ||
        screenX >= screenWidth ||
        screenY < 0 ||
        screenY >= screenHeight
      )
        continue;

      // Sample from depth map
      const sampleX = Math.floor((x / bounds.width) * depthWidth);
      const sampleY = Math.floor((y / bounds.height) * depthHeight);
      const sampleIdx = sampleY * depthWidth + sampleX;

      let depthValue: number;
      if (depthData instanceof Float32Array) {
        depthValue = depthData[sampleIdx];
      } else {
        // Uint8 normalized to 0-1
        depthValue = depthData[sampleIdx] / 255;
      }

      // Convert normalized depth to world units
      const worldDepth = nearClip + depthValue * (farClip - nearClip);

      // Write to depth buffer (z-buffer style: keep closest)
      const bufferIdx = screenY * screenWidth + screenX;
      if (worldDepth < depthBuffer[bufferIdx]) {
        depthBuffer[bufferIdx] = worldDepth;
      }
    }
  }
}

/**
 * Fill depth buffer with uniform depth value
 */
/**
 * Fill depth buffer from particle layer
 * Each particle contributes to depth based on its position and size
 */
/**
 * Interface for particle layers with getActiveParticles method
 */
interface ParticleLayerWithParticles extends BaseLayer {
  getActiveParticles(): ExportedParticle[];
}

/**
 * Type guard for particle layers with getActiveParticles method
 */
function isParticleLayerWithParticles(layer: BaseLayer | null): layer is ParticleLayerWithParticles {
  return layer !== null && typeof (layer as ParticleLayerWithParticles).getActiveParticles === "function";
}

function fillDepthFromParticles(
  depthBuffer: Float32Array,
  layer: Layer,
  screenWidth: number,
  screenHeight: number,
  camera: Camera3D,
  frame: number,
  nearClip: number,
  farClip: number,
): void {
  // Access the engine's particle layer to get active particles
  const engine: LatticeEngine | undefined = window.__latticeEngine;
  if (!engine) return;

  // Get the particle layer from the engine
  const particleLayer = engine.getLayer(layer.id);
  if (!isParticleLayerWithParticles(particleLayer)) {
    return;
  }

  // Get active particles at current frame
  const particles = particleLayer.getActiveParticles();
  if (!particles || particles.length === 0) return;

  const cameraZ = camera.position.z;
  const f32NearClip = Math.fround(nearClip);
  const f32FarClip = Math.fround(farClip);

  // Render each particle as a circular depth splat
  for (const p of particles) {
    // Validate particle position
    if (!Number.isFinite(p.x) || !Number.isFinite(p.y) || !Number.isFinite(p.z)) {
      continue;
    }

    // Calculate particle depth relative to camera
    const relativeDepth = Math.abs(p.z - cameraZ);
    const clampedDepth = Math.fround(
      Math.max(f32NearClip, Math.min(f32FarClip, relativeDepth))
    );

    // Particle screen position (assuming normalized 0-1 coords mapped to screen)
    const screenX = Math.floor(p.x);
    const screenY = Math.floor(p.y);

    // Particle radius in pixels (half of size)
    const radius = Math.max(1, Math.floor((p.size ?? 10) / 2));

    // Render circular splat
    for (let dy = -radius; dy <= radius; dy++) {
      for (let dx = -radius; dx <= radius; dx++) {
        // Circle check
        if (dx * dx + dy * dy > radius * radius) continue;

        const px = screenX + dx;
        const py = screenY + dy;

        // Bounds check
        if (px < 0 || px >= screenWidth || py < 0 || py >= screenHeight) continue;

        const idx = py * screenWidth + px;

        // Depth test - closer wins (particle opacity assumed > 0.5)
        if (clampedDepth < depthBuffer[idx]) {
          depthBuffer[idx] = clampedDepth;
        }
      }
    }
  }
}

function fillUniformDepth(
  depthBuffer: Float32Array,
  bounds: { x: number; y: number; width: number; height: number },
  depth: number,
  opacity: number,
  screenWidth: number,
  screenHeight: number,
): void {
  const startX = Math.floor(bounds.x);
  const startY = Math.floor(bounds.y);
  const endX = Math.min(screenWidth, Math.ceil(bounds.x + bounds.width));
  const endY = Math.min(screenHeight, Math.ceil(bounds.y + bounds.height));

  for (let y = startY; y < endY; y++) {
    for (let x = startX; x < endX; x++) {
      const idx = y * screenWidth + x;

      // Alpha blending for depth (closer wins if opaque enough)
      if (opacity > 0.5 && depth < depthBuffer[idx]) {
        depthBuffer[idx] = depth;
      }
    }
  }
}

/**
 * Interpolate value from keyframes
 */
/**
 * Keyframe interface for interpolation
 */
interface Keyframe {
  frame: number;
  value: number | number[];
}

function interpolateValue(
  keyframes: Keyframe[],
  frame: number,
  index?: number,
): number | null {
  if (!keyframes || keyframes.length === 0) return null;

  // Find surrounding keyframes
  let prev = keyframes[0];
  let next = keyframes[keyframes.length - 1];

  for (let i = 0; i < keyframes.length; i++) {
    if (keyframes[i].frame <= frame) {
      prev = keyframes[i];
    }
    if (keyframes[i].frame >= frame && i < keyframes.length) {
      next = keyframes[i];
      break;
    }
  }

  if (prev.frame === next.frame) {
    const value = prev.value;
    return index !== undefined && Array.isArray(value) ? value[index] : value;
  }

  // Linear interpolation
  const t = (frame - prev.frame) / (next.frame - prev.frame);
  const prevValue =
    index !== undefined && Array.isArray(prev.value)
      ? prev.value[index]
      : prev.value;
  const nextValue =
    index !== undefined && Array.isArray(next.value)
      ? next.value[index]
      : next.value;

  return prevValue + (nextValue - prevValue) * t;
}

// ============================================================================
// Depth Format Conversion
// ============================================================================

/**
 * Convert depth buffer to export format.
 * Returns Float32Array for 'raw' format.
 */
export function convertDepthToFormat(
  result: DepthRenderResult,
  format: DepthMapFormat,
): Float32Array | Uint8Array | Uint16Array {
  const spec = DEPTH_FORMAT_SPECS[format];

  // Validate format exists in spec table
  if (!spec) {
    throw new Error(`Unknown depth format: ${format}. Valid formats: ${Object.keys(DEPTH_FORMAT_SPECS).join(', ')}`);
  }

  const { depthBuffer, width, height, minDepth, maxDepth } = result;

  // Validate dimensions - zero or negative dimensions are invalid
  if (!Number.isFinite(width) || width <= 0) {
    throw new Error(`Invalid dimensions: width=${width}. Width must be a positive number.`);
  }
  if (!Number.isFinite(height) || height <= 0) {
    throw new Error(`Invalid dimensions: height=${height}. Height must be a positive number.`);
  }

  const pixelCount = width * height;

  // Raw format: return Float32Array copy directly without conversion
  if (format === 'raw' || spec.bitDepth === 32) {
    // Return a copy of the depth buffer
    return new Float32Array(depthBuffer);
  }

  // Guard against division by zero when all depths are identical
  const depthRange = maxDepth - minDepth;
  const safeRange = depthRange > 0 ? depthRange : 1;

  if (spec.bitDepth === 16) {
    const output = new Uint16Array(pixelCount);

    for (let i = 0; i < pixelCount; i++) {
      let normalized: number;

      if (spec.normalize) {
        // Normalize to 0-1 range
        normalized = (depthBuffer[i] - minDepth) / safeRange;
      } else {
        // Keep metric value, scale to 16-bit
        normalized = depthBuffer[i] / spec.farClip;
      }

      // Clamp before inversion to prevent out-of-range values
      normalized = Math.max(0, Math.min(1, normalized));

      if (spec.invert) {
        normalized = 1 - normalized;
      }

      output[i] = Math.max(0, Math.min(65535, Math.round(normalized * 65535)));
    }

    return output;
  } else {
    const output = new Uint8Array(pixelCount);

    for (let i = 0; i < pixelCount; i++) {
      let normalized = (depthBuffer[i] - minDepth) / safeRange;

      // Clamp before inversion to prevent out-of-range values
      normalized = Math.max(0, Math.min(1, normalized));

      if (spec.invert) {
        normalized = 1 - normalized;
      }

      output[i] = Math.max(0, Math.min(255, Math.round(normalized * 255)));
    }

    return output;
  }
}

/**
 * Create PNG image data from depth buffer.
 * Accepts DepthRenderResult or converted depth data.
 */
export function depthToImageData(
  input: DepthRenderResult | Uint8Array | Uint16Array | Float32Array,
  width?: number,
  height?: number,
): ImageData {
  // Handle DepthRenderResult input
  if ('depthBuffer' in input) {
    const result = input as DepthRenderResult;
    const { depthBuffer, minDepth, maxDepth } = result;
    const w = result.width;
    const h = result.height;
    
    // Validate buffer size matches dimensions
    if (depthBuffer.length !== w * h) {
      throw new Error(`Depth buffer size ${depthBuffer.length} doesn't match ${w}x${h}`);
    }
    
    const imageData = new ImageData(w, h);
    const depthRange = maxDepth - minDepth;
    const safeRange = depthRange > 0 ? depthRange : 1;

    for (let i = 0; i < w * h; i++) {
      // Normalize Float32 to 0-255
      const normalized = (depthBuffer[i] - minDepth) / safeRange;
      // Clamp to 8-bit range [0, 255]
      const value = Math.max(0, Math.min(255, Math.round(normalized * 255)));

      const pixelIdx = i * 4;
      imageData.data[pixelIdx] = value; // R
      imageData.data[pixelIdx + 1] = value; // G
      imageData.data[pixelIdx + 2] = value; // B
      // Alpha always opaque for depth maps
      imageData.data[pixelIdx + 3] = 255;
    }

    return imageData;
  }
  
  // Handle Uint8Array/Uint16Array/Float32Array input (legacy API)
  const depthData = input as Uint8Array | Uint16Array | Float32Array;
  const w = width!;
  const h = height!;

  if (!w || !h) {
    throw new Error('Width and height required when passing typed array');
  }

  const imageData = new ImageData(w, h);
  const is16bit = depthData instanceof Uint16Array;
  const is32bit = depthData instanceof Float32Array;

  for (let i = 0; i < w * h; i++) {
    let value: number;
    if (is32bit) {
      // Float32Array: assume 0-1 range, scale to 0-255
      value = Math.floor(depthData[i] * 255);
    } else if (is16bit) {
      value = Math.floor(depthData[i] / 256);
    } else {
      value = depthData[i];
    }
    // Clamp to valid 8-bit range
    const clampedValue = Math.max(0, Math.min(255, value));

    const pixelIdx = i * 4;
    imageData.data[pixelIdx] = clampedValue; // R
    imageData.data[pixelIdx + 1] = clampedValue; // G
    imageData.data[pixelIdx + 2] = clampedValue; // B
    // Depth maps must be fully opaque for correct downstream processing
    imageData.data[pixelIdx + 3] = 255; // A
  }

  return imageData;
}

/**
 * Apply colormap to depth data for visualization.
 * Accepts DepthRenderResult or converted depth data.
 * Supports viridis, plasma, magma, inferno, and turbo colormaps.
 */
export function applyColormap(
  input: DepthRenderResult | Uint8Array | Uint16Array,
  colormapOrWidth: "grayscale" | "viridis" | "magma" | "plasma" | "inferno" | "turbo" | number,
  height?: number,
  colormap?: "grayscale" | "viridis" | "magma" | "plasma" | "inferno" | "turbo",
): ImageData {
  // Handle DepthRenderResult input (new API)
  if ('depthBuffer' in input) {
    const result = input as DepthRenderResult;
    const { depthBuffer, width: w, height: h, minDepth, maxDepth } = result;
    const cmap = colormapOrWidth as "grayscale" | "viridis" | "magma" | "plasma" | "inferno" | "turbo";
    
    const imageData = new ImageData(w, h);
    const depthRange = maxDepth - minDepth;
    const safeRange = depthRange > 0 ? depthRange : 1;

    for (let i = 0; i < w * h; i++) {
      // AI models (MiDaS, Depth-Anything) expect near=bright, far=dark
      // Invert normalized value: 0=far (dark), 1=near (bright)
      const normalized = 1 - Math.max(0, Math.min(1, (depthBuffer[i] - minDepth) / safeRange));
      const [r, g, b] = getColormapColor(normalized, cmap);

      const pixelIdx = i * 4;
      imageData.data[pixelIdx] = r;
      imageData.data[pixelIdx + 1] = g;
      imageData.data[pixelIdx + 2] = b;
      imageData.data[pixelIdx + 3] = 255;
    }

    return imageData;
  }
  
  // Handle legacy API: (Uint8Array | Uint16Array, width, height, colormap)
  const depthData = input as Uint8Array | Uint16Array;
  const w = colormapOrWidth as number;
  const h = height!;
  const cmap = colormap!;
  
  if (!w || !h || !cmap) {
    throw new Error('Width, height, and colormap required when passing Uint8Array/Uint16Array');
  }
  
  const imageData = new ImageData(w, h);
  const is16bit = depthData instanceof Uint16Array;
  const maxValue = is16bit ? 65535 : 255;

  for (let i = 0; i < w * h; i++) {
    const normalized = depthData[i] / maxValue;
    const [r, g, b] = getColormapColor(normalized, cmap);

    const pixelIdx = i * 4;
    imageData.data[pixelIdx] = r;
    imageData.data[pixelIdx + 1] = g;
    imageData.data[pixelIdx + 2] = b;
    imageData.data[pixelIdx + 3] = 255;
  }

  return imageData;
}

/**
 * Get color from colormap.
 * Supports viridis, plasma, magma, inferno, and turbo colormaps.
 */
function getColormapColor(
  t: number,
  colormap: string,
): [number, number, number] {
  // Clamp t to 0-1
  t = Math.max(0, Math.min(1, t));

  switch (colormap) {
    case "viridis":
      return viridisColormap(t);
    case "magma":
      return magmaColormap(t);
    case "plasma":
      return plasmaColormap(t);
    case "inferno":
      return infernoColormap(t);
    case "turbo":
      return turboColormap(t);
    case "grayscale":
    default: {
      const v = Math.round(t * 255);
      return [v, v, v];
    }
  }
}

// Viridis colormap (simplified)
function viridisColormap(t: number): [number, number, number] {
  const colors = [
    [68, 1, 84],
    [72, 40, 120],
    [62, 74, 137],
    [49, 104, 142],
    [38, 130, 142],
    [31, 158, 137],
    [53, 183, 121],
    [109, 205, 89],
    [180, 222, 44],
    [253, 231, 37],
  ];

  const idx = t * (colors.length - 1);
  const i = Math.floor(idx);
  const f = idx - i;

  if (i >= colors.length - 1)
    return colors[colors.length - 1] as [number, number, number];

  return [
    Math.round(colors[i][0] + (colors[i + 1][0] - colors[i][0]) * f),
    Math.round(colors[i][1] + (colors[i + 1][1] - colors[i][1]) * f),
    Math.round(colors[i][2] + (colors[i + 1][2] - colors[i][2]) * f),
  ];
}

// Magma colormap (simplified)
function magmaColormap(t: number): [number, number, number] {
  const colors = [
    [0, 0, 4],
    [28, 16, 68],
    [79, 18, 123],
    [129, 37, 129],
    [181, 54, 122],
    [229, 80, 100],
    [251, 135, 97],
    [254, 194, 135],
    [252, 253, 191],
  ];

  const idx = t * (colors.length - 1);
  const i = Math.floor(idx);
  const f = idx - i;

  if (i >= colors.length - 1)
    return colors[colors.length - 1] as [number, number, number];

  return [
    Math.round(colors[i][0] + (colors[i + 1][0] - colors[i][0]) * f),
    Math.round(colors[i][1] + (colors[i + 1][1] - colors[i][1]) * f),
    Math.round(colors[i][2] + (colors[i + 1][2] - colors[i][2]) * f),
  ];
}

// Plasma colormap (simplified)
function plasmaColormap(t: number): [number, number, number] {
  const colors = [
    [13, 8, 135],
    [75, 3, 161],
    [125, 3, 168],
    [168, 34, 150],
    [203, 70, 121],
    [229, 107, 93],
    [248, 148, 65],
    [253, 195, 40],
    [240, 249, 33],
  ];

  const idx = t * (colors.length - 1);
  const i = Math.floor(idx);
  const f = idx - i;

  if (i >= colors.length - 1)
    return colors[colors.length - 1] as [number, number, number];

  return [
    Math.round(colors[i][0] + (colors[i + 1][0] - colors[i][0]) * f),
    Math.round(colors[i][1] + (colors[i + 1][1] - colors[i][1]) * f),
    Math.round(colors[i][2] + (colors[i + 1][2] - colors[i][2]) * f),
  ];
}

// Inferno colormap - perceptually uniform, good for depth visualization
function infernoColormap(t: number): [number, number, number] {
  const colors = [
    [0, 0, 4],
    [22, 11, 57],
    [66, 10, 104],
    [106, 23, 110],
    [147, 38, 103],
    [188, 55, 84],
    [221, 81, 58],
    [243, 118, 27],
    [252, 165, 10],
    [246, 215, 70],
    [252, 255, 164],
  ];

  const idx = t * (colors.length - 1);
  const i = Math.floor(idx);
  const f = idx - i;

  if (i >= colors.length - 1)
    return colors[colors.length - 1] as [number, number, number];

  return [
    Math.round(colors[i][0] + (colors[i + 1][0] - colors[i][0]) * f),
    Math.round(colors[i][1] + (colors[i + 1][1] - colors[i][1]) * f),
    Math.round(colors[i][2] + (colors[i + 1][2] - colors[i][2]) * f),
  ];
}

// Turbo colormap - Google's rainbow alternative with better perceptual uniformity
function turboColormap(t: number): [number, number, number] {
  const colors = [
    [48, 18, 59],
    [70, 68, 172],
    [62, 121, 229],
    [38, 170, 225],
    [31, 212, 182],
    [76, 237, 123],
    [149, 249, 67],
    [212, 241, 31],
    [253, 207, 37],
    [252, 150, 38],
    [239, 85, 33],
    [205, 33, 28],
    [122, 4, 3],
  ];

  const idx = t * (colors.length - 1);
  const i = Math.floor(idx);
  const f = idx - i;

  if (i >= colors.length - 1)
    return colors[colors.length - 1] as [number, number, number];

  return [
    Math.round(colors[i][0] + (colors[i + 1][0] - colors[i][0]) * f),
    Math.round(colors[i][1] + (colors[i + 1][1] - colors[i][1]) * f),
    Math.round(colors[i][2] + (colors[i + 1][2] - colors[i][2]) * f),
  ];
}

// ============================================================================
// Export Functions
// ============================================================================

/**
 * Export depth sequence as PNG files
 */
export async function exportDepthSequence(
  layers: Layer[],
  camera: Camera3D,
  options: {
    startFrame: number;
    endFrame: number;
    width: number;
    height: number;
    format: DepthMapFormat;
    outputDir: string;
  },
  onProgress?: (frame: number, total: number) => void,
): Promise<string[]> {
  const outputPaths: string[] = [];
  const spec = DEPTH_FORMAT_SPECS[options.format];
  const totalFrames = options.endFrame - options.startFrame + 1;

  for (let i = 0; i < totalFrames; i++) {
    const frame = options.startFrame + i;

    // Render depth
    const result = renderDepthFrame({
      width: options.width,
      height: options.height,
      nearClip: spec.nearClip,
      farClip: spec.farClip,
      camera,
      layers,
      frame,
    });

    // Convert to format
    const depthData = convertDepthToFormat(result, options.format);

    // Create image data
    const _imageData = depthToImageData(
      depthData,
      options.width,
      options.height,
    );

    // Generate filename
    const filename = `depth_${String(i).padStart(5, "0")}.png`;
    const outputPath = `${options.outputDir}/depth/${filename}`;

    // Note: Actual file saving would need to use canvas.toBlob() or similar
    // This returns the path that would be used
    outputPaths.push(outputPath);

    onProgress?.(i + 1, totalFrames);
  }

  return outputPaths;
}

/**
 * Depth metadata structure returned by generateDepthMetadata
 */
export interface DepthMetadata {
  format: DepthMapFormat;
  bitDepth: number;
  nearClip: number;
  farClip: number;
  inverted: boolean;
  normalized: boolean;
  frameCount: number;
  width: number;
  height: number;
  actualRange: {
    min: number;
    max: number;
  };
  generatedAt: string; // ISO 8601 timestamp
  generator: string;
}

/**
 * Generate depth metadata JSON
 */
export function generateDepthMetadata(
  format: DepthMapFormat,
  frameCount: number,
  width: number,
  height: number,
  minDepth: number,
  maxDepth: number,
): DepthMetadata {
  const spec = DEPTH_FORMAT_SPECS[format];

  return {
    format,
    bitDepth: spec.bitDepth,
    nearClip: spec.nearClip,
    farClip: spec.farClip,
    inverted: spec.invert,
    normalized: spec.normalize,
    frameCount,
    width,
    height,
    actualRange: {
      min: minDepth,
      max: maxDepth,
    },
    generatedAt: new Date().toISOString(),
    generator: "Lattice Compositor",
  };
}
