/**
 * Depth Map Renderer
 * Generates depth maps from compositor scene for AI video generation
 */

import type { Camera3D } from '@/types/camera';
import type { Layer } from '@/types/project';
import type { DepthMapFormat, DepthExportOptions } from '@/types/export';
import { DEPTH_FORMAT_SPECS } from '@/config/exportPresets';

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
export function renderDepthFrame(options: DepthRenderOptions): DepthRenderResult {
  const { width, height, nearClip, farClip, camera, layers, frame } = options;

  // Create depth buffer
  const depthBuffer = new Float32Array(width * height);
  depthBuffer.fill(farClip); // Initialize to far clip

  let minDepth = farClip;
  let maxDepth = nearClip;

  // Sort layers by Z depth (front to back from camera's perspective)
  const sortedLayers = [...layers]
    .filter(l => l.visible)
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
    const clampedDepth = Math.max(nearClip, Math.min(farClip, relativeDepth));

    // Update min/max tracking
    minDepth = Math.min(minDepth, clampedDepth);
    maxDepth = Math.max(maxDepth, clampedDepth);

    // Fill depth buffer for layer area
    // For layers with depth maps (depthflow), use their depth data
    if (layer.type === 'depthflow' && hasDepthData(layer)) {
      fillDepthFromDepthflow(depthBuffer, layer, bounds, width, height, nearClip, farClip);
    } else {
      // Solid layers get uniform depth
      fillUniformDepth(depthBuffer, bounds, clampedDepth, layerOpacity, width, height);
    }
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
    if (typeof value === 'object' && 'z' in value) {
      return (value as { z?: number }).z ?? 0;
    }
  }

  // Default to 0 (on the focal plane)
  return 0;
}

/**
 * Get layer opacity at frame
 */
function getLayerOpacity(layer: Layer, frame: number): number {
  if (layer.opacity && 'keyframes' in layer.opacity && layer.opacity.keyframes?.length > 0) {
    return (interpolateValue(layer.opacity.keyframes, frame) || 100) / 100;
  }

  if (layer.opacity && 'value' in layer.opacity) {
    return (layer.opacity.value || 100) / 100;
  }

  return 1;
}

/**
 * Get layer bounds in screen space
 */
function getLayerScreenBounds(
  layer: Layer,
  frame: number,
  camera: Camera3D,
  screenWidth: number,
  screenHeight: number
): { x: number; y: number; width: number; height: number } | null {
  // Get layer position from transform
  let x = 0, y = 0;

  const position = layer.transform?.position;
  if (position && 'value' in position) {
    const value = position.value;
    if (Array.isArray(value)) {
      x = value[0] || 0;
      y = value[1] || 0;
    }
  }

  // Get layer dimensions (assuming they're stored or can be derived)
  const layerWidth = (layer as any).width || screenWidth;
  const layerHeight = (layer as any).height || screenHeight;

  // Get scale from transform
  let scaleX = 1, scaleY = 1;
  const scale = layer.transform?.scale;
  if (scale && 'value' in scale) {
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
  let anchorX = 0.5, anchorY = 0.5;
  const anchorPoint = layer.transform?.anchorPoint;
  if (anchorPoint && 'value' in anchorPoint) {
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
  const clippedWidth = Math.max(0, Math.min(screenWidth - clippedX, finalWidth - (clippedX - screenX)));
  const clippedHeight = Math.max(0, Math.min(screenHeight - clippedY, finalHeight - (clippedY - screenY)));

  if (clippedWidth <= 0 || clippedHeight <= 0) return null;

  return {
    x: clippedX,
    y: clippedY,
    width: clippedWidth,
    height: clippedHeight,
  };
}

/**
 * Check if layer has depth data (depthflow layers)
 */
function hasDepthData(layer: Layer): boolean {
  return layer.type === 'depthflow' && !!(layer as any).depthMapData;
}

/**
 * Fill depth buffer from depthflow layer's depth map
 */
function fillDepthFromDepthflow(
  depthBuffer: Float32Array,
  layer: Layer,
  bounds: { x: number; y: number; width: number; height: number },
  screenWidth: number,
  screenHeight: number,
  nearClip: number,
  farClip: number
): void {
  const depthData = (layer as any).depthMapData as Uint8Array | Float32Array;
  const depthWidth = (layer as any).depthWidth || bounds.width;
  const depthHeight = (layer as any).depthHeight || bounds.height;

  for (let y = 0; y < bounds.height; y++) {
    for (let x = 0; x < bounds.width; x++) {
      const screenX = Math.floor(bounds.x + x);
      const screenY = Math.floor(bounds.y + y);

      if (screenX < 0 || screenX >= screenWidth || screenY < 0 || screenY >= screenHeight) continue;

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
function fillUniformDepth(
  depthBuffer: Float32Array,
  bounds: { x: number; y: number; width: number; height: number },
  depth: number,
  opacity: number,
  screenWidth: number,
  screenHeight: number
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
function interpolateValue(keyframes: any[], frame: number, index?: number): number | null {
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
  const prevValue = index !== undefined && Array.isArray(prev.value) ? prev.value[index] : prev.value;
  const nextValue = index !== undefined && Array.isArray(next.value) ? next.value[index] : next.value;

  return prevValue + (nextValue - prevValue) * t;
}

// ============================================================================
// Depth Format Conversion
// ============================================================================

/**
 * Convert depth buffer to export format
 */
export function convertDepthToFormat(
  result: DepthRenderResult,
  format: DepthMapFormat
): Uint8Array | Uint16Array {
  const spec = DEPTH_FORMAT_SPECS[format];
  const { depthBuffer, width, height, minDepth, maxDepth } = result;

  const pixelCount = width * height;

  if (spec.bitDepth === 16) {
    const output = new Uint16Array(pixelCount);

    for (let i = 0; i < pixelCount; i++) {
      let normalized: number;

      if (spec.normalize) {
        // Normalize to 0-1 range
        normalized = (depthBuffer[i] - minDepth) / (maxDepth - minDepth);
      } else {
        // Keep metric value, scale to 16-bit
        normalized = depthBuffer[i] / spec.farClip;
      }

      if (spec.invert) {
        normalized = 1 - normalized;
      }

      output[i] = Math.max(0, Math.min(65535, Math.round(normalized * 65535)));
    }

    return output;
  } else {
    const output = new Uint8Array(pixelCount);

    for (let i = 0; i < pixelCount; i++) {
      let normalized = (depthBuffer[i] - minDepth) / (maxDepth - minDepth);

      if (spec.invert) {
        normalized = 1 - normalized;
      }

      output[i] = Math.max(0, Math.min(255, Math.round(normalized * 255)));
    }

    return output;
  }
}

/**
 * Create PNG image data from depth buffer
 */
export function depthToImageData(
  depthData: Uint8Array | Uint16Array,
  width: number,
  height: number
): ImageData {
  const imageData = new ImageData(width, height);
  const is16bit = depthData instanceof Uint16Array;

  for (let i = 0; i < width * height; i++) {
    const value = is16bit ? Math.floor(depthData[i] / 256) : depthData[i];

    const pixelIdx = i * 4;
    imageData.data[pixelIdx] = value;     // R
    imageData.data[pixelIdx + 1] = value; // G
    imageData.data[pixelIdx + 2] = value; // B
    imageData.data[pixelIdx + 3] = 255;   // A
  }

  return imageData;
}

/**
 * Apply colormap to depth data for visualization
 */
export function applyColormap(
  depthData: Uint8Array | Uint16Array,
  width: number,
  height: number,
  colormap: 'grayscale' | 'viridis' | 'magma' | 'plasma'
): ImageData {
  const imageData = new ImageData(width, height);
  const is16bit = depthData instanceof Uint16Array;
  const maxValue = is16bit ? 65535 : 255;

  for (let i = 0; i < width * height; i++) {
    const normalized = depthData[i] / maxValue;
    const [r, g, b] = getColormapColor(normalized, colormap);

    const pixelIdx = i * 4;
    imageData.data[pixelIdx] = r;
    imageData.data[pixelIdx + 1] = g;
    imageData.data[pixelIdx + 2] = b;
    imageData.data[pixelIdx + 3] = 255;
  }

  return imageData;
}

/**
 * Get color from colormap
 */
function getColormapColor(
  t: number,
  colormap: string
): [number, number, number] {
  // Clamp t to 0-1
  t = Math.max(0, Math.min(1, t));

  switch (colormap) {
    case 'viridis':
      return viridisColormap(t);
    case 'magma':
      return magmaColormap(t);
    case 'plasma':
      return plasmaColormap(t);
    case 'grayscale':
    default:
      const v = Math.round(t * 255);
      return [v, v, v];
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

  if (i >= colors.length - 1) return colors[colors.length - 1] as [number, number, number];

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

  if (i >= colors.length - 1) return colors[colors.length - 1] as [number, number, number];

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

  if (i >= colors.length - 1) return colors[colors.length - 1] as [number, number, number];

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
  onProgress?: (frame: number, total: number) => void
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
    const imageData = depthToImageData(depthData, options.width, options.height);

    // Generate filename
    const filename = `depth_${String(i).padStart(5, '0')}.png`;
    const outputPath = `${options.outputDir}/depth/${filename}`;

    // Note: Actual file saving would need to use canvas.toBlob() or similar
    // This returns the path that would be used
    outputPaths.push(outputPath);

    onProgress?.(i + 1, totalFrames);
  }

  return outputPaths;
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
  maxDepth: number
): object {
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
    generator: 'Lattice Compositor',
  };
}
