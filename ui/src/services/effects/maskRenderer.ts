/**
 * Mask Renderer - Professional mask and track matte compositing
 *
 * Supports:
 * - Bezier path masks with feathering
 * - Multiple mask modes (add, subtract, intersect, etc.)
 * - Track mattes (alpha and luma)
 * - Animated mask paths
 * - Mask expansion/contraction
 */

import type { LayerMask, MaskPath, MaskVertex, MaskMode, TrackMatteType } from '@/types/project';

// ============================================================================
// MASK PATH RENDERING
// ============================================================================

/**
 * Render a bezier mask path to a canvas context
 */
function renderMaskPath(ctx: CanvasRenderingContext2D, path: MaskPath): void {
  if (path.vertices.length < 2) return;

  ctx.beginPath();

  const vertices = path.vertices;
  const n = vertices.length;

  // Move to first point
  ctx.moveTo(vertices[0].x, vertices[0].y);

  // Draw bezier curves between vertices
  for (let i = 0; i < n; i++) {
    const current = vertices[i];
    const next = vertices[(i + 1) % n];

    // Skip last segment if not closed
    if (!path.closed && i === n - 1) break;

    // Control points
    const cp1x = current.x + current.outTangentX;
    const cp1y = current.y + current.outTangentY;
    const cp2x = next.x + next.inTangentX;
    const cp2y = next.y + next.inTangentY;

    // Check if this is a straight line (no tangents)
    if (cp1x === current.x && cp1y === current.y &&
        cp2x === next.x && cp2y === next.y) {
      ctx.lineTo(next.x, next.y);
    } else {
      ctx.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, next.x, next.y);
    }
  }

  if (path.closed) {
    ctx.closePath();
  }
}

/**
 * Apply expansion (positive) or contraction (negative) to a mask path
 */
function expandMaskPath(path: MaskPath, expansion: number): MaskPath {
  if (expansion === 0) return path;

  // For simplicity, we'll use a uniform offset approach
  // A more accurate implementation would use polygon offsetting algorithms
  const vertices = path.vertices.map(v => {
    // Calculate normal at this vertex (perpendicular to curve direction)
    // For now, use a simple approximation
    return {
      ...v,
      x: v.x, // Expansion would modify these
      y: v.y,
    };
  });

  // TODO: Implement proper polygon offset for accurate expansion
  // This requires calculating normals at each vertex and offsetting along them
  // For now, we'll apply expansion as a post-process blur scale

  return { ...path, vertices };
}

// ============================================================================
// SINGLE MASK RENDERING
// ============================================================================

/**
 * Render a single mask to a grayscale canvas
 * White = opaque, Black = transparent
 */
export function renderMask(
  mask: LayerMask,
  width: number,
  height: number,
  frame: number
): HTMLCanvasElement {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext('2d')!;

  // Start with black (transparent)
  ctx.fillStyle = 'black';
  ctx.fillRect(0, 0, width, height);

  if (!mask.enabled) return canvas;

  // Get animated path value
  const path = mask.path.value; // TODO: Interpolate keyframes at frame

  // Apply expansion
  const expandedPath = expandMaskPath(path, mask.expansion.value);

  // Render the mask shape in white
  ctx.fillStyle = 'white';
  renderMaskPath(ctx, expandedPath);
  ctx.fill();

  // Apply mask opacity
  if (mask.opacity.value < 100) {
    const opacity = mask.opacity.value / 100;
    const imageData = ctx.getImageData(0, 0, width, height);
    for (let i = 0; i < imageData.data.length; i += 4) {
      imageData.data[i] = Math.round(imageData.data[i] * opacity);
    }
    ctx.putImageData(imageData, 0, 0);
  }

  // Apply feather (blur)
  if (mask.feather.value > 0) {
    // Create a temporary canvas for blur
    const blurCanvas = document.createElement('canvas');
    blurCanvas.width = width;
    blurCanvas.height = height;
    const blurCtx = blurCanvas.getContext('2d')!;

    blurCtx.filter = `blur(${mask.feather.value}px)`;
    blurCtx.drawImage(canvas, 0, 0);

    // Copy back
    ctx.clearRect(0, 0, width, height);
    ctx.drawImage(blurCanvas, 0, 0);
  }

  // Apply inversion
  if (mask.inverted) {
    const imageData = ctx.getImageData(0, 0, width, height);
    for (let i = 0; i < imageData.data.length; i += 4) {
      imageData.data[i] = 255 - imageData.data[i];
      imageData.data[i + 1] = 255 - imageData.data[i + 1];
      imageData.data[i + 2] = 255 - imageData.data[i + 2];
    }
    ctx.putImageData(imageData, 0, 0);
  }

  return canvas;
}

// ============================================================================
// MULTIPLE MASKS COMBINATION
// ============================================================================

/**
 * Combine multiple masks using their blend modes
 */
export function combineMasks(
  masks: LayerMask[],
  width: number,
  height: number,
  frame: number
): HTMLCanvasElement {
  const resultCanvas = document.createElement('canvas');
  resultCanvas.width = width;
  resultCanvas.height = height;
  const resultCtx = resultCanvas.getContext('2d')!;

  // Start with white (fully visible) if no masks, black otherwise
  const enabledMasks = masks.filter(m => m.enabled && m.mode !== 'none');
  if (enabledMasks.length === 0) {
    resultCtx.fillStyle = 'white';
    resultCtx.fillRect(0, 0, width, height);
    return resultCanvas;
  }

  // Start with black (nothing visible)
  resultCtx.fillStyle = 'black';
  resultCtx.fillRect(0, 0, width, height);

  // Get result image data for pixel manipulation
  const resultData = resultCtx.getImageData(0, 0, width, height);
  const result = resultData.data;

  // Process each mask
  for (const mask of enabledMasks) {
    const maskCanvas = renderMask(mask, width, height, frame);
    const maskCtx = maskCanvas.getContext('2d')!;
    const maskData = maskCtx.getImageData(0, 0, width, height);
    const maskPixels = maskData.data;

    // Apply mask mode
    for (let i = 0; i < result.length; i += 4) {
      const maskValue = maskPixels[i]; // Use red channel as grayscale

      switch (mask.mode) {
        case 'add':
          // Union: max of values
          result[i] = Math.max(result[i], maskValue);
          result[i + 1] = Math.max(result[i + 1], maskValue);
          result[i + 2] = Math.max(result[i + 2], maskValue);
          break;

        case 'subtract':
          // Subtract: result minus mask
          result[i] = Math.max(0, result[i] - maskValue);
          result[i + 1] = Math.max(0, result[i + 1] - maskValue);
          result[i + 2] = Math.max(0, result[i + 2] - maskValue);
          break;

        case 'intersect':
          // Intersection: min of values
          result[i] = Math.min(result[i], maskValue);
          result[i + 1] = Math.min(result[i + 1], maskValue);
          result[i + 2] = Math.min(result[i + 2], maskValue);
          break;

        case 'lighten':
          // Max
          result[i] = Math.max(result[i], maskValue);
          result[i + 1] = Math.max(result[i + 1], maskValue);
          result[i + 2] = Math.max(result[i + 2], maskValue);
          break;

        case 'darken':
          // Min
          result[i] = Math.min(result[i], maskValue);
          result[i + 1] = Math.min(result[i + 1], maskValue);
          result[i + 2] = Math.min(result[i + 2], maskValue);
          break;

        case 'difference':
          // Absolute difference
          result[i] = Math.abs(result[i] - maskValue);
          result[i + 1] = Math.abs(result[i + 1] - maskValue);
          result[i + 2] = Math.abs(result[i + 2] - maskValue);
          break;
      }
    }
  }

  resultCtx.putImageData(resultData, 0, 0);
  return resultCanvas;
}

// ============================================================================
// TRACK MATTE APPLICATION
// ============================================================================

/**
 * Apply a track matte to a layer
 */
export function applyTrackMatte(
  layerCanvas: HTMLCanvasElement,
  matteCanvas: HTMLCanvasElement,
  matteType: TrackMatteType
): HTMLCanvasElement {
  if (matteType === 'none') return layerCanvas;

  const width = layerCanvas.width;
  const height = layerCanvas.height;

  const resultCanvas = document.createElement('canvas');
  resultCanvas.width = width;
  resultCanvas.height = height;
  const resultCtx = resultCanvas.getContext('2d')!;

  // Get layer pixel data
  const layerCtx = layerCanvas.getContext('2d')!;
  const layerData = layerCtx.getImageData(0, 0, width, height);
  const layer = layerData.data;

  // Get matte pixel data (scale if needed)
  const matteScaled = document.createElement('canvas');
  matteScaled.width = width;
  matteScaled.height = height;
  const matteScaledCtx = matteScaled.getContext('2d')!;
  matteScaledCtx.drawImage(matteCanvas, 0, 0, width, height);
  const matteData = matteScaledCtx.getImageData(0, 0, width, height);
  const matte = matteData.data;

  // Apply matte based on type
  for (let i = 0; i < layer.length; i += 4) {
    let matteValue: number;

    switch (matteType) {
      case 'alpha':
        // Use alpha channel directly
        matteValue = matte[i + 3] / 255;
        break;

      case 'alpha_inverted':
        // Invert alpha channel
        matteValue = 1 - (matte[i + 3] / 255);
        break;

      case 'luma':
        // Calculate luminance
        matteValue = (matte[i] * 0.299 + matte[i + 1] * 0.587 + matte[i + 2] * 0.114) / 255;
        break;

      case 'luma_inverted':
        // Invert luminance
        matteValue = 1 - (matte[i] * 0.299 + matte[i + 1] * 0.587 + matte[i + 2] * 0.114) / 255;
        break;

      default:
        matteValue = 1;
    }

    // Apply matte to layer alpha
    layer[i + 3] = Math.round(layer[i + 3] * matteValue);
  }

  resultCtx.putImageData(layerData, 0, 0);
  return resultCanvas;
}

// ============================================================================
// MASK APPLICATION TO LAYER
// ============================================================================

/**
 * Apply masks to a layer canvas
 */
export function applyMasksToLayer(
  layerCanvas: HTMLCanvasElement,
  masks: LayerMask[] | undefined,
  frame: number
): HTMLCanvasElement {
  if (!masks || masks.length === 0) return layerCanvas;

  const width = layerCanvas.width;
  const height = layerCanvas.height;

  // Combine all masks into a single mask
  const combinedMask = combineMasks(masks, width, height, frame);

  // Apply combined mask to layer
  const resultCanvas = document.createElement('canvas');
  resultCanvas.width = width;
  resultCanvas.height = height;
  const resultCtx = resultCanvas.getContext('2d')!;

  // Get layer data
  const layerCtx = layerCanvas.getContext('2d')!;
  const layerData = layerCtx.getImageData(0, 0, width, height);
  const layer = layerData.data;

  // Get mask data
  const maskCtx = combinedMask.getContext('2d')!;
  const maskData = maskCtx.getImageData(0, 0, width, height);
  const mask = maskData.data;

  // Apply mask to alpha channel
  for (let i = 0; i < layer.length; i += 4) {
    const maskValue = mask[i] / 255; // Use red channel as grayscale
    layer[i + 3] = Math.round(layer[i + 3] * maskValue);
  }

  resultCtx.putImageData(layerData, 0, 0);
  return resultCanvas;
}

// ============================================================================
// EXPORTS
// ============================================================================

export default {
  renderMask,
  combineMasks,
  applyTrackMatte,
  applyMasksToLayer,
};
