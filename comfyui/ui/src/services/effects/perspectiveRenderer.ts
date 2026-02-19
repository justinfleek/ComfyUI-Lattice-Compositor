/**
 * perspectiveRenderer.ts - 3D/Perspective Effect Renderers
 *
 * Renders depth-based effects like Fog 3D, Depth Matte, and 3D Glasses.
 * These effects use Z-depth information to create atmospheric and stereoscopic effects.
 */

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

export interface Fog3DParams {
  fogStartDepth: number;
  fogEndDepth: number;
  fogColor: { r: number; g: number; b: number };
  fogOpacity: number;
  scattering: number;
  gradientMode: "linear" | "exponential" | "exponential2";
  useCompCamera: boolean;
  layerDepth: number;
}

export interface DepthMatteParams {
  nearDepth: number;
  farDepth: number;
  invert: boolean;
  softness: number;
}

export interface Glasses3DParams {
  view3D: "red-cyan" | "green-magenta" | "amber-blue";
  leftView: "red" | "green" | "blue";
  rightView: "cyan" | "magenta" | "yellow";
  convergence: number;
  balance: number;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // fog // 3d // effect
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Calculate fog factor based on depth and gradient mode
 */
function calculateFogFactor(
  depth: number,
  startDepth: number,
  endDepth: number,
  mode: "linear" | "exponential" | "exponential2",
): number {
  // Normalize depth to 0-1 range
  const range = endDepth - startDepth;
  if (range === 0) return depth >= startDepth ? 1 : 0;

  const normalizedDepth = Math.max(
    0,
    Math.min(1, (depth - startDepth) / range),
  );

  switch (mode) {
    case "linear":
      return normalizedDepth;

    case "exponential": {
      // GL_EXP fog: f = e^(-density * depth)
      const density = 2.0; // Adjustable
      return 1 - Math.exp(-density * normalizedDepth);
    }

    case "exponential2": {
      // GL_EXP2 fog: f = e^(-(density * depth)^2)
      const density2 = 2.0;
      return 1 - Math.exp(-((density2 * normalizedDepth) ** 2));
    }

    default:
      return normalizedDepth;
  }
}

/**
 * Apply Fog 3D effect to an image based on depth
 */
export function applyFog3D(
  input: ImageData,
  depthMap: ImageData | null,
  params: Fog3DParams,
  cameraDepth: number = 0,
): ImageData {
  const output = new ImageData(
    new Uint8ClampedArray(input.data),
    input.width,
    input.height,
  );

  const data = output.data;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const depthData = (depthMap != null && typeof depthMap === "object" && "data" in depthMap && depthMap.data != null) ? depthMap.data : undefined;

  const fogR = params.fogColor.r;
  const fogG = params.fogColor.g;
  const fogB = params.fogColor.b;
  const maxOpacity = params.fogOpacity / 100;

  for (let i = 0; i < data.length; i += 4) {
    // Get depth value
    let depth: number;

    if (depthData) {
      // Use depth map (grayscale - higher value = further away)
      const depthValue = depthData[i]; // Use red channel
      // Map 0-255 to depth range
      const depthRange = params.fogEndDepth - params.fogStartDepth;
      depth = params.fogStartDepth + (depthValue / 255) * depthRange;
    } else {
      // Use layer depth parameter
      depth = params.layerDepth;
    }

    // Adjust for camera position if using comp camera
    if (params.useCompCamera) {
      depth -= cameraDepth;
    }

    // Calculate fog factor
    let fogFactor = calculateFogFactor(
      depth,
      params.fogStartDepth,
      params.fogEndDepth,
      params.gradientMode,
    );

    // Apply scattering (adds slight color variation)
    if (params.scattering > 0) {
      const scatter = params.scattering / 100;
      const pixelIndex = i / 4;
      const scatterNoise = Math.sin(pixelIndex * 0.1) * scatter * 0.1;
      fogFactor = Math.max(0, Math.min(1, fogFactor + scatterNoise));
    }

    // Apply maximum opacity
    fogFactor *= maxOpacity;

    // Blend original color with fog color
    data[i] = Math.round(data[i] * (1 - fogFactor) + fogR * fogFactor);
    data[i + 1] = Math.round(data[i + 1] * (1 - fogFactor) + fogG * fogFactor);
    data[i + 2] = Math.round(data[i + 2] * (1 - fogFactor) + fogB * fogFactor);
    // Alpha unchanged
  }

  return output;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                 // depth // matte // effect
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Create a matte based on Z-depth
 */
export function applyDepthMatte(
  input: ImageData,
  depthMap: ImageData | null,
  params: DepthMatteParams,
  layerDepth: number = 0,
): ImageData {
  const output = new ImageData(
    new Uint8ClampedArray(input.data),
    input.width,
    input.height,
  );

  const data = output.data;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const depthData = (depthMap != null && typeof depthMap === "object" && "data" in depthMap && depthMap.data != null) ? depthMap.data : undefined;

  const range = params.farDepth - params.nearDepth;
  const softnessFactor = params.softness / 100;

  for (let i = 0; i < data.length; i += 4) {
    // Get depth value
    let depth: number;

    if (depthData) {
      const depthValue = depthData[i];
      depth = params.nearDepth + (depthValue / 255) * range;
    } else {
      depth = layerDepth;
    }

    // Calculate matte value
    let matteValue: number;

    if (softnessFactor > 0) {
      // Soft edges
      const softRange = range * softnessFactor;
      if (depth <= params.nearDepth - softRange) {
        matteValue = 0;
      } else if (depth >= params.farDepth + softRange) {
        matteValue = 1;
      } else if (depth < params.nearDepth) {
        matteValue =
          ((depth - (params.nearDepth - softRange)) / softRange) * 0.5;
      } else if (depth > params.farDepth) {
        matteValue =
          0.5 + ((softRange - (depth - params.farDepth)) / softRange) * 0.5;
      } else {
        // Within range
        matteValue = (depth - params.nearDepth) / range;
      }
    } else {
      // Hard edges
      if (depth < params.nearDepth || depth > params.farDepth) {
        matteValue = 0;
      } else {
        matteValue = (depth - params.nearDepth) / range;
      }
    }

    // Apply invert
    if (params.invert) {
      matteValue = 1 - matteValue;
    }

    // Apply to alpha channel
    data[i + 3] = Math.round(data[i + 3] * matteValue);
  }

  return output;
}

// ═══════════════════════════════════════════════════════════════════════════
// 3D GLASSES (ANAGLYPH) EFFECT
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Apply anaglyph 3D glasses effect
 */
export function apply3DGlasses(
  leftImage: ImageData,
  rightImage: ImageData | null,
  params: Glasses3DParams,
): ImageData {
  const output = new ImageData(
    new Uint8ClampedArray(leftImage.data),
    leftImage.width,
    leftImage.height,
  );

  const leftData = leftImage.data;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const rightImageData = (rightImage != null && typeof rightImage === "object" && "data" in rightImage && rightImage.data != null) ? rightImage.data : undefined;
  const rightData = rightImageData != null ? rightImageData : leftImage.data;
  const outData = output.data;

  // Apply convergence offset
  const convergenceOffset = Math.round(params.convergence);
  const balanceFactor = (params.balance + 100) / 200; // 0 to 1

  for (let y = 0; y < leftImage.height; y++) {
    for (let x = 0; x < leftImage.width; x++) {
      const i = (y * leftImage.width + x) * 4;

      // Get offset indices for convergence
      const leftX = Math.max(
        0,
        Math.min(leftImage.width - 1, x - convergenceOffset),
      );
      const rightX = Math.max(
        0,
        Math.min(leftImage.width - 1, x + convergenceOffset),
      );

      const leftI = (y * leftImage.width + leftX) * 4;
      const rightI = (y * leftImage.width + rightX) * 4;

      // Get color channels
      const leftR = leftData[leftI];
      const leftG = leftData[leftI + 1];
      const leftB = leftData[leftI + 2];

      const rightR = rightData[rightI];
      const rightG = rightData[rightI + 1];
      const rightB = rightData[rightI + 2];

      // Apply anaglyph based on mode
      switch (params.view3D) {
        case "red-cyan":
          // Left eye = red channel, Right eye = cyan (green + blue)
          outData[i] = Math.round(
            leftR * balanceFactor + rightR * (1 - balanceFactor) * 0.3,
          );
          outData[i + 1] = Math.round(
            rightG * balanceFactor + leftG * (1 - balanceFactor) * 0.3,
          );
          outData[i + 2] = Math.round(
            rightB * balanceFactor + leftB * (1 - balanceFactor) * 0.3,
          );
          break;

        case "green-magenta":
          // Left eye = green, Right eye = magenta (red + blue)
          outData[i] = Math.round(
            rightR * balanceFactor + leftR * (1 - balanceFactor) * 0.3,
          );
          outData[i + 1] = Math.round(
            leftG * balanceFactor + rightG * (1 - balanceFactor) * 0.3,
          );
          outData[i + 2] = Math.round(
            rightB * balanceFactor + leftB * (1 - balanceFactor) * 0.3,
          );
          break;

        case "amber-blue":
          // Left eye = amber (red + green), Right eye = blue
          outData[i] = Math.round(
            leftR * balanceFactor + rightR * (1 - balanceFactor) * 0.3,
          );
          outData[i + 1] = Math.round(
            leftG * balanceFactor + rightG * (1 - balanceFactor) * 0.3,
          );
          outData[i + 2] = Math.round(
            rightB * balanceFactor + leftB * (1 - balanceFactor) * 0.3,
          );
          break;
      }

      // Preserve alpha
      outData[i + 3] = leftData[i + 3];
    }
  }

  return output;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                    // default // parameters
// ═══════════════════════════════════════════════════════════════════════════

export const DEFAULT_FOG_3D_PARAMS: Fog3DParams = {
  fogStartDepth: 0,
  fogEndDepth: 2000,
  fogColor: { r: 200, g: 200, b: 220 },
  fogOpacity: 100,
  scattering: 0,
  gradientMode: "linear",
  useCompCamera: true,
  layerDepth: 0,
};

export const DEFAULT_DEPTH_MATTE_PARAMS: DepthMatteParams = {
  nearDepth: 0,
  farDepth: 1000,
  invert: false,
  softness: 0,
};

export const DEFAULT_3D_GLASSES_PARAMS: Glasses3DParams = {
  view3D: "red-cyan",
  leftView: "red",
  rightView: "cyan",
  convergence: 0,
  balance: 0,
};
