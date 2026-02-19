/**
 * Layer Style Renderers
 *
 * Industry-standard layer styles:
 * - Drop Shadow, Inner Shadow
 * - Outer Glow, Inner Glow
 * - Bevel and Emboss
 * - Satin
 * - Color Overlay, Gradient Overlay
 * - Stroke
 *
 * Styles render in fixed order (back to front):
 * 1. Drop Shadow (behind layer)
 * 2. Inner Shadow
 * 3. Outer Glow (behind layer)
 * 4. Inner Glow
 * 5. Bevel and Emboss
 * 6. Satin
 * 7. Color Overlay
 * 8. Gradient Overlay
 * 9. Stroke (on top)
 */

import type {
  BevelEmbossStyle,
  ColorOverlayStyle,
  DropShadowStyle,
  GlobalLightSettings,
  GradientOverlayStyle,
  InnerGlowStyle,
  InnerShadowStyle,
  LayerStyles,
  OuterGlowStyle,
  RGBA,
  SatinStyle,
  StrokeStyle,
} from "@/types/layerStyles";
import { isFiniteNumber } from "@/utils/typeGuards";
import type { AnimatableProperty } from "@/types/project";
import { canvasPool } from "@/utils/canvasPool";
// blendModes module provides blendImages, blendPixel etc. via default export
// import blendModes from '../blendModes';
import { interpolateProperty } from "../interpolation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // utility // functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Current frame for animation evaluation (set per render call)
 */
let currentFrame = 0;

/**
 * Set current frame for getValue calls
 */
export function setCurrentFrame(frame: number): void {
  currentFrame = frame;
}

/**
 * Get value from animatable property at current frame
 * Uses keyframe interpolation when property is animated
 */
function getValue<T>(
  prop: AnimatableProperty<T> | undefined,
  defaultValue: T,
): T {
  if (!prop) return defaultValue;

  // Use keyframe interpolation if property is animated
  if (prop.animated && prop.keyframes && prop.keyframes.length > 0) {
    const interpolated = interpolateProperty(prop, currentFrame);
    // Type proof: interpolated ∈ T | undefined, prop.value ∈ T | undefined → T
    const interpolatedValue = interpolated as T;
    if (interpolatedValue !== undefined && interpolatedValue !== null) {
      return interpolatedValue;
    }
    const propValue = prop.value;
    if (propValue !== undefined && propValue !== null) {
      return propValue as T;
    }
    return defaultValue;
  }

  // Type proof: prop.value ∈ T | undefined → T
  const propValue = prop.value;
  return propValue !== undefined && propValue !== null ? (propValue as T) : defaultValue;
}

/**
 * Create a canvas matching input dimensions using the canvas pool
 */
function createMatchingCanvas(source: HTMLCanvasElement): {
  canvas: HTMLCanvasElement;
  ctx: CanvasRenderingContext2D;
} {
  const result = canvasPool.acquire(source.width, source.height);
  return { canvas: result.canvas, ctx: result.ctx };
}

/**
 * Release a canvas back to the pool
 */
function releaseMatchingCanvas(canvas: HTMLCanvasElement): void {
  canvasPool.release(canvas);
}

/**
 * Convert RGBA to CSS color string
 */
function rgbaToString(color: RGBA, opacity: number = 1): string {
  return `rgba(${Math.round(color.r)}, ${Math.round(color.g)}, ${Math.round(color.b)}, ${color.a * opacity})`;
}

/**
 * Calculate offset from angle and distance
 */
function angleToOffset(
  angleDeg: number,
  distance: number,
): { x: number; y: number } {
  // Convert angle: 0° = right, 90° = up (matching Photoshop)
  const angleRad = ((angleDeg - 90) * Math.PI) / 180;
  return {
    x: Math.cos(angleRad) * distance,
    y: -Math.sin(angleRad) * distance,
  };
}

/**
 * Get alpha channel as separate canvas
 */
function extractAlpha(source: HTMLCanvasElement): ImageData {
  const ctx = source.getContext("2d", { willReadFrequently: true })!;
  return ctx.getImageData(0, 0, source.width, source.height);
}

/**
 * Apply Gaussian blur to canvas
 */
function applyBlur(canvas: HTMLCanvasElement, radius: number): void {
  if (radius <= 0) return;
  const ctx = canvas.getContext("2d")!;
  ctx.filter = `blur(${radius}px)`;
  const temp = createMatchingCanvas(canvas);
  try {
    temp.ctx.drawImage(canvas, 0, 0);
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.drawImage(temp.canvas, 0, 0);
    ctx.filter = "none";
  } finally {
    releaseMatchingCanvas(temp.canvas);
  }
}

/**
 * Dilate (expand) alpha channel
 */
function dilateAlpha(imageData: ImageData, amount: number): ImageData {
  if (amount <= 0) return imageData;

  const { width, height, data } = imageData;
  const result = new ImageData(width, height);
  const radius = Math.ceil(amount);

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let maxAlpha = 0;

      for (let dy = -radius; dy <= radius; dy++) {
        for (let dx = -radius; dx <= radius; dx++) {
          const dist = Math.sqrt(dx * dx + dy * dy);
          if (dist <= amount) {
            const nx = Math.min(width - 1, Math.max(0, x + dx));
            const ny = Math.min(height - 1, Math.max(0, y + dy));
            const idx = (ny * width + nx) * 4;
            maxAlpha = Math.max(maxAlpha, data[idx + 3]);
          }
        }
      }

      const idx = (y * width + x) * 4;
      result.data[idx] = data[idx];
      result.data[idx + 1] = data[idx + 1];
      result.data[idx + 2] = data[idx + 2];
      result.data[idx + 3] = maxAlpha;
    }
  }

  return result;
}

/**
 * Erode (shrink) alpha channel
 */
function erodeAlpha(imageData: ImageData, amount: number): ImageData {
  if (amount <= 0) return imageData;

  const { width, height, data } = imageData;
  const result = new ImageData(width, height);
  const radius = Math.ceil(amount);

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let minAlpha = 255;

      for (let dy = -radius; dy <= radius; dy++) {
        for (let dx = -radius; dx <= radius; dx++) {
          const dist = Math.sqrt(dx * dx + dy * dy);
          if (dist <= amount) {
            const nx = Math.min(width - 1, Math.max(0, x + dx));
            const ny = Math.min(height - 1, Math.max(0, y + dy));
            const idx = (ny * width + nx) * 4;
            minAlpha = Math.min(minAlpha, data[idx + 3]);
          }
        }
      }

      const idx = (y * width + x) * 4;
      result.data[idx] = data[idx];
      result.data[idx + 1] = data[idx + 1];
      result.data[idx + 2] = data[idx + 2];
      result.data[idx + 3] = minAlpha;
    }
  }

  return result;
}

// ════════════════════════════════════════════════════════════════════════════
//                                       // drop // shadow // style // renderer
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render drop shadow style
 */
export function renderDropShadowStyle(
  input: HTMLCanvasElement,
  style: DropShadowStyle,
  globalLight?: GlobalLightSettings,
): HTMLCanvasElement {
  if (!style.enabled) return input;

  const opacity = getValue(style.opacity, 75) / 100;
  const color = getValue(style.color, { r: 0, g: 0, b: 0, a: 1 });
  const angle =
    style.useGlobalLight && globalLight
      ? getValue(globalLight.angle, 120)
      : getValue(style.angle, 120);
  const distance = getValue(style.distance, 5);
  const spread = getValue(style.spread, 0);
  const size = getValue(style.size, 5);

  const { canvas: output, ctx } = createMatchingCanvas(input);
  const { x: offsetX, y: offsetY } = angleToOffset(angle, distance);

  // Create shadow layer
  const { canvas: shadowCanvas, ctx: shadowCtx } = createMatchingCanvas(input);

  try {
    // Draw input alpha as solid color for shadow
    shadowCtx.fillStyle = rgbaToString(color, 1);
    shadowCtx.fillRect(0, 0, shadowCanvas.width, shadowCanvas.height);
    shadowCtx.globalCompositeOperation = "destination-in";
    shadowCtx.drawImage(input, 0, 0);
    shadowCtx.globalCompositeOperation = "source-over";

    // Apply spread (choke)
    if (spread > 0) {
      const spreadAmount = (spread / 100) * size;
      const imageData = shadowCtx.getImageData(
        0,
        0,
        shadowCanvas.width,
        shadowCanvas.height,
      );
      const dilated = dilateAlpha(imageData, spreadAmount);
      shadowCtx.putImageData(dilated, 0, 0);
    }

    // Apply blur
    if (size > 0) {
      applyBlur(shadowCanvas, size * (1 - spread / 100));
    }

    // Draw shadow with offset
    ctx.globalAlpha = opacity;
    ctx.drawImage(shadowCanvas, offsetX, offsetY);
    ctx.globalAlpha = 1;

    // Draw original on top (unless knockedOut)
    if (!style.layerKnocksOut) {
      ctx.drawImage(input, 0, 0);
    } else {
      // Knock out shadow where original exists
      ctx.globalCompositeOperation = "destination-out";
      ctx.drawImage(input, 0, 0);
      ctx.globalCompositeOperation = "source-over";
      ctx.drawImage(input, 0, 0);
    }

    return output;
  } finally {
    releaseMatchingCanvas(shadowCanvas);
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                      // inner // shadow // style // renderer
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render inner shadow style
 */
export function renderInnerShadowStyle(
  input: HTMLCanvasElement,
  style: InnerShadowStyle,
  globalLight?: GlobalLightSettings,
): HTMLCanvasElement {
  if (!style.enabled) return input;

  const opacity = getValue(style.opacity, 75) / 100;
  const color = getValue(style.color, { r: 0, g: 0, b: 0, a: 1 });
  const angle =
    style.useGlobalLight && globalLight
      ? getValue(globalLight.angle, 120)
      : getValue(style.angle, 120);
  const distance = getValue(style.distance, 5);
  const choke = getValue(style.choke, 0);
  const size = getValue(style.size, 5);

  const { canvas: output, ctx } = createMatchingCanvas(input);
  const { x: offsetX, y: offsetY } = angleToOffset(angle, distance);

  // Start with original
  ctx.drawImage(input, 0, 0);

  // Create inverted alpha mask (shadow appears inside)
  const { canvas: shadowCanvas, ctx: shadowCtx } = createMatchingCanvas(input);
  const { canvas: clippedShadow, ctx: clippedCtx } = createMatchingCanvas(input);

  try {
    // Fill with shadow color
    shadowCtx.fillStyle = rgbaToString(color, 1);
    shadowCtx.fillRect(0, 0, shadowCanvas.width, shadowCanvas.height);

    // Cut out the layer shape (inverted)
    shadowCtx.globalCompositeOperation = "destination-out";
    shadowCtx.drawImage(input, -offsetX, -offsetY);
    shadowCtx.globalCompositeOperation = "source-over";

    // Apply choke
    if (choke > 0) {
      const chokeAmount = (choke / 100) * size;
      const imageData = shadowCtx.getImageData(
        0,
        0,
        shadowCanvas.width,
        shadowCanvas.height,
      );
      const eroded = erodeAlpha(imageData, chokeAmount);
      shadowCtx.putImageData(eroded, 0, 0);
    }

    // Apply blur
    if (size > 0) {
      applyBlur(shadowCanvas, size * (1 - choke / 100));
    }

    // Clip shadow to original shape
    clippedCtx.drawImage(shadowCanvas, 0, 0);
    clippedCtx.globalCompositeOperation = "destination-in";
    clippedCtx.drawImage(input, 0, 0);

    // Composite shadow onto output using blend mode
    ctx.globalAlpha = opacity;
    ctx.globalCompositeOperation =
      style.blendMode === "multiply" ? "multiply" : "source-over";
    ctx.drawImage(clippedShadow, 0, 0);
    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = "source-over";

    return output;
  } finally {
    releaseMatchingCanvas(shadowCanvas);
    releaseMatchingCanvas(clippedShadow);
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                        // outer // glow // style // renderer
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render outer glow style
 */
export function renderOuterGlowStyle(
  input: HTMLCanvasElement,
  style: OuterGlowStyle,
): HTMLCanvasElement {
  if (!style.enabled) return input;

  const opacity = getValue(style.opacity, 75) / 100;
  const color = getValue(style.color, { r: 255, g: 255, b: 190, a: 1 });
  const spread = getValue(style.spread, 0);
  const size = getValue(style.size, 5);

  const { canvas: output, ctx } = createMatchingCanvas(input);

  // Create glow layer
  const { canvas: glowCanvas, ctx: glowCtx } = createMatchingCanvas(input);

  try {
    // Draw input alpha as glow color
    glowCtx.fillStyle = rgbaToString(color, 1);
    glowCtx.fillRect(0, 0, glowCanvas.width, glowCanvas.height);
    glowCtx.globalCompositeOperation = "destination-in";
    glowCtx.drawImage(input, 0, 0);
    glowCtx.globalCompositeOperation = "source-over";

    // Apply spread
    if (spread > 0) {
      const spreadAmount = (spread / 100) * size;
      const imageData = glowCtx.getImageData(
        0,
        0,
        glowCanvas.width,
        glowCanvas.height,
      );
      const dilated = dilateAlpha(imageData, spreadAmount);
      glowCtx.putImageData(dilated, 0, 0);
    }

    // Apply blur
    if (size > 0) {
      applyBlur(glowCanvas, size);
    }

    // Draw glow behind original
    ctx.globalAlpha = opacity;
    ctx.globalCompositeOperation =
      style.blendMode === "screen" ? "screen" : "lighter";
    ctx.drawImage(glowCanvas, 0, 0);
    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = "source-over";

    // Draw original on top
    ctx.drawImage(input, 0, 0);

    return output;
  } finally {
    releaseMatchingCanvas(glowCanvas);
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                        // inner // glow // style // renderer
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render inner glow style
 */
export function renderInnerGlowStyle(
  input: HTMLCanvasElement,
  style: InnerGlowStyle,
): HTMLCanvasElement {
  if (!style.enabled) return input;

  const opacity = getValue(style.opacity, 75) / 100;
  const color = getValue(style.color, { r: 255, g: 255, b: 190, a: 1 });
  // Type proof: source ∈ string | undefined → string
  const source = typeof style.source === "string" ? style.source : "edge";
  const choke = getValue(style.choke, 0);
  const size = getValue(style.size, 5);

  const { canvas: output, ctx } = createMatchingCanvas(input);

  // Start with original
  ctx.drawImage(input, 0, 0);

  // Create glow layer
  const { canvas: glowCanvas, ctx: glowCtx } = createMatchingCanvas(input);
  const { canvas: clippedGlow, ctx: clippedCtx } = createMatchingCanvas(input);
  let erodedCanvas: HTMLCanvasElement | null = null;

  try {
    if (source === "edge") {
      // Glow from edges inward
      // Create inverted alpha for edge detection
      glowCtx.fillStyle = rgbaToString(color, 1);
      glowCtx.fillRect(0, 0, glowCanvas.width, glowCanvas.height);
      glowCtx.globalCompositeOperation = "destination-out";

      // Erode the shape to create edge glow
      const erodedResult = createMatchingCanvas(input);
      erodedCanvas = erodedResult.canvas;
      const erodedCtx = erodedResult.ctx;
      erodedCtx.drawImage(input, 0, 0);
      if (size > 0) {
        const imageData = erodedCtx.getImageData(
          0,
          0,
          erodedCanvas.width,
          erodedCanvas.height,
        );
        const eroded = erodeAlpha(imageData, size);
        erodedCtx.putImageData(eroded, 0, 0);
      }

      glowCtx.drawImage(erodedCanvas, 0, 0);
      glowCtx.globalCompositeOperation = "source-over";
    } else {
      // Glow from center
      // Create radial gradient from center
      const centerX = glowCanvas.width / 2;
      const centerY = glowCanvas.height / 2;
      const maxDist = Math.sqrt(centerX * centerX + centerY * centerY);

      const gradient = glowCtx.createRadialGradient(
        centerX,
        centerY,
        0,
        centerX,
        centerY,
        maxDist,
      );
      gradient.addColorStop(0, rgbaToString(color, 1));
      gradient.addColorStop(1, rgbaToString(color, 0));

      glowCtx.fillStyle = gradient;
      glowCtx.fillRect(0, 0, glowCanvas.width, glowCanvas.height);
    }

    // Apply blur
    if (size > 0 && source === "edge") {
      applyBlur(glowCanvas, size * (1 - choke / 100));
    }

    // Clip glow to original shape
    clippedCtx.drawImage(glowCanvas, 0, 0);
    clippedCtx.globalCompositeOperation = "destination-in";
    clippedCtx.drawImage(input, 0, 0);

    // Composite glow onto output
    ctx.globalAlpha = opacity;
    ctx.globalCompositeOperation =
      style.blendMode === "screen" ? "screen" : "lighter";
    ctx.drawImage(clippedGlow, 0, 0);
    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = "source-over";

    return output;
  } finally {
    releaseMatchingCanvas(glowCanvas);
    releaseMatchingCanvas(clippedGlow);
    if (erodedCanvas) {
      releaseMatchingCanvas(erodedCanvas);
    }
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                               // bevel // and // emboss // style // renderer
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render bevel and emboss style
 */
export function renderBevelEmbossStyle(
  input: HTMLCanvasElement,
  style: BevelEmbossStyle,
  globalLight?: GlobalLightSettings,
): HTMLCanvasElement {
  if (!style.enabled) return input;

  const depth = getValue(style.depth, 100) / 100;
  const size = getValue(style.size, 5);
  const soften = getValue(style.soften, 0);
  const angle =
    style.useGlobalLight && globalLight
      ? getValue(globalLight.angle, 120)
      : getValue(style.angle, 120);
  const altitude = getValue(style.altitude, 30);
  const highlightColor = getValue(style.highlightColor, {
    r: 255,
    g: 255,
    b: 255,
    a: 1,
  });
  const shadowColor = getValue(style.shadowColor, { r: 0, g: 0, b: 0, a: 1 });
  const highlightOpacity = getValue(style.highlightOpacity, 75) / 100;
  const shadowOpacity = getValue(style.shadowOpacity, 75) / 100;

  const { canvas: output, ctx } = createMatchingCanvas(input);

  // Start with original
  ctx.drawImage(input, 0, 0);

  // Calculate light direction
  const lightAngleRad = ((angle - 90) * Math.PI) / 180;
  const lightX = Math.cos(lightAngleRad);
  const lightY = -Math.sin(lightAngleRad);
  const lightZ = Math.sin((altitude * Math.PI) / 180);

  // Create height map from alpha
  const inputCtx = input.getContext("2d", { willReadFrequently: true })!;
  const inputData = inputCtx.getImageData(0, 0, input.width, input.height);

  // Create highlight and shadow passes
  const { canvas: highlightCanvas, ctx: highlightCtx } =
    createMatchingCanvas(input);
  const { canvas: shadowCanvas, ctx: shadowCtx } = createMatchingCanvas(input);

  try {
    const highlightData = highlightCtx.createImageData(input.width, input.height);
    const shadowData = shadowCtx.createImageData(input.width, input.height);

    const width = input.width;
    const height = input.height;

    for (let y = 1; y < height - 1; y++) {
      for (let x = 1; x < width - 1; x++) {
        const idx = (y * width + x) * 4;
        const alpha = inputData.data[idx + 3];

        if (alpha === 0) continue;

        // Calculate normal from alpha gradients (Sobel-like)
        const leftIdx = (y * width + (x - 1)) * 4;
        const rightIdx = (y * width + (x + 1)) * 4;
        const topIdx = ((y - 1) * width + x) * 4;
        const bottomIdx = ((y + 1) * width + x) * 4;

        const gradX =
          (inputData.data[rightIdx + 3] - inputData.data[leftIdx + 3]) / 255;
        const gradY =
          (inputData.data[bottomIdx + 3] - inputData.data[topIdx + 3]) / 255;

        // Calculate lighting
        const normalX = -gradX * size * depth;
        const normalY = -gradY * size * depth;
        const normalZ = 1;
        const normalLen = Math.sqrt(
          normalX * normalX + normalY * normalY + normalZ * normalZ,
        );

        const dot =
          (normalX / normalLen) * lightX +
          (normalY / normalLen) * lightY +
          (normalZ / normalLen) * lightZ;

        if (dot > 0) {
          // Highlight
          const intensity = dot * highlightOpacity * (alpha / 255);
          highlightData.data[idx] = highlightColor.r;
          highlightData.data[idx + 1] = highlightColor.g;
          highlightData.data[idx + 2] = highlightColor.b;
          highlightData.data[idx + 3] = Math.min(255, intensity * 255);
        } else {
          // Shadow
          const intensity = -dot * shadowOpacity * (alpha / 255);
          shadowData.data[idx] = shadowColor.r;
          shadowData.data[idx + 1] = shadowColor.g;
          shadowData.data[idx + 2] = shadowColor.b;
          shadowData.data[idx + 3] = Math.min(255, intensity * 255);
        }
      }
    }

    highlightCtx.putImageData(highlightData, 0, 0);
    shadowCtx.putImageData(shadowData, 0, 0);

    // Apply soften blur
    if (soften > 0) {
      applyBlur(highlightCanvas, soften);
      applyBlur(shadowCanvas, soften);
    }

    // Composite highlight and shadow
    ctx.globalCompositeOperation =
      style.highlightMode === "screen" ? "screen" : "lighter";
    ctx.drawImage(highlightCanvas, 0, 0);

    ctx.globalCompositeOperation =
      style.shadowMode === "multiply" ? "multiply" : "darken";
    ctx.drawImage(shadowCanvas, 0, 0);

    ctx.globalCompositeOperation = "source-over";

    return output;
  } finally {
    releaseMatchingCanvas(highlightCanvas);
    releaseMatchingCanvas(shadowCanvas);
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                // satin // style // renderer
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render satin style
 */
export function renderSatinStyle(
  input: HTMLCanvasElement,
  style: SatinStyle,
): HTMLCanvasElement {
  if (!style.enabled) return input;

  const opacity = getValue(style.opacity, 50) / 100;
  const color = getValue(style.color, { r: 0, g: 0, b: 0, a: 1 });
  const angle = getValue(style.angle, 19);
  const distance = getValue(style.distance, 11);
  const size = getValue(style.size, 14);
  // Type proof: invert ∈ boolean | undefined → boolean
  const invert = typeof style.invert === "boolean" ? style.invert : true;

  const { canvas: output, ctx } = createMatchingCanvas(input);

  // Start with original
  ctx.drawImage(input, 0, 0);

  const { x: offsetX, y: offsetY } = angleToOffset(angle, distance);

  // Create satin effect by combining offset copies
  const { canvas: satinCanvas, ctx: satinCtx } = createMatchingCanvas(input);
  const { canvas: coloredCanvas, ctx: coloredCtx } = createMatchingCanvas(input);

  try {
    // Draw two offset copies of the alpha
    satinCtx.globalCompositeOperation = "source-over";
    satinCtx.drawImage(input, offsetX, offsetY);
    satinCtx.globalCompositeOperation = invert ? "xor" : "source-over";
    satinCtx.drawImage(input, -offsetX, -offsetY);

    // Apply blur
    if (size > 0) {
      applyBlur(satinCanvas, size);
    }

    // Colorize
    coloredCtx.fillStyle = rgbaToString(color, 1);
    coloredCtx.fillRect(0, 0, coloredCanvas.width, coloredCanvas.height);
    coloredCtx.globalCompositeOperation = "destination-in";
    coloredCtx.drawImage(satinCanvas, 0, 0);

    // Clip to original shape
    coloredCtx.globalCompositeOperation = "destination-in";
    coloredCtx.drawImage(input, 0, 0);

    // Composite
    ctx.globalAlpha = opacity;
    ctx.globalCompositeOperation =
      style.blendMode === "multiply" ? "multiply" : "source-over";
    ctx.drawImage(coloredCanvas, 0, 0);
    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = "source-over";

    return output;
  } finally {
    releaseMatchingCanvas(satinCanvas);
    releaseMatchingCanvas(coloredCanvas);
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                     // color // overlay // style // renderer
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render color overlay style
 */
export function renderColorOverlayStyle(
  input: HTMLCanvasElement,
  style: ColorOverlayStyle,
): HTMLCanvasElement {
  if (!style.enabled) return input;

  const opacity = getValue(style.opacity, 100) / 100;
  const color = getValue(style.color, { r: 255, g: 0, b: 0, a: 1 });

  const { canvas: output, ctx } = createMatchingCanvas(input);

  // Start with original
  ctx.drawImage(input, 0, 0);

  // Create color overlay
  const { canvas: overlayCanvas, ctx: overlayCtx } =
    createMatchingCanvas(input);

  try {
    overlayCtx.fillStyle = rgbaToString(color, 1);
    overlayCtx.fillRect(0, 0, overlayCanvas.width, overlayCanvas.height);

    // Clip to original shape
    overlayCtx.globalCompositeOperation = "destination-in";
    overlayCtx.drawImage(input, 0, 0);

    // Apply with blend mode
    ctx.globalAlpha = opacity;

    // Map blend modes to canvas composite operations
    const compositeOp = getCompositeOperation(style.blendMode);
    ctx.globalCompositeOperation = compositeOp;
    ctx.drawImage(overlayCanvas, 0, 0);

    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = "source-over";

    return output;
  } finally {
    releaseMatchingCanvas(overlayCanvas);
  }
}

/**
 * Map blend mode to canvas composite operation
 */
function getCompositeOperation(blendMode: string): GlobalCompositeOperation {
  const modeMap: Record<string, GlobalCompositeOperation> = {
    normal: "source-over",
    multiply: "multiply",
    screen: "screen",
    overlay: "overlay",
    darken: "darken",
    lighten: "lighten",
    "color-dodge": "color-dodge",
    "color-burn": "color-burn",
    "hard-light": "hard-light",
    "soft-light": "soft-light",
    difference: "difference",
    exclusion: "exclusion",
    hue: "hue",
    saturation: "saturation",
    color: "color",
    luminosity: "luminosity",
  };
  // Type proof: modeMap[blendMode] ∈ string | undefined → string
  const mappedMode = modeMap[blendMode];
  return typeof mappedMode === "string" ? mappedMode : "source-over";
}

// ════════════════════════════════════════════════════════════════════════════
//                                  // gradient // overlay // style // renderer
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render gradient overlay style
 */
export function renderGradientOverlayStyle(
  input: HTMLCanvasElement,
  style: GradientOverlayStyle,
): HTMLCanvasElement {
  if (!style.enabled) return input;

  const opacity = getValue(style.opacity, 100) / 100;
  const gradientDef = getValue(style.gradient, {
    type: "linear",
    stops: [
      { position: 0, color: { r: 0, g: 0, b: 0, a: 1 } },
      { position: 1, color: { r: 255, g: 255, b: 255, a: 1 } },
    ],
  });
  const angle = getValue(style.angle, 90);
  const scale = getValue(style.scale, 100) / 100;
  const offset = getValue(style.offset, { x: 0, y: 0 });
  // Type proof: reverse ∈ boolean | undefined → boolean
  const reverse = typeof style.reverse === "boolean" ? style.reverse : false;

  const { canvas: output, ctx } = createMatchingCanvas(input);
  const { width, height } = input;

  // Start with original
  ctx.drawImage(input, 0, 0);

  // Create gradient overlay
  const { canvas: overlayCanvas, ctx: overlayCtx } =
    createMatchingCanvas(input);

  try {
    const centerX = width / 2 + offset.x;
    const centerY = height / 2 + offset.y;

    let gradient: CanvasGradient;

    switch (style.style) {
      case "radial":
      case "diamond": {
        const radius = (Math.max(width, height) * scale) / 2;
        gradient = overlayCtx.createRadialGradient(
          centerX,
          centerY,
          0,
          centerX,
          centerY,
          radius,
        );
        break;
      }
      case "angle": {
        // Angle gradient approximated with conic gradient (not directly supported)
        // Fall back to linear for now
        const angleRad = ((angle - 90) * Math.PI) / 180;
        const length = Math.max(width, height) * scale;
        gradient = overlayCtx.createLinearGradient(
          centerX - (Math.cos(angleRad) * length) / 2,
          centerY + (Math.sin(angleRad) * length) / 2,
          centerX + (Math.cos(angleRad) * length) / 2,
          centerY - (Math.sin(angleRad) * length) / 2,
        );
        break;
      }
      case "reflected": {
        // Reflected gradient: goes from edge to center to edge
        const angleRad = ((angle - 90) * Math.PI) / 180;
        const length = Math.max(width, height) * scale;
        gradient = overlayCtx.createLinearGradient(
          centerX - (Math.cos(angleRad) * length) / 2,
          centerY + (Math.sin(angleRad) * length) / 2,
          centerX + (Math.cos(angleRad) * length) / 2,
          centerY - (Math.sin(angleRad) * length) / 2,
        );
        // Add mirrored stops
        const stops = reverse
          ? [...gradientDef.stops].reverse()
          : gradientDef.stops;
        stops.forEach((stop) => {
          const pos = stop.position / 2; // First half
          gradient.addColorStop(pos, rgbaToString(stop.color, 1));
        });
        [...stops].reverse().forEach((stop) => {
          const pos = 0.5 + (1 - stop.position) / 2; // Second half mirrored
          gradient.addColorStop(pos, rgbaToString(stop.color, 1));
        });
        overlayCtx.fillStyle = gradient;
        overlayCtx.fillRect(0, 0, width, height);
        // Skip normal stop addition
        overlayCtx.globalCompositeOperation = "destination-in";
        overlayCtx.drawImage(input, 0, 0);
        ctx.globalAlpha = opacity;
        ctx.globalCompositeOperation = getCompositeOperation(style.blendMode);
        ctx.drawImage(overlayCanvas, 0, 0);
        ctx.globalAlpha = 1;
        ctx.globalCompositeOperation = "source-over";
        return output;
      }
      default: {
        const angleRad = ((angle - 90) * Math.PI) / 180;
        const length = Math.max(width, height) * scale;
        gradient = overlayCtx.createLinearGradient(
          centerX - (Math.cos(angleRad) * length) / 2,
          centerY + (Math.sin(angleRad) * length) / 2,
          centerX + (Math.cos(angleRad) * length) / 2,
          centerY - (Math.sin(angleRad) * length) / 2,
        );
        break;
      }
    }

    // Add gradient stops
    const stops = reverse ? [...gradientDef.stops].reverse() : gradientDef.stops;
    stops.forEach((stop) => {
      const pos = reverse ? 1 - stop.position : stop.position;
      gradient.addColorStop(pos, rgbaToString(stop.color, 1));
    });

    overlayCtx.fillStyle = gradient;
    overlayCtx.fillRect(0, 0, width, height);

    // Clip to original shape
    overlayCtx.globalCompositeOperation = "destination-in";
    overlayCtx.drawImage(input, 0, 0);

    // Apply with blend mode
    ctx.globalAlpha = opacity;
    ctx.globalCompositeOperation = getCompositeOperation(style.blendMode);
    ctx.drawImage(overlayCanvas, 0, 0);

    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = "source-over";

    return output;
  } finally {
    releaseMatchingCanvas(overlayCanvas);
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                               // stroke // style // renderer
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render stroke style
 */
export function renderStrokeStyle(
  input: HTMLCanvasElement,
  style: StrokeStyle,
): HTMLCanvasElement {
  if (!style.enabled) return input;

  const opacity = getValue(style.opacity, 100) / 100;
  const color = getValue(style.color, { r: 255, g: 0, b: 0, a: 1 });
  const size = getValue(style.size, 3);
  // Type proof: position ∈ string | undefined → string
  const position = typeof style.position === "string" ? style.position : "outside";

  const { canvas: output, ctx } = createMatchingCanvas(input);
  const { width, height } = input;

  // Get input image data for alpha processing
  const inputCtx = input.getContext("2d", { willReadFrequently: true })!;
  const inputData = inputCtx.getImageData(0, 0, width, height);

  // Create stroke based on position
  const { canvas: strokeCanvas, ctx: strokeCtx } = createMatchingCanvas(input);
  let erodedCanvas: HTMLCanvasElement | null = null;

  try {
    switch (position) {
      case "outside": {
        // Dilate alpha, then subtract original
        const dilatedData = dilateAlpha(inputData, size);
        strokeCtx.putImageData(dilatedData, 0, 0);
        strokeCtx.globalCompositeOperation = "destination-out";
        strokeCtx.drawImage(input, 0, 0);
        break;
      }
      case "inside": {
        // Original minus eroded
        strokeCtx.drawImage(input, 0, 0);
        const erodedData = erodeAlpha(inputData, size);
        const erodedResult = createMatchingCanvas(input);
        erodedCanvas = erodedResult.canvas;
        const erodedCtx = erodedResult.ctx;
        erodedCtx.putImageData(erodedData, 0, 0);
        strokeCtx.globalCompositeOperation = "destination-out";
        strokeCtx.drawImage(erodedCanvas, 0, 0);
        break;
      }
      case "center": {
        // Half outside, half inside
        const halfSize = size / 2;
        const dilatedData = dilateAlpha(inputData, halfSize);
        const erodedData = erodeAlpha(inputData, halfSize);

        strokeCtx.putImageData(dilatedData, 0, 0);
        const erodedResult = createMatchingCanvas(input);
        erodedCanvas = erodedResult.canvas;
        const erodedCtx = erodedResult.ctx;
        erodedCtx.putImageData(erodedData, 0, 0);
        strokeCtx.globalCompositeOperation = "destination-out";
        strokeCtx.drawImage(erodedCanvas, 0, 0);
        break;
      }
    }

    // Colorize stroke
    strokeCtx.globalCompositeOperation = "source-in";

    if (style.fillType === "gradient" && style.gradient) {
      // Apply gradient fill
      const gradientAngle = getValue(style.gradientAngle, 90);
      const angleRad = ((gradientAngle - 90) * Math.PI) / 180;
      const length = Math.max(width, height);
      const gradient = strokeCtx.createLinearGradient(
        width / 2 - (Math.cos(angleRad) * length) / 2,
        height / 2 + (Math.sin(angleRad) * length) / 2,
        width / 2 + (Math.cos(angleRad) * length) / 2,
        height / 2 - (Math.sin(angleRad) * length) / 2,
      );
      style.gradient.stops.forEach((stop) => {
        gradient.addColorStop(stop.position, rgbaToString(stop.color, 1));
      });
      strokeCtx.fillStyle = gradient;
    } else {
      strokeCtx.fillStyle = rgbaToString(color, 1);
    }
    strokeCtx.fillRect(0, 0, width, height);

    strokeCtx.globalCompositeOperation = "source-over";

    // Composite: stroke behind or on top depending on position
    if (position === "outside") {
      // Stroke behind
      ctx.globalAlpha = opacity;
      ctx.globalCompositeOperation = getCompositeOperation(style.blendMode);
      ctx.drawImage(strokeCanvas, 0, 0);
      ctx.globalAlpha = 1;
      ctx.globalCompositeOperation = "source-over";
      ctx.drawImage(input, 0, 0);
    } else {
      // Stroke on top (inside or center)
      ctx.drawImage(input, 0, 0);
      ctx.globalAlpha = opacity;
      ctx.globalCompositeOperation = getCompositeOperation(style.blendMode);
      ctx.drawImage(strokeCanvas, 0, 0);
      ctx.globalAlpha = 1;
      ctx.globalCompositeOperation = "source-over";
    }

    return output;
  } finally {
    releaseMatchingCanvas(strokeCanvas);
    if (erodedCanvas) {
      releaseMatchingCanvas(erodedCanvas);
    }
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                // main // render // function
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render all layer styles in the correct order
 *
 * Order (back to front):
 * 1. Drop Shadow
 * 2. Inner Shadow
 * 3. Outer Glow
 * 4. Inner Glow
 * 5. Bevel and Emboss
 * 6. Satin
 * 7. Color Overlay
 * 8. Gradient Overlay
 * 9. Stroke
 */
export function renderLayerStyles(
  input: HTMLCanvasElement,
  styles: LayerStyles,
  globalLight?: GlobalLightSettings,
): HTMLCanvasElement {
  if (!styles.enabled) return input;

  let result = input;

  // Apply Fill Opacity if blending options exist
  if (styles.blendingOptions) {
    const fillOpacity = getValue(styles.blendingOptions.fillOpacity, 100) / 100;
    if (fillOpacity < 1) {
      const { canvas: fadedCanvas, ctx: fadedCtx } =
        createMatchingCanvas(input);
      fadedCtx.globalAlpha = fillOpacity;
      fadedCtx.drawImage(input, 0, 0);
      result = fadedCanvas;
    }
  }

  // 1. Drop Shadow (renders behind)
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const dropShadow = (styles != null && typeof styles === "object" && "dropShadow" in styles && styles.dropShadow != null && typeof styles.dropShadow === "object") ? styles.dropShadow : undefined;
  if (dropShadow != null && typeof dropShadow === "object" && "enabled" in dropShadow && typeof dropShadow.enabled === "boolean" && dropShadow.enabled) {
    result = renderDropShadowStyle(result, dropShadow, globalLight);
  }

  // 2. Inner Shadow
  const innerShadow = (styles != null && typeof styles === "object" && "innerShadow" in styles && styles.innerShadow != null && typeof styles.innerShadow === "object") ? styles.innerShadow : undefined;
  if (innerShadow != null && typeof innerShadow === "object" && "enabled" in innerShadow && typeof innerShadow.enabled === "boolean" && innerShadow.enabled) {
    result = renderInnerShadowStyle(result, innerShadow, globalLight);
  }

  // 3. Outer Glow (renders behind)
  const outerGlow = (styles != null && typeof styles === "object" && "outerGlow" in styles && styles.outerGlow != null && typeof styles.outerGlow === "object") ? styles.outerGlow : undefined;
  if (outerGlow != null && typeof outerGlow === "object" && "enabled" in outerGlow && typeof outerGlow.enabled === "boolean" && outerGlow.enabled) {
    result = renderOuterGlowStyle(result, outerGlow);
  }

  // 4. Inner Glow
  const innerGlow = (styles != null && typeof styles === "object" && "innerGlow" in styles && styles.innerGlow != null && typeof styles.innerGlow === "object") ? styles.innerGlow : undefined;
  if (innerGlow != null && typeof innerGlow === "object" && "enabled" in innerGlow && typeof innerGlow.enabled === "boolean" && innerGlow.enabled) {
    result = renderInnerGlowStyle(result, innerGlow);
  }

  // 5. Bevel and Emboss
  const bevelEmboss = (styles != null && typeof styles === "object" && "bevelEmboss" in styles && styles.bevelEmboss != null && typeof styles.bevelEmboss === "object") ? styles.bevelEmboss : undefined;
  if (bevelEmboss != null && typeof bevelEmboss === "object" && "enabled" in bevelEmboss && typeof bevelEmboss.enabled === "boolean" && bevelEmboss.enabled) {
    result = renderBevelEmbossStyle(result, bevelEmboss, globalLight);
  }

  // 6. Satin
  const satin = (styles != null && typeof styles === "object" && "satin" in styles && styles.satin != null && typeof styles.satin === "object") ? styles.satin : undefined;
  if (satin != null && typeof satin === "object" && "enabled" in satin && typeof satin.enabled === "boolean" && satin.enabled) {
    result = renderSatinStyle(result, satin);
  }

  // 7. Color Overlay
  const colorOverlay = (styles != null && typeof styles === "object" && "colorOverlay" in styles && styles.colorOverlay != null && typeof styles.colorOverlay === "object") ? styles.colorOverlay : undefined;
  if (colorOverlay != null && typeof colorOverlay === "object" && "enabled" in colorOverlay && typeof colorOverlay.enabled === "boolean" && colorOverlay.enabled) {
    result = renderColorOverlayStyle(result, colorOverlay);
  }

  // 8. Gradient Overlay
  const gradientOverlay = (styles != null && typeof styles === "object" && "gradientOverlay" in styles && styles.gradientOverlay != null && typeof styles.gradientOverlay === "object") ? styles.gradientOverlay : undefined;
  if (gradientOverlay != null && typeof gradientOverlay === "object" && "enabled" in gradientOverlay && typeof gradientOverlay.enabled === "boolean" && gradientOverlay.enabled) {
    result = renderGradientOverlayStyle(result, gradientOverlay);
  }

  // 9. Stroke (renders on top)
  const stroke = (styles != null && typeof styles === "object" && "stroke" in styles && styles.stroke != null && typeof styles.stroke === "object") ? styles.stroke : undefined;
  if (stroke != null && typeof stroke === "object" && "enabled" in stroke && typeof stroke.enabled === "boolean" && stroke.enabled) {
    result = renderStrokeStyle(result, stroke);
  }

  return result;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // exports
// ════════════════════════════════════════════════════════════════════════════

export {
  getValue,
  createMatchingCanvas,
  rgbaToString,
  angleToOffset,
  extractAlpha,
  applyBlur,
  dilateAlpha,
  erodeAlpha,
  getCompositeOperation,
};
