/**
 * Blur Effect Renderer
 *
 * Implements Gaussian Blur using the StackBlur algorithm.
 * StackBlur is a fast approximation of Gaussian blur that processes
 * pixels in a sliding window, making it O(n) per pixel regardless of radius.
 *
 * Based on: http://www.quasimondo.com/StackBlurForCanvas/StackBlurDemo.html
 */
import {
  registerEffectRenderer,
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams
} from '../effectProcessor';

/**
 * StackBlur multiplication lookup tables for fast integer division approximation
 */
const MUL_TABLE = [
  512, 512, 456, 512, 328, 456, 335, 512, 405, 328, 271, 456, 388, 335, 292, 512,
  454, 405, 364, 328, 298, 271, 496, 456, 420, 388, 360, 335, 312, 292, 273, 512,
  482, 454, 428, 405, 383, 364, 345, 328, 312, 298, 284, 271, 259, 496, 475, 456,
  437, 420, 404, 388, 374, 360, 347, 335, 323, 312, 302, 292, 282, 273, 265, 512,
  497, 482, 468, 454, 441, 428, 417, 405, 394, 383, 373, 364, 354, 345, 337, 328,
  320, 312, 305, 298, 291, 284, 278, 271, 265, 259, 507, 496, 485, 475, 465, 456,
  446, 437, 428, 420, 412, 404, 396, 388, 381, 374, 367, 360, 354, 347, 341, 335,
  329, 323, 318, 312, 307, 302, 297, 292, 287, 282, 278, 273, 269, 265, 261, 512,
  505, 497, 489, 482, 475, 468, 461, 454, 447, 441, 435, 428, 422, 417, 411, 405,
  399, 394, 389, 383, 378, 373, 368, 364, 359, 354, 350, 345, 341, 337, 332, 328,
  324, 320, 316, 312, 309, 305, 301, 298, 294, 291, 287, 284, 281, 278, 274, 271,
  268, 265, 262, 259, 257, 507, 501, 496, 491, 485, 480, 475, 470, 465, 460, 456,
  451, 446, 442, 437, 433, 428, 424, 420, 416, 412, 408, 404, 400, 396, 392, 388,
  385, 381, 377, 374, 370, 367, 363, 360, 357, 354, 350, 347, 344, 341, 338, 335,
  332, 329, 326, 323, 320, 318, 315, 312, 310, 307, 304, 302, 299, 297, 294, 292,
  289, 287, 285, 282, 280, 278, 275, 273, 271, 269, 267, 265, 263, 261, 259
];

const SHG_TABLE = [
  9, 11, 12, 13, 13, 14, 14, 15, 15, 15, 15, 16, 16, 16, 16, 17,
  17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 23,
  23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23,
  23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23,
  23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23,
  23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24
];

/**
 * BlurStack node for the sliding window
 */
interface BlurStack {
  r: number;
  g: number;
  b: number;
  a: number;
  next: BlurStack | null;
}

/**
 * Create a circular linked list of BlurStack nodes
 */
function createBlurStack(size: number): BlurStack {
  const first: BlurStack = { r: 0, g: 0, b: 0, a: 0, next: null };
  let current = first;

  for (let i = 1; i < size; i++) {
    current.next = { r: 0, g: 0, b: 0, a: 0, next: null };
    current = current.next;
  }

  current.next = first; // Make circular
  return first;
}

/**
 * Apply StackBlur to ImageData
 *
 * @param imageData - Source image data (will be modified in place)
 * @param radiusX - Horizontal blur radius (0-255)
 * @param radiusY - Vertical blur radius (0-255)
 */
function stackBlur(imageData: ImageData, radiusX: number, radiusY: number): void {
  const pixels = imageData.data;
  const width = imageData.width;
  const height = imageData.height;

  // Clamp radii
  radiusX = Math.max(0, Math.min(255, Math.round(radiusX)));
  radiusY = Math.max(0, Math.min(255, Math.round(radiusY)));

  if (radiusX === 0 && radiusY === 0) return;

  // Horizontal pass
  if (radiusX > 0) {
    stackBlurHorizontal(pixels, width, height, radiusX);
  }

  // Vertical pass
  if (radiusY > 0) {
    stackBlurVertical(pixels, width, height, radiusY);
  }
}

/**
 * Horizontal blur pass
 */
function stackBlurHorizontal(
  pixels: Uint8ClampedArray,
  width: number,
  height: number,
  radius: number
): void {
  const div = radius + radius + 1;
  const widthMinus1 = width - 1;
  const mulSum = MUL_TABLE[radius];
  const shgSum = SHG_TABLE[radius];

  const stack = createBlurStack(div);

  for (let y = 0; y < height; y++) {
    let rInSum = 0, gInSum = 0, bInSum = 0, aInSum = 0;
    let rOutSum = 0, gOutSum = 0, bOutSum = 0, aOutSum = 0;
    let rSum = 0, gSum = 0, bSum = 0, aSum = 0;

    const yOffset = y * width;
    let stackIn = stack;
    let stackOut = stack;

    // Initialize stack with first pixel repeated
    const pr = pixels[(yOffset) * 4];
    const pg = pixels[(yOffset) * 4 + 1];
    const pb = pixels[(yOffset) * 4 + 2];
    const pa = pixels[(yOffset) * 4 + 3];

    for (let i = 0; i <= radius; i++) {
      stackIn.r = pr;
      stackIn.g = pg;
      stackIn.b = pb;
      stackIn.a = pa;

      const rbs = radius + 1 - i;
      rSum += pr * rbs;
      gSum += pg * rbs;
      bSum += pb * rbs;
      aSum += pa * rbs;

      if (i > 0) {
        rInSum += pr;
        gInSum += pg;
        bInSum += pb;
        aInSum += pa;
      } else {
        rOutSum += pr;
        gOutSum += pg;
        bOutSum += pb;
        aOutSum += pa;
      }

      stackIn = stackIn.next!;
    }

    // Fill rest of stack with right-side pixels
    for (let i = 1; i <= radius; i++) {
      const p = Math.min(i, widthMinus1);
      const pOffset = (yOffset + p) * 4;
      const pr = pixels[pOffset];
      const pg = pixels[pOffset + 1];
      const pb = pixels[pOffset + 2];
      const pa = pixels[pOffset + 3];

      stackIn.r = pr;
      stackIn.g = pg;
      stackIn.b = pb;
      stackIn.a = pa;

      const rbs = radius + 1 - i;
      rSum += pr * rbs;
      gSum += pg * rbs;
      bSum += pb * rbs;
      aSum += pa * rbs;

      rInSum += pr;
      gInSum += pg;
      bInSum += pb;
      aInSum += pa;

      stackIn = stackIn.next!;
    }

    // Find stack start for output
    let stackStart = stack;
    for (let i = 0; i < radius; i++) {
      stackStart = stackStart.next!;
    }
    stackOut = stackStart.next!;

    // Process each pixel in the row
    for (let x = 0; x < width; x++) {
      const pOffset = (yOffset + x) * 4;

      pixels[pOffset] = (rSum * mulSum) >>> shgSum;
      pixels[pOffset + 1] = (gSum * mulSum) >>> shgSum;
      pixels[pOffset + 2] = (bSum * mulSum) >>> shgSum;
      pixels[pOffset + 3] = (aSum * mulSum) >>> shgSum;

      rSum -= rOutSum;
      gSum -= gOutSum;
      bSum -= bOutSum;
      aSum -= aOutSum;

      rOutSum -= stackStart.r;
      gOutSum -= stackStart.g;
      bOutSum -= stackStart.b;
      aOutSum -= stackStart.a;

      const p = Math.min(x + radius + 1, widthMinus1);
      const pIn = (yOffset + p) * 4;

      stackStart.r = pixels[pIn];
      stackStart.g = pixels[pIn + 1];
      stackStart.b = pixels[pIn + 2];
      stackStart.a = pixels[pIn + 3];

      rInSum += stackStart.r;
      gInSum += stackStart.g;
      bInSum += stackStart.b;
      aInSum += stackStart.a;

      rSum += rInSum;
      gSum += gInSum;
      bSum += bInSum;
      aSum += aInSum;

      stackStart = stackStart.next!;

      rOutSum += stackOut.r;
      gOutSum += stackOut.g;
      bOutSum += stackOut.b;
      aOutSum += stackOut.a;

      rInSum -= stackOut.r;
      gInSum -= stackOut.g;
      bInSum -= stackOut.b;
      aInSum -= stackOut.a;

      stackOut = stackOut.next!;
    }
  }
}

/**
 * Vertical blur pass
 */
function stackBlurVertical(
  pixels: Uint8ClampedArray,
  width: number,
  height: number,
  radius: number
): void {
  const div = radius + radius + 1;
  const heightMinus1 = height - 1;
  const mulSum = MUL_TABLE[radius];
  const shgSum = SHG_TABLE[radius];

  const stack = createBlurStack(div);

  for (let x = 0; x < width; x++) {
    let rInSum = 0, gInSum = 0, bInSum = 0, aInSum = 0;
    let rOutSum = 0, gOutSum = 0, bOutSum = 0, aOutSum = 0;
    let rSum = 0, gSum = 0, bSum = 0, aSum = 0;

    let stackIn = stack;
    let stackOut = stack;

    // Initialize stack with first pixel repeated
    const pr = pixels[x * 4];
    const pg = pixels[x * 4 + 1];
    const pb = pixels[x * 4 + 2];
    const pa = pixels[x * 4 + 3];

    for (let i = 0; i <= radius; i++) {
      stackIn.r = pr;
      stackIn.g = pg;
      stackIn.b = pb;
      stackIn.a = pa;

      const rbs = radius + 1 - i;
      rSum += pr * rbs;
      gSum += pg * rbs;
      bSum += pb * rbs;
      aSum += pa * rbs;

      if (i > 0) {
        rInSum += pr;
        gInSum += pg;
        bInSum += pb;
        aInSum += pa;
      } else {
        rOutSum += pr;
        gOutSum += pg;
        bOutSum += pb;
        aOutSum += pa;
      }

      stackIn = stackIn.next!;
    }

    // Fill rest of stack with bottom pixels
    for (let i = 1; i <= radius; i++) {
      const p = Math.min(i, heightMinus1);
      const pOffset = (p * width + x) * 4;
      const pr = pixels[pOffset];
      const pg = pixels[pOffset + 1];
      const pb = pixels[pOffset + 2];
      const pa = pixels[pOffset + 3];

      stackIn.r = pr;
      stackIn.g = pg;
      stackIn.b = pb;
      stackIn.a = pa;

      const rbs = radius + 1 - i;
      rSum += pr * rbs;
      gSum += pg * rbs;
      bSum += pb * rbs;
      aSum += pa * rbs;

      rInSum += pr;
      gInSum += pg;
      bInSum += pb;
      aInSum += pa;

      stackIn = stackIn.next!;
    }

    // Find stack start for output
    let stackStart = stack;
    for (let i = 0; i < radius; i++) {
      stackStart = stackStart.next!;
    }
    stackOut = stackStart.next!;

    // Process each pixel in the column
    for (let y = 0; y < height; y++) {
      const pOffset = (y * width + x) * 4;

      pixels[pOffset] = (rSum * mulSum) >>> shgSum;
      pixels[pOffset + 1] = (gSum * mulSum) >>> shgSum;
      pixels[pOffset + 2] = (bSum * mulSum) >>> shgSum;
      pixels[pOffset + 3] = (aSum * mulSum) >>> shgSum;

      rSum -= rOutSum;
      gSum -= gOutSum;
      bSum -= bOutSum;
      aSum -= aOutSum;

      rOutSum -= stackStart.r;
      gOutSum -= stackStart.g;
      bOutSum -= stackStart.b;
      aOutSum -= stackStart.a;

      const p = Math.min(y + radius + 1, heightMinus1);
      const pIn = (p * width + x) * 4;

      stackStart.r = pixels[pIn];
      stackStart.g = pixels[pIn + 1];
      stackStart.b = pixels[pIn + 2];
      stackStart.a = pixels[pIn + 3];

      rInSum += stackStart.r;
      gInSum += stackStart.g;
      bInSum += stackStart.b;
      aInSum += stackStart.a;

      rSum += rInSum;
      gSum += gInSum;
      bSum += bInSum;
      aSum += aInSum;

      stackStart = stackStart.next!;

      rOutSum += stackOut.r;
      gOutSum += stackOut.g;
      bOutSum += stackOut.b;
      aOutSum += stackOut.a;

      rInSum -= stackOut.r;
      gInSum -= stackOut.g;
      bInSum -= stackOut.b;
      aInSum -= stackOut.a;

      stackOut = stackOut.next!;
    }
  }
}

/**
 * Gaussian Blur effect renderer
 *
 * Parameters:
 * - blurriness: Blur radius (0-250)
 * - blur_dimensions: 'both' | 'horizontal' | 'vertical'
 * - repeat_edge_pixels: boolean (handled by StackBlur edge handling)
 */
export function gaussianBlurRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const blurriness = params.blurriness ?? 10;
  const dimensions = params.blur_dimensions ?? 'both';

  // No blur needed
  if (blurriness <= 0) {
    return input;
  }

  // Create output canvas
  const output = createMatchingCanvas(input.canvas);

  // Get image data
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);

  // Determine radii based on dimensions
  let radiusX = 0;
  let radiusY = 0;

  switch (dimensions) {
    case 'horizontal':
      radiusX = blurriness;
      break;
    case 'vertical':
      radiusY = blurriness;
      break;
    case 'both':
    default:
      radiusX = blurriness;
      radiusY = blurriness;
      break;
  }

  // Apply StackBlur
  stackBlur(imageData, radiusX, radiusY);

  // Put processed data to output
  output.ctx.putImageData(imageData, 0, 0);

  return output;
}

/**
 * Register the Gaussian Blur effect renderer
 */
export function registerBlurEffects(): void {
  registerEffectRenderer('gaussian-blur', gaussianBlurRenderer);
}

export default {
  gaussianBlurRenderer,
  registerBlurEffects
};
