/**
 * Browser Test Setup
 * 
 * Utilities for testing Canvas, WebGL, WebGPU, and Web Audio
 * in a real browser environment via Playwright.
 */

/**
 * Create a test canvas with 2D context
 */
export function createTestCanvas(width = 256, height = 256): {
  canvas: HTMLCanvasElement;
  ctx: CanvasRenderingContext2D;
} {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext('2d');
  if (!ctx) throw new Error('Failed to get 2D context');
  return { canvas, ctx };
}

/**
 * Create a test canvas with WebGL context
 */
export function createWebGLCanvas(width = 256, height = 256): {
  canvas: HTMLCanvasElement;
  gl: WebGLRenderingContext;
} | null {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  const gl = canvas.getContext('webgl');
  if (!gl) return null;
  return { canvas, gl };
}

/**
 * Create a test canvas with WebGL2 context
 */
export function createWebGL2Canvas(width = 256, height = 256): {
  canvas: HTMLCanvasElement;
  gl: WebGL2RenderingContext;
} | null {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  const gl = canvas.getContext('webgl2');
  if (!gl) return null;
  return { canvas, gl };
}

/**
 * Check if WebGPU is available
 */
export async function hasWebGPU(): Promise<boolean> {
  if (!navigator.gpu) return false;
  try {
    const adapter = await navigator.gpu.requestAdapter();
    return adapter !== null;
  } catch {
    return false;
  }
}

/**
 * Create AudioContext for Web Audio tests
 */
export function createAudioContext(): AudioContext | null {
  try {
    return new AudioContext();
  } catch {
    return null;
  }
}

/**
 * Get pixel data from canvas at specific location
 */
export function getPixelAt(
  ctx: CanvasRenderingContext2D,
  x: number,
  y: number
): { r: number; g: number; b: number; a: number } {
  const data = ctx.getImageData(x, y, 1, 1).data;
  return { r: data[0], g: data[1], b: data[2], a: data[3] };
}

/**
 * Compare two ImageData objects
 */
export function compareImageData(
  a: ImageData,
  b: ImageData,
  tolerance = 0
): boolean {
  if (a.width !== b.width || a.height !== b.height) return false;
  for (let i = 0; i < a.data.length; i++) {
    if (Math.abs(a.data[i] - b.data[i]) > tolerance) return false;
  }
  return true;
}

/**
 * Fill canvas with solid color for testing
 */
export function fillSolid(
  ctx: CanvasRenderingContext2D,
  color: string
): void {
  ctx.fillStyle = color;
  ctx.fillRect(0, 0, ctx.canvas.width, ctx.canvas.height);
}
