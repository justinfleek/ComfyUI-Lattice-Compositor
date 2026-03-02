// @ts-check
/**
 * Lattice CanvasPool FFI
 * Canvas element creation and management
 */

/**
 * Create a new canvas element with specified dimensions
 * @param {number} width
 * @param {number} height
 * @returns {function(): HTMLCanvasElement}
 */
export function createCanvas(width) {
  return (height) => () => {
    const canvas = document.createElement("canvas");
    canvas.width = width;
    canvas.height = height;
    return canvas;
  };
}

/**
 * Get 2D rendering context from canvas
 * @param {HTMLCanvasElement} canvas
 * @returns {function(): CanvasRenderingContext2D}
 */
export function getContext2D(canvas) {
  return () => {
    const ctx = canvas.getContext("2d");
    if (!ctx) {
      throw new Error("Failed to get 2D context from canvas");
    }
    return ctx;
  };
}

/**
 * Clear a rectangular region on the canvas
 * @param {CanvasRenderingContext2D} ctx
 * @param {number} x
 * @param {number} y
 * @param {number} width
 * @param {number} height
 * @returns {function(): void}
 */
export function clearRect(ctx) {
  return (x) => (y) => (width) => (height) => () => {
    ctx.clearRect(x, y, width, height);
  };
}

/**
 * Check if two canvas elements are the same
 * @param {HTMLCanvasElement} a
 * @param {HTMLCanvasElement} b
 * @returns {boolean}
 */
export function canvasEquals(a) {
  return (b) => a === b;
}
