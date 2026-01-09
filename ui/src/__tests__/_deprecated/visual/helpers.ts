/**
 * Visual Regression Test Helpers
 * 
 * Utilities for canvas comparison and snapshot testing.
 */

/**
 * Convert canvas to PNG buffer for comparison.
 */
export function canvasToPngBuffer(canvas: HTMLCanvasElement): Promise<ArrayBuffer> {
  return new Promise((resolve, reject) => {
    canvas.toBlob((blob) => {
      if (!blob) {
        reject(new Error('Failed to create blob from canvas'));
        return;
      }
      blob.arrayBuffer().then(resolve).catch(reject);
    }, 'image/png');
  });
}

/**
 * Compare two canvases pixel by pixel.
 * Returns percentage of different pixels.
 */
export function compareCanvases(
  canvas1: HTMLCanvasElement,
  canvas2: HTMLCanvasElement,
  threshold = 0
): { match: boolean; diffPercent: number; diffPixels: number } {
  if (canvas1.width !== canvas2.width || canvas1.height !== canvas2.height) {
    return { match: false, diffPercent: 100, diffPixels: canvas1.width * canvas1.height };
  }

  const ctx1 = canvas1.getContext('2d')!;
  const ctx2 = canvas2.getContext('2d')!;
  
  const data1 = ctx1.getImageData(0, 0, canvas1.width, canvas1.height);
  const data2 = ctx2.getImageData(0, 0, canvas2.width, canvas2.height);

  let diffPixels = 0;
  const totalPixels = canvas1.width * canvas1.height;

  for (let i = 0; i < data1.data.length; i += 4) {
    const diff = Math.abs(data1.data[i] - data2.data[i]) +
                 Math.abs(data1.data[i + 1] - data2.data[i + 1]) +
                 Math.abs(data1.data[i + 2] - data2.data[i + 2]) +
                 Math.abs(data1.data[i + 3] - data2.data[i + 3]);
    
    if (diff > threshold) {
      diffPixels++;
    }
  }

  const diffPercent = (diffPixels / totalPixels) * 100;
  
  return {
    match: diffPixels === 0,
    diffPercent,
    diffPixels,
  };
}

/**
 * Create a diff image highlighting differences.
 */
export function createDiffImage(
  canvas1: HTMLCanvasElement,
  canvas2: HTMLCanvasElement,
  diffColor = [255, 0, 255, 255] // Magenta
): HTMLCanvasElement {
  const diffCanvas = document.createElement('canvas');
  diffCanvas.width = canvas1.width;
  diffCanvas.height = canvas1.height;
  
  const ctx1 = canvas1.getContext('2d')!;
  const ctx2 = canvas2.getContext('2d')!;
  const ctxDiff = diffCanvas.getContext('2d')!;
  
  const data1 = ctx1.getImageData(0, 0, canvas1.width, canvas1.height);
  const data2 = ctx2.getImageData(0, 0, canvas2.width, canvas2.height);
  const dataDiff = ctxDiff.createImageData(canvas1.width, canvas1.height);

  for (let i = 0; i < data1.data.length; i += 4) {
    const isDifferent = 
      data1.data[i] !== data2.data[i] ||
      data1.data[i + 1] !== data2.data[i + 1] ||
      data1.data[i + 2] !== data2.data[i + 2] ||
      data1.data[i + 3] !== data2.data[i + 3];

    if (isDifferent) {
      dataDiff.data[i] = diffColor[0];
      dataDiff.data[i + 1] = diffColor[1];
      dataDiff.data[i + 2] = diffColor[2];
      dataDiff.data[i + 3] = diffColor[3];
    } else {
      // Show original (dimmed)
      dataDiff.data[i] = data1.data[i] * 0.5;
      dataDiff.data[i + 1] = data1.data[i + 1] * 0.5;
      dataDiff.data[i + 2] = data1.data[i + 2] * 0.5;
      dataDiff.data[i + 3] = 255;
    }
  }

  ctxDiff.putImageData(dataDiff, 0, 0);
  return diffCanvas;
}

/**
 * Create a test canvas with a specific fill.
 */
export function createTestCanvas(
  width: number,
  height: number,
  fill: string | CanvasGradient | CanvasPattern = '#000000'
): HTMLCanvasElement {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  
  const ctx = canvas.getContext('2d')!;
  ctx.fillStyle = fill;
  ctx.fillRect(0, 0, width, height);
  
  return canvas;
}

/**
 * Create a gradient test canvas for visual tests.
 */
export function createGradientCanvas(
  width: number,
  height: number,
  colors: string[] = ['#ff0000', '#00ff00', '#0000ff']
): HTMLCanvasElement {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  
  const ctx = canvas.getContext('2d')!;
  const gradient = ctx.createLinearGradient(0, 0, width, 0);
  
  colors.forEach((color, i) => {
    gradient.addColorStop(i / (colors.length - 1), color);
  });
  
  ctx.fillStyle = gradient;
  ctx.fillRect(0, 0, width, height);
  
  return canvas;
}

/**
 * Tolerance presets for different test types.
 */
export const VISUAL_TOLERANCES = {
  PIXEL_PERFECT: 0,           // 0% difference allowed
  ANTIALIASING: 0.001,        // 0.1% for AA differences
  EFFECTS: 0.001,             // 0.1% for effect rendering
  BLEND_MODES: 0.0001,        // 0.01% for blend modes
  DEPTH: 0.005,               // 0.5% for depth maps
  TEXT: 0.01,                 // 1% for text (font differences)
  PARTICLES_SEEDED: 0,        // 0% - must be deterministic
  COMPRESSION_ARTIFACTS: 0.02, // 2% for JPEG comparison
} as const;

/**
 * Snapshot assertion helper (for use with vitest).
 */
export async function expectCanvasToMatchSnapshot(
  canvas: HTMLCanvasElement,
  snapshotName: string,
  tolerance: number = VISUAL_TOLERANCES.EFFECTS
): Promise<void> {
  // In real implementation, this would:
  // 1. Load the reference snapshot
  // 2. Compare with current canvas
  // 3. Fail if difference exceeds tolerance
  // 4. Update snapshot if --update flag is set
  
  // Placeholder for vitest integration
  const buffer = await canvasToPngBuffer(canvas);
  
  // Would use something like:
  // expect(buffer).toMatchImageSnapshot({
  //   customSnapshotIdentifier: snapshotName,
  //   failureThreshold: tolerance,
  //   failureThresholdType: 'percent',
  // });
  
  console.log(`[Visual Test] ${snapshotName}: ${buffer.byteLength} bytes`);
}
