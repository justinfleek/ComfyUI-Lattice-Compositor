/**
 * Image Trace Service
 *
 * Vectorizes raster images into bezier paths.
 * Similar to Adobe Illustrator's Image Trace feature.
 *
 * Uses Potrace-inspired algorithm for bitmap tracing.
 */

import type { Point2D, BezierPath, BezierVertex } from '@/types/shapes';
import { addPoints, subtractPoints, scalePoint, distance, normalize } from './shapeOperations';

// ============================================================================
// TYPES
// ============================================================================

export type TraceMode = 'blackAndWhite' | 'grayscale' | 'color';

export interface TraceOptions {
  mode: TraceMode;
  threshold: number;        // 0-255 for B&W mode
  colors: number;           // Max colors for color mode (2-256)
  cornerAngle: number;      // Degrees, threshold for corner detection
  pathFitting: number;      // Tolerance for path simplification (0-10)
  noiseReduction: number;   // Min area to keep (0-100 pixels)
  ignoreWhite: boolean;     // Don't trace white areas
  expandStrokes: boolean;   // Expand strokes to filled shapes
}

export interface TraceResult {
  paths: BezierPath[];
  colors: string[];         // Hex colors for each path
  width: number;
  height: number;
}

// ============================================================================
// DEFAULT OPTIONS
// ============================================================================

export const DEFAULT_TRACE_OPTIONS: TraceOptions = {
  mode: 'blackAndWhite',
  threshold: 128,
  colors: 16,
  cornerAngle: 20,
  pathFitting: 2,
  noiseReduction: 25,
  ignoreWhite: true,
  expandStrokes: false,
};

// ============================================================================
// MAIN TRACE FUNCTION
// ============================================================================

/**
 * Trace an image into vector paths
 */
export async function traceImage(
  source: HTMLImageElement | HTMLCanvasElement | ImageData,
  options: Partial<TraceOptions> = {}
): Promise<TraceResult> {
  const opts = { ...DEFAULT_TRACE_OPTIONS, ...options };

  // Get image data
  const imageData = getImageData(source);

  switch (opts.mode) {
    case 'blackAndWhite':
      return traceBlackAndWhite(imageData, opts);
    case 'grayscale':
      return traceGrayscale(imageData, opts);
    case 'color':
      return traceColor(imageData, opts);
    default:
      return traceBlackAndWhite(imageData, opts);
  }
}

/**
 * Get ImageData from various sources
 */
function getImageData(source: HTMLImageElement | HTMLCanvasElement | ImageData): ImageData {
  if (source instanceof ImageData) {
    return source;
  }

  const canvas = document.createElement('canvas');
  const ctx = canvas.getContext('2d')!;

  if (source instanceof HTMLImageElement) {
    canvas.width = source.naturalWidth || source.width;
    canvas.height = source.naturalHeight || source.height;
    ctx.drawImage(source, 0, 0);
  } else {
    canvas.width = source.width;
    canvas.height = source.height;
    ctx.drawImage(source, 0, 0);
  }

  return ctx.getImageData(0, 0, canvas.width, canvas.height);
}

// ============================================================================
// BLACK AND WHITE TRACING
// ============================================================================

/**
 * Trace black and white image
 */
function traceBlackAndWhite(imageData: ImageData, options: TraceOptions): TraceResult {
  const { width, height, data } = imageData;

  // Create binary bitmap
  const bitmap = new Uint8Array(width * height);
  for (let i = 0; i < width * height; i++) {
    const idx = i * 4;
    const gray = (data[idx] + data[idx + 1] + data[idx + 2]) / 3;
    bitmap[i] = gray < options.threshold ? 1 : 0;
  }

  // Extract contours
  const contours = extractContours(bitmap, width, height, options.noiseReduction);

  // Convert contours to bezier paths
  const paths = contours.map(contour =>
    contourToBezierPath(contour, options.cornerAngle, options.pathFitting)
  );

  return {
    paths,
    colors: paths.map(() => '#000000'),
    width,
    height,
  };
}

/**
 * Trace grayscale image (multiple threshold levels)
 */
function traceGrayscale(imageData: ImageData, options: TraceOptions): TraceResult {
  const { width, height, data } = imageData;
  const levels = Math.min(16, Math.max(2, Math.floor(options.colors)));

  const allPaths: BezierPath[] = [];
  const allColors: string[] = [];

  // Trace at different threshold levels
  for (let level = 0; level < levels; level++) {
    const threshold = Math.floor((255 * (level + 1)) / (levels + 1));

    // Create binary bitmap at this threshold
    const bitmap = new Uint8Array(width * height);
    for (let i = 0; i < width * height; i++) {
      const idx = i * 4;
      const gray = (data[idx] + data[idx + 1] + data[idx + 2]) / 3;
      bitmap[i] = gray < threshold ? 1 : 0;
    }

    // Extract contours
    const contours = extractContours(bitmap, width, height, options.noiseReduction);

    // Convert to paths
    for (const contour of contours) {
      const path = contourToBezierPath(contour, options.cornerAngle, options.pathFitting);
      allPaths.push(path);

      // Calculate grayscale color for this level
      const grayValue = Math.floor(255 * (1 - level / levels));
      const hex = grayValue.toString(16).padStart(2, '0');
      allColors.push(`#${hex}${hex}${hex}`);
    }
  }

  return {
    paths: allPaths,
    colors: allColors,
    width,
    height,
  };
}

/**
 * Trace color image
 */
function traceColor(imageData: ImageData, options: TraceOptions): TraceResult {
  const { width, height, data } = imageData;

  // Quantize colors
  const palette = quantizeColors(data, options.colors);

  const allPaths: BezierPath[] = [];
  const allColors: string[] = [];

  // Trace each color
  for (const color of palette) {
    // Create bitmap for this color
    const bitmap = new Uint8Array(width * height);
    for (let i = 0; i < width * height; i++) {
      const idx = i * 4;
      const r = data[idx];
      const g = data[idx + 1];
      const b = data[idx + 2];

      // Check if pixel matches this color (with tolerance)
      const dr = r - color.r;
      const dg = g - color.g;
      const db = b - color.b;
      const dist = Math.sqrt(dr * dr + dg * dg + db * db);

      bitmap[i] = dist < 50 ? 1 : 0; // Color tolerance
    }

    // Extract contours
    const contours = extractContours(bitmap, width, height, options.noiseReduction);

    // Convert to paths
    for (const contour of contours) {
      const path = contourToBezierPath(contour, options.cornerAngle, options.pathFitting);
      allPaths.push(path);

      // Convert color to hex
      const hex = `#${color.r.toString(16).padStart(2, '0')}${color.g.toString(16).padStart(2, '0')}${color.b.toString(16).padStart(2, '0')}`;
      allColors.push(hex);
    }
  }

  return {
    paths: allPaths,
    colors: allColors,
    width,
    height,
  };
}

// ============================================================================
// CONTOUR EXTRACTION (Marching Squares)
// ============================================================================

interface Contour {
  points: Point2D[];
  isHole: boolean;
}

/**
 * Extract contours from binary bitmap using marching squares
 */
function extractContours(
  bitmap: Uint8Array,
  width: number,
  height: number,
  minArea: number
): Contour[] {
  const visited = new Set<string>();
  const contours: Contour[] = [];

  // Pad bitmap to handle edge cases
  const padded = new Uint8Array((width + 2) * (height + 2));
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      padded[(y + 1) * (width + 2) + (x + 1)] = bitmap[y * width + x];
    }
  }

  // Find contour starting points
  for (let y = 0; y < height + 1; y++) {
    for (let x = 0; x < width + 1; x++) {
      const key = `${x},${y}`;
      if (visited.has(key)) continue;

      // Check if this is a contour edge
      const idx = y * (width + 2) + x;
      const tl = padded[idx];
      const tr = padded[idx + 1];
      const bl = padded[idx + (width + 2)];
      const br = padded[idx + (width + 2) + 1];

      const pattern = (tl << 3) | (tr << 2) | (br << 1) | bl;

      // If there's a transition, trace the contour
      if (pattern !== 0 && pattern !== 15) {
        const contour = traceContour(padded, width + 2, height + 2, x, y, visited);
        if (contour.points.length >= 3) {
          // Calculate area
          const area = calculateContourArea(contour.points);
          if (Math.abs(area) >= minArea) {
            contour.isHole = area < 0;
            contours.push(contour);
          }
        }
      }
    }
  }

  return contours;
}

/**
 * Trace a single contour using marching squares
 */
function traceContour(
  bitmap: Uint8Array,
  width: number,
  height: number,
  startX: number,
  startY: number,
  visited: Set<string>
): Contour {
  const points: Point2D[] = [];
  let x = startX;
  let y = startY;
  let prevDir = 0;

  const directions = [
    { dx: 1, dy: 0 },   // Right
    { dx: 0, dy: 1 },   // Down
    { dx: -1, dy: 0 },  // Left
    { dx: 0, dy: -1 },  // Up
  ];

  // Marching squares lookup table
  const getNextDir = (pattern: number, prevDir: number): number => {
    // Simplified direction lookup
    switch (pattern) {
      case 1: return 3; // Up
      case 2: return 0; // Right
      case 3: return 0; // Right
      case 4: return 1; // Down
      case 5: return 3; // Saddle - prefer previous direction
      case 6: return 1; // Down
      case 7: return 0; // Right
      case 8: return 2; // Left
      case 9: return 3; // Up
      case 10: return prevDir; // Saddle - keep previous
      case 11: return 3; // Up
      case 12: return 2; // Left
      case 13: return 2; // Left
      case 14: return 1; // Down
      default: return 0;
    }
  };

  const maxIterations = width * height * 2;
  let iterations = 0;

  do {
    const key = `${x},${y}`;

    // Get marching squares pattern
    const idx = y * width + x;
    const tl = bitmap[idx] || 0;
    const tr = bitmap[idx + 1] || 0;
    const bl = bitmap[idx + width] || 0;
    const br = bitmap[idx + width + 1] || 0;

    const pattern = (tl << 3) | (tr << 2) | (br << 1) | bl;

    if (pattern === 0 || pattern === 15) break;

    // Add point (interpolate edge position)
    const point = getEdgePoint(x, y, pattern);
    points.push({ x: point.x - 1, y: point.y - 1 }); // Subtract padding offset

    visited.add(key);

    // Get next direction
    const nextDir = getNextDir(pattern, prevDir);
    x += directions[nextDir].dx;
    y += directions[nextDir].dy;
    prevDir = nextDir;

    iterations++;
  } while ((x !== startX || y !== startY) && iterations < maxIterations);

  return { points, isHole: false };
}

/**
 * Get interpolated edge point for marching squares
 */
function getEdgePoint(x: number, y: number, pattern: number): Point2D {
  // Return center of cell for simplicity
  // A more accurate implementation would interpolate along edges
  return { x: x + 0.5, y: y + 0.5 };
}

/**
 * Calculate signed area of contour (negative = clockwise = hole)
 */
function calculateContourArea(points: Point2D[]): number {
  let area = 0;
  for (let i = 0; i < points.length; i++) {
    const j = (i + 1) % points.length;
    area += points[i].x * points[j].y;
    area -= points[j].x * points[i].y;
  }
  return area / 2;
}

// ============================================================================
// CONTOUR TO BEZIER CONVERSION
// ============================================================================

/**
 * Convert a polygon contour to a bezier path
 */
function contourToBezierPath(
  contour: Contour,
  cornerAngle: number,
  tolerance: number
): BezierPath {
  const points = contour.points;
  if (points.length < 3) {
    return { vertices: [], closed: true };
  }

  // Simplify the contour
  const simplified = douglasPeucker(points, tolerance);

  // Detect corners vs smooth points
  const cornerThreshold = Math.cos((180 - cornerAngle) * Math.PI / 180);
  const vertices: BezierVertex[] = [];

  for (let i = 0; i < simplified.length; i++) {
    const prev = simplified[(i - 1 + simplified.length) % simplified.length];
    const curr = simplified[i];
    const next = simplified[(i + 1) % simplified.length];

    // Calculate angle at this vertex
    const toPrev = normalize(subtractPoints(prev, curr));
    const toNext = normalize(subtractPoints(next, curr));
    const dotProd = toPrev.x * toNext.x + toPrev.y * toNext.y;

    const isCorner = dotProd > cornerThreshold;

    // Calculate handle length based on neighboring distances
    const distPrev = distance(curr, prev);
    const distNext = distance(curr, next);
    const handleLength = Math.min(distPrev, distNext) / 3;

    if (isCorner) {
      // Sharp corner - no handles
      vertices.push({
        point: { x: curr.x, y: curr.y },
        inHandle: { x: 0, y: 0 },
        outHandle: { x: 0, y: 0 },
      });
    } else {
      // Smooth point - calculate tangent handles
      const avgDir = normalize({
        x: toNext.x - toPrev.x,
        y: toNext.y - toPrev.y,
      });

      vertices.push({
        point: { x: curr.x, y: curr.y },
        inHandle: { x: -avgDir.x * handleLength, y: -avgDir.y * handleLength },
        outHandle: { x: avgDir.x * handleLength, y: avgDir.y * handleLength },
      });
    }
  }

  return { vertices, closed: true };
}

/**
 * Douglas-Peucker simplification
 */
function douglasPeucker(points: Point2D[], tolerance: number): Point2D[] {
  if (points.length <= 2) return [...points];

  let maxDist = 0;
  let maxIndex = 0;

  const start = points[0];
  const end = points[points.length - 1];

  for (let i = 1; i < points.length - 1; i++) {
    const dist = perpendicularDistance(points[i], start, end);
    if (dist > maxDist) {
      maxDist = dist;
      maxIndex = i;
    }
  }

  if (maxDist > tolerance) {
    const left = douglasPeucker(points.slice(0, maxIndex + 1), tolerance);
    const right = douglasPeucker(points.slice(maxIndex), tolerance);
    return [...left.slice(0, -1), ...right];
  } else {
    return [start, end];
  }
}

/**
 * Perpendicular distance from point to line
 */
function perpendicularDistance(point: Point2D, lineStart: Point2D, lineEnd: Point2D): number {
  const dx = lineEnd.x - lineStart.x;
  const dy = lineEnd.y - lineStart.y;
  const length = Math.sqrt(dx * dx + dy * dy);

  if (length < 0.0001) return distance(point, lineStart);

  const t = ((point.x - lineStart.x) * dx + (point.y - lineStart.y) * dy) / (length * length);
  const closest = {
    x: lineStart.x + Math.max(0, Math.min(1, t)) * dx,
    y: lineStart.y + Math.max(0, Math.min(1, t)) * dy,
  };

  return distance(point, closest);
}

// ============================================================================
// COLOR QUANTIZATION
// ============================================================================

interface RGB {
  r: number;
  g: number;
  b: number;
}

/**
 * Quantize image colors using median cut algorithm
 */
function quantizeColors(data: Uint8ClampedArray, maxColors: number): RGB[] {
  // Collect all unique colors (sampling for performance)
  const colors: RGB[] = [];
  const step = Math.max(1, Math.floor(data.length / 4 / 10000));

  for (let i = 0; i < data.length; i += 4 * step) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    const a = data[i + 3];

    if (a > 128) { // Skip transparent pixels
      colors.push({ r, g, b });
    }
  }

  if (colors.length === 0) {
    return [{ r: 0, g: 0, b: 0 }];
  }

  // Apply median cut
  const buckets = medianCut(colors, maxColors);

  // Get average color of each bucket
  return buckets.map(bucket => {
    if (bucket.length === 0) return { r: 0, g: 0, b: 0 };

    let rSum = 0, gSum = 0, bSum = 0;
    for (const c of bucket) {
      rSum += c.r;
      gSum += c.g;
      bSum += c.b;
    }

    return {
      r: Math.round(rSum / bucket.length),
      g: Math.round(gSum / bucket.length),
      b: Math.round(bSum / bucket.length),
    };
  });
}

/**
 * Median cut algorithm for color quantization
 */
function medianCut(colors: RGB[], maxBuckets: number): RGB[][] {
  if (colors.length === 0) return [[]];

  let buckets: RGB[][] = [colors];

  while (buckets.length < maxBuckets) {
    // Find bucket with largest range
    let maxRange = 0;
    let maxBucketIdx = 0;
    let maxChannel: 'r' | 'g' | 'b' = 'r';

    for (let i = 0; i < buckets.length; i++) {
      const bucket = buckets[i];
      if (bucket.length < 2) continue;

      // Find range in each channel
      for (const channel of ['r', 'g', 'b'] as const) {
        const values = bucket.map(c => c[channel]);
        const range = Math.max(...values) - Math.min(...values);
        if (range > maxRange) {
          maxRange = range;
          maxBucketIdx = i;
          maxChannel = channel;
        }
      }
    }

    if (maxRange === 0) break;

    // Split the bucket at median
    const bucket = buckets[maxBucketIdx];
    bucket.sort((a, b) => a[maxChannel] - b[maxChannel]);

    const mid = Math.floor(bucket.length / 2);
    buckets.splice(maxBucketIdx, 1, bucket.slice(0, mid), bucket.slice(mid));
  }

  return buckets;
}

// ============================================================================
// EXPORTS
// ============================================================================

export const ImageTrace = {
  traceImage,
  DEFAULT_TRACE_OPTIONS,
};

export default ImageTrace;
