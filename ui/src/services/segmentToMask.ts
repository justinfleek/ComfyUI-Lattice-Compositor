/**
 * Segmentation to Mask Conversion
 *
 * Converts binary segmentation masks (from SAM, SAM2, or other AI models)
 * into editable bezier mask paths.
 *
 * Process:
 * 1. Extract contour from binary mask
 * 2. Simplify contour using Douglas-Peucker algorithm
 * 3. Fit bezier curves to simplified points
 * 4. Create LayerMask with editable vertices
 */

import type {
  AnimatableProperty,
  LayerMask,
  MaskPath,
  MaskVertex,
} from "@/types/project";

// ============================================================================
// TYPES
// ============================================================================

export interface Point2D {
  x: number;
  y: number;
}

export interface ContourOptions {
  /** Minimum distance between contour points (default: 2) */
  minDistance?: number;
  /** Maximum points in the contour (default: 1000) */
  maxPoints?: number;
}

export interface SimplifyOptions {
  /** Tolerance for Douglas-Peucker simplification (default: 2.0) */
  tolerance?: number;
  /** Minimum points to keep (default: 4) */
  minPoints?: number;
  /** Maximum points to keep (default: 100) */
  maxPoints?: number;
}

export interface BezierFitOptions {
  /** Error tolerance for bezier fitting (default: 4.0) */
  error?: number;
  /** Maximum iterations for fitting (default: 100) */
  maxIterations?: number;
  /** Corner detection angle threshold in degrees (default: 60) */
  cornerThreshold?: number;
}

export interface SegmentToMaskOptions {
  contour?: ContourOptions;
  simplify?: SimplifyOptions;
  bezier?: BezierFitOptions;
  /** Mask name (default: "Mask from Segmentation") */
  name?: string;
  /** Mask color (default: "#FF00FF") */
  color?: string;
}

// ============================================================================
// CONTOUR EXTRACTION (Marching Squares)
// ============================================================================

/**
 * Extract contour points from a binary mask using marching squares algorithm
 *
 * @param mask - Binary mask (ImageData or 2D array)
 * @param threshold - Threshold for binary classification (default: 128)
 * @param options - Contour extraction options
 * @returns Array of contour points
 */
export function extractContour(
  mask: ImageData | number[][],
  threshold: number = 128,
  options: ContourOptions = {},
): Point2D[] {
  const { minDistance = 2, maxPoints = 1000 } = options;

  // Convert to 2D array if ImageData
  const data: number[][] = Array.isArray(mask)
    ? mask
    : imageDataToArray(mask, threshold);

  const height = data.length;
  const width = data[0]?.length ?? 0;

  if (height === 0 || width === 0) return [];

  // Find starting point (first edge pixel)
  let startX = -1;
  let startY = -1;

  outer: for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      if (data[y][x] === 1 && isEdgePixel(data, x, y)) {
        startX = x;
        startY = y;
        break outer;
      }
    }
  }

  if (startX === -1) return []; // No contour found

  // Trace contour using Moore neighborhood
  const contour: Point2D[] = [];
  const directions = [
    { dx: 1, dy: 0 }, // Right
    { dx: 1, dy: 1 }, // Down-right
    { dx: 0, dy: 1 }, // Down
    { dx: -1, dy: 1 }, // Down-left
    { dx: -1, dy: 0 }, // Left
    { dx: -1, dy: -1 }, // Up-left
    { dx: 0, dy: -1 }, // Up
    { dx: 1, dy: -1 }, // Up-right
  ];

  let x = startX;
  let y = startY;
  let dir = 0; // Start looking right
  let lastPoint: Point2D | null = null;

  do {
    // Add point if far enough from last
    if (!lastPoint || distance(lastPoint, { x, y }) >= minDistance) {
      contour.push({ x, y });
      lastPoint = { x, y };

      if (contour.length >= maxPoints) break;
    }

    // Moore neighborhood tracing
    let found = false;
    for (let i = 0; i < 8; i++) {
      const checkDir = (dir + 6 + i) % 8; // Start from back-left
      const { dx, dy } = directions[checkDir];
      const nx = x + dx;
      const ny = y + dy;

      if (
        nx >= 0 &&
        nx < width &&
        ny >= 0 &&
        ny < height &&
        data[ny][nx] === 1
      ) {
        x = nx;
        y = ny;
        dir = checkDir;
        found = true;
        break;
      }
    }

    if (!found) break; // Dead end
  } while (x !== startX || y !== startY || contour.length < 3);

  return contour;
}

/**
 * Convert ImageData to binary 2D array
 */
function imageDataToArray(imageData: ImageData, threshold: number): number[][] {
  const { width, height, data } = imageData;
  const result: number[][] = [];

  for (let y = 0; y < height; y++) {
    const row: number[] = [];
    for (let x = 0; x < width; x++) {
      const idx = (y * width + x) * 4;
      // Use alpha channel if available, otherwise use grayscale
      const value = data[idx + 3] > 0 ? data[idx] : 0;
      row.push(value >= threshold ? 1 : 0);
    }
    result.push(row);
  }

  return result;
}

/**
 * Check if a pixel is on the edge of the mask
 */
function isEdgePixel(data: number[][], x: number, y: number): boolean {
  const height = data.length;
  const width = data[0].length;

  if (data[y][x] !== 1) return false;

  // Check 4-neighbors
  const neighbors = [
    [x - 1, y],
    [x + 1, y],
    [x, y - 1],
    [x, y + 1],
  ];

  for (const [nx, ny] of neighbors) {
    if (nx < 0 || nx >= width || ny < 0 || ny >= height || data[ny][nx] === 0) {
      return true;
    }
  }

  return false;
}

// ============================================================================
// CONTOUR SIMPLIFICATION (Douglas-Peucker)
// ============================================================================

/**
 * Simplify contour using Douglas-Peucker algorithm
 *
 * @param points - Input contour points
 * @param options - Simplification options
 * @returns Simplified points
 */
export function simplifyContour(
  points: Point2D[],
  options: SimplifyOptions = {},
): Point2D[] {
  const { tolerance = 2.0, minPoints = 4, maxPoints = 100 } = options;

  if (points.length <= minPoints) return points;

  // Douglas-Peucker recursive simplification
  const simplified = douglasPeucker(points, tolerance);

  // Ensure minimum points
  if (simplified.length < minPoints) {
    return resampleContour(points, minPoints);
  }

  // Downsample if too many points
  if (simplified.length > maxPoints) {
    return resampleContour(simplified, maxPoints);
  }

  return simplified;
}

/**
 * Douglas-Peucker recursive simplification
 */
function douglasPeucker(points: Point2D[], epsilon: number): Point2D[] {
  if (points.length <= 2) return points;

  // Find the point with maximum distance from line
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

  // If max distance is greater than epsilon, recursively simplify
  if (maxDist > epsilon) {
    const left = douglasPeucker(points.slice(0, maxIndex + 1), epsilon);
    const right = douglasPeucker(points.slice(maxIndex), epsilon);
    return [...left.slice(0, -1), ...right];
  }

  return [start, end];
}

/**
 * Calculate perpendicular distance from point to line
 */
function perpendicularDistance(
  point: Point2D,
  lineStart: Point2D,
  lineEnd: Point2D,
): number {
  const dx = lineEnd.x - lineStart.x;
  const dy = lineEnd.y - lineStart.y;
  const length = Math.sqrt(dx * dx + dy * dy);

  if (length === 0) return distance(point, lineStart);

  const t = Math.max(
    0,
    Math.min(
      1,
      ((point.x - lineStart.x) * dx + (point.y - lineStart.y) * dy) /
        (length * length),
    ),
  );

  const projX = lineStart.x + t * dx;
  const projY = lineStart.y + t * dy;

  return distance(point, { x: projX, y: projY });
}

/**
 * Resample contour to target number of points
 */
function resampleContour(points: Point2D[], targetCount: number): Point2D[] {
  if (points.length <= targetCount) return points;

  const result: Point2D[] = [points[0]];
  const step = (points.length - 1) / (targetCount - 1);

  for (let i = 1; i < targetCount - 1; i++) {
    const idx = Math.round(i * step);
    result.push(points[idx]);
  }

  result.push(points[points.length - 1]);
  return result;
}

// ============================================================================
// BEZIER FITTING
// ============================================================================

/**
 * Fit bezier curves to simplified contour points
 *
 * This uses a simplified approach that:
 * 1. Detects corners (high angle changes)
 * 2. Fits smooth curves between corners
 *
 * @param points - Simplified contour points
 * @param options - Bezier fitting options
 * @returns Array of MaskVertex with bezier handles
 */
export function fitBezierToContour(
  points: Point2D[],
  options: BezierFitOptions = {},
): MaskVertex[] {
  const { cornerThreshold = 60 } = options;

  if (points.length < 2) return [];

  const vertices: MaskVertex[] = [];

  // Detect corners and create vertices
  for (let i = 0; i < points.length; i++) {
    const prev = points[(i - 1 + points.length) % points.length];
    const curr = points[i];
    const next = points[(i + 1) % points.length];

    const angle = calculateAngle(prev, curr, next);
    const isCorner = Math.abs(180 - angle) > cornerThreshold;

    if (isCorner) {
      // Corner vertex - no tangents
      vertices.push({
        x: curr.x,
        y: curr.y,
        inTangentX: 0,
        inTangentY: 0,
        outTangentX: 0,
        outTangentY: 0,
      });
    } else {
      // Smooth vertex - calculate tangents
      const tangentLength = Math.min(
        distance(prev, curr) / 3,
        distance(curr, next) / 3,
      );

      // Direction from prev to next (smoothed)
      const dx = next.x - prev.x;
      const dy = next.y - prev.y;
      const len = Math.sqrt(dx * dx + dy * dy);

      if (len > 0) {
        const nx = (dx / len) * tangentLength;
        const ny = (dy / len) * tangentLength;

        vertices.push({
          x: curr.x,
          y: curr.y,
          inTangentX: -nx,
          inTangentY: -ny,
          outTangentX: nx,
          outTangentY: ny,
        });
      } else {
        vertices.push({
          x: curr.x,
          y: curr.y,
          inTangentX: 0,
          inTangentY: 0,
          outTangentX: 0,
          outTangentY: 0,
        });
      }
    }
  }

  return vertices;
}

/**
 * Calculate angle between three points (in degrees)
 */
function calculateAngle(a: Point2D, b: Point2D, c: Point2D): number {
  const ba = { x: a.x - b.x, y: a.y - b.y };
  const bc = { x: c.x - b.x, y: c.y - b.y };

  const dot = ba.x * bc.x + ba.y * bc.y;
  const cross = ba.x * bc.y - ba.y * bc.x;

  return Math.abs(Math.atan2(cross, dot) * (180 / Math.PI));
}

/**
 * Calculate distance between two points
 */
function distance(a: Point2D, b: Point2D): number {
  const dx = b.x - a.x;
  const dy = b.y - a.y;
  return Math.sqrt(dx * dx + dy * dy);
}

// ============================================================================
// MAIN CONVERSION FUNCTION
// ============================================================================

/**
 * Convert a segmentation mask to an editable LayerMask
 *
 * @param mask - Binary segmentation mask (ImageData, canvas, or 2D array)
 * @param options - Conversion options
 * @returns LayerMask with bezier path
 */
export function segmentationToMask(
  mask: ImageData | HTMLCanvasElement | number[][],
  options: SegmentToMaskOptions = {},
): LayerMask | null {
  const { name = "Mask from Segmentation", color = "#FF00FF" } = options;

  // Convert canvas to ImageData if needed
  let imageData: ImageData | number[][];
  if (mask instanceof HTMLCanvasElement) {
    const ctx = mask.getContext("2d");
    if (!ctx) return null;
    imageData = ctx.getImageData(0, 0, mask.width, mask.height);
  } else {
    imageData = mask;
  }

  // Extract contour
  const contour = extractContour(imageData, 128, options.contour);
  if (contour.length < 3) {
    console.warn("Segmentation mask produced too few contour points");
    return null;
  }

  // Simplify contour
  const simplified = simplifyContour(contour, options.simplify);

  // Fit bezier curves
  const vertices = fitBezierToContour(simplified, options.bezier);
  if (vertices.length < 3) {
    console.warn("Bezier fitting produced too few vertices");
    return null;
  }

  // Create unique ID
  const maskId = `mask_seg_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;

  // Create mask path
  const path: MaskPath = {
    closed: true,
    vertices,
  };

  // Create animatable properties
  const pathProp: AnimatableProperty<MaskPath> = {
    id: `path_${maskId}`,
    name: "Mask Path",
    type: "position",
    value: path,
    animated: false,
    keyframes: [],
  };

  const opacityProp: AnimatableProperty<number> = {
    id: `opacity_${maskId}`,
    name: "Mask Opacity",
    type: "number",
    value: 100,
    animated: false,
    keyframes: [],
  };

  const featherProp: AnimatableProperty<number> = {
    id: `feather_${maskId}`,
    name: "Mask Feather",
    type: "number",
    value: 0,
    animated: false,
    keyframes: [],
  };

  const expansionProp: AnimatableProperty<number> = {
    id: `expansion_${maskId}`,
    name: "Mask Expansion",
    type: "number",
    value: 0,
    animated: false,
    keyframes: [],
  };

  // Create LayerMask
  const layerMask: LayerMask = {
    id: maskId,
    name,
    enabled: true,
    locked: false,
    mode: "add",
    inverted: false,
    path: pathProp,
    opacity: opacityProp,
    feather: featherProp,
    expansion: expansionProp,
    color,
  };

  return layerMask;
}

/**
 * Convert multiple segmentation regions to masks
 *
 * @param masks - Array of segmentation masks
 * @param options - Conversion options
 * @returns Array of LayerMasks
 */
export function batchSegmentationToMasks(
  masks: Array<ImageData | HTMLCanvasElement | number[][]>,
  options: SegmentToMaskOptions = {},
): LayerMask[] {
  const colors = [
    "#FF00FF",
    "#00FFFF",
    "#FFFF00",
    "#FF8800",
    "#88FF00",
    "#0088FF",
  ];

  return masks
    .map((mask, index) => {
      const maskOptions = {
        ...options,
        name: options.name ?? `Segmentation ${index + 1}`,
        color: options.color ?? colors[index % colors.length],
      };

      return segmentationToMask(mask, maskOptions);
    })
    .filter((m): m is LayerMask => m !== null);
}

/**
 * Refine a mask by adding more control points
 * Useful after initial conversion for detailed editing
 *
 * @param mask - Existing LayerMask
 * @param targetPoints - Target number of points
 * @returns New LayerMask with more points
 */
export function refineMask(mask: LayerMask, targetPoints: number): LayerMask {
  const path = mask.path.value;
  if (!path || path.vertices.length >= targetPoints) {
    return mask;
  }

  const vertices = path.vertices;
  const newVertices: MaskVertex[] = [];

  // Add intermediate points between existing vertices
  const pointsToAdd = targetPoints - vertices.length;
  const ratio = pointsToAdd / (vertices.length - 1);

  for (let i = 0; i < vertices.length; i++) {
    newVertices.push(vertices[i]);

    if (i < vertices.length - 1 || path.closed) {
      const next = vertices[(i + 1) % vertices.length];
      const additions = Math.round(ratio);

      for (let j = 1; j <= additions; j++) {
        const t = j / (additions + 1);
        const newVertex: MaskVertex = {
          x: vertices[i].x + (next.x - vertices[i].x) * t,
          y: vertices[i].y + (next.y - vertices[i].y) * t,
          inTangentX: 0,
          inTangentY: 0,
          outTangentX: 0,
          outTangentY: 0,
        };
        newVertices.push(newVertex);
      }
    }
  }

  // Create new path
  const newPath: MaskPath = {
    closed: path.closed,
    vertices: newVertices,
  };

  return {
    ...mask,
    path: {
      ...mask.path,
      value: newPath,
    },
  };
}
