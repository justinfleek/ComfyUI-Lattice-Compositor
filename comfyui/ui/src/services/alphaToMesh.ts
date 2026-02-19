/**
 * Alpha-to-Mesh Generator
 *
 * Generates a triangulated mesh from an image's alpha channel.
 * Used by the MeshDeform effect to create deformable meshes from raster layers.
 *
 * Algorithm:
 * 1. Extract alpha contour (find edges where alpha > threshold)
 * 2. Generate boundary points along contour
 * 3. Generate interior points for triangle density
 * 4. Apply expansion to push boundary outward
 * 5. Triangulate using Bowyer-Watson algorithm
 */

import { createLogger } from "@/utils/logger";

const logger = createLogger("AlphaToMesh");

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

interface Point2D {
  x: number;
  y: number;
}

interface Triangle {
  a: number;
  b: number;
  c: number;
}

export interface MeshFromAlphaResult {
  /** Vertex positions as x,y pairs (length = vertexCount * 2) */
  vertices: Float32Array;
  /** Triangle indices, 3 per triangle (length = triangleCount * 3) */
  triangles: Uint32Array;
  /** Bounding box of the mesh */
  bounds: { x: number; y: number; width: number; height: number };
  /** Number of vertices */
  vertexCount: number;
  /** Number of triangles */
  triangleCount: number;
}

export interface AlphaToMeshOptions {
  /** Target triangle count (affects point density). Default: 200 */
  triangleCount?: number;
  /** Pixels to expand boundary beyond alpha edge. Default: 3 */
  expansion?: number;
  /** Alpha threshold (0-255) for edge detection. Default: 128 */
  alphaThreshold?: number;
  /** Minimum distance between boundary points. Default: 5 */
  minBoundarySpacing?: number;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                          // main // function
// ════════════════════════════════════════════════════════════════════════════

/**
 * Generate a triangulated mesh from an image's alpha channel
 *
 * @param imageData - ImageData from canvas.getImageData()
 * @param options - Mesh generation options
 * @returns Mesh data ready for deformation
 */
export function generateMeshFromAlpha(
  imageData: ImageData,
  options: AlphaToMeshOptions = {},
): MeshFromAlphaResult {
  const {
    triangleCount: targetTriangles = 200,
    expansion = 3,
    alphaThreshold = 128,
    minBoundarySpacing = 5,
  } = options;

  const { width, height, data } = imageData;

  logger.debug(
    `Generating mesh from alpha: ${width}x${height}, target triangles: ${targetTriangles}`,
  );

  // Step 1: Extract alpha mask and find bounds
  const alphaMask = extractAlphaMask(data, width, height, alphaThreshold);
  const bounds = findAlphaBounds(alphaMask, width, height);

  if (bounds.width === 0 || bounds.height === 0) {
    // No alpha content - return minimal mesh covering full image
    logger.warn("No alpha content found, creating full-image mesh");
    return createFullImageMesh(width, height);
  }

  // Step 2: Extract boundary contour points
  const boundaryPoints = extractBoundaryPoints(
    alphaMask,
    width,
    height,
    bounds,
    minBoundarySpacing,
  );

  // Step 3: Apply expansion to boundary points
  const expandedBoundary = expandBoundary(
    boundaryPoints,
    alphaMask,
    width,
    height,
    expansion,
  );

  // Step 4: Generate interior points for triangle density
  const interiorPoints = generateInteriorPoints(
    alphaMask,
    width,
    height,
    bounds,
    targetTriangles,
    expandedBoundary.length,
  );

  // Combine all points
  const allPoints = [...expandedBoundary, ...interiorPoints];

  if (allPoints.length < 3) {
    logger.warn("Not enough points for triangulation, creating minimal mesh");
    return createFullImageMesh(width, height);
  }

  // Step 5: Triangulate
  const triangles = delaunayTriangulate(allPoints);

  if (triangles.length === 0) {
    logger.warn("Triangulation failed, creating minimal mesh");
    return createFullImageMesh(width, height);
  }

  // Convert to output format
  const vertices = new Float32Array(allPoints.length * 2);
  for (let i = 0; i < allPoints.length; i++) {
    vertices[i * 2] = allPoints[i].x;
    vertices[i * 2 + 1] = allPoints[i].y;
  }

  const triangleIndices = new Uint32Array(triangles.length * 3);
  for (let i = 0; i < triangles.length; i++) {
    triangleIndices[i * 3] = triangles[i].a;
    triangleIndices[i * 3 + 1] = triangles[i].b;
    triangleIndices[i * 3 + 2] = triangles[i].c;
  }

  logger.debug(
    `Mesh generated: ${allPoints.length} vertices, ${triangles.length} triangles`,
  );

  return {
    vertices,
    triangles: triangleIndices,
    bounds: {
      x: bounds.minX,
      y: bounds.minY,
      width: bounds.width,
      height: bounds.height,
    },
    vertexCount: allPoints.length,
    triangleCount: triangles.length,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                       // alpha // extraction
// ════════════════════════════════════════════════════════════════════════════

/**
 * Extract alpha values into a boolean mask
 */
function extractAlphaMask(
  data: Uint8ClampedArray,
  width: number,
  height: number,
  threshold: number,
): boolean[] {
  const mask = new Array<boolean>(width * height);
  for (let i = 0; i < width * height; i++) {
    // Alpha is at index i*4 + 3 (RGBA format)
    mask[i] = data[i * 4 + 3] >= threshold;
  }
  return mask;
}

/**
 * Find bounding box of alpha content
 */
function findAlphaBounds(
  mask: boolean[],
  width: number,
  height: number,
): {
  minX: number;
  minY: number;
  maxX: number;
  maxY: number;
  width: number;
  height: number;
} {
  let minX = width;
  let minY = height;
  let maxX = 0;
  let maxY = 0;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      if (mask[y * width + x]) {
        minX = Math.min(minX, x);
        minY = Math.min(minY, y);
        maxX = Math.max(maxX, x);
        maxY = Math.max(maxY, y);
      }
    }
  }

  return {
    minX,
    minY,
    maxX,
    maxY,
    width: maxX > minX ? maxX - minX + 1 : 0,
    height: maxY > minY ? maxY - minY + 1 : 0,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                    // boundary // extraction
// ════════════════════════════════════════════════════════════════════════════

/**
 * Extract boundary points from alpha edge
 * Uses a simple edge detection: pixel is on boundary if it's solid but has a non-solid neighbor
 */
function extractBoundaryPoints(
  mask: boolean[],
  width: number,
  height: number,
  bounds: { minX: number; minY: number; maxX: number; maxY: number },
  minSpacing: number,
): Point2D[] {
  const boundaryPixels: Point2D[] = [];

  // Find all boundary pixels
  for (let y = bounds.minY; y <= bounds.maxY; y++) {
    for (let x = bounds.minX; x <= bounds.maxX; x++) {
      const idx = y * width + x;
      if (!mask[idx]) continue;

      // Check if this pixel is on the boundary (has a non-solid neighbor)
      const hasEmptyNeighbor =
        x === 0 ||
        !mask[idx - 1] || // left
        x === width - 1 ||
        !mask[idx + 1] || // right
        y === 0 ||
        !mask[idx - width] || // top
        y === height - 1 ||
        !mask[idx + width]; // bottom

      if (hasEmptyNeighbor) {
        boundaryPixels.push({ x, y });
      }
    }
  }

  // Subsample boundary points to maintain minimum spacing
  return subsamplePoints(boundaryPixels, minSpacing);
}

/**
 * Subsample points to maintain minimum spacing
 */
function subsamplePoints(points: Point2D[], minSpacing: number): Point2D[] {
  if (points.length === 0) return [];

  const result: Point2D[] = [points[0]];
  const spacingSq = minSpacing * minSpacing;

  for (let i = 1; i < points.length; i++) {
    const p = points[i];
    let tooClose = false;

    // Check against recently added points (not all, for performance)
    for (let j = Math.max(0, result.length - 20); j < result.length; j++) {
      const r = result[j];
      const dx = p.x - r.x;
      const dy = p.y - r.y;
      if (dx * dx + dy * dy < spacingSq) {
        tooClose = true;
        break;
      }
    }

    if (!tooClose) {
      result.push(p);
    }
  }

  return result;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                     // boundary // expansion
// ════════════════════════════════════════════════════════════════════════════

/**
 * Expand boundary points outward from the alpha shape
 */
function expandBoundary(
  points: Point2D[],
  mask: boolean[],
  width: number,
  height: number,
  expansion: number,
): Point2D[] {
  if (expansion <= 0) return points;

  return points.map((p) => {
    // Calculate outward normal by sampling neighborhood
    const normal = calculateOutwardNormal(p, mask, width, height);

    // Expand along normal
    return {
      x: Math.max(0, Math.min(width - 1, p.x + normal.x * expansion)),
      y: Math.max(0, Math.min(height - 1, p.y + normal.y * expansion)),
    };
  });
}

/**
 * Calculate outward-pointing normal at a boundary point
 */
function calculateOutwardNormal(
  point: Point2D,
  mask: boolean[],
  width: number,
  height: number,
): Point2D {
  const { x, y } = point;
  let nx = 0;
  let ny = 0;

  // Sample in a small radius to find the direction away from solid pixels
  const radius = 3;
  for (let dy = -radius; dy <= radius; dy++) {
    for (let dx = -radius; dx <= radius; dx++) {
      if (dx === 0 && dy === 0) continue;

      const sx = x + dx;
      const sy = y + dy;

      if (sx < 0 || sx >= width || sy < 0 || sy >= height) {
        // Out of bounds = empty, push away
        nx += dx;
        ny += dy;
      } else if (!mask[sy * width + sx]) {
        // Empty pixel, push toward it
        nx += dx;
        ny += dy;
      }
    }
  }

  // Normalize
  const len = Math.sqrt(nx * nx + ny * ny);
  if (len < 0.001) {
    return { x: 0, y: -1 }; // Default: up
  }

  return { x: nx / len, y: ny / len };
}

// ════════════════════════════════════════════════════════════════════════════
//                                           // interior // point // generation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Generate interior points for triangle density
 * Uses Poisson disk-like sampling inside the alpha region
 */
function generateInteriorPoints(
  mask: boolean[],
  width: number,
  height: number,
  bounds: {
    minX: number;
    minY: number;
    maxX: number;
    maxY: number;
    width: number;
    height: number;
  },
  targetTriangles: number,
  boundaryPointCount: number,
): Point2D[] {
  // Estimate needed interior points
  // Roughly: triangles ≈ 2 * vertices - 5 (for convex hull)
  // So vertices ≈ (triangles + 5) / 2
  const targetVertices = Math.ceil((targetTriangles + 5) / 2);
  const neededInterior = Math.max(0, targetVertices - boundaryPointCount);

  if (neededInterior === 0) return [];

  // Calculate grid spacing to achieve target density
  const area = bounds.width * bounds.height;
  const spacing = Math.sqrt(area / (neededInterior * 1.5)); // 1.5 factor for some overlap

  const points: Point2D[] = [];

  // Grid-based sampling with jitter
  for (let y = bounds.minY + spacing / 2; y < bounds.maxY; y += spacing) {
    for (let x = bounds.minX + spacing / 2; x < bounds.maxX; x += spacing) {
      // Add jitter for more natural distribution
      const jx = x + (Math.random() - 0.5) * spacing * 0.5;
      const jy = y + (Math.random() - 0.5) * spacing * 0.5;

      const ix = Math.round(jx);
      const iy = Math.round(jy);

      // Only add if inside alpha region
      if (ix >= 0 && ix < width && iy >= 0 && iy < height) {
        if (mask[iy * width + ix]) {
          points.push({ x: jx, y: jy });
        }
      }

      // Stop if we have enough points
      if (points.length >= neededInterior) break;
    }
    if (points.length >= neededInterior) break;
  }

  return points;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                 // delaunay // triangulation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Delaunay triangulation using Bowyer-Watson algorithm
 */
function delaunayTriangulate(points: Point2D[]): Triangle[] {
  if (points.length < 3) {
    return [];
  }

  // Create super triangle that encompasses all points
  const minX = Math.min(...points.map((p) => p.x));
  const maxX = Math.max(...points.map((p) => p.x));
  const minY = Math.min(...points.map((p) => p.y));
  const maxY = Math.max(...points.map((p) => p.y));

  const dx = maxX - minX;
  const dy = maxY - minY;
  const deltaMax = Math.max(dx, dy) * 2;

  // Super triangle vertices
  const superA: Point2D = { x: minX - deltaMax, y: minY - deltaMax };
  const superB: Point2D = { x: minX + deltaMax * 2, y: minY - deltaMax };
  const superC: Point2D = { x: minX + deltaMax / 2, y: maxY + deltaMax * 2 };

  // All points including super triangle
  const allPoints = [...points, superA, superB, superC];
  const superIndices = [points.length, points.length + 1, points.length + 2];

  // Initial triangle is the super triangle
  let triangles: Triangle[] = [
    { a: superIndices[0], b: superIndices[1], c: superIndices[2] },
  ];

  // Add each point one at a time
  for (let i = 0; i < points.length; i++) {
    const point = points[i];
    const badTriangles: Triangle[] = [];
    const polygon: Array<{ a: number; b: number }> = [];

    // Find all triangles whose circumcircle contains the point
    for (const tri of triangles) {
      if (
        isPointInCircumcircle(
          point,
          allPoints[tri.a],
          allPoints[tri.b],
          allPoints[tri.c],
        )
      ) {
        badTriangles.push(tri);
      }
    }

    // Find the boundary of the polygonal hole
    for (const tri of badTriangles) {
      const edges = [
        { a: tri.a, b: tri.b },
        { a: tri.b, b: tri.c },
        { a: tri.c, b: tri.a },
      ];

      for (const edge of edges) {
        // Check if edge is shared with another bad triangle
        let isShared = false;
        for (const other of badTriangles) {
          if (other === tri) continue;
          const otherEdges = [
            { a: other.a, b: other.b },
            { a: other.b, b: other.c },
            { a: other.c, b: other.a },
          ];
          for (const otherEdge of otherEdges) {
            if (
              (edge.a === otherEdge.a && edge.b === otherEdge.b) ||
              (edge.a === otherEdge.b && edge.b === otherEdge.a)
            ) {
              isShared = true;
              break;
            }
          }
          if (isShared) break;
        }

        if (!isShared) {
          polygon.push(edge);
        }
      }
    }

    // Remove bad triangles
    triangles = triangles.filter((t) => !badTriangles.includes(t));

    // Create new triangles from polygon edges to new point
    for (const edge of polygon) {
      triangles.push({ a: edge.a, b: edge.b, c: i });
    }
  }

  // Remove triangles that include super triangle vertices
  return triangles.filter(
    (t) =>
      !superIndices.includes(t.a) &&
      !superIndices.includes(t.b) &&
      !superIndices.includes(t.c),
  );
}

/**
 * Check if a point is inside the circumcircle of a triangle
 */
function isPointInCircumcircle(
  point: Point2D,
  a: Point2D,
  b: Point2D,
  c: Point2D,
): boolean {
  const ax = a.x - point.x;
  const ay = a.y - point.y;
  const bx = b.x - point.x;
  const by = b.y - point.y;
  const cx = c.x - point.x;
  const cy = c.y - point.y;

  const det =
    (ax * ax + ay * ay) * (bx * cy - cx * by) -
    (bx * bx + by * by) * (ax * cy - cx * ay) +
    (cx * cx + cy * cy) * (ax * by - bx * ay);

  // Counter-clockwise orientation means positive det is inside
  const orientation = (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);

  return orientation > 0 ? det > 0 : det < 0;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                          // fallback // mesh
// ════════════════════════════════════════════════════════════════════════════

/**
 * Create a simple mesh covering the full image (fallback)
 */
function createFullImageMesh(
  width: number,
  height: number,
): MeshFromAlphaResult {
  // Create a simple grid mesh
  const cols = 4;
  const rows = 4;
  const points: Point2D[] = [];

  for (let y = 0; y <= rows; y++) {
    for (let x = 0; x <= cols; x++) {
      points.push({
        x: (x / cols) * width,
        y: (y / rows) * height,
      });
    }
  }

  const triangles: Triangle[] = [];
  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {
      const i = y * (cols + 1) + x;
      // Two triangles per grid cell
      triangles.push({ a: i, b: i + 1, c: i + cols + 1 });
      triangles.push({ a: i + 1, b: i + cols + 2, c: i + cols + 1 });
    }
  }

  const vertices = new Float32Array(points.length * 2);
  for (let i = 0; i < points.length; i++) {
    vertices[i * 2] = points[i].x;
    vertices[i * 2 + 1] = points[i].y;
  }

  const triangleIndices = new Uint32Array(triangles.length * 3);
  for (let i = 0; i < triangles.length; i++) {
    triangleIndices[i * 3] = triangles[i].a;
    triangleIndices[i * 3 + 1] = triangles[i].b;
    triangleIndices[i * 3 + 2] = triangles[i].c;
  }

  return {
    vertices,
    triangles: triangleIndices,
    bounds: { x: 0, y: 0, width, height },
    vertexCount: points.length,
    triangleCount: triangles.length,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // exports
// ════════════════════════════════════════════════════════════════════════════

export default {
  generateMeshFromAlpha,
};
