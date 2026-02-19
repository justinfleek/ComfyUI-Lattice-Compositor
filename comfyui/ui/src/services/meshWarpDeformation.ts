/**
 * Mesh Warp Deformation Service
 *
 * Implements VectorSkinning-style mesh deformation using control pins.
 * Uses inverse-distance weighting for smooth deformations.
 *
 * Key features:
 * - Delaunay triangulation of control points
 * - Inverse-distance weight calculation
 * - Real-time mesh deformation
 * - Support for position, rotation, and starch pins
 */

import type {
  WarpDeformationResult,
  WarpMesh,
  WarpPin,
  WarpPinRestState,
  WarpWeightOptions,
} from "@/types/meshWarp";
import { DEFAULT_WARP_WEIGHT_OPTIONS } from "@/types/meshWarp";
import type { ControlPoint } from "@/types/project";
import { createLogger } from "@/utils/logger";
import { isFiniteNumber } from "@/utils/typeGuards";
import { interpolateProperty } from "./interpolation";

const logger = createLogger("MeshWarpDeformation");

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

interface Point2D {
  x: number;
  y: number;
}

interface Triangle {
  a: number;
  b: number;
  c: number;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                     // utility // functions
// ═══════════════════════════════════════════════════════════════════════════

/** Calculate distance between two points */
function distance(a: Point2D, b: Point2D): number {
  const dx = b.x - a.x;
  const dy = b.y - a.y;
  return Math.sqrt(dx * dx + dy * dy);
}

/** Linear interpolation between two values */
function _lerp(a: number, b: number, t: number): number {
  return a + (b - a) * t;
}

/** Clamp a value between min and max */
function _clamp(value: number, min: number, max: number): number {
  return Math.max(min, Math.min(max, value));
}

/** Rotate a point around an origin */
function rotatePoint(
  point: Point2D,
  origin: Point2D,
  angleDegrees: number,
): Point2D {
  const angleRadians = (angleDegrees * Math.PI) / 180;
  const cos = Math.cos(angleRadians);
  const sin = Math.sin(angleRadians);
  const dx = point.x - origin.x;
  const dy = point.y - origin.y;

  return {
    x: origin.x + dx * cos - dy * sin,
    y: origin.y + dx * sin + dy * cos,
  };
}

/** Scale a point relative to an origin */
function scalePoint(point: Point2D, origin: Point2D, scale: number): Point2D {
  return {
    x: origin.x + (point.x - origin.x) * scale,
    y: origin.y + (point.y - origin.y) * scale,
  };
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                // delaunay // triangulation
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Simple Delaunay triangulation using Bowyer-Watson algorithm
 * For production use, consider a dedicated library like delaunator
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

// ═══════════════════════════════════════════════════════════════════════════
//                                                    // weight // calculation
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Calculate pin influence weights for all vertices
 */
function calculateWeights(
  vertices: Float32Array,
  pins: WarpPin[],
  options: WarpWeightOptions = DEFAULT_WARP_WEIGHT_OPTIONS,
): Float32Array {
  const vertexCount = vertices.length / 2;
  const pinCount = pins.length;

  if (pinCount === 0) {
    return new Float32Array(0);
  }

  // weights[vertexIndex * pinCount + pinIndex] = weight
  const weights = new Float32Array(vertexCount * pinCount);

  for (let v = 0; v < vertexCount; v++) {
    const vx = vertices[v * 2];
    const vy = vertices[v * 2 + 1];

    let totalWeight = 0;
    const vertexWeights: number[] = [];

    for (let p = 0; p < pinCount; p++) {
      const pin = pins[p];
      const pinPos = pin.position.value;
      const dist = distance({ x: vx, y: vy }, pinPos);

      // Calculate weight based on method
      let weight: number;

      switch (options.method) {
        default: {
          // Inverse distance weighting with falloff
          if (dist < 0.001) {
            weight = 1000; // Very close - high weight
          } else if (dist > pin.radius * 3) {
            weight = 0; // Too far - no influence
          } else {
            // Smooth falloff using radius
            const normalizedDist = dist / pin.radius;
            weight = (1 / (1 + normalizedDist)) ** options.falloffPower;

            // Apply stiffness (starch pins reduce deformation)
            if (pin.stiffness > 0) {
              weight *= 1 - pin.stiffness * 0.5;
            }
          }
          break;
        }
      }

      // Apply minimum threshold
      if (weight < options.minWeight) {
        weight = 0;
      }

      vertexWeights.push(weight);
      totalWeight += weight;
    }

    // Normalize weights if requested
    for (let p = 0; p < pinCount; p++) {
      let finalWeight = vertexWeights[p];
      if (options.normalize && totalWeight > 0) {
        finalWeight = finalWeight / totalWeight;
      }
      weights[v * pinCount + p] = finalWeight;
    }
  }

  return weights;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                              // deformation
// ═══════════════════════════════════════════════════════════════════════════

/** Evaluated pin state at a specific frame */
interface EvaluatedPinState {
  position: Point2D;
  rotation: number;
  scale: number;
  delta: Point2D;
  /** Overlap depth (only for overlap pins) */
  inFront?: number;
}

/**
 * Evaluate a pin's animated properties at a specific frame
 */
function evaluatePinAtFrame(
  pin: WarpPin,
  restState: WarpPinRestState,
  frame: number,
): EvaluatedPinState {
  const position = {
    x: interpolateProperty(pin.position, frame).x,
    y: interpolateProperty(pin.position, frame).y,
  };
  const rotation = interpolateProperty(pin.rotation, frame);
  const scale = interpolateProperty(pin.scale, frame);

  const delta = {
    x: position.x - restState.position.x,
    y: position.y - restState.position.y,
  };

  // Evaluate inFront for overlap pins
  const inFront = pin.inFront
    ? interpolateProperty(pin.inFront, frame)
    : undefined;

  return { position, rotation, scale, delta, inFront };
}

/**
 * Deform a mesh based on pin positions at a specific frame
 */
function deformMesh(mesh: WarpMesh, frame: number): Float32Array {
  const { originalVertices, pins, weights, pinRestStates, vertexCount } = mesh;
  const pinCount = pins.length;

  if (pinCount === 0 || vertexCount === 0) {
    return new Float32Array(originalVertices);
  }

  // Evaluate all pins at this frame
  const pinStates = pins.map((pin, i) =>
    evaluatePinAtFrame(pin, pinRestStates[i], frame),
  );

  // Create output array
  const deformedVertices = new Float32Array(vertexCount * 2);

  for (let v = 0; v < vertexCount; v++) {
    const origX = originalVertices[v * 2];
    const origY = originalVertices[v * 2 + 1];
    const _origPoint = { x: origX, y: origY };

    let deformedX = 0;
    let deformedY = 0;
    let totalWeight = 0;

    for (let p = 0; p < pinCount; p++) {
      const weight = weights[v * pinCount + p];
      if (weight <= 0) continue;

      const pin = pins[p];
      const pinState = pinStates[p];
      const restState = pinRestStates[p];

      // Calculate deformed position for this pin's influence
      let pinDeformed = { x: origX, y: origY };

      // Apply translation (only for position and advanced pins)
      // Other pin types (starch, overlap, bend, rotation) use fixed reference positions
      if (pin.type === "position" || pin.type === "advanced") {
        pinDeformed = {
          x: pinDeformed.x + pinState.delta.x,
          y: pinDeformed.y + pinState.delta.y,
        };
      }

      // Apply rotation (around pin's rest position)
      // For rotation/bend/advanced pins, or any pin with rotation change
      if (
        pin.type === "rotation" ||
        pin.type === "bend" ||
        pin.type === "advanced" ||
        Math.abs(pinState.rotation - restState.rotation) > 0.001
      ) {
        const rotationDelta = pinState.rotation - restState.rotation;
        pinDeformed = rotatePoint(
          pinDeformed,
          pinState.position,
          rotationDelta,
        );
      }

      // Apply scale (around pin's rest position)
      // For bend/advanced pins, or any pin with scale change
      if (
        pin.type === "bend" ||
        pin.type === "advanced" ||
        Math.abs(pinState.scale - restState.scale) > 0.001
      ) {
        const scaleDelta = pinState.scale / restState.scale;
        pinDeformed = scalePoint(pinDeformed, pinState.position, scaleDelta);
      }

      // Accumulate weighted contribution
      deformedX += pinDeformed.x * weight;
      deformedY += pinDeformed.y * weight;
      totalWeight += weight;
    }

    // Normalize and store result
    if (totalWeight > 0) {
      deformedVertices[v * 2] = deformedX / totalWeight;
      deformedVertices[v * 2 + 1] = deformedY / totalWeight;
    } else {
      // No influence - keep original position
      deformedVertices[v * 2] = origX;
      deformedVertices[v * 2 + 1] = origY;
    }
  }

  return deformedVertices;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                 // main // service // class
// ═══════════════════════════════════════════════════════════════════════════

export class MeshWarpDeformationService {
  private meshCache = new Map<string, WarpMesh>();

  /**
   * Build a warp mesh from control points and pins
   */
  buildMesh(
    layerId: string,
    controlPoints: ControlPoint[],
    pins: WarpPin[],
    options: WarpWeightOptions = DEFAULT_WARP_WEIGHT_OPTIONS,
  ): WarpMesh {
    // Convert control points to flat vertex array
    const vertices = new Float32Array(controlPoints.length * 2);
    for (let i = 0; i < controlPoints.length; i++) {
      vertices[i * 2] = controlPoints[i].x;
      vertices[i * 2 + 1] = controlPoints[i].y;
    }

    // Create pin rest states
    const pinRestStates: WarpPinRestState[] = pins.map((pin) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const pinInFront = (pin != null && typeof pin === "object" && "inFront" in pin && pin.inFront != null && typeof pin.inFront === "object") ? pin.inFront : undefined;
      const inFrontValue = (pinInFront != null && typeof pinInFront === "object" && "value" in pinInFront && typeof pinInFront.value === "boolean") ? pinInFront.value : undefined;
      return {
        pinId: pin.id,
        position: { ...pin.position.value },
        rotation: pin.rotation.value,
        scale: pin.scale.value,
        inFront: inFrontValue,
      };
    });

    // Triangulate the mesh (control points + pins)
    const allPoints: Point2D[] = [
      ...controlPoints.map((cp) => ({ x: cp.x, y: cp.y })),
      ...pins.map((pin) => pin.position.value),
    ];
    const triangles = delaunayTriangulate(allPoints);

    // Flatten triangulation
    const triangulation: number[] = [];
    for (const tri of triangles) {
      triangulation.push(tri.a, tri.b, tri.c);
    }

    // Calculate weights
    const weights = calculateWeights(vertices, pins, options);

    const mesh: WarpMesh = {
      layerId,
      pins,
      triangulation,
      weights,
      originalVertices: vertices,
      pinRestStates,
      vertexCount: controlPoints.length,
      dirty: false,
    };

    // Cache the mesh
    this.meshCache.set(layerId, mesh);

    logger.debug(
      `Built warp mesh: ${controlPoints.length} vertices, ${pins.length} pins`,
    );

    return mesh;
  }

  /**
   * Get or build a mesh for a layer
   */
  getMesh(layerId: string): WarpMesh | undefined {
    return this.meshCache.get(layerId);
  }

  /**
   * Clear cached mesh for a layer
   */
  clearMesh(layerId: string): void {
    this.meshCache.delete(layerId);
  }

  /**
   * Update mesh when pins change
   */
  updateMeshPins(
    layerId: string,
    pins: WarpPin[],
    options: WarpWeightOptions = DEFAULT_WARP_WEIGHT_OPTIONS,
  ): void {
    const mesh = this.meshCache.get(layerId);
    if (!mesh) return;

    mesh.pins = pins;
    mesh.pinRestStates = pins.map((pin) => ({
      pinId: pin.id,
      position: { ...pin.position.value },
      rotation: pin.rotation.value,
      scale: pin.scale.value,
    }));
    mesh.weights = calculateWeights(mesh.originalVertices, pins, options);
    mesh.dirty = false;
  }

  /**
   * Add a pin to an existing mesh
   */
  addPin(
    layerId: string,
    pin: WarpPin,
    options: WarpWeightOptions = DEFAULT_WARP_WEIGHT_OPTIONS,
  ): void {
    const mesh = this.meshCache.get(layerId);
    if (!mesh) return;

    mesh.pins.push(pin);
    mesh.pinRestStates.push({
      pinId: pin.id,
      position: { ...pin.position.value },
      rotation: pin.rotation.value,
      scale: pin.scale.value,
    });
    mesh.weights = calculateWeights(mesh.originalVertices, mesh.pins, options);
  }

  /**
   * Remove a pin from an existing mesh
   */
  removePin(
    layerId: string,
    pinId: string,
    options: WarpWeightOptions = DEFAULT_WARP_WEIGHT_OPTIONS,
  ): void {
    const mesh = this.meshCache.get(layerId);
    if (!mesh) return;

    const pinIndex = mesh.pins.findIndex((p) => p.id === pinId);
    if (pinIndex === -1) return;

    mesh.pins.splice(pinIndex, 1);
    mesh.pinRestStates.splice(pinIndex, 1);
    mesh.weights = calculateWeights(mesh.originalVertices, mesh.pins, options);
  }

  /**
   * Get deformed control points at a specific frame
   */
  getDeformedControlPoints(
    layerId: string,
    frame: number,
    originalControlPoints: ControlPoint[],
  ): ControlPoint[] {
    const mesh = this.meshCache.get(layerId);
    if (!mesh || mesh.pins.length === 0) {
      return originalControlPoints;
    }

    const deformedVertices = deformMesh(mesh, frame);

    // Reconstruct control points with deformed positions
    const deformedPoints: ControlPoint[] = originalControlPoints.map(
      (cp, i) => {
        const newX = deformedVertices[i * 2];
        const newY = deformedVertices[i * 2 + 1];
        const dx = newX - cp.x;
        const dy = newY - cp.y;

        return {
          ...cp,
          x: newX,
          y: newY,
          // Also offset handles to maintain shape
          handleIn: cp.handleIn
            ? { x: cp.handleIn.x + dx, y: cp.handleIn.y + dy }
            : null,
          handleOut: cp.handleOut
            ? { x: cp.handleOut.x + dx, y: cp.handleOut.y + dy }
            : null,
        };
      },
    );

    return deformedPoints;
  }

  /**
   * Deform a mesh and return result
   * 
   * System F/Omega proof: Explicit validation of mesh cache
   * Type proof: layerId ∈ string, frame ∈ number → WarpDeformationResult (non-nullable)
   * Mathematical proof: Mesh must be cached to deform it
   * Pattern proof: Missing mesh is an explicit failure condition, not a lazy null return
   */
  deform(layerId: string, frame: number): WarpDeformationResult {
    const mesh = this.meshCache.get(layerId);
    
    // System F/Omega proof: Explicit validation of mesh existence
    // Type proof: meshCache.get(layerId) returns Mesh | undefined
    // Mathematical proof: Mesh must be cached before deformation
    if (!mesh) {
      throw new Error(
        `[MeshWarpDeformation] Cannot deform mesh: Mesh not cached. ` +
        `Layer ID: ${layerId}, frame: ${frame}, cache size: ${this.meshCache.size}. ` +
        `Mesh must be cached before deformation. ` +
        `Wrap in try/catch if "mesh not cached" is an expected state.`
      );
    }

    const vertices = deformMesh(mesh, frame);

    // Convert to control point format
    const controlPoints: WarpDeformationResult["controlPoints"] = [];
    for (let i = 0; i < mesh.vertexCount; i++) {
      controlPoints.push({
        x: vertices[i * 2],
        y: vertices[i * 2 + 1],
        inHandle: { x: 0, y: 0 },
        outHandle: { x: 0, y: 0 },
      });
    }

    return { vertices, controlPoints };
  }

  /**
   * Get all pins for a layer
   */
  getPins(layerId: string): WarpPin[] {
    // Type proof: mesh ∈ WarpMesh | undefined → pins ∈ WarpPin[]
    const mesh = this.meshCache.get(layerId);
    if (mesh !== undefined && typeof mesh === "object" && mesh !== null && "pins" in mesh && Array.isArray(mesh.pins)) {
      return mesh.pins;
    }
    return [];
  }

  /**
   * Update a pin's position (for UI dragging)
   */
  updatePinPosition(
    layerId: string,
    pinId: string,
    x: number,
    y: number,
  ): void {
    const mesh = this.meshCache.get(layerId);
    if (!mesh) return;

    const pin = mesh.pins.find((p) => p.id === pinId);
    if (pin) {
      pin.position.value = { x, y };
    }
  }

  /**
   * Clear all cached meshes
   */
  clearAllMeshes(): void {
    this.meshCache.clear();
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                    // singleton // instance
// ═══════════════════════════════════════════════════════════════════════════

export const meshWarpDeformation = new MeshWarpDeformationService();

// ═══════════════════════════════════════════════════════════════════════════
//                                                                  // exports
// ═══════════════════════════════════════════════════════════════════════════

export { delaunayTriangulate, calculateWeights, deformMesh };

// Backwards compatibility aliases
/** @deprecated Use MeshWarpDeformationService instead */
export const PuppetDeformationService = MeshWarpDeformationService;
/** @deprecated Use meshWarpDeformation instead */
export const puppetDeformation = meshWarpDeformation;

export default meshWarpDeformation;
