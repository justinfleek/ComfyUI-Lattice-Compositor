/**
 * Mesh Deform Effect Renderer
 *
 * Puppet pin-style deformation for raster images.
 * Uses alpha channel to generate triangulated mesh, then deforms
 * based on control pins (position, bend, starch, overlap, advanced).
 *
 * Algorithm:
 * 1. Generate mesh from alpha (cached until source/params change)
 * 2. Calculate pin weights per vertex (inverse distance falloff)
 * 3. Evaluate pin transforms at current frame
 * 4. Deform vertices based on pin influences
 * 5. Render deformed triangles with texture mapping
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import type { WarpPin } from "@/types/meshWarp";
import type { EffectInstance, MeshDeformEffectInstance } from "@/types/effects";
import { createLogger } from "@/utils/logger";
import {
  generateMeshFromAlpha,
  type MeshFromAlphaResult,
} from "../alphaToMesh";
import {
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams,
  registerEffectRenderer,
} from "../effectProcessor";
import { interpolateProperty } from "../interpolation";

const logger = createLogger("MeshDeformRenderer");

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

interface Point2D {
  x: number;
  y: number;
}

interface DeformedMesh {
  /** Original vertex positions */
  original: Float32Array;
  /** Deformed vertex positions */
  deformed: Float32Array;
  /** Triangle indices */
  triangles: Uint32Array;
  /** Number of vertices */
  vertexCount: number;
  /** Number of triangles */
  triangleCount: number;
  /** Pin weights per vertex (pinCount weights per vertex) */
  weights: Float32Array;
}

interface MeshCache {
  mesh: MeshFromAlphaResult;
  weights: Float32Array;
  inputHash: string;
  params: {
    triangleCount: number;
    expansion: number;
    alphaThreshold: number;
  };
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                            // mesh // cache
// Per-effect mesh caching to avoid regenerating mesh every frame
// ═══════════════════════════════════════════════════════════════════════════

const meshCaches = new Map<string, MeshCache>();

/**
 * Generate a hash from input canvas for cache invalidation
 */
function hashCanvas(canvas: HTMLCanvasElement): string {
  // Sample sparse pixels for fast comparison
  const ctx = canvas.getContext("2d");
  if (!ctx) return "";

  const { width, height } = canvas;
  const samples: number[] = [width, height];

  // Sample 9 pixels in a grid
  for (let y = 0; y < 3; y++) {
    for (let x = 0; x < 3; x++) {
      const px = Math.floor(((x + 0.5) * width) / 3);
      const py = Math.floor(((y + 0.5) * height) / 3);
      const data = ctx.getImageData(px, py, 1, 1).data;
      samples.push(data[3]); // Just alpha for mesh generation
    }
  }

  return samples.join(",");
}

/**
 * Get or generate mesh for an effect instance
 */
function getOrGenerateMesh(
  effectId: string,
  inputCanvas: HTMLCanvasElement,
  params: EvaluatedEffectParams,
  pins: WarpPin[],
): { mesh: MeshFromAlphaResult; weights: Float32Array } {
  // Type proof: triangle_count ∈ ℕ ∧ finite(triangle_count) → triangle_count ∈ ℕ₊
  const triangleCountValue = params.triangle_count;
  const triangleCount = isFiniteNumber(triangleCountValue) && Number.isInteger(triangleCountValue) && triangleCountValue > 0 ? triangleCountValue : 200;
  // Type proof: expansion ∈ ℝ ∧ finite(expansion) → expansion ∈ ℝ₊
  const expansionValue = params.expansion;
  const expansion = isFiniteNumber(expansionValue) && expansionValue > 0 ? expansionValue : 3;
  // Type proof: alpha_threshold ∈ ℕ ∧ finite(alpha_threshold) → alpha_threshold ∈ [0, 255]
  const alphaThresholdValue = params.alpha_threshold;
  const alphaThreshold = isFiniteNumber(alphaThresholdValue) && Number.isInteger(alphaThresholdValue) && alphaThresholdValue >= 0 && alphaThresholdValue <= 255 ? alphaThresholdValue : 128;

  const inputHash = hashCanvas(inputCanvas);

  // Check cache
  const cached = meshCaches.get(effectId);
  if (
    cached &&
    cached.inputHash === inputHash &&
    cached.params.triangleCount === triangleCount &&
    cached.params.expansion === expansion &&
    cached.params.alphaThreshold === alphaThreshold
  ) {
    // Recalculate weights if pin count changed
    if (
      pins.length > 0 &&
      cached.weights.length !== cached.mesh.vertexCount * pins.length
    ) {
      cached.weights = calculatePinWeights(cached.mesh, pins, params);
    }
    return { mesh: cached.mesh, weights: cached.weights };
  }

  // Generate new mesh
  const ctx = inputCanvas.getContext("2d")!;
  const imageData = ctx.getImageData(
    0,
    0,
    inputCanvas.width,
    inputCanvas.height,
  );

  const mesh = generateMeshFromAlpha(imageData, {
    triangleCount,
    expansion,
    alphaThreshold,
  });

  // Calculate weights
  const weights = calculatePinWeights(mesh, pins, params);

  // Cache
  meshCaches.set(effectId, {
    mesh,
    weights,
    inputHash,
    params: { triangleCount, expansion, alphaThreshold },
  });

  logger.debug(
    `Generated mesh for ${effectId}: ${mesh.vertexCount} vertices, ${mesh.triangleCount} triangles`,
  );

  return { mesh, weights };
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                    // weight // calculation
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Calculate pin influence weights for each vertex
 * Returns Float32Array with (vertexCount * pinCount) weights
 */
function calculatePinWeights(
  mesh: MeshFromAlphaResult,
  pins: WarpPin[],
  params: EvaluatedEffectParams,
): Float32Array {
  if (pins.length === 0) {
    return new Float32Array(0);
  }

  // Type proof: pin_falloff ∈ string | undefined → string
  const falloffMethodValue = params.pin_falloff;
  const falloffMethod = typeof falloffMethodValue === "string" ? falloffMethodValue : "inverse-distance";
  // Type proof: falloff_power ∈ ℝ ∧ finite(falloff_power) → falloff_power ∈ ℝ₊
  const falloffPowerValue = params.falloff_power;
  const falloffPower = isFiniteNumber(falloffPowerValue) && falloffPowerValue > 0 ? falloffPowerValue : 2;

  const weights = new Float32Array(mesh.vertexCount * pins.length);

  for (let v = 0; v < mesh.vertexCount; v++) {
    const vx = mesh.vertices[v * 2];
    const vy = mesh.vertices[v * 2 + 1];

    let totalWeight = 0;

    for (let p = 0; p < pins.length; p++) {
      const pin = pins[p];
      const px = pin.position.value.x;
      const py = pin.position.value.y;
      const radius = pin.radius;

      const dx = vx - px;
      const dy = vy - py;
      const dist = Math.sqrt(dx * dx + dy * dy);

      let weight = 0;

      if (falloffMethod === "radial-basis") {
        // Gaussian RBF
        const sigma = radius / 3;
        weight = Math.exp(-(dist * dist) / (2 * sigma * sigma));
      } else {
        // Inverse distance (default)
        if (dist < 0.001) {
          weight = 1000; // Near-infinite weight at pin position
        } else if (dist < radius) {
          weight = (1 - dist / radius) ** falloffPower;
        } else {
          weight = 0;
        }
      }

      // Starch pins reduce influence
      if (pin.type === "starch") {
        // Starch doesn't contribute to deformation, but affects nearby weights
        weight = 0;
      }

      weights[v * pins.length + p] = weight;
      totalWeight += weight;
    }

    // Normalize weights to sum to 1
    if (totalWeight > 0.001) {
      for (let p = 0; p < pins.length; p++) {
        weights[v * pins.length + p] /= totalWeight;
      }
    }

    // Apply starch stiffness reduction
    for (let p = 0; p < pins.length; p++) {
      const pin = pins[p];
      if (pin.type === "starch" && pin.stiffness > 0) {
        const px = pin.position.value.x;
        const py = pin.position.value.y;
        const dx = vx - px;
        const dy = vy - py;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist < pin.radius) {
          const stiffFactor = 1 - pin.stiffness * (1 - dist / pin.radius);
          // Reduce all weights for this vertex by stiffness factor
          for (let q = 0; q < pins.length; q++) {
            weights[v * pins.length + q] *= stiffFactor;
          }
        }
      }
    }
  }

  return weights;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                              // deformation
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Evaluate a pin's transform at the current frame
 */
function evaluatePinAtFrame(
  pin: WarpPin,
  frame: number,
): { position: Point2D; rotation: number; scale: number } {
  const position = interpolateProperty(pin.position, frame) as Point2D;
  const rotation = interpolateProperty(pin.rotation, frame) as number;
  const scale = interpolateProperty(pin.scale, frame) as number;

  return { position, rotation, scale };
}

/**
 * Deform mesh vertices based on pin transforms at current frame
 */
function deformMesh(
  mesh: MeshFromAlphaResult,
  pins: WarpPin[],
  weights: Float32Array,
  frame: number,
): Float32Array {
  const deformed = new Float32Array(mesh.vertices.length);

  if (pins.length === 0) {
    // No pins = no deformation
    deformed.set(mesh.vertices);
    return deformed;
  }

  // Evaluate all pins at current frame
  const pinStates = pins.map((pin) => {
    const current = evaluatePinAtFrame(pin, frame);
    const rest = { x: pin.position.value.x, y: pin.position.value.y };
    return {
      pin,
      current,
      rest,
      delta: {
        x: current.position.x - rest.x,
        y: current.position.y - rest.y,
      },
    };
  });

  // Deform each vertex
  for (let v = 0; v < mesh.vertexCount; v++) {
    const vx = mesh.vertices[v * 2];
    const vy = mesh.vertices[v * 2 + 1];

    let dx = 0;
    let dy = 0;

    for (let p = 0; p < pins.length; p++) {
      const state = pinStates[p];
      const weight = weights[v * pins.length + p];

      if (weight < 0.0001) continue;

      const { pin, current, rest, delta } = state;

      // Skip overlap pins (they don't affect vertex positions)
      if (pin.type === "overlap") continue;

      // Calculate deformation based on pin type
      let pinDx = 0;
      let pinDy = 0;

      // Position translation (for position and advanced types)
      if (pin.type === "position" || pin.type === "advanced") {
        pinDx += delta.x;
        pinDy += delta.y;
      }

      // Rotation (for bend, rotation, and advanced types)
      if (
        pin.type === "bend" ||
        pin.type === "rotation" ||
        pin.type === "advanced"
      ) {
        const rotationRad = (current.rotation * Math.PI) / 180;
        if (Math.abs(rotationRad) > 0.0001) {
          // Rotate vertex around pin's rest position
          const relX = vx - rest.x;
          const relY = vy - rest.y;
          const cos = Math.cos(rotationRad);
          const sin = Math.sin(rotationRad);
          const rotatedX = relX * cos - relY * sin;
          const rotatedY = relX * sin + relY * cos;
          pinDx += rotatedX - relX;
          pinDy += rotatedY - relY;
        }
      }

      // Scale (for bend and advanced types)
      if (pin.type === "bend" || pin.type === "advanced") {
        if (Math.abs(current.scale - 1) > 0.0001) {
          const relX = vx - rest.x;
          const relY = vy - rest.y;
          pinDx += relX * (current.scale - 1);
          pinDy += relY * (current.scale - 1);
        }
      }

      dx += pinDx * weight;
      dy += pinDy * weight;
    }

    deformed[v * 2] = vx + dx;
    deformed[v * 2 + 1] = vy + dy;
  }

  return deformed;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                    // triangle // rendering
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Render a single triangle with texture mapping
 * Uses barycentric coordinates for pixel-accurate mapping
 */
function renderTriangle(
  outputData: ImageData,
  inputData: ImageData,
  // Original (source) triangle vertices
  srcA: Point2D,
  srcB: Point2D,
  srcC: Point2D,
  // Deformed (destination) triangle vertices
  dstA: Point2D,
  dstB: Point2D,
  dstC: Point2D,
): void {
  const { width, height, data: dst } = outputData;
  const { width: srcWidth, height: srcHeight, data: src } = inputData;

  // Calculate bounding box of destination triangle
  const minX = Math.max(0, Math.floor(Math.min(dstA.x, dstB.x, dstC.x)));
  const maxX = Math.min(width - 1, Math.ceil(Math.max(dstA.x, dstB.x, dstC.x)));
  const minY = Math.max(0, Math.floor(Math.min(dstA.y, dstB.y, dstC.y)));
  const maxY = Math.min(
    height - 1,
    Math.ceil(Math.max(dstA.y, dstB.y, dstC.y)),
  );

  // Precompute barycentric coordinate denominators
  const denom =
    (dstB.y - dstC.y) * (dstA.x - dstC.x) +
    (dstC.x - dstB.x) * (dstA.y - dstC.y);
  if (Math.abs(denom) < 0.0001) return; // Degenerate triangle

  // Process each pixel in bounding box
  for (let y = minY; y <= maxY; y++) {
    for (let x = minX; x <= maxX; x++) {
      // Calculate barycentric coordinates
      const w1 =
        ((dstB.y - dstC.y) * (x - dstC.x) + (dstC.x - dstB.x) * (y - dstC.y)) /
        denom;
      const w2 =
        ((dstC.y - dstA.y) * (x - dstC.x) + (dstA.x - dstC.x) * (y - dstC.y)) /
        denom;
      const w3 = 1 - w1 - w2;

      // Check if point is inside triangle
      if (w1 < 0 || w2 < 0 || w3 < 0) continue;

      // Map back to source coordinates using barycentric interpolation
      const srcX = w1 * srcA.x + w2 * srcB.x + w3 * srcC.x;
      const srcY = w1 * srcA.y + w2 * srcB.y + w3 * srcC.y;

      // Clamp to source bounds
      if (srcX < 0 || srcX >= srcWidth - 1 || srcY < 0 || srcY >= srcHeight - 1)
        continue;

      // Bilinear sample from source
      const x0 = Math.floor(srcX);
      const y0 = Math.floor(srcY);
      const x1 = Math.min(x0 + 1, srcWidth - 1);
      const y1 = Math.min(y0 + 1, srcHeight - 1);
      const fx = srcX - x0;
      const fy = srcY - y0;

      const i00 = (y0 * srcWidth + x0) * 4;
      const i10 = (y0 * srcWidth + x1) * 4;
      const i01 = (y1 * srcWidth + x0) * 4;
      const i11 = (y1 * srcWidth + x1) * 4;
      const outIdx = (y * width + x) * 4;

      // Interpolate each channel
      for (let c = 0; c < 4; c++) {
        const v00 = src[i00 + c];
        const v10 = src[i10 + c];
        const v01 = src[i01 + c];
        const v11 = src[i11 + c];

        const value = Math.round(
          v00 * (1 - fx) * (1 - fy) +
            v10 * fx * (1 - fy) +
            v01 * (1 - fx) * fy +
            v11 * fx * fy,
        );

        // Alpha blend with existing content
        if (c === 3) {
          // Alpha channel
          dst[outIdx + c] = Math.max(dst[outIdx + c], value);
        } else {
          // RGB - blend based on alpha
          const alpha = value / 255;
          dst[outIdx + c] = Math.round(
            dst[outIdx + c] * (1 - alpha) + value * alpha,
          );
        }
      }
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                              // overlap // depth // sorting
// ═══════════════════════════════════════════════════════════════════════════

interface TriangleDepth {
  index: number;
  depth: number;
}

/**
 * Calculate depth value for each triangle based on overlap pin influence
 * Triangles with higher depth (higher inFront values) render on top
 */
function calculateTriangleDepths(
  mesh: MeshFromAlphaResult,
  deformedVertices: Float32Array,
  pins: WarpPin[],
  frame: number,
): TriangleDepth[] {
  const overlapPins = pins.filter((p) => p.type === "overlap");

  if (overlapPins.length === 0) {
    // No overlap pins - return triangles in original order with depth 0
    return Array.from({ length: mesh.triangleCount }, (_, i) => ({
      index: i,
      depth: 0,
    }));
  }

  const depths: TriangleDepth[] = [];

  for (let t = 0; t < mesh.triangleCount; t++) {
    const i0 = mesh.triangles[t * 3];
    const i1 = mesh.triangles[t * 3 + 1];
    const i2 = mesh.triangles[t * 3 + 2];

    // Calculate triangle centroid (using deformed positions)
    const cx =
      (deformedVertices[i0 * 2] +
        deformedVertices[i1 * 2] +
        deformedVertices[i2 * 2]) /
      3;
    const cy =
      (deformedVertices[i0 * 2 + 1] +
        deformedVertices[i1 * 2 + 1] +
        deformedVertices[i2 * 2 + 1]) /
      3;

    // Calculate weighted depth from overlap pins
    let totalDepth = 0;
    let totalWeight = 0;

    for (const pin of overlapPins) {
      // Get animated inFront value at current frame
      const inFront = pin.inFront
        ? (interpolateProperty(pin.inFront, frame) as number)
        : 0;

      // Calculate distance from centroid to pin (using rest position)
      const px = pin.position.value.x;
      const py = pin.position.value.y;
      const dx = cx - px;
      const dy = cy - py;
      const dist = Math.sqrt(dx * dx + dy * dy);

      // Weight based on distance and pin radius
      if (dist < pin.radius) {
        const weight = 1 - dist / pin.radius;
        totalDepth += inFront * weight;
        totalWeight += weight;
      }
    }

    // Normalize depth
    const depth = totalWeight > 0 ? totalDepth / totalWeight : 0;
    depths.push({ index: t, depth });
  }

  return depths;
}

/**
 * Render all triangles of deformed mesh with optional depth sorting
 */
function renderDeformedMesh(
  outputCtx: CanvasRenderingContext2D,
  inputCanvas: HTMLCanvasElement,
  mesh: MeshFromAlphaResult,
  deformedVertices: Float32Array,
  pins: WarpPin[] = [],
  frame: number = 0,
  enableOverlap: boolean = false,
): void {
  const { width, height } = outputCtx.canvas;

  // Get input image data
  const inputCtx = inputCanvas.getContext("2d")!;
  const inputData = inputCtx.getImageData(
    0,
    0,
    inputCanvas.width,
    inputCanvas.height,
  );

  // Create output image data (cleared)
  const outputData = outputCtx.createImageData(width, height);

  // Calculate and sort triangle depths if overlap is enabled
  let triangleOrder: number[];

  if (enableOverlap) {
    const depths = calculateTriangleDepths(mesh, deformedVertices, pins, frame);
    // Sort by depth ascending (lower depth = behind = render first)
    depths.sort((a, b) => a.depth - b.depth);
    triangleOrder = depths.map((d) => d.index);
  } else {
    // Original order
    triangleOrder = Array.from({ length: mesh.triangleCount }, (_, i) => i);
  }

  // Render triangles in sorted order
  for (const t of triangleOrder) {
    const i0 = mesh.triangles[t * 3];
    const i1 = mesh.triangles[t * 3 + 1];
    const i2 = mesh.triangles[t * 3 + 2];

    // Source (original) vertices
    const srcA = { x: mesh.vertices[i0 * 2], y: mesh.vertices[i0 * 2 + 1] };
    const srcB = { x: mesh.vertices[i1 * 2], y: mesh.vertices[i1 * 2 + 1] };
    const srcC = { x: mesh.vertices[i2 * 2], y: mesh.vertices[i2 * 2 + 1] };

    // Destination (deformed) vertices
    const dstA = {
      x: deformedVertices[i0 * 2],
      y: deformedVertices[i0 * 2 + 1],
    };
    const dstB = {
      x: deformedVertices[i1 * 2],
      y: deformedVertices[i1 * 2 + 1],
    };
    const dstC = {
      x: deformedVertices[i2 * 2],
      y: deformedVertices[i2 * 2 + 1],
    };

    renderTriangle(outputData, inputData, srcA, srcB, srcC, dstA, dstB, dstC);
  }

  outputCtx.putImageData(outputData, 0, 0);
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                       // debug // rendering
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Render mesh wireframe for debugging
 */
function renderMeshWireframe(
  ctx: CanvasRenderingContext2D,
  vertices: Float32Array,
  triangles: Uint32Array,
  _vertexCount: number,
  triangleCount: number,
): void {
  ctx.strokeStyle = "rgba(0, 255, 0, 0.5)";
  ctx.lineWidth = 1;

  for (let t = 0; t < triangleCount; t++) {
    const i0 = triangles[t * 3];
    const i1 = triangles[t * 3 + 1];
    const i2 = triangles[t * 3 + 2];

    const ax = vertices[i0 * 2];
    const ay = vertices[i0 * 2 + 1];
    const bx = vertices[i1 * 2];
    const by = vertices[i1 * 2 + 1];
    const cx = vertices[i2 * 2];
    const cy = vertices[i2 * 2 + 1];

    ctx.beginPath();
    ctx.moveTo(ax, ay);
    ctx.lineTo(bx, by);
    ctx.lineTo(cx, cy);
    ctx.closePath();
    ctx.stroke();
  }
}

/**
 * Render pins for debugging
 */
function renderPins(
  ctx: CanvasRenderingContext2D,
  pins: WarpPin[],
  frame: number,
): void {
  for (const pin of pins) {
    const { position, rotation, scale } = evaluatePinAtFrame(pin, frame);

    // Pin color based on type
    let color: string;
    switch (pin.type) {
      case "position":
        color = "yellow";
        break;
      case "bend":
        color = "orange";
        break;
      case "starch":
        color = "cyan";
        break;
      case "overlap":
        color = "magenta";
        break;
      case "advanced":
        color = "white";
        break;
      default:
        color = "gray";
    }

    // Draw pin
    ctx.fillStyle = color;
    ctx.strokeStyle = "black";
    ctx.lineWidth = 2;

    ctx.beginPath();
    ctx.arc(position.x, position.y, 6, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();

    // Draw influence radius
    ctx.strokeStyle = `${color}40`;
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.arc(position.x, position.y, pin.radius, 0, Math.PI * 2);
    ctx.stroke();

    // Draw rotation indicator for bend/rotation/advanced pins
    if (
      pin.type === "bend" ||
      pin.type === "rotation" ||
      pin.type === "advanced"
    ) {
      const rad = (rotation * Math.PI) / 180;
      const indicatorLen = 15;
      ctx.strokeStyle = color;
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.moveTo(position.x, position.y);
      ctx.lineTo(
        position.x + Math.cos(rad) * indicatorLen,
        position.y + Math.sin(rad) * indicatorLen,
      );
      ctx.stroke();
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                         // main // renderer
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Mesh Deform effect renderer
 *
 * Parameters:
 * - triangle_count: Target number of triangles (50-1000)
 * - expansion: Pixels to expand boundary (0-50)
 * - alpha_threshold: Alpha cutoff for edge detection (0-255)
 * - show_mesh: Boolean to show wireframe
 * - show_pins: Boolean to show pin markers
 * - pin_falloff: 'inverse-distance' | 'radial-basis'
 * - falloff_power: Falloff exponent (1-5)
 * - enable_overlap: Boolean to enable overlap depth sorting
 *
 * Special injected params:
 * - _effectInstance: MeshDeformEffectInstance with pins array
 * - _frame: Current frame number
 */
export function meshDeformRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  const effectInstance = params._effectInstance;
  // Type proof: _frame ∈ ℕ ∪ {undefined} → ℕ
  const frameValue = params._frame;
  const frame = isFiniteNumber(frameValue) && Number.isInteger(frameValue) && frameValue >= 0 ? frameValue : 0;
  // Type proof: show_mesh ∈ boolean | undefined → boolean
  const showMesh = typeof params.show_mesh === "boolean" ? params.show_mesh : false;
  // Type proof: show_pins ∈ boolean | undefined → boolean
  const showPins = typeof params.show_pins === "boolean" ? params.show_pins : true;

  // Get pins from effect instance (injected by render pipeline)
  // Type proof: effectInstance is MeshDeformEffectInstance when effectKey === 'mesh-deform'
  // pins ∈ WarpPin[] | undefined → WarpPin[]
  const isMeshDeformInstance = (
    inst: EffectInstance | undefined
  ): inst is MeshDeformEffectInstance =>
    inst !== undefined && inst.effectKey === "mesh-deform" && "pins" in inst;

  const pinsValue = isMeshDeformInstance(effectInstance) ? effectInstance.pins : undefined;
  const pins: WarpPin[] = Array.isArray(pinsValue) ? pinsValue : [];

  // No pins = no deformation
  if (pins.length === 0) {
    // Still show debug overlays if requested
    if (showMesh || showPins) {
      const output = createMatchingCanvas(input.canvas);
      output.ctx.drawImage(input.canvas, 0, 0);

      if (showMesh) {
        // Type proof: id ∈ string | undefined → string
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const effectIdValue = (effectInstance != null && typeof effectInstance === "object" && "id" in effectInstance && typeof effectInstance.id === "string") ? effectInstance.id : undefined;
        const effectId = typeof effectIdValue === "string" ? effectIdValue : "temp";
        const { mesh } = getOrGenerateMesh(effectId, input.canvas, params, []);
        renderMeshWireframe(
          output.ctx,
          mesh.vertices,
          mesh.triangles,
          mesh.vertexCount,
          mesh.triangleCount,
        );
      }

      return output;
    }
    return input;
  }

  // Type proof: id ∈ string | undefined → string
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const effectIdValue = (effectInstance != null && typeof effectInstance === "object" && "id" in effectInstance && typeof effectInstance.id === "string") ? effectInstance.id : undefined;
  const effectId = typeof effectIdValue === "string" ? effectIdValue : `temp-${Date.now()}`;

  // Get or generate mesh
  const { mesh, weights } = getOrGenerateMesh(
    effectId,
    input.canvas,
    params,
    pins,
  );

  // Deform mesh
  const deformedVertices = deformMesh(mesh, pins, weights, frame);

  // Check if overlap depth sorting is enabled
  // Type proof: enable_overlap ∈ boolean | undefined → boolean
  const enableOverlap = typeof params.enable_overlap === "boolean" ? params.enable_overlap : false;

  // Create output and render deformed mesh
  const output = createMatchingCanvas(input.canvas);
  renderDeformedMesh(
    output.ctx,
    input.canvas,
    mesh,
    deformedVertices,
    pins,
    frame,
    enableOverlap,
  );

  // Debug overlays
  if (showMesh) {
    renderMeshWireframe(
      output.ctx,
      deformedVertices,
      mesh.triangles,
      mesh.vertexCount,
      mesh.triangleCount,
    );
  }

  if (showPins) {
    renderPins(output.ctx, pins, frame);
  }

  return output;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                             // registration
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Register mesh-deform effect renderer
 */
export function registerMeshDeformEffect(): void {
  registerEffectRenderer("mesh-deform", meshDeformRenderer);
}

/**
 * Clear mesh caches (call when loading new project)
 */
export function clearMeshDeformCaches(): void {
  meshCaches.clear();
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                        // test // utilities
// Exported for unit testing - allows verification of internal state
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Get cached mesh for an effect ID (for testing)
 * Returns undefined if not cached
 */
export function _testGetCachedMesh(effectId: string): MeshCache | undefined {
  return meshCaches.get(effectId);
}

/**
 * Get mesh cache size (for testing)
 */
export function _testGetCacheSize(): number {
  return meshCaches.size;
}

/**
 * Directly calculate weights for testing
 */
export function _testCalculateWeights(
  mesh: MeshFromAlphaResult,
  pins: WarpPin[],
  params: EvaluatedEffectParams,
): Float32Array {
  return calculatePinWeights(mesh, pins, params);
}

/**
 * Directly deform mesh for testing
 */
export function _testDeformMesh(
  mesh: MeshFromAlphaResult,
  pins: WarpPin[],
  weights: Float32Array,
  frame: number,
): Float32Array {
  return deformMesh(mesh, pins, weights, frame);
}

/**
 * Calculate triangle depths for testing overlap sorting
 */
export function _testCalculateTriangleDepths(
  mesh: MeshFromAlphaResult,
  deformedVertices: Float32Array,
  pins: WarpPin[],
  frame: number,
): Array<{ index: number; depth: number }> {
  return calculateTriangleDepths(mesh, deformedVertices, pins, frame);
}

export default {
  meshDeformRenderer,
  registerMeshDeformEffect,
  clearMeshDeformCaches,
};
