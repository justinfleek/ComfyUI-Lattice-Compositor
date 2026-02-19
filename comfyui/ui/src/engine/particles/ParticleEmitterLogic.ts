/**
 * Particle Emitter Logic
 *
 * Handles spawn position calculation based on emitter shape
 * and emission direction calculation with spread cone.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import * as THREE from "three";
import type { EmitterConfig } from "./types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

export type SplineProvider = (
  splineId: string,
  t: number,
) => { x: number; y: number; z?: number } | null;
export type RNGFunction = () => number;

// ═══════════════════════════════════════════════════════════════════════════
//                                       // emitter // position // calculation
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Get spawn position based on emitter shape
 * @param emitter - The emitter configuration
 * @param rng - Seeded random number generator function
 * @param splineProvider - Optional function to get points along a spline
 */
export function getEmitterPosition(
  emitter: EmitterConfig,
  rng: RNGFunction,
  splineProvider?: SplineProvider | null,
): THREE.Vector3 {
  const shape = emitter.shape;
  // Negate Y to match THREE.js coordinate system (Y-up) and gizmo positioning
  const base = new THREE.Vector3(
    emitter.position.x,
    -emitter.position.y,
    emitter.position.z,
  );

  switch (shape.type) {
    case "point":
      return base;

    case "circle": {
      const angle = rng() * Math.PI * 2;
      // Validate radius
      // Type proof: radius ∈ number | undefined → number
      const rawRadius = shape !== undefined && typeof shape === "object" && shape !== null && "radius" in shape && isFiniteNumber(shape.radius) && shape.radius >= 0
        ? shape.radius
        : 50;
      let radius = (Number.isFinite(rawRadius) && rawRadius > 0) ? rawRadius : 50;
      if (!shape.emitFromEdge) {
        radius *= Math.sqrt(rng()); // Uniform distribution in circle
      }
      return base.add(
        new THREE.Vector3(
          Math.cos(angle) * radius,
          Math.sin(angle) * radius,
          0,
        ),
      );
    }

    case "sphere": {
      const theta = rng() * Math.PI * 2;
      const phi = Math.acos(2 * rng() - 1);
      // Validate radius
      // Type proof: radius ∈ number | undefined → number
      const rawRadius = shape !== undefined && typeof shape === "object" && shape !== null && "radius" in shape && isFiniteNumber(shape.radius) && shape.radius >= 0
        ? shape.radius
        : 50;
      let radius = (Number.isFinite(rawRadius) && rawRadius > 0) ? rawRadius : 50;
      if (!shape.emitFromEdge) {
        radius *= Math.cbrt(rng()); // Uniform distribution in sphere
      }
      return base.add(
        new THREE.Vector3(
          Math.sin(phi) * Math.cos(theta) * radius,
          Math.sin(phi) * Math.sin(theta) * radius,
          Math.cos(phi) * radius,
        ),
      );
    }

    case "box": {
      // Type proof: boxSize ∈ { x: number; y: number; z: number } | undefined → { x: number; y: number; z: number }
      const boxSize = shape !== undefined && typeof shape === "object" && shape !== null && "boxSize" in shape && shape.boxSize !== undefined && typeof shape.boxSize === "object" && shape.boxSize !== null && "x" in shape.boxSize && "y" in shape.boxSize && "z" in shape.boxSize && isFiniteNumber(shape.boxSize.x) && isFiniteNumber(shape.boxSize.y) && isFiniteNumber(shape.boxSize.z)
        ? shape.boxSize
        : { x: 100, y: 100, z: 100 };
      // Validate box dimensions
      const sx = Number.isFinite(boxSize.x) ? boxSize.x : 100;
      const sy = Number.isFinite(boxSize.y) ? boxSize.y : 100;
      const sz = Number.isFinite(boxSize.z) ? boxSize.z : 100;
      return base.add(
        new THREE.Vector3(
          (rng() - 0.5) * sx,
          (rng() - 0.5) * sy,
          (rng() - 0.5) * sz,
        ),
      );
    }

    case "line": {
      // Type proof: lineStart ∈ { x: number; y: number; z: number } | undefined → { x: number; y: number; z: number }
      const start = shape !== undefined && typeof shape === "object" && shape !== null && "lineStart" in shape && shape.lineStart !== undefined && typeof shape.lineStart === "object" && shape.lineStart !== null && "x" in shape.lineStart && "y" in shape.lineStart && "z" in shape.lineStart && isFiniteNumber(shape.lineStart.x) && isFiniteNumber(shape.lineStart.y) && isFiniteNumber(shape.lineStart.z)
        ? shape.lineStart
        : { x: -50, y: 0, z: 0 };
      // Type proof: lineEnd ∈ { x: number; y: number; z: number } | undefined → { x: number; y: number; z: number }
      const end = shape !== undefined && typeof shape === "object" && shape !== null && "lineEnd" in shape && shape.lineEnd !== undefined && typeof shape.lineEnd === "object" && shape.lineEnd !== null && "x" in shape.lineEnd && "y" in shape.lineEnd && "z" in shape.lineEnd && isFiniteNumber(shape.lineEnd.x) && isFiniteNumber(shape.lineEnd.y) && isFiniteNumber(shape.lineEnd.z)
        ? shape.lineEnd
        : { x: 50, y: 0, z: 0 };
      const t = rng();
      return base.add(
        new THREE.Vector3(
          start.x + (end.x - start.x) * t,
          start.y + (end.y - start.y) * t,
          start.z + (end.z - start.z) * t,
        ),
      );
    }

    case "cone": {
      const angle = rng() * Math.PI * 2;
      const t = rng();
      // Validate cone dimensions
      // Type proof: coneRadius ∈ number | undefined → number
      const rawConeRadius = shape !== undefined && typeof shape === "object" && shape !== null && "coneRadius" in shape && isFiniteNumber(shape.coneRadius) && shape.coneRadius >= 0
        ? shape.coneRadius
        : 50;
      const coneRadius = (Number.isFinite(rawConeRadius) && rawConeRadius > 0) ? rawConeRadius : 50;
      // Type proof: coneLength ∈ number | undefined → number
      const rawConeLength = shape !== undefined && typeof shape === "object" && shape !== null && "coneLength" in shape && isFiniteNumber(shape.coneLength) && shape.coneLength >= 0
        ? shape.coneLength
        : 100;
      const coneLength = (Number.isFinite(rawConeLength) && rawConeLength > 0) ? rawConeLength : 100;
      const radius = t * coneRadius;
      const height = t * coneLength;
      return base.add(
        new THREE.Vector3(
          Math.cos(angle) * radius,
          height,
          Math.sin(angle) * radius,
        ),
      );
    }

    case "image": {
      // Emit from non-transparent pixels of an image
      if (!shape.imageData) return base;

      const { width, height, data } = shape.imageData;
      // Validate threshold
      // Type proof: emissionThreshold ∈ number | undefined → number (clamped 0-1)
      const rawThreshold = shape !== undefined && typeof shape === "object" && shape !== null && "emissionThreshold" in shape && isFiniteNumber(shape.emissionThreshold) && shape.emissionThreshold >= 0 && shape.emissionThreshold <= 1
        ? shape.emissionThreshold
        : 0.1;
      const threshold = Number.isFinite(rawThreshold) ? rawThreshold : 0.1;

      // Try up to 100 times to find a valid pixel
      for (let attempt = 0; attempt < 100; attempt++) {
        const px = Math.floor(rng() * width);
        const py = Math.floor(rng() * height);
        const idx = (py * width + px) * 4;
        const alpha = data[idx + 3] / 255;

        if (alpha > threshold) {
          // Found a valid pixel - return position in image space
          // Center the emission on the emitter position
          return base.add(
            new THREE.Vector3(
              px - width / 2,
              -(py - height / 2), // Flip Y for screen coords
              0,
            ),
          );
        }
      }
      return base; // Fallback to center
    }

    case "depthEdge": {
      // Emit from depth discontinuities (silhouette edges)
      if (!shape.depthData || !shape.imageData) return base;

      const { width, height } = shape.imageData;
      // Validate dimensions
      if (width < 3 || height < 3) return base; // Need at least 3x3 for gradient calc

      const depthData = shape.depthData;
      // Validate threshold
      // Type proof: emissionThreshold ∈ number | undefined → number (clamped 0-1)
      const rawThreshold = shape !== undefined && typeof shape === "object" && shape !== null && "emissionThreshold" in shape && isFiniteNumber(shape.emissionThreshold) && shape.emissionThreshold >= 0 && shape.emissionThreshold <= 1
        ? shape.emissionThreshold
        : 0.05;
      const threshold = Number.isFinite(rawThreshold) ? rawThreshold : 0.05;

      // Try up to 100 times to find an edge pixel
      for (let attempt = 0; attempt < 100; attempt++) {
        const px = Math.floor(rng() * (width - 2)) + 1;
        const py = Math.floor(rng() * (height - 2)) + 1;
        const idx = py * width + px;

        // Sample depth and neighbors
        const d = depthData[idx];
        const dLeft = depthData[idx - 1];
        const dRight = depthData[idx + 1];
        const dUp = depthData[idx - width];
        const dDown = depthData[idx + width];

        // Calculate depth gradient magnitude
        const gradX = Math.abs(dRight - dLeft);
        const gradY = Math.abs(dDown - dUp);
        const gradient = Math.sqrt(gradX * gradX + gradY * gradY);

        if (gradient > threshold) {
          // Found an edge pixel
          // Use depth value for Z position (normalized 0-1, scale to reasonable range)
          const z = d * 500; // Scale depth to world units

          return base.add(
            new THREE.Vector3(
              px - width / 2,
              -(py - height / 2), // Flip Y for screen coords
              z,
            ),
          );
        }
      }
      return base; // Fallback to center
    }

    case "spline": {
      // Emit along a spline path
      if (!shape.splineId || !splineProvider) return base;

      // Get point along spline
      // Type proof: splineOffset ∈ number | undefined → number (clamped 0-1)
      const splineOffset = shape !== undefined && typeof shape === "object" && shape !== null && "splineOffset" in shape && isFiniteNumber(shape.splineOffset) && shape.splineOffset >= 0 && shape.splineOffset <= 1
        ? shape.splineOffset
        : undefined;
      let t = splineOffset !== undefined ? splineOffset : rng(); // Use offset or random position
      if (splineOffset === undefined) {
        t = rng(); // Random position along path
      }

      const point = splineProvider(shape.splineId, t);
      if (point) {
        // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
        const zValue = point.z;
        const z = isFiniteNumber(zValue) ? zValue : 0;
        return new THREE.Vector3(point.x, -point.y, z);
      }
      return base;
    }

    case "mesh": {
      // Emit from mesh vertices
      if (!shape.meshVertices) return base;

      const vertexCount = shape.meshVertices.length / 3;
      if (vertexCount === 0) return base;

      // Random vertex
      const vertexIndex = Math.floor(rng() * vertexCount);
      const vx = shape.meshVertices[vertexIndex * 3];
      const vy = shape.meshVertices[vertexIndex * 3 + 1];
      const vz = shape.meshVertices[vertexIndex * 3 + 2];

      return base.add(new THREE.Vector3(vx, vy, vz));
    }

    default:
      return base;
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                     // emission // direction // calculation
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Get emission direction based on emitter settings
 * Applies spread cone for random direction variation
 * @param emitter - The emitter configuration
 * @param rng - Seeded random number generator function
 */
export function getEmissionDirection(
  emitter: EmitterConfig,
  rng: RNGFunction,
): THREE.Vector3 {
  const baseDir = new THREE.Vector3(
    emitter.emissionDirection.x,
    emitter.emissionDirection.y,
    emitter.emissionDirection.z,
  ).normalize();

  if (emitter.emissionSpread <= 0) {
    return baseDir;
  }

  // Validate spread
  const safeSpread = Number.isFinite(emitter.emissionSpread) ? Math.max(0, emitter.emissionSpread) : 0;
  if (safeSpread <= 0) {
    return baseDir;
  }

  // Apply spread (cone distribution)
  const spreadRad = (safeSpread * Math.PI) / 180;
  const theta = rng() * Math.PI * 2;
  const phi = Math.acos(1 - rng() * (1 - Math.cos(spreadRad)));

  // Create rotation from base direction
  const up =
    Math.abs(baseDir.y) < 0.99
      ? new THREE.Vector3(0, 1, 0)
      : new THREE.Vector3(1, 0, 0);
  const right = new THREE.Vector3().crossVectors(up, baseDir).normalize();
  const realUp = new THREE.Vector3().crossVectors(baseDir, right);

  return new THREE.Vector3()
    .addScaledVector(baseDir, Math.cos(phi))
    .addScaledVector(right, Math.sin(phi) * Math.cos(theta))
    .addScaledVector(realUp, Math.sin(phi) * Math.sin(theta))
    .normalize();
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                  // velocity // inheritance
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Calculate initial velocity for a spawned particle
 * @param emitter - The emitter configuration (with velocity)
 * @param rng - Seeded random number generator function
 * @param splineProvider - Optional function to get points along a spline
 */
export function calculateInitialVelocity(
  emitter: EmitterConfig & { velocity: THREE.Vector3 },
  rng: RNGFunction,
): { velocity: THREE.Vector3; direction: THREE.Vector3; speed: number } {
  const direction = getEmissionDirection(emitter, rng);
  // Validate speed parameters
  const safeInitialSpeed = Number.isFinite(emitter.initialSpeed) ? Math.max(0, emitter.initialSpeed) : 100;
  const safeSpeedVariance = Number.isFinite(emitter.speedVariance) ? Math.max(0, emitter.speedVariance) : 0;
  const speed = safeInitialSpeed + (rng() - 0.5) * 2 * safeSpeedVariance;

  // Inherit emitter velocity (validate inheritance factor)
  const safeInherit = Number.isFinite(emitter.inheritEmitterVelocity) ? emitter.inheritEmitterVelocity : 0;
  const inheritVel = emitter.velocity
    .clone()
    .multiplyScalar(safeInherit);

  const velocity = new THREE.Vector3(
    direction.x * speed + inheritVel.x,
    direction.y * speed + inheritVel.y,
    direction.z * speed + inheritVel.z,
  );

  return { velocity, direction, speed };
}
