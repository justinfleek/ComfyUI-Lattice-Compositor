/**
 * Particle Emitter Logic
 *
 * Handles spawn position calculation based on emitter shape
 * and emission direction calculation with spread cone.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import * as THREE from 'three';
import type { EmitterConfig, EmitterShapeConfig } from './types';

// ============================================================================
// TYPES
// ============================================================================

export type SplineProvider = (splineId: string, t: number) => { x: number; y: number; z?: number } | null;
export type RNGFunction = () => number;

// ============================================================================
// EMITTER POSITION CALCULATION
// ============================================================================

/**
 * Get spawn position based on emitter shape
 * @param emitter - The emitter configuration
 * @param rng - Seeded random number generator function
 * @param splineProvider - Optional function to get points along a spline
 */
export function getEmitterPosition(
  emitter: EmitterConfig,
  rng: RNGFunction,
  splineProvider?: SplineProvider | null
): THREE.Vector3 {
  const shape = emitter.shape;
  // Negate Y to match THREE.js coordinate system (Y-up) and gizmo positioning
  const base = new THREE.Vector3(emitter.position.x, -emitter.position.y, emitter.position.z);

  switch (shape.type) {
    case 'point':
      return base;

    case 'circle': {
      const angle = rng() * Math.PI * 2;
      let radius = shape.radius ?? 50;
      if (!shape.emitFromEdge) {
        radius *= Math.sqrt(rng());  // Uniform distribution in circle
      }
      return base.add(new THREE.Vector3(
        Math.cos(angle) * radius,
        Math.sin(angle) * radius,
        0
      ));
    }

    case 'sphere': {
      const theta = rng() * Math.PI * 2;
      const phi = Math.acos(2 * rng() - 1);
      let radius = shape.radius ?? 50;
      if (!shape.emitFromEdge) {
        radius *= Math.cbrt(rng());  // Uniform distribution in sphere
      }
      return base.add(new THREE.Vector3(
        Math.sin(phi) * Math.cos(theta) * radius,
        Math.sin(phi) * Math.sin(theta) * radius,
        Math.cos(phi) * radius
      ));
    }

    case 'box': {
      const size = shape.boxSize ?? { x: 100, y: 100, z: 100 };
      return base.add(new THREE.Vector3(
        (rng() - 0.5) * size.x,
        (rng() - 0.5) * size.y,
        (rng() - 0.5) * size.z
      ));
    }

    case 'line': {
      const start = shape.lineStart ?? { x: -50, y: 0, z: 0 };
      const end = shape.lineEnd ?? { x: 50, y: 0, z: 0 };
      const t = rng();
      return base.add(new THREE.Vector3(
        start.x + (end.x - start.x) * t,
        start.y + (end.y - start.y) * t,
        start.z + (end.z - start.z) * t
      ));
    }

    case 'cone': {
      const angle = rng() * Math.PI * 2;
      const t = rng();
      const radius = t * (shape.coneRadius ?? 50);
      const height = t * (shape.coneLength ?? 100);
      return base.add(new THREE.Vector3(
        Math.cos(angle) * radius,
        height,
        Math.sin(angle) * radius
      ));
    }

    case 'image': {
      // Emit from non-transparent pixels of an image
      if (!shape.imageData) return base;

      const { width, height, data } = shape.imageData;
      const threshold = shape.emissionThreshold ?? 0.1;

      // Try up to 100 times to find a valid pixel
      for (let attempt = 0; attempt < 100; attempt++) {
        const px = Math.floor(rng() * width);
        const py = Math.floor(rng() * height);
        const idx = (py * width + px) * 4;
        const alpha = data[idx + 3] / 255;

        if (alpha > threshold) {
          // Found a valid pixel - return position in image space
          // Center the emission on the emitter position
          return base.add(new THREE.Vector3(
            px - width / 2,
            -(py - height / 2), // Flip Y for screen coords
            0
          ));
        }
      }
      return base; // Fallback to center
    }

    case 'depthEdge': {
      // Emit from depth discontinuities (silhouette edges)
      if (!shape.depthData || !shape.imageData) return base;

      const { width, height } = shape.imageData;
      const depthData = shape.depthData;
      const threshold = shape.emissionThreshold ?? 0.05; // Depth difference threshold

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

          return base.add(new THREE.Vector3(
            px - width / 2,
            -(py - height / 2), // Flip Y for screen coords
            z
          ));
        }
      }
      return base; // Fallback to center
    }

    case 'spline': {
      // Emit along a spline path
      if (!shape.splineId || !splineProvider) return base;

      // Get point along spline
      let t = shape.splineOffset ?? rng(); // Use offset or random position
      if (shape.splineOffset === undefined) {
        t = rng(); // Random position along path
      }

      const point = splineProvider(shape.splineId, t);
      if (point) {
        return new THREE.Vector3(point.x, -point.y, point.z ?? 0);
      }
      return base;
    }

    case 'mesh': {
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

// ============================================================================
// EMISSION DIRECTION CALCULATION
// ============================================================================

/**
 * Get emission direction based on emitter settings
 * Applies spread cone for random direction variation
 * @param emitter - The emitter configuration
 * @param rng - Seeded random number generator function
 */
export function getEmissionDirection(
  emitter: EmitterConfig,
  rng: RNGFunction
): THREE.Vector3 {
  const baseDir = new THREE.Vector3(
    emitter.emissionDirection.x,
    emitter.emissionDirection.y,
    emitter.emissionDirection.z
  ).normalize();

  if (emitter.emissionSpread <= 0) {
    return baseDir;
  }

  // Apply spread (cone distribution)
  const spreadRad = (emitter.emissionSpread * Math.PI) / 180;
  const theta = rng() * Math.PI * 2;
  const phi = Math.acos(1 - rng() * (1 - Math.cos(spreadRad)));

  // Create rotation from base direction
  const up = Math.abs(baseDir.y) < 0.99
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

// ============================================================================
// VELOCITY INHERITANCE
// ============================================================================

/**
 * Calculate initial velocity for a spawned particle
 * @param emitter - The emitter configuration (with velocity)
 * @param rng - Seeded random number generator function
 * @param splineProvider - Optional function to get points along a spline
 */
export function calculateInitialVelocity(
  emitter: EmitterConfig & { velocity: THREE.Vector3 },
  rng: RNGFunction
): { velocity: THREE.Vector3; direction: THREE.Vector3; speed: number } {
  const direction = getEmissionDirection(emitter, rng);
  const speed = emitter.initialSpeed + (rng() - 0.5) * 2 * emitter.speedVariance;

  // Inherit emitter velocity
  const inheritVel = emitter.velocity.clone().multiplyScalar(emitter.inheritEmitterVelocity);

  const velocity = new THREE.Vector3(
    direction.x * speed + inheritVel.x,
    direction.y * speed + inheritVel.y,
    direction.z * speed + inheritVel.z
  );

  return { velocity, direction, speed };
}
