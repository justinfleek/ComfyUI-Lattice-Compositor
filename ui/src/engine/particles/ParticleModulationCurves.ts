/**
 * Particle Modulation Curves
 *
 * Handles evaluation of lifetime modulation curves for particle properties:
 * - Size over lifetime
 * - Opacity over lifetime
 * - Color over lifetime
 *
 * Supports multiple curve types: constant, linear, bezier curves, random, and randomCurve.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import * as THREE from 'three';
import type { ModulationCurve } from './types';

// ============================================================================
// TYPES
// ============================================================================

export interface CurvePoint {
  time: number;
  value: number;
  inTangent?: number;
  outTangent?: number;
}

export interface ColorStop {
  time: number;
  color: [number, number, number, number];
}

export interface ModulationTextures {
  sizeOverLifetime: THREE.DataTexture;
  opacityOverLifetime: THREE.DataTexture;
  colorOverLifetime: THREE.DataTexture;
}

export interface LifetimeModulation {
  sizeOverLifetime?: ModulationCurve;
  opacityOverLifetime?: ModulationCurve;
  colorOverLifetime?: ColorStop[];
}

// ============================================================================
// MODULATION CURVE EVALUATOR CLASS
// ============================================================================

export class ParticleModulationCurves {
  private rng: () => number;
  private resolution: number;

  /**
   * @param rng - Seeded random number generator function
   * @param resolution - Texture resolution (default 256)
   */
  constructor(rng: () => number, resolution: number = 256) {
    this.rng = rng;
    this.resolution = resolution;
  }

  /**
   * Set the RNG function (for restoring deterministic state)
   */
  setRng(rng: () => number): void {
    this.rng = rng;
  }

  // ============================================================================
  // CURVE EVALUATION
  // ============================================================================

  /**
   * Evaluate a modulation curve at time t (0-1)
   */
  evaluateCurve(curve: ModulationCurve | undefined, t: number): number {
    if (!curve) return 1;

    switch (curve.type) {
      case 'constant':
        return curve.value;

      case 'linear':
        return curve.start + (curve.end - curve.start) * t;

      case 'curve': {
        // Find surrounding keyframes
        const points = curve.points;
        if (points.length === 0) return 1;
        if (points.length === 1) return points[0].value;

        let p0 = points[0];
        let p1 = points[points.length - 1];

        for (let i = 0; i < points.length - 1; i++) {
          if (t >= points[i].time && t <= points[i + 1].time) {
            p0 = points[i];
            p1 = points[i + 1];
            break;
          }
        }

        const localT = (t - p0.time) / (p1.time - p0.time);
        // Hermite interpolation
        const t2 = localT * localT;
        const t3 = t2 * localT;
        const h1 = 2 * t3 - 3 * t2 + 1;
        const h2 = -2 * t3 + 3 * t2;
        const h3 = t3 - 2 * t2 + localT;
        const h4 = t3 - t2;

        return h1 * p0.value + h2 * p1.value +
               h3 * (p0.outTangent ?? 0) + h4 * (p1.inTangent ?? 0);
      }

      case 'random':
        return curve.min + this.rng() * (curve.max - curve.min);

      case 'randomCurve': {
        const min = this.evaluateCurve(curve.minCurve, t);
        const max = this.evaluateCurve(curve.maxCurve, t);
        return min + this.rng() * (max - min);
      }

      default:
        return 1;
    }
  }

  // ============================================================================
  // TEXTURE GENERATION
  // ============================================================================

  /**
   * Create modulation textures for GPU rendering
   */
  createTextures(modulation: LifetimeModulation): ModulationTextures {
    // Size over lifetime
    const sizeData = new Float32Array(this.resolution);
    this.sampleCurve(modulation.sizeOverLifetime, sizeData);
    const sizeTexture = new THREE.DataTexture(
      sizeData, this.resolution, 1, THREE.RedFormat, THREE.FloatType
    );
    sizeTexture.needsUpdate = true;

    // Opacity over lifetime
    const opacityData = new Float32Array(this.resolution);
    this.sampleCurve(modulation.opacityOverLifetime, opacityData);
    const opacityTexture = new THREE.DataTexture(
      opacityData, this.resolution, 1, THREE.RedFormat, THREE.FloatType
    );
    opacityTexture.needsUpdate = true;

    // Color over lifetime
    const colorStops = modulation.colorOverLifetime || [
      { time: 0, color: [1, 1, 1, 1] as [number, number, number, number] },
      { time: 1, color: [1, 1, 1, 1] as [number, number, number, number] },
    ];
    const colorData = new Float32Array(this.resolution * 4);
    for (let i = 0; i < this.resolution; i++) {
      const t = i / (this.resolution - 1);
      const color = this.sampleColorGradient(colorStops, t);
      colorData[i * 4] = color[0];
      colorData[i * 4 + 1] = color[1];
      colorData[i * 4 + 2] = color[2];
      colorData[i * 4 + 3] = color[3];
    }
    const colorTexture = new THREE.DataTexture(
      colorData, this.resolution, 1, THREE.RGBAFormat, THREE.FloatType
    );
    colorTexture.needsUpdate = true;

    return {
      sizeOverLifetime: sizeTexture,
      opacityOverLifetime: opacityTexture,
      colorOverLifetime: colorTexture,
    };
  }

  /**
   * Sample a modulation curve into a float array
   */
  sampleCurve(curve: ModulationCurve | undefined, output: Float32Array): void {
    const len = output.length;

    if (!curve) {
      output.fill(1);
      return;
    }

    for (let i = 0; i < len; i++) {
      const t = i / (len - 1);
      output[i] = this.evaluateCurve(curve, t);
    }
  }

  /**
   * Sample color gradient at time t
   */
  sampleColorGradient(stops: ColorStop[], t: number): [number, number, number, number] {
    if (stops.length === 0) return [1, 1, 1, 1];
    if (stops.length === 1) return stops[0].color;

    // Find surrounding stops
    let s0 = stops[0];
    let s1 = stops[stops.length - 1];

    for (let i = 0; i < stops.length - 1; i++) {
      if (t >= stops[i].time && t <= stops[i + 1].time) {
        s0 = stops[i];
        s1 = stops[i + 1];
        break;
      }
    }

    // Handle edge cases
    if (t <= s0.time) return s0.color;
    if (t >= s1.time) return s1.color;

    // Interpolate
    const localT = (t - s0.time) / (s1.time - s0.time);
    return [
      s0.color[0] + (s1.color[0] - s0.color[0]) * localT,
      s0.color[1] + (s1.color[1] - s0.color[1]) * localT,
      s0.color[2] + (s1.color[2] - s0.color[2]) * localT,
      s0.color[3] + (s1.color[3] - s0.color[3]) * localT,
    ];
  }

  // ============================================================================
  // CLEANUP
  // ============================================================================

  /**
   * Dispose modulation textures
   */
  disposeTextures(textures: ModulationTextures): void {
    textures.sizeOverLifetime.dispose();
    textures.opacityOverLifetime.dispose();
    textures.colorOverLifetime.dispose();
  }
}
