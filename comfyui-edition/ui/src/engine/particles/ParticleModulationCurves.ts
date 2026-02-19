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

import * as THREE from "three";
import type { ModulationCurve } from "./types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

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

// ════════════════════════════════════════════════════════════════════════════
//                                 // modulation // curve // evaluator // class
// ════════════════════════════════════════════════════════════════════════════

export class ParticleModulationCurves {
  private rng: () => number;
  private resolution: number;

  /**
   * @param rng - Seeded random number generator function
   * @param resolution - Texture resolution (default 256)
   */
  constructor(rng: () => number, resolution: number = 256) {
    this.rng = rng;
    // Validate resolution
    this.resolution = Number.isFinite(resolution) && resolution >= 2
      ? Math.floor(resolution)
      : 256;
  }

  /**
   * Set the RNG function (for restoring deterministic state)
   */
  setRng(rng: () => number): void {
    this.rng = rng;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // curve // evaluation
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Evaluate a modulation curve at time t (0-1)
   * @param curve - The modulation curve to evaluate
   * @param t - Normalized time (0-1) representing particle lifetime progress
   * @param randomOffset - Per-particle random offset (0-1) for deterministic random curves
   */
  evaluateCurve(
    curve: ModulationCurve | undefined,
    t: number,
    randomOffset?: number,
  ): number {
    if (!curve) return 1;

    switch (curve.type) {
      case "constant":
        // Validate value
        return Number.isFinite(curve.value) ? curve.value : 1;

      case "linear": {
        // Validate start/end
        const start = Number.isFinite(curve.start) ? curve.start : 1;
        const end = Number.isFinite(curve.end) ? curve.end : 1;
        return start + (end - start) * t;
      }

      case "curve": {
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

        // Guard against division by zero when adjacent points share same time
        const timeDiff = p1.time - p0.time;
        if (timeDiff === 0) {
          // Return average of the two values at the same time
          return (p0.value + p1.value) / 2;
        }

        const localT = (t - p0.time) / timeDiff;
        // Hermite interpolation
        const t2 = localT * localT;
        const t3 = t2 * localT;
        const h1 = 2 * t3 - 3 * t2 + 1;
        const h2 = -2 * t3 + 3 * t2;
        const h3 = t3 - 2 * t2 + localT;
        const h4 = t3 - t2;

        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        const p0OutTangent = (typeof p0.outTangent === "number" && Number.isFinite(p0.outTangent)) ? p0.outTangent : 0;
        const p1InTangent = (typeof p1.inTangent === "number" && Number.isFinite(p1.inTangent)) ? p1.inTangent : 0;
        return (
          h1 * p0.value +
          h2 * p1.value +
          h3 * p0OutTangent +
          h4 * p1InTangent
        );
      }

      case "random": {
        // Use per-particle random offset for determinism (same particle = same random value)
        const randVal = randomOffset !== undefined ? randomOffset : this.rng();
        // Validate min/max
        const min = Number.isFinite(curve.min) ? curve.min : 0;
        const max = Number.isFinite(curve.max) ? curve.max : 1;
        return min + randVal * (max - min);
      }

      case "randomCurve": {
        // Pass randomOffset to nested curves for consistent deterministic behavior
        const min = this.evaluateCurve(curve.minCurve, t, randomOffset);
        const max = this.evaluateCurve(curve.maxCurve, t, randomOffset);
        // Use same random offset for interpolation between min/max curves
        const randInterp =
          randomOffset !== undefined ? randomOffset : this.rng();
        return min + randInterp * (max - min);
      }

      default:
        return 1;
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                     // texture // generation
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Create modulation textures for GPU rendering
   */
  createTextures(modulation: LifetimeModulation): ModulationTextures {
    // Size over lifetime
    const sizeData = new Float32Array(this.resolution);
    this.sampleCurve(modulation.sizeOverLifetime, sizeData);
    const sizeTexture = new THREE.DataTexture(
      sizeData,
      this.resolution,
      1,
      THREE.RedFormat,
      THREE.FloatType,
    );
    sizeTexture.needsUpdate = true;

    // Opacity over lifetime
    const opacityData = new Float32Array(this.resolution);
    this.sampleCurve(modulation.opacityOverLifetime, opacityData);
    const opacityTexture = new THREE.DataTexture(
      opacityData,
      this.resolution,
      1,
      THREE.RedFormat,
      THREE.FloatType,
    );
    opacityTexture.needsUpdate = true;

    // Color over lifetime
    const colorStops = modulation.colorOverLifetime || [
      { time: 0, color: [1, 1, 1, 1] as [number, number, number, number] },
      { time: 1, color: [1, 1, 1, 1] as [number, number, number, number] },
    ];
    const colorData = new Float32Array(this.resolution * 4);
    // Guard against division by zero
    const divisor = Math.max(1, this.resolution - 1);
    for (let i = 0; i < this.resolution; i++) {
      const t = i / divisor;
      const color = this.sampleColorGradient(colorStops, t);
      colorData[i * 4] = color[0];
      colorData[i * 4 + 1] = color[1];
      colorData[i * 4 + 2] = color[2];
      colorData[i * 4 + 3] = color[3];
    }
    const colorTexture = new THREE.DataTexture(
      colorData,
      this.resolution,
      1,
      THREE.RGBAFormat,
      THREE.FloatType,
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

    // Guard against division by zero
    const divisor = Math.max(1, len - 1);
    for (let i = 0; i < len; i++) {
      const t = i / divisor;
      output[i] = this.evaluateCurve(curve, t);
    }
  }

  /**
   * Sample color gradient at time t
   */
  sampleColorGradient(
    stops: ColorStop[],
    t: number,
  ): [number, number, number, number] {
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

    // Interpolate (guard against same time)
    const timeDiff = s1.time - s0.time;
    if (timeDiff === 0) return s0.color;
    const localT = (t - s0.time) / timeDiff;
    return [
      s0.color[0] + (s1.color[0] - s0.color[0]) * localT,
      s0.color[1] + (s1.color[1] - s0.color[1]) * localT,
      s0.color[2] + (s1.color[2] - s0.color[2]) * localT,
      s0.color[3] + (s1.color[3] - s0.color[3]) * localT,
    ];
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                   // cleanup
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Dispose modulation textures
   */
  disposeTextures(textures: ModulationTextures): void {
    textures.sizeOverLifetime.dispose();
    textures.opacityOverLifetime.dispose();
    textures.colorOverLifetime.dispose();
  }
}
