/**
 * Particle Trail System
 *
 * Handles trail rendering for GPU particle systems.
 * Maintains position history for each particle and renders as line segments.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import * as THREE from "three";
import { PARTICLE_STRIDE } from "./types";

// ============================================================================
// TYPES
// ============================================================================

export interface TrailConfig {
  trailLength: number;
  trailSegments: number;
  trailWidthStart: number;
  trailWidthEnd: number;
  trailFadeMode: "none" | "alpha" | "width" | "both";
}

export interface TrailBlendingConfig {
  blendMode: "normal" | "additive" | "multiply" | "screen" | "premultiplied";
}

// ============================================================================
// PARTICLE TRAIL SYSTEM CLASS
// ============================================================================

export class ParticleTrailSystem {
  private readonly maxParticles: number;
  private readonly TRAIL_POSITIONS_PER_PARTICLE = 16;

  // Trail buffers
  private trailBuffer: Float32Array | null = null;
  private trailMesh: THREE.LineSegments | null = null;
  private trailGeometry: THREE.BufferGeometry | null = null;
  private trailMaterial: THREE.LineBasicMaterial | null = null;

  // Configuration
  private config: TrailConfig;
  private blendingConfig: TrailBlendingConfig;

  constructor(
    maxParticles: number,
    config: TrailConfig,
    blendingConfig: TrailBlendingConfig,
  ) {
    // Validate maxParticles to prevent infinite loop/memory exhaustion
    this.maxParticles = Number.isFinite(maxParticles) && maxParticles > 0
      ? Math.min(Math.floor(maxParticles), 1_000_000)  // Cap lower for trails (memory intensive)
      : 10000;
    this.config = config;
    this.blendingConfig = blendingConfig;
  }

  // ============================================================================
  // INITIALIZATION
  // ============================================================================

  /**
   * Initialize trail rendering resources
   */
  initialize(): void {
    // Validate trailLength
    const rawTrailLength = Number.isFinite(this.config.trailLength) && this.config.trailLength > 0
      ? this.config.trailLength
      : 8;  // Default trail length
    const trailLength = Math.min(rawTrailLength, this.TRAIL_POSITIONS_PER_PARTICLE);
    if (trailLength <= 0) return;

    const maxTrailVertices = this.maxParticles * trailLength * 2; // 2 vertices per segment

    // Trail history buffer: stores past positions for each particle
    // Format: [x, y, z, age] per trail point
    this.trailBuffer = new Float32Array(
      this.maxParticles * this.TRAIL_POSITIONS_PER_PARTICLE * 4,
    );

    // Create line geometry for trails
    this.trailGeometry = new THREE.BufferGeometry();
    const trailPositions = new Float32Array(maxTrailVertices * 3);
    const trailColors = new Float32Array(maxTrailVertices * 4);

    this.trailGeometry.setAttribute(
      "position",
      new THREE.BufferAttribute(trailPositions, 3),
    );
    this.trailGeometry.setAttribute(
      "color",
      new THREE.BufferAttribute(trailColors, 4),
    );
    (
      this.trailGeometry.getAttribute("position") as THREE.BufferAttribute
    ).setUsage(THREE.DynamicDrawUsage);
    (
      this.trailGeometry.getAttribute("color") as THREE.BufferAttribute
    ).setUsage(THREE.DynamicDrawUsage);

    // Trail material
    this.trailMaterial = new THREE.LineBasicMaterial({
      vertexColors: true,
      transparent: true,
      blending: this.getThreeBlending(),
      depthWrite: false,
    });

    this.trailMesh = new THREE.LineSegments(
      this.trailGeometry,
      this.trailMaterial,
    );
    this.trailMesh.frustumCulled = false;
  }

  // ============================================================================
  // UPDATE
  // ============================================================================

  /**
   * Update trail positions for all particles
   * @param particleBuffer - The current particle data buffer
   */
  update(particleBuffer: Float32Array): void {
    if (!this.trailBuffer || !this.trailGeometry) return;

    // Validate trailLength (same validation as initialize)
    const rawTrailLength = Number.isFinite(this.config.trailLength) && this.config.trailLength > 0
      ? this.config.trailLength
      : 8;
    const trailLength = Math.min(rawTrailLength, this.TRAIL_POSITIONS_PER_PARTICLE);
    if (trailLength <= 0) return;

    const posAttr = this.trailGeometry.getAttribute(
      "position",
    ) as THREE.BufferAttribute;
    const colorAttr = this.trailGeometry.getAttribute(
      "color",
    ) as THREE.BufferAttribute;

    let vertexIndex = 0;
    const fadeMode = this.config.trailFadeMode;

    for (let i = 0; i < this.maxParticles; i++) {
      const particleOffset = i * PARTICLE_STRIDE;
      const lifetime = particleBuffer[particleOffset + 7];
      const age = particleBuffer[particleOffset + 6];

      // Skip dead particles
      if (lifetime <= 0 || age >= lifetime) continue;

      // Get current position
      const currentX = particleBuffer[particleOffset + 0];
      const currentY = particleBuffer[particleOffset + 1];
      const currentZ = particleBuffer[particleOffset + 2];
      const currentColor = [
        particleBuffer[particleOffset + 12],
        particleBuffer[particleOffset + 13],
        particleBuffer[particleOffset + 14],
        particleBuffer[particleOffset + 15],
      ];

      // Shift trail history and insert new position
      const trailOffset = i * this.TRAIL_POSITIONS_PER_PARTICLE * 4;

      // Shift existing trail points back
      for (let t = this.TRAIL_POSITIONS_PER_PARTICLE - 1; t > 0; t--) {
        const srcOffset = trailOffset + (t - 1) * 4;
        const dstOffset = trailOffset + t * 4;
        this.trailBuffer[dstOffset + 0] = this.trailBuffer[srcOffset + 0];
        this.trailBuffer[dstOffset + 1] = this.trailBuffer[srcOffset + 1];
        this.trailBuffer[dstOffset + 2] = this.trailBuffer[srcOffset + 2];
        this.trailBuffer[dstOffset + 3] = this.trailBuffer[srcOffset + 3] + 1; // Increment age
      }

      // Insert current position at front
      this.trailBuffer[trailOffset + 0] = currentX;
      this.trailBuffer[trailOffset + 1] = currentY;
      this.trailBuffer[trailOffset + 2] = currentZ;
      this.trailBuffer[trailOffset + 3] = 0; // Age = 0 for newest

      // Build line segments for this particle's trail
      for (let t = 0; t < trailLength - 1; t++) {
        const p1Offset = trailOffset + t * 4;
        const p2Offset = trailOffset + (t + 1) * 4;

        // Check if trail points are valid (age < trail length)
        if (this.trailBuffer[p2Offset + 3] >= trailLength) break;

        const x1 = this.trailBuffer[p1Offset + 0];
        const y1 = this.trailBuffer[p1Offset + 1];
        const z1 = this.trailBuffer[p1Offset + 2];
        const x2 = this.trailBuffer[p2Offset + 0];
        const y2 = this.trailBuffer[p2Offset + 1];
        const z2 = this.trailBuffer[p2Offset + 2];

        // Skip if positions are invalid (0,0,0)
        if (x1 === 0 && y1 === 0 && z1 === 0) break;
        if (x2 === 0 && y2 === 0 && z2 === 0) break;

        // Calculate alpha falloff along trail
        // Use trailWidthEnd as the final alpha multiplier (0 = full fade, 1 = no fade)
        const t1Ratio = t / (trailLength - 1);
        const t2Ratio = (t + 1) / (trailLength - 1);

        let alpha1 = currentColor[3];
        let alpha2 = currentColor[3];

        if (fadeMode === "alpha" || fadeMode === "both") {
          // Interpolate from 1.0 (start) to trailWidthEnd (end)
          // Validate trailWidthEnd
          const endAlpha = Number.isFinite(this.config.trailWidthEnd) 
            ? Math.max(0, Math.min(1, this.config.trailWidthEnd))  // Clamp to [0, 1]
            : 0;  // Default: full fade
          alpha1 *= 1 - t1Ratio * (1 - endAlpha);
          alpha2 *= 1 - t2Ratio * (1 - endAlpha);
        }

        // Set vertex positions
        posAttr.setXYZ(vertexIndex, x1, y1, z1);
        colorAttr.setXYZW(
          vertexIndex,
          currentColor[0],
          currentColor[1],
          currentColor[2],
          alpha1,
        );
        vertexIndex++;

        posAttr.setXYZ(vertexIndex, x2, y2, z2);
        colorAttr.setXYZW(
          vertexIndex,
          currentColor[0],
          currentColor[1],
          currentColor[2],
          alpha2,
        );
        vertexIndex++;
      }
    }

    // Update draw range
    this.trailGeometry.setDrawRange(0, vertexIndex);
    posAttr.needsUpdate = true;
    colorAttr.needsUpdate = true;
  }

  // ============================================================================
  // ACCESSORS
  // ============================================================================

  /**
   * Get the trail mesh for adding to scene
   */
  getMesh(): THREE.LineSegments | null {
    return this.trailMesh;
  }

  /**
   * Check if trail system is initialized
   */
  isInitialized(): boolean {
    return this.trailMesh !== null;
  }

  /**
   * Update trail configuration
   */
  updateConfig(config: Partial<TrailConfig>): void {
    Object.assign(this.config, config);
  }

  // ============================================================================
  // CLEANUP
  // ============================================================================

  /**
   * Reset trail history (e.g., when scrubbing)
   */
  reset(): void {
    if (this.trailBuffer) {
      this.trailBuffer.fill(0);
    }
    if (this.trailGeometry) {
      this.trailGeometry.setDrawRange(0, 0);
    }
  }

  /**
   * Dispose of all resources
   */
  dispose(): void {
    if (this.trailGeometry) {
      this.trailGeometry.dispose();
      this.trailGeometry = null;
    }
    if (this.trailMaterial) {
      this.trailMaterial.dispose();
      this.trailMaterial = null;
    }
    this.trailMesh = null;
    this.trailBuffer = null;
  }

  // ============================================================================
  // PRIVATE HELPERS
  // ============================================================================

  private getThreeBlending(): THREE.Blending {
    switch (this.blendingConfig.blendMode) {
      case "additive":
        return THREE.AdditiveBlending;
      case "multiply":
        return THREE.MultiplyBlending;
      case "screen":
        return THREE.CustomBlending;
      default:
        return THREE.NormalBlending;
    }
  }
}
