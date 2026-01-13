/**
 * Smoothed Particle Hydrodynamics (SPH) Fluid System
 *
 * Implements SPH for realistic fluid simulation:
 * - Density calculation using kernel functions
 * - Pressure forces (Navier-Stokes)
 * - Viscosity forces
 * - Surface tension (optional)
 *
 * Based on Müller et al. "Particle-Based Fluid Simulation for Interactive Applications"
 */

import { PARTICLE_STRIDE } from "./types";
import type { SpatialHashGrid } from "./SpatialHashGrid";

// ============================================================================
// SPH CONSTANTS
// ============================================================================

const PI = Math.PI;

// ============================================================================
// KERNEL FUNCTIONS
// ============================================================================

/**
 * Poly6 kernel - used for density calculation
 * Smooth, works well for density
 */
function poly6Kernel(r: number, h: number): number {
  if (r > h || r < 0) return 0;
  const h2 = h * h;
  const r2 = r * r;
  const diff = h2 - r2;
  // W_poly6 = 315 / (64 * π * h^9) * (h² - r²)³
  return (315 / (64 * PI * Math.pow(h, 9))) * diff * diff * diff;
}

/**
 * Poly6 kernel gradient - used for surface tension
 */
function poly6KernelGradient(rx: number, ry: number, rz: number, r: number, h: number): { x: number; y: number; z: number } {
  if (r > h || r < 0.0001) return { x: 0, y: 0, z: 0 };
  const h2 = h * h;
  const r2 = r * r;
  const diff = h2 - r2;
  // ∇W_poly6 = -945 / (32 * π * h^9) * (h² - r²)² * r
  const coeff = (-945 / (32 * PI * Math.pow(h, 9))) * diff * diff;
  return { x: coeff * rx, y: coeff * ry, z: coeff * rz };
}

/**
 * Spiky kernel gradient - used for pressure forces
 * Has non-zero gradient at r=0, which is important for pressure
 */
function spikyKernelGradient(rx: number, ry: number, rz: number, r: number, h: number): { x: number; y: number; z: number } {
  if (r > h || r < 0.0001) return { x: 0, y: 0, z: 0 };
  const diff = h - r;
  // ∇W_spiky = -45 / (π * h^6) * (h - r)² * r_normalized
  const coeff = (-45 / (PI * Math.pow(h, 6))) * diff * diff / r;
  return { x: coeff * rx, y: coeff * ry, z: coeff * rz };
}

/**
 * Viscosity kernel Laplacian - used for viscosity forces
 * Always positive, which ensures viscosity dampens relative motion
 */
function viscosityKernelLaplacian(r: number, h: number): number {
  if (r > h || r < 0) return 0;
  // ∇²W_viscosity = 45 / (π * h^6) * (h - r)
  return (45 / (PI * Math.pow(h, 6))) * (h - r);
}

// ============================================================================
// TYPES
// ============================================================================

export interface SPHConfig {
  /** Smoothing radius (kernel support radius) */
  smoothingRadius: number;
  /** Rest density (kg/m³) - water is ~1000 */
  restDensity: number;
  /** Gas constant for pressure (higher = stiffer) */
  gasConstant: number;
  /** Viscosity coefficient (higher = thicker fluid) */
  viscosity: number;
  /** Surface tension coefficient */
  surfaceTension: number;
  /** Enable surface tension calculation (expensive) */
  enableSurfaceTension: boolean;
  /** Gravity */
  gravity: { x: number; y: number; z: number };
  /** Time step for stability (smaller = more stable but slower) */
  maxTimeStep: number;
}

/**
 * Per-particle SPH data
 */
interface SPHParticleData {
  density: number;
  pressure: number;
  forceX: number;
  forceY: number;
  forceZ: number;
}

// ============================================================================
// SPH FLUID SYSTEM
// ============================================================================

export class ParticleSPHSystem {
  private maxParticles: number;
  private config: SPHConfig;
  private spatialHash: SpatialHashGrid | null = null;

  // Per-particle SPH data
  private sphData: SPHParticleData[] = [];

  constructor(maxParticles: number, config: Partial<SPHConfig> = {}) {
    // Validate maxParticles
    this.maxParticles = Number.isFinite(maxParticles) && maxParticles > 0
      ? Math.min(Math.floor(maxParticles), 500_000) // Lower cap for SPH (more expensive)
      : 10000;

    this.config = {
      smoothingRadius: config.smoothingRadius ?? 50,
      restDensity: config.restDensity ?? 1000,
      gasConstant: config.gasConstant ?? 2000,
      viscosity: config.viscosity ?? 200,
      surfaceTension: config.surfaceTension ?? 0.0728,
      enableSurfaceTension: config.enableSurfaceTension ?? false,
      gravity: config.gravity ?? { x: 0, y: -980, z: 0 },
      maxTimeStep: config.maxTimeStep ?? 0.004,
    };

    // Initialize SPH data array
    for (let i = 0; i < this.maxParticles; i++) {
      this.sphData.push({
        density: this.config.restDensity,
        pressure: 0,
        forceX: 0,
        forceY: 0,
        forceZ: 0,
      });
    }
  }

  /**
   * Set the spatial hash grid for neighbor queries
   */
  setSpatialHash(hash: SpatialHashGrid): void {
    this.spatialHash = hash;
  }

  /**
   * Main SPH simulation step
   */
  update(particleBuffer: Float32Array, dt: number): void {
    if (!this.spatialHash) {
      console.warn("SPH: No spatial hash set. Call setSpatialHash() first.");
      return;
    }

    // Clamp time step for stability
    const safeDt = Math.min(
      Number.isFinite(dt) && dt > 0 ? dt : 0.016,
      this.config.maxTimeStep
    );

    // If dt is larger than maxTimeStep, substep
    let remainingTime = safeDt;
    while (remainingTime > 0) {
      const stepDt = Math.min(remainingTime, this.config.maxTimeStep);
      this.substep(particleBuffer, stepDt);
      remainingTime -= stepDt;
    }
  }

  /**
   * Single SPH substep
   */
  private substep(buffer: Float32Array, dt: number): void {
    const h = this.config.smoothingRadius;

    // Step 1: Calculate density and pressure for all particles
    this.computeDensityPressure(buffer, h);

    // Step 2: Calculate forces (pressure + viscosity + surface tension)
    this.computeForces(buffer, h);

    // Step 3: Integrate (update velocities and positions)
    this.integrate(buffer, dt);
  }

  /**
   * Compute density and pressure at each particle
   */
  private computeDensityPressure(buffer: Float32Array, h: number): void {
    if (!this.spatialHash) {
      throw new Error("SPH computeDensityPressure called without spatialHash");
    }
    const spatialHash = this.spatialHash;
    const restDensity = this.config.restDensity;
    const gasConstant = this.config.gasConstant;

    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = buffer[offset + 7];
      const age = buffer[offset + 6];

      // Skip dead particles
      if (lifetime <= 0 || age >= lifetime) {
        this.sphData[i].density = 0;
        this.sphData[i].pressure = 0;
        continue;
      }

      const px = buffer[offset + 0];
      const py = buffer[offset + 1];
      const pz = buffer[offset + 2];
      const mass = Math.max(buffer[offset + 8], 0.1);

      // Sum density contributions from neighbors
      let density = 0;

      // Self-contribution
      density += mass * poly6Kernel(0, h);

      // Neighbor contributions
      for (const j of spatialHash.getNeighbors(px, py, pz)) {
        if (j === i) continue;

        const jOffset = j * PARTICLE_STRIDE;
        const jLifetime = buffer[jOffset + 7];
        const jAge = buffer[jOffset + 6];
        if (jLifetime <= 0 || jAge >= jLifetime) continue;

        const jx = buffer[jOffset + 0];
        const jy = buffer[jOffset + 1];
        const jz = buffer[jOffset + 2];
        const jMass = Math.max(buffer[jOffset + 8], 0.1);

        const dx = px - jx;
        const dy = py - jy;
        const dz = pz - jz;
        const r = Math.sqrt(dx * dx + dy * dy + dz * dz);

        density += jMass * poly6Kernel(r, h);
      }

      // Store density and compute pressure using equation of state
      // P = k * (ρ - ρ₀) - simple linear EOS
      // Could also use: P = k * ((ρ/ρ₀)^γ - 1) for Tait equation
      this.sphData[i].density = density;
      this.sphData[i].pressure = Math.max(0, gasConstant * (density - restDensity));
    }
  }

  /**
   * Compute pressure, viscosity, and surface tension forces
   */
  private computeForces(buffer: Float32Array, h: number): void {
    if (!this.spatialHash) {
      throw new Error("SPH computeForces called without spatialHash");
    }
    const spatialHash = this.spatialHash;
    const viscosity = this.config.viscosity;
    const surfaceTension = this.config.surfaceTension;
    const enableST = this.config.enableSurfaceTension;

    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = buffer[offset + 7];
      const age = buffer[offset + 6];

      // Reset forces
      this.sphData[i].forceX = 0;
      this.sphData[i].forceY = 0;
      this.sphData[i].forceZ = 0;

      if (lifetime <= 0 || age >= lifetime) continue;

      const density_i = this.sphData[i].density;
      if (density_i < 0.0001) continue;

      const pressure_i = this.sphData[i].pressure;
      const px = buffer[offset + 0];
      const py = buffer[offset + 1];
      const pz = buffer[offset + 2];
      const vx = buffer[offset + 3];
      const vy = buffer[offset + 4];
      const vz = buffer[offset + 5];

      let fPressureX = 0, fPressureY = 0, fPressureZ = 0;
      let fViscosityX = 0, fViscosityY = 0, fViscosityZ = 0;
      let colorFieldGradX = 0, colorFieldGradY = 0, colorFieldGradZ = 0;
      let colorFieldLaplacian = 0;

      // Sum forces from neighbors
      for (const j of spatialHash.getNeighbors(px, py, pz)) {
        if (j === i) continue;

        const jOffset = j * PARTICLE_STRIDE;
        const jLifetime = buffer[jOffset + 7];
        const jAge = buffer[jOffset + 6];
        if (jLifetime <= 0 || jAge >= jLifetime) continue;

        const density_j = this.sphData[j].density;
        if (density_j < 0.0001) continue;

        const pressure_j = this.sphData[j].pressure;
        const jx = buffer[jOffset + 0];
        const jy = buffer[jOffset + 1];
        const jz = buffer[jOffset + 2];
        const jvx = buffer[jOffset + 3];
        const jvy = buffer[jOffset + 4];
        const jvz = buffer[jOffset + 5];
        const jMass = Math.max(buffer[jOffset + 8], 0.1);

        const dx = px - jx;
        const dy = py - jy;
        const dz = pz - jz;
        const r = Math.sqrt(dx * dx + dy * dy + dz * dz);

        if (r > h || r < 0.0001) continue;

        // Pressure force: -∑ m_j * (P_i + P_j) / (2 * ρ_j) * ∇W_spiky
        const pressureGrad = spikyKernelGradient(dx, dy, dz, r, h);
        const pressureTerm = jMass * (pressure_i + pressure_j) / (2 * density_j);
        fPressureX -= pressureTerm * pressureGrad.x;
        fPressureY -= pressureTerm * pressureGrad.y;
        fPressureZ -= pressureTerm * pressureGrad.z;

        // Viscosity force: μ * ∑ m_j * (v_j - v_i) / ρ_j * ∇²W_viscosity
        const viscLaplacian = viscosityKernelLaplacian(r, h);
        const viscTerm = jMass / density_j * viscLaplacian;
        fViscosityX += viscTerm * (jvx - vx);
        fViscosityY += viscTerm * (jvy - vy);
        fViscosityZ += viscTerm * (jvz - vz);

        // Surface tension (expensive, optional)
        if (enableST) {
          // Color field gradient
          const colorGrad = poly6KernelGradient(dx, dy, dz, r, h);
          const colorTerm = jMass / density_j;
          colorFieldGradX += colorTerm * colorGrad.x;
          colorFieldGradY += colorTerm * colorGrad.y;
          colorFieldGradZ += colorTerm * colorGrad.z;

          // Color field Laplacian (approximation)
          colorFieldLaplacian += colorTerm * poly6Kernel(r, h);
        }
      }

      // Apply viscosity coefficient
      fViscosityX *= viscosity;
      fViscosityY *= viscosity;
      fViscosityZ *= viscosity;

      // Surface tension force: -σ * κ * n = -σ * ∇²c / |∇c| * ∇c / |∇c|
      let fSurfaceX = 0, fSurfaceY = 0, fSurfaceZ = 0;
      if (enableST) {
        const gradMag = Math.sqrt(
          colorFieldGradX * colorFieldGradX +
          colorFieldGradY * colorFieldGradY +
          colorFieldGradZ * colorFieldGradZ
        );

        // Only apply surface tension at fluid surface (where gradient is significant)
        if (gradMag > 0.1) {
          const curvature = -colorFieldLaplacian / gradMag;
          fSurfaceX = surfaceTension * curvature * colorFieldGradX / gradMag;
          fSurfaceY = surfaceTension * curvature * colorFieldGradY / gradMag;
          fSurfaceZ = surfaceTension * curvature * colorFieldGradZ / gradMag;
        }
      }

      // Total force
      this.sphData[i].forceX = fPressureX + fViscosityX + fSurfaceX;
      this.sphData[i].forceY = fPressureY + fViscosityY + fSurfaceY;
      this.sphData[i].forceZ = fPressureZ + fViscosityZ + fSurfaceZ;
    }
  }

  /**
   * Integrate velocities and positions
   */
  private integrate(buffer: Float32Array, dt: number): void {
    const gravity = this.config.gravity;

    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = buffer[offset + 7];
      const age = buffer[offset + 6];

      if (lifetime <= 0 || age >= lifetime) continue;

      const density = this.sphData[i].density;
      if (density < 0.0001) continue;

      const mass = Math.max(buffer[offset + 8], 0.1);

      // Acceleration = Force / mass + gravity
      // SPH forces are per-unit-volume, so divide by density
      const ax = this.sphData[i].forceX / density + gravity.x;
      const ay = this.sphData[i].forceY / density + gravity.y;
      const az = this.sphData[i].forceZ / density + gravity.z;

      // Update velocity
      buffer[offset + 3] += ax * dt;
      buffer[offset + 4] += ay * dt;
      buffer[offset + 5] += az * dt;

      // Update position
      buffer[offset + 0] += buffer[offset + 3] * dt;
      buffer[offset + 1] += buffer[offset + 4] * dt;
      buffer[offset + 2] += buffer[offset + 5] * dt;
    }
  }

  // ============================================================================
  // ACCESSORS
  // ============================================================================

  /**
   * Get density at a particle (useful for coloring)
   */
  getDensity(particleIndex: number): number {
    if (particleIndex < 0 || particleIndex >= this.maxParticles) return 0;
    return this.sphData[particleIndex].density;
  }

  /**
   * Get pressure at a particle
   */
  getPressure(particleIndex: number): number {
    if (particleIndex < 0 || particleIndex >= this.maxParticles) return 0;
    return this.sphData[particleIndex].pressure;
  }

  /**
   * Update configuration
   */
  updateConfig(config: Partial<SPHConfig>): void {
    Object.assign(this.config, config);
  }

  /**
   * Get current configuration
   */
  getConfig(): SPHConfig {
    return { ...this.config };
  }

  /**
   * Preset: Water
   */
  static waterPreset(): Partial<SPHConfig> {
    return {
      smoothingRadius: 40,
      restDensity: 1000,
      gasConstant: 3000,
      viscosity: 100,
      surfaceTension: 0.0728,
      enableSurfaceTension: true,
      gravity: { x: 0, y: -980, z: 0 },
    };
  }

  /**
   * Preset: Honey (high viscosity)
   */
  static honeyPreset(): Partial<SPHConfig> {
    return {
      smoothingRadius: 50,
      restDensity: 1400,
      gasConstant: 2000,
      viscosity: 5000, // Much higher viscosity
      surfaceTension: 0.05,
      enableSurfaceTension: true,
      gravity: { x: 0, y: -500, z: 0 }, // Slower fall
    };
  }

  /**
   * Preset: Lava (very high viscosity, slow)
   */
  static lavaPreset(): Partial<SPHConfig> {
    return {
      smoothingRadius: 60,
      restDensity: 3000,
      gasConstant: 1500,
      viscosity: 20000,
      surfaceTension: 0.1,
      enableSurfaceTension: false, // Too expensive for this use case
      gravity: { x: 0, y: -200, z: 0 },
    };
  }

  /**
   * Preset: Gas/Smoke (low density, low viscosity)
   */
  static gasPreset(): Partial<SPHConfig> {
    return {
      smoothingRadius: 80,
      restDensity: 1.2, // Air density
      gasConstant: 50,
      viscosity: 2,
      surfaceTension: 0,
      enableSurfaceTension: false,
      gravity: { x: 0, y: 100, z: 0 }, // Rises!
    };
  }
}
