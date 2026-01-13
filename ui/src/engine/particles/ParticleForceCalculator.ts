/**
 * Particle Force Calculator
 *
 * Calculates forces from force fields on particles.
 * Supports: gravity, point attractors, vortex, turbulence,
 * drag, wind, lorenz attractor, and more.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import * as THREE from "three";
import type { ForceFieldConfig } from "./types";

// ============================================================================
// FORCE CALCULATION
// ============================================================================

/**
 * Calculate force from a force field on a particle
 * @param field - Force field configuration
 * @param px - Particle X position
 * @param py - Particle Y position
 * @param pz - Particle Z position
 * @param vx - Particle X velocity
 * @param vy - Particle Y velocity
 * @param vz - Particle Z velocity
 * @param mass - Particle mass
 * @param simulationTime - Current simulation time (for time-varying forces)
 */
export function calculateForceField(
  field: ForceFieldConfig,
  px: number,
  py: number,
  pz: number,
  vx: number,
  vy: number,
  vz: number,
  mass: number,
  simulationTime: number = 0,
): THREE.Vector3 {
  const force = new THREE.Vector3();

  // Calculate distance and falloff
  const dx = px - field.position.x;
  const dy = py - field.position.y;
  const dz = pz - field.position.z;
  const dist = Math.sqrt(dx * dx + dy * dy + dz * dz);

  let falloff = 1;
  if (dist > field.falloffStart) {
    // Guard against division by zero when falloffEnd equals falloffStart
    const falloffRange = field.falloffEnd - field.falloffStart;
    const t =
      falloffRange > 0
        ? Math.min((dist - field.falloffStart) / falloffRange, 1)
        : 1; // If no range, full falloff
    switch (field.falloffType) {
      case "linear":
        falloff = 1 - t;
        break;
      case "quadratic":
        falloff = 1 - t * t;
        break;
      case "exponential":
        falloff = Math.exp(-t * 3);
        break;
      case "smoothstep":
        falloff = 1 - (3 * t * t - 2 * t * t * t);
        break;
    }
  }

  // Validate strength to prevent NaN/Infinity propagation
  const rawStrength = field.strength * falloff;
  const strength = Number.isFinite(rawStrength) ? rawStrength : 0;

  switch (field.type) {
    case "gravity":
      force.set(
        (field.direction?.x ?? 0) * strength,
        (field.direction?.y ?? 1) * strength,
        (field.direction?.z ?? 0) * strength,
      );
      break;

    case "point":
      if (dist > 0.001) {
        const dir = new THREE.Vector3(-dx, -dy, -dz).normalize();
        // Guard against zero/negative mass to prevent Infinity/NaN
        const safeMass = Math.max(mass, 0.001);
        force.copy(dir).multiplyScalar(strength / safeMass);
      }
      break;

    case "vortex":
      if (dist > 0.001) {
        const axis = new THREE.Vector3(
          field.vortexAxis?.x ?? 0,
          field.vortexAxis?.y ?? 0,
          field.vortexAxis?.z ?? 1,
        ).normalize();
        const toParticle = new THREE.Vector3(dx, dy, dz);
        const tangent = new THREE.Vector3()
          .crossVectors(axis, toParticle)
          .normalize();
        const inward = toParticle
          .normalize()
          .multiplyScalar(-(field.inwardForce ?? 0));
        force.copy(tangent).multiplyScalar(strength).add(inward);
      }
      break;

    case "turbulence": {
      const rawScale = field.noiseScale ?? 0.01;
      const scale = Number.isFinite(rawScale) ? rawScale : 0.01;
      const rawSpeed = field.noiseSpeed ?? 0.5;
      const speed = Number.isFinite(rawSpeed) ? rawSpeed : 0.5;
      // Guard against Infinity time causing Math.sin(Infinity) = NaN
      const time = Number.isFinite(simulationTime * speed) ? simulationTime * speed : 0;

      // Simple 3D noise approximation
      const nx =
        Math.sin(px * scale + time) * Math.cos(py * scale * 1.3) * strength;
      const ny =
        Math.sin(py * scale + time * 1.1) *
        Math.cos(pz * scale * 1.2) *
        strength;
      const nz =
        Math.sin(pz * scale + time * 0.9) *
        Math.cos(px * scale * 1.1) *
        strength;
      force.set(nx, ny, nz);
      break;
    }

    case "drag": {
      const speed = Math.sqrt(vx * vx + vy * vy + vz * vz);
      if (speed > 0.001) {
        // Validate drag coefficients to prevent NaN
        const rawLinearDrag = field.linearDrag ?? 0.1;
        const linearDrag = Number.isFinite(rawLinearDrag) ? rawLinearDrag : 0.1;
        const rawQuadDrag = field.quadraticDrag ?? 0.01;
        const quadDrag = Number.isFinite(rawQuadDrag) ? rawQuadDrag : 0.01;
        const dragMag = linearDrag * speed + quadDrag * speed * speed;
        // Drag opposes velocity: F = -c * v_normalized * |v|^n
        // set(-v) then multiply by positive gives force opposing velocity
        force
          .set(-vx, -vy, -vz)
          .normalize()
          .multiplyScalar(dragMag * strength); // Removed double-negative
      }
      break;
    }

    case "wind": {
      const windDir = new THREE.Vector3(
        field.windDirection?.x ?? 1,
        field.windDirection?.y ?? 0,
        field.windDirection?.z ?? 0,
      ).normalize();
      const gust =
        Math.sin(simulationTime * (field.gustFrequency ?? 0.5)) *
        (field.gustStrength ?? 0);
      force.copy(windDir).multiplyScalar(strength + gust);
      break;
    }

    case "lorenz": {
      // Lorenz strange attractor - validate to prevent NaN
      const rawSigma = field.lorenzSigma ?? 10;
      const sigma = Number.isFinite(rawSigma) ? rawSigma : 10;
      const rawRho = field.lorenzRho ?? 28;
      const rho = Number.isFinite(rawRho) ? rawRho : 28;
      const rawBeta = field.lorenzBeta ?? 2.667;
      const beta = Number.isFinite(rawBeta) ? rawBeta : 2.667;
      force
        .set(sigma * (dy - dx), dx * (rho - dz) - dy, dx * dy - beta * dz)
        .multiplyScalar(strength * 0.01);
      break;
    }

    case "curl": {
      // Curl noise - divergence-free flow field
      const rawScale = field.noiseScale ?? 0.01;
      const scale = Number.isFinite(rawScale) ? rawScale : 0.01;
      const rawSpeed = field.noiseSpeed ?? 0.5;
      const speed = Number.isFinite(rawSpeed) ? rawSpeed : 0.5;
      // Guard against Infinity time causing Math.sin(Infinity) = NaN
      const time = Number.isFinite(simulationTime * speed) ? simulationTime * speed : 0;

      // Compute curl of noise field (approximation)
      const eps = 0.01;
      // dF/dy - dF/dz for x component
      const dFdy_z =
        Math.sin((py + eps) * scale + time) -
        Math.sin((py - eps) * scale + time);
      const dFdz_y =
        Math.cos((pz + eps) * scale + time) -
        Math.cos((pz - eps) * scale + time);
      // dF/dz - dF/dx for y component
      const dFdz_x =
        Math.sin((pz + eps) * scale + time) -
        Math.sin((pz - eps) * scale + time);
      const dFdx_z =
        Math.cos((px + eps) * scale + time) -
        Math.cos((px - eps) * scale + time);
      // dF/dx - dF/dy for z component
      const dFdx_y =
        Math.sin((px + eps) * scale + time) -
        Math.sin((px - eps) * scale + time);
      const dFdy_x =
        Math.cos((py + eps) * scale + time) -
        Math.cos((py - eps) * scale + time);

      force.set(
        (dFdy_z - dFdz_y) * strength,
        (dFdz_x - dFdx_z) * strength,
        (dFdx_y - dFdy_x) * strength,
      );
      break;
    }

    case "magnetic": {
      // Lorentz force: F = q(v × B)
      // B field direction is the vortexAxis
      const B = new THREE.Vector3(
        field.vortexAxis?.x ?? 0,
        field.vortexAxis?.y ?? 1,
        field.vortexAxis?.z ?? 0,
      ).multiplyScalar(strength);
      const v = new THREE.Vector3(vx, vy, vz);
      force.crossVectors(v, B);
      break;
    }

    case "orbit": {
      // Centripetal force for orbital motion
      if (dist > 0.001) {
        const orbitRadius = field.pathRadius ?? 100;
        // Force toward orbit center, proportional to deviation from orbit radius
        const deviation = dist - orbitRadius;
        const centripetal = new THREE.Vector3(-dx, -dy, -dz).normalize();
        force.copy(centripetal).multiplyScalar(deviation * strength * 0.1);

        // Add tangential component for orbit
        const axis = new THREE.Vector3(
          field.vortexAxis?.x ?? 0,
          field.vortexAxis?.y ?? 1,
          field.vortexAxis?.z ?? 0,
        ).normalize();
        const tangent = new THREE.Vector3()
          .crossVectors(axis, centripetal)
          .normalize();
        force.addScaledVector(tangent, strength * 0.5);
      }
      break;
    }
  }

  return force;
}

// ============================================================================
// FORCE FIELD TYPE INDICES (for GPU shaders)
// ============================================================================

/**
 * Get numeric index for force field type (for GPU shader)
 */
export function getForceFieldTypeIndex(type: ForceFieldConfig["type"]): number {
  switch (type) {
    case "gravity":
      return 0;
    case "point":
      return 1;
    case "vortex":
      return 2;
    case "turbulence":
      return 3;
    case "drag":
      return 4;
    case "wind":
      return 5;
    case "lorenz":
      return 6;
    case "curl":
      return 7;
    case "magnetic":
      return 8;
    case "orbit":
      return 9;
    case "path":
      return 9; // Alias for orbit
    default:
      return 0;
  }
}

/**
 * Get numeric index for falloff type (for GPU shader)
 */
export function getFalloffTypeIndex(
  type: ForceFieldConfig["falloffType"],
): number {
  switch (type) {
    case "none":
      return 0;
    case "linear":
      return 1;
    case "quadratic":
      return 2;
    case "exponential":
      return 3;
    case "smoothstep":
      return 4;
    default:
      return 0;
  }
}
