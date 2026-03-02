/**
 * Particle Force Calculator
 *
 * Calculates forces from force fields on particles.
 * Supports: gravity, point attractors, vortex, turbulence,
 * drag, wind, lorenz attractor, and more.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import * as THREE from "three";
import type { ForceFieldConfig } from "./types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // force // calculation
// ════════════════════════════════════════════════════════════════════════════

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
      // Type proof: direction.x ∈ number | undefined → number
      const gravityDirX = field.direction !== undefined && typeof field.direction === "object" && field.direction !== null && "x" in field.direction && isFiniteNumber(field.direction.x)
        ? field.direction.x
        : 0;
      // Type proof: direction.y ∈ number | undefined → number
      const gravityDirY = field.direction !== undefined && typeof field.direction === "object" && field.direction !== null && "y" in field.direction && isFiniteNumber(field.direction.y)
        ? field.direction.y
        : 1;
      // Type proof: direction.z ∈ ℝ ∪ {undefined} → ℝ
      const gravityDirZ = field.direction !== undefined && typeof field.direction === "object" && field.direction !== null && "z" in field.direction && isFiniteNumber(field.direction.z)
        ? field.direction.z
        : 0;
      force.set(
        gravityDirX * strength,
        gravityDirY * strength,
        gravityDirZ * strength,
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
        // Type proof: vortexAxis.x ∈ number | undefined → number
        const vortexAxisX = field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && field.vortexAxis !== null && "x" in field.vortexAxis && isFiniteNumber(field.vortexAxis.x)
          ? field.vortexAxis.x
          : 0;
        // Type proof: vortexAxis.y ∈ number | undefined → number
        const vortexAxisY = field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && field.vortexAxis !== null && "y" in field.vortexAxis && isFiniteNumber(field.vortexAxis.y)
          ? field.vortexAxis.y
          : 0;
        // Type proof: vortexAxis.z ∈ ℝ ∪ {undefined} → ℝ
        const vortexAxisZ = field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && field.vortexAxis !== null && "z" in field.vortexAxis && isFiniteNumber(field.vortexAxis.z)
          ? field.vortexAxis.z
          : 1;
        const axis = new THREE.Vector3(vortexAxisX, vortexAxisY, vortexAxisZ).normalize();
        const toParticle = new THREE.Vector3(dx, dy, dz);
        const tangent = new THREE.Vector3()
          .crossVectors(axis, toParticle)
          .normalize();
        // Type proof: inwardForce ∈ number | undefined → number
        const inwardForce = isFiniteNumber(field.inwardForce)
          ? field.inwardForce
          : 0;
        const inward = toParticle
          .normalize()
          .multiplyScalar(-inwardForce);
        force.copy(tangent).multiplyScalar(strength).add(inward);
      }
      break;

    case "turbulence": {
      // Type proof: noiseScale ∈ number | undefined → number
      const rawScale = isFiniteNumber(field.noiseScale) && field.noiseScale > 0
        ? field.noiseScale
        : 0.01;
      const scale = Number.isFinite(rawScale) ? rawScale : 0.01;
      // Type proof: noiseSpeed ∈ number | undefined → number
      const rawSpeed = isFiniteNumber(field.noiseSpeed) && field.noiseSpeed >= 0
        ? field.noiseSpeed
        : 0.5;
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
        // Type proof: linearDrag ∈ number | undefined → number
        const rawLinearDrag = isFiniteNumber(field.linearDrag) && field.linearDrag >= 0
          ? field.linearDrag
          : 0.1;
        const linearDrag = Number.isFinite(rawLinearDrag) ? rawLinearDrag : 0.1;
        // Type proof: quadraticDrag ∈ number | undefined → number
        const rawQuadDrag = isFiniteNumber(field.quadraticDrag) && field.quadraticDrag >= 0
          ? field.quadraticDrag
          : 0.01;
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
      // Type proof: windDirection.x ∈ number | undefined → number
      const windDirX = field.windDirection !== undefined && typeof field.windDirection === "object" && field.windDirection !== null && "x" in field.windDirection && isFiniteNumber(field.windDirection.x)
        ? field.windDirection.x
        : 1;
      // Type proof: windDirection.y ∈ number | undefined → number
      const windDirY = field.windDirection !== undefined && typeof field.windDirection === "object" && field.windDirection !== null && "y" in field.windDirection && isFiniteNumber(field.windDirection.y)
        ? field.windDirection.y
        : 0;
      // Type proof: windDirection.z ∈ ℝ ∪ {undefined} → ℝ
      const windDirZ = field.windDirection !== undefined && typeof field.windDirection === "object" && field.windDirection !== null && "z" in field.windDirection && isFiniteNumber(field.windDirection.z)
        ? field.windDirection.z
        : 0;
      const windDir = new THREE.Vector3(windDirX, windDirY, windDirZ).normalize();
      // Type proof: gustFrequency ∈ number | undefined → number
      const gustFrequency = isFiniteNumber(field.gustFrequency) && field.gustFrequency >= 0
        ? field.gustFrequency
        : 0.5;
      // Type proof: gustStrength ∈ number | undefined → number
      const gustStrength = isFiniteNumber(field.gustStrength)
        ? field.gustStrength
        : 0;
      const gust = Math.sin(simulationTime * gustFrequency) * gustStrength;
      force.copy(windDir).multiplyScalar(strength + gust);
      break;
    }

    case "lorenz": {
      // Lorenz strange attractor - validate to prevent NaN
      // Type proof: lorenzSigma ∈ number | undefined → number
      const rawSigma = isFiniteNumber(field.lorenzSigma) && field.lorenzSigma > 0
        ? field.lorenzSigma
        : 10;
      const sigma = Number.isFinite(rawSigma) ? rawSigma : 10;
      // Type proof: lorenzRho ∈ number | undefined → number
      const rawRho = isFiniteNumber(field.lorenzRho) && field.lorenzRho > 0
        ? field.lorenzRho
        : 28;
      const rho = Number.isFinite(rawRho) ? rawRho : 28;
      // Type proof: lorenzBeta ∈ number | undefined → number
      const rawBeta = isFiniteNumber(field.lorenzBeta) && field.lorenzBeta > 0
        ? field.lorenzBeta
        : 2.667;
      const beta = Number.isFinite(rawBeta) ? rawBeta : 2.667;
      force
        .set(sigma * (dy - dx), dx * (rho - dz) - dy, dx * dy - beta * dz)
        .multiplyScalar(strength * 0.01);
      break;
    }

    case "curl": {
      // Curl noise - divergence-free flow field
      // Type proof: noiseScale ∈ number | undefined → number
      const rawScale = isFiniteNumber(field.noiseScale) && field.noiseScale > 0
        ? field.noiseScale
        : 0.01;
      const scale = Number.isFinite(rawScale) ? rawScale : 0.01;
      // Type proof: noiseSpeed ∈ number | undefined → number
      const rawSpeed = isFiniteNumber(field.noiseSpeed) && field.noiseSpeed >= 0
        ? field.noiseSpeed
        : 0.5;
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
      // Type proof: vortexAxis.x ∈ number | undefined → number
      const magneticAxisX = field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && field.vortexAxis !== null && "x" in field.vortexAxis && isFiniteNumber(field.vortexAxis.x)
        ? field.vortexAxis.x
        : 0;
      // Type proof: vortexAxis.y ∈ number | undefined → number
      const magneticAxisY = field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && field.vortexAxis !== null && "y" in field.vortexAxis && isFiniteNumber(field.vortexAxis.y)
        ? field.vortexAxis.y
        : 1;
      // Type proof: vortexAxis.z ∈ ℝ ∪ {undefined} → ℝ
      const magneticAxisZ = field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && field.vortexAxis !== null && "z" in field.vortexAxis && isFiniteNumber(field.vortexAxis.z)
        ? field.vortexAxis.z
        : 0;
      const B = new THREE.Vector3(magneticAxisX, magneticAxisY, magneticAxisZ).multiplyScalar(strength);
      const v = new THREE.Vector3(vx, vy, vz);
      force.crossVectors(v, B);
      break;
    }

    case "orbit": {
      // Centripetal force for orbital motion
      if (dist > 0.001) {
        // Type proof: pathRadius ∈ number | undefined → number
        const orbitRadius = isFiniteNumber(field.pathRadius) && field.pathRadius > 0
          ? field.pathRadius
          : 100;
        // Force toward orbit center, proportional to deviation from orbit radius
        const deviation = dist - orbitRadius;
        const centripetal = new THREE.Vector3(-dx, -dy, -dz).normalize();
        force.copy(centripetal).multiplyScalar(deviation * strength * 0.1);

        // Add tangential component for orbit
        // Type proof: vortexAxis.x ∈ number | undefined → number
        const orbitAxisX = field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && field.vortexAxis !== null && "x" in field.vortexAxis && isFiniteNumber(field.vortexAxis.x)
          ? field.vortexAxis.x
          : 0;
        // Type proof: vortexAxis.y ∈ number | undefined → number
        const orbitAxisY = field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && field.vortexAxis !== null && "y" in field.vortexAxis && isFiniteNumber(field.vortexAxis.y)
          ? field.vortexAxis.y
          : 1;
        // Type proof: vortexAxis.z ∈ ℝ ∪ {undefined} → ℝ
        const orbitAxisZ = field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && field.vortexAxis !== null && "z" in field.vortexAxis && isFiniteNumber(field.vortexAxis.z)
          ? field.vortexAxis.z
          : 0;
        const axis = new THREE.Vector3(orbitAxisX, orbitAxisY, orbitAxisZ).normalize();
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

// ════════════════════════════════════════════════════════════════════════════
//                                         // force // field // type // indices
// ════════════════════════════════════════════════════════════════════════════

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
