/**
 * Particle Collision System
 *
 * Handles collision detection and response for particles.
 * Supports boundary collisions and particle-particle collisions.
 * Uses shared SpatialHashGrid for efficient O(n) neighbor queries.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import { PARTICLE_STRIDE, type ISpatialHash } from "./types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

export type BoundsBehavior =
  | "none"
  | "kill"
  | "bounce"
  | "wrap"
  | "clamp"
  | "stick";

/**
 * Collision plane definition (infinite plane for floor/wall/ceiling)
 */
export interface CollisionPlane {
  /** Unique identifier */
  id: string;
  /** Whether this plane is active */
  enabled: boolean;
  /** Point on the plane */
  point: { x: number; y: number; z: number };
  /** Normal vector (direction plane faces, points toward particle space) */
  normal: { x: number; y: number; z: number };
  /** Bounciness coefficient (0 = no bounce, 1 = perfect bounce) */
  bounciness: number;
  /** Friction coefficient (0 = no friction, 1 = full stop on tangent) */
  friction: number;
}

export interface CollisionConfig {
  enabled: boolean;
  particleCollision: boolean;
  particleRadius: number;
  bounciness: number;
  friction: number;
  /** Collision response strength (0-1) */
  collisionResponse: number;
  /** Damping on bounce (0-1) */
  bounceDamping: number;
  bounds?: {
    min: { x: number; y: number; z: number };
    max: { x: number; y: number; z: number };
  };
  boundsBehavior: BoundsBehavior;
  /** Collision planes (floor, walls, ceiling) */
  planes?: CollisionPlane[];
}

// ════════════════════════════════════════════════════════════════════════════
//                                  // particle // collision // system // class
// ════════════════════════════════════════════════════════════════════════════

export class ParticleCollisionSystem {
  private readonly maxParticles: number;
  private config: CollisionConfig;

  // Reference to shared spatial hash (set externally)
  private spatialHash: ISpatialHash | null = null;

  constructor(maxParticles: number, config: Partial<CollisionConfig> = {}) {
    // Validate maxParticles to prevent infinite loop
    this.maxParticles = Number.isFinite(maxParticles) && maxParticles > 0
      ? Math.min(Math.floor(maxParticles), 10_000_000)
      : 10000;
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const enabled = (typeof config.enabled === "boolean") ? config.enabled : true;
    const particleCollision = (typeof config.particleCollision === "boolean") ? config.particleCollision : false;
    const particleRadius = (typeof config.particleRadius === "number" && Number.isFinite(config.particleRadius) && config.particleRadius > 0) ? config.particleRadius : 5;
    const bounciness = (typeof config.bounciness === "number" && Number.isFinite(config.bounciness) && config.bounciness >= 0) ? config.bounciness : 0.5;
    const friction = (typeof config.friction === "number" && Number.isFinite(config.friction) && config.friction >= 0) ? config.friction : 0.1;
    const collisionResponse = (typeof config.collisionResponse === "number" && Number.isFinite(config.collisionResponse) && config.collisionResponse >= 0) ? config.collisionResponse : 0.5;
    const bounceDamping = (typeof config.bounceDamping === "number" && Number.isFinite(config.bounceDamping) && config.bounceDamping >= 0) ? config.bounceDamping : 0.8;
    const boundsBehavior = (typeof config.boundsBehavior === "string" && config.boundsBehavior.length > 0) ? config.boundsBehavior : "none";
    const planes = (Array.isArray(config.planes)) ? config.planes : [];  // Must explicitly copy - collision planes wouldn't work otherwise
    this.config = {
      enabled,
      particleCollision,
      particleRadius,
      bounciness,
      friction,
      collisionResponse,
      bounceDamping,
      bounds: config.bounds,
      boundsBehavior,
      planes,
    };
  }

  /**
   * Set the shared spatial hash grid reference
   * This should be called once during initialization
   */
  setSpatialHash(hash: ISpatialHash): void {
    this.spatialHash = hash;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                    // update
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Apply collision detection and response
   * @param particleBuffer - The current particle data buffer (modified in place)
   */
  update(particleBuffer: Float32Array): void {
    if (!this.config.enabled) return;

    // Apply boundary collisions
    if (this.config.bounds && this.config.boundsBehavior !== "none") {
      this.applyBoundaryCollisions(particleBuffer);
    }

    // Apply collision plane collisions (floor/walls)
    if (this.config.planes && this.config.planes.length > 0) {
      this.applyPlaneCollisions(particleBuffer);
    }

    // Apply particle-particle collisions (expensive, uses spatial hash)
    if (this.config.particleCollision) {
      this.applyParticleCollisions(particleBuffer);
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                    // boundary // collisions
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Apply boundary collision response
   */
  private applyBoundaryCollisions(buffer: Float32Array): void {
    if (!this.config.bounds) return;

    const { min, max } = this.config.bounds;
    // Validate bounciness to prevent NaN propagation
    const bounciness = Number.isFinite(this.config.bounciness) ? this.config.bounciness : 0.5;
    const behavior = this.config.boundsBehavior;
    
    // Calculate bounds dimensions for wrap modulo - guard against zero
    const dimX = Math.max(1, max.x - min.x);
    const dimY = Math.max(1, max.y - min.y);
    const dimZ = Math.max(1, max.z - min.z);

    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = buffer[offset + 7];
      const age = buffer[offset + 6];

      if (lifetime <= 0 || age >= lifetime) continue;

      let px = buffer[offset + 0];
      let py = buffer[offset + 1];
      let pz = buffer[offset + 2];
      let vx = buffer[offset + 3];
      let vy = buffer[offset + 4];
      let vz = buffer[offset + 5];

      let collided = false;

      // X boundaries
      if (px < min.x) {
        if (behavior === "bounce") {
          px = min.x + (min.x - px);
          vx = -vx * bounciness;
          // Clamp to ensure we don't overshoot to the other side
          if (px > max.x) px = max.x;
        } else if (behavior === "wrap") {
          px = max.x - (min.x - px);
          // Wrap can overshoot, use modulo-like behavior (dimX guaranteed >= 1)
          if (px > max.x) px = min.x + ((px - min.x) % dimX);
        } else if (behavior === "kill") {
          buffer[offset + 6] = buffer[offset + 7]; // Set age = lifetime (kill)
          continue;
        } else if (behavior === "clamp") {
          px = min.x;
          vx = 0; // Stop X velocity but keep other motion
        } else if (behavior === "stick") {
          px = min.x;
          vx = 0;
          vy = 0;
          vz = 0; // Stop all motion when stuck
        }
        collided = true;
      } else if (px > max.x) {
        if (behavior === "bounce") {
          px = max.x - (px - max.x);
          vx = -vx * bounciness;
          // Clamp to ensure we don't overshoot to the other side
          if (px < min.x) px = min.x;
        } else if (behavior === "wrap") {
          px = min.x + (px - max.x);
          // Wrap can overshoot, use modulo-like behavior (dimX guaranteed >= 1)
          if (px < min.x) px = max.x - ((max.x - px) % dimX);
        } else if (behavior === "kill") {
          buffer[offset + 6] = buffer[offset + 7];
          continue;
        } else if (behavior === "clamp") {
          px = max.x;
          vx = 0; // Stop X velocity but keep other motion
        } else if (behavior === "stick") {
          px = max.x;
          vx = 0;
          vy = 0;
          vz = 0;
        }
        collided = true;
      }

      // Y boundaries (includes floor/ceiling)
      if (py < min.y) {
        if (behavior === "bounce") {
          py = min.y + (min.y - py);
          vy = -vy * bounciness;
          if (py > max.y) py = max.y;
        } else if (behavior === "wrap") {
          py = max.y - (min.y - py);
          if (py > max.y) py = min.y + ((py - min.y) % dimY);
        } else if (behavior === "kill") {
          buffer[offset + 6] = buffer[offset + 7];
          continue;
        } else if (behavior === "clamp") {
          py = min.y;
          vy = 0; // Stop Y velocity but keep other motion
        } else if (behavior === "stick") {
          py = min.y;
          vx = 0;
          vy = 0;
          vz = 0;
        }
        collided = true;
      } else if (py > max.y) {
        if (behavior === "bounce") {
          py = max.y - (py - max.y);
          vy = -vy * bounciness;
          if (py < min.y) py = min.y;
        } else if (behavior === "wrap") {
          py = min.y + (py - max.y);
          if (py < min.y) py = max.y - ((max.y - py) % dimY);
        } else if (behavior === "kill") {
          buffer[offset + 6] = buffer[offset + 7];
          continue;
        } else if (behavior === "clamp") {
          py = max.y;
          vy = 0; // Stop Y velocity but keep other motion
        } else if (behavior === "stick") {
          py = max.y;
          vx = 0;
          vy = 0;
          vz = 0;
        }
        collided = true;
      }

      // Z boundaries
      if (pz < min.z) {
        if (behavior === "bounce") {
          pz = min.z + (min.z - pz);
          vz = -vz * bounciness;
          if (pz > max.z) pz = max.z;
        } else if (behavior === "wrap") {
          pz = max.z - (min.z - pz);
          if (pz > max.z) pz = min.z + ((pz - min.z) % dimZ);
        } else if (behavior === "kill") {
          buffer[offset + 6] = buffer[offset + 7];
          continue;
        } else if (behavior === "clamp") {
          pz = min.z;
          vz = 0; // Stop Z velocity but keep other motion
        } else if (behavior === "stick") {
          pz = min.z;
          vx = 0;
          vy = 0;
          vz = 0;
        }
        collided = true;
      } else if (pz > max.z) {
        if (behavior === "bounce") {
          pz = max.z - (pz - max.z);
          vz = -vz * bounciness;
          if (pz < min.z) pz = min.z;
        } else if (behavior === "wrap") {
          pz = min.z + (pz - max.z);
          if (pz < min.z) pz = max.z - ((max.z - pz) % dimZ);
        } else if (behavior === "kill") {
          buffer[offset + 6] = buffer[offset + 7];
          continue;
        } else if (behavior === "clamp") {
          pz = max.z;
          vz = 0; // Stop Z velocity but keep other motion
        } else if (behavior === "stick") {
          pz = max.z;
          vx = 0;
          vy = 0;
          vz = 0;
        }
        collided = true;
      }

      if (collided) {
        buffer[offset + 0] = px;
        buffer[offset + 1] = py;
        buffer[offset + 2] = pz;
        buffer[offset + 3] = vx;
        buffer[offset + 4] = vy;
        buffer[offset + 5] = vz;
      }
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // plane // collisions
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Apply collision response for infinite planes
   * Planes are defined by a point and normal vector
   */
  private applyPlaneCollisions(buffer: Float32Array): void {
    const planes = this.config.planes;
    if (!planes || planes.length === 0) return;

    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = buffer[offset + 7];
      const age = buffer[offset + 6];

      // Skip dead particles
      if (lifetime <= 0 || age >= lifetime) continue;

      let px = buffer[offset + 0];
      let py = buffer[offset + 1];
      let pz = buffer[offset + 2];
      let vx = buffer[offset + 3];
      let vy = buffer[offset + 4];
      let vz = buffer[offset + 5];
      let collided = false;

      for (const plane of planes) {
        if (!plane.enabled) continue;

        // Calculate signed distance from particle to plane
        // d = (p - plane.point) · plane.normal
        const dpx = px - plane.point.x;
        const dpy = py - plane.point.y;
        const dpz = pz - plane.point.z;

        // Normalize normal (in case it's not already)
        const nx = plane.normal.x;
        const ny = plane.normal.y;
        const nz = plane.normal.z;
        const nLen = Math.sqrt(nx * nx + ny * ny + nz * nz);
        if (nLen < 0.001) continue;  // Skip degenerate normals

        const normalX = nx / nLen;
        const normalY = ny / nLen;
        const normalZ = nz / nLen;

        const dist = dpx * normalX + dpy * normalY + dpz * normalZ;

        // Check if particle has crossed the plane (dist < 0 means behind plane)
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        const particleRadius = (typeof this.config.particleRadius === "number" && Number.isFinite(this.config.particleRadius) && this.config.particleRadius > 0) ? this.config.particleRadius : 5;
        if (dist < particleRadius) {
          // Particle is touching or behind plane
          const bounciness = Number.isFinite(plane.bounciness) ? plane.bounciness : 0.5;
          const friction = Number.isFinite(plane.friction) ? plane.friction : 0.1;

          // Calculate velocity component normal to plane
          const vDotN = vx * normalX + vy * normalY + vz * normalZ;

          // Only respond if particle is moving toward the plane
          if (vDotN < 0) {
            // Reflect velocity: v' = v - (1 + bounciness) * (v · n) * n
            const factor = (1 + bounciness) * vDotN;
            vx -= factor * normalX;
            vy -= factor * normalY;
            vz -= factor * normalZ;

            // Apply friction to tangential velocity
            if (friction > 0) {
              // Tangent velocity = total - normal component
              const tanVx = vx - (vx * normalX) * normalX;
              const tanVy = vy - (vy * normalY) * normalY;
              const tanVz = vz - (vz * normalZ) * normalZ;
              
              vx -= tanVx * friction;
              vy -= tanVy * friction;
              vz -= tanVz * friction;
            }

            // Push particle out of plane
            const penetration = particleRadius - dist;
            px += normalX * penetration;
            py += normalY * penetration;
            pz += normalZ * penetration;

            collided = true;
          }
        }
      }

      if (collided) {
        buffer[offset + 0] = px;
        buffer[offset + 1] = py;
        buffer[offset + 2] = pz;
        buffer[offset + 3] = vx;
        buffer[offset + 4] = vy;
        buffer[offset + 5] = vz;
      }
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                  // particle
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Apply particle-particle collision response
   * Uses shared spatial hash for efficiency
   */
  private applyParticleCollisions(buffer: Float32Array): void {
    if (!this.spatialHash) return;

    // Validate radius to prevent NaN/Infinity breaking collision detection
    const radius = Number.isFinite(this.config.particleRadius) && this.config.particleRadius > 0
      ? this.config.particleRadius
      : 5;
    const radiusSq = radius * radius * 4; // 2*radius squared for collision detection
    const bounciness = Number.isFinite(this.config.bounciness) ? this.config.bounciness : 0.5;

    // Check collisions using shared spatial hash
    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = buffer[offset + 7];
      const age = buffer[offset + 6];

      if (lifetime <= 0 || age >= lifetime) continue;

      const px = buffer[offset + 0];
      const py = buffer[offset + 1];
      const pz = buffer[offset + 2];
      let vx = buffer[offset + 3];
      let vy = buffer[offset + 4];
      let vz = buffer[offset + 5];
      const mass1 = buffer[offset + 8];

      // Use shared spatial hash for neighbor queries
      for (const j of this.spatialHash.getNeighbors(px, py, pz)) {
        if (j <= i) continue; // Avoid duplicate checks

        const jOffset = j * PARTICLE_STRIDE;
        const jx = buffer[jOffset + 0];
        const jy = buffer[jOffset + 1];
        const jz = buffer[jOffset + 2];

        const dx = jx - px;
        const dy = jy - py;
        const dz = jz - pz;
        const distSq = dx * dx + dy * dy + dz * dz;

        if (distSq < radiusSq && distSq > 0.001) {
          // Collision detected - simple elastic collision response
          const dist = Math.sqrt(distSq);
          const nx = dx / dist;
          const ny = dy / dist;
          const nz = dz / dist;

          let jvx = buffer[jOffset + 3];
          let jvy = buffer[jOffset + 4];
          let jvz = buffer[jOffset + 5];
          const mass2 = buffer[jOffset + 8];

          // Relative velocity
          const dvx = vx - jvx;
          const dvy = vy - jvy;
          const dvz = vz - jvz;
          const dvn = dvx * nx + dvy * ny + dvz * nz;

          // Only resolve if particles are approaching
          if (dvn > 0) continue;

          // Impulse magnitude - guard against zero/NaN mass
          const safeMass1 = Number.isFinite(mass1) && mass1 > 0 ? mass1 : 1;
          const safeMass2 = Number.isFinite(mass2) && mass2 > 0 ? mass2 : 1;
          const totalMass = safeMass1 + safeMass2;
          const impulse = (-(1 + bounciness) * dvn) / totalMass;

          // Apply impulse using validated masses
          vx += impulse * safeMass2 * nx;
          vy += impulse * safeMass2 * ny;
          vz += impulse * safeMass2 * nz;

          jvx -= impulse * safeMass1 * nx;
          jvy -= impulse * safeMass1 * ny;
          jvz -= impulse * safeMass1 * nz;

          buffer[jOffset + 3] = jvx;
          buffer[jOffset + 4] = jvy;
          buffer[jOffset + 5] = jvz;

          // Separate particles to prevent overlap
          const overlap = (radius * 2 - dist) / 2;
          buffer[offset + 0] -= nx * overlap;
          buffer[offset + 1] -= ny * overlap;
          buffer[offset + 2] -= nz * overlap;
          buffer[jOffset + 0] += nx * overlap;
          buffer[jOffset + 1] += ny * overlap;
          buffer[jOffset + 2] += nz * overlap;
        }
      }

      buffer[offset + 3] = vx;
      buffer[offset + 4] = vy;
      buffer[offset + 5] = vz;
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                 // accessors
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Check if collision system is enabled
   */
  isEnabled(): boolean {
    return this.config.enabled;
  }

  /**
   * Enable or disable collisions
   */
  setEnabled(enabled: boolean): void {
    this.config.enabled = enabled;
  }

  /**
   * Update collision configuration
   */
  updateConfig(config: Partial<CollisionConfig>): void {
    Object.assign(this.config, config);
  }

  /**
   * Get current configuration
   */
  getConfig(): CollisionConfig {
    return { ...this.config };
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                          // collision // plane // management
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Add a collision plane (floor, wall, ceiling)
   */
  addPlane(plane: CollisionPlane): void {
    if (!this.config.planes) {
      this.config.planes = [];
    }
    // Remove existing plane with same ID
    this.config.planes = this.config.planes.filter(p => p.id !== plane.id);
    this.config.planes.push(plane);
  }

  /**
   * Remove a collision plane by ID
   */
  removePlane(id: string): void {
    if (!this.config.planes) return;
    this.config.planes = this.config.planes.filter(p => p.id !== id);
  }

  /**
   * Create a floor plane (horizontal at Y position)
   */
  static createFloorPlane(id: string, y: number, bounciness = 0.5, friction = 0.1): CollisionPlane {
    return {
      id,
      enabled: true,
      point: { x: 0, y, z: 0 },
      normal: { x: 0, y: 1, z: 0 },  // Points up
      bounciness,
      friction,
    };
  }

  /**
   * Create a ceiling plane (horizontal at Y position)
   */
  static createCeilingPlane(id: string, y: number, bounciness = 0.5, friction = 0.1): CollisionPlane {
    return {
      id,
      enabled: true,
      point: { x: 0, y, z: 0 },
      normal: { x: 0, y: -1, z: 0 },  // Points down
      bounciness,
      friction,
    };
  }

  /**
   * Create a wall plane (vertical)
   */
  static createWallPlane(
    id: string,
    position: { x: number; y: number; z: number },
    normal: { x: number; y: number; z: number },
    bounciness = 0.5,
    friction = 0.1
  ): CollisionPlane {
    return {
      id,
      enabled: true,
      point: position,
      normal,
      bounciness,
      friction,
    };
  }

  /**
   * Get all collision planes
   * Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
   */
  getPlanes(): CollisionPlane[] {
    const planes = (Array.isArray(this.config.planes)) ? this.config.planes : [];
    return [...planes];
  }
}
