/**
 * @module services/physics/PhysicsEngine
 * @description Main physics engine orchestrator for Newton Physics Simulation.
 *
 * Features:
 * - Deterministic simulation with checkpointing for scrubbing
 * - Rigid body dynamics with collision detection
 * - Soft body simulation (Verlet integration)
 * - Cloth and ragdoll systems
 * - Force fields (gravity, wind, attraction, etc.)
 * - Keyframe export for animation baking
 */

import type {
  PhysicsSpaceConfig,
  PhysicsSimulationState,
  RigidBodyConfig,
  RigidBodyState,
  SoftBodyConfig,
  SoftBodyState,
  ClothConfig,
  ClothState,
  RagdollConfig,
  RagdollState,
  JointConfig,
  ForceField,
  ContactInfo,
  PhysicsVec2,
  KeyframeExportOptions,
  ExportedKeyframes,
  DEFAULT_SPACE_CONFIG,
} from '@/types/physics';

import { SeededRandom } from '../particleSystem';

// =============================================================================
// SEEDED RANDOM FOR PHYSICS
// =============================================================================

/**
 * Deterministic random number generator for physics
 */
class PhysicsRandom {
  private state: number;
  private initialSeed: number;

  constructor(seed: number) {
    this.initialSeed = seed;
    this.state = seed;
  }

  reset(): void {
    this.state = this.initialSeed;
  }

  next(): number {
    // Mulberry32 - same as particle system for consistency
    let t = (this.state += 0x6d2b79f5);
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  }

  range(min: number, max: number): number {
    return min + this.next() * (max - min);
  }

  gaussian(): number {
    // Box-Muller transform
    const u1 = this.next();
    const u2 = this.next();
    return Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
  }
}

// =============================================================================
// VECTOR MATH UTILITIES
// =============================================================================

const vec2 = {
  create: (x = 0, y = 0): PhysicsVec2 => ({ x, y }),

  clone: (v: PhysicsVec2): PhysicsVec2 => ({ x: v.x, y: v.y }),

  add: (a: PhysicsVec2, b: PhysicsVec2): PhysicsVec2 => ({
    x: a.x + b.x,
    y: a.y + b.y,
  }),

  sub: (a: PhysicsVec2, b: PhysicsVec2): PhysicsVec2 => ({
    x: a.x - b.x,
    y: a.y - b.y,
  }),

  scale: (v: PhysicsVec2, s: number): PhysicsVec2 => ({
    x: v.x * s,
    y: v.y * s,
  }),

  length: (v: PhysicsVec2): number => Math.sqrt(v.x * v.x + v.y * v.y),

  lengthSq: (v: PhysicsVec2): number => v.x * v.x + v.y * v.y,

  normalize: (v: PhysicsVec2): PhysicsVec2 => {
    const len = vec2.length(v);
    if (len === 0) return { x: 0, y: 0 };
    return { x: v.x / len, y: v.y / len };
  },

  dot: (a: PhysicsVec2, b: PhysicsVec2): number => a.x * b.x + a.y * b.y,

  cross: (a: PhysicsVec2, b: PhysicsVec2): number => a.x * b.y - a.y * b.x,

  perpendicular: (v: PhysicsVec2): PhysicsVec2 => ({ x: -v.y, y: v.x }),

  rotate: (v: PhysicsVec2, angle: number): PhysicsVec2 => {
    const cos = Math.cos(angle);
    const sin = Math.sin(angle);
    return {
      x: v.x * cos - v.y * sin,
      y: v.x * sin + v.y * cos,
    };
  },

  lerp: (a: PhysicsVec2, b: PhysicsVec2, t: number): PhysicsVec2 => ({
    x: a.x + (b.x - a.x) * t,
    y: a.y + (b.y - a.y) * t,
  }),

  distance: (a: PhysicsVec2, b: PhysicsVec2): number => vec2.length(vec2.sub(b, a)),

  distanceSq: (a: PhysicsVec2, b: PhysicsVec2): number => vec2.lengthSq(vec2.sub(b, a)),
};

// =============================================================================
// RIGID BODY SIMULATOR
// =============================================================================

interface InternalRigidBody {
  config: RigidBodyConfig;
  position: PhysicsVec2;
  velocity: PhysicsVec2;
  angle: number;
  angularVelocity: number;
  force: PhysicsVec2;
  torque: number;
  inverseMass: number;
  inverseInertia: number;
  isSleeping: boolean;
  sleepTime: number;
}

class RigidBodySimulator {
  private bodies: Map<string, InternalRigidBody> = new Map();
  private config: PhysicsSpaceConfig;

  constructor(config: PhysicsSpaceConfig) {
    this.config = config;
  }

  addBody(bodyConfig: RigidBodyConfig): void {
    const inverseMass = bodyConfig.type === 'static' || bodyConfig.type === 'dead' ? 0 : 1 / bodyConfig.mass;

    // Calculate moment of inertia if not provided
    let moment = bodyConfig.moment;
    if (!moment && bodyConfig.mass > 0) {
      moment = this.calculateMomentOfInertia(bodyConfig);
    }
    const inverseInertia = bodyConfig.type === 'static' || bodyConfig.type === 'dead' || bodyConfig.fixedRotation ? 0 : 1 / (moment || 1);

    const body: InternalRigidBody = {
      config: bodyConfig,
      position: vec2.clone(bodyConfig.position),
      velocity: vec2.clone(bodyConfig.velocity),
      angle: bodyConfig.angle,
      angularVelocity: bodyConfig.angularVelocity,
      force: vec2.create(),
      torque: 0,
      inverseMass,
      inverseInertia,
      isSleeping: false,
      sleepTime: 0,
    };

    this.bodies.set(bodyConfig.id, body);
  }

  removeBody(id: string): void {
    this.bodies.delete(id);
  }

  getBody(id: string): InternalRigidBody | undefined {
    return this.bodies.get(id);
  }

  getAllBodies(): InternalRigidBody[] {
    return Array.from(this.bodies.values());
  }

  private calculateMomentOfInertia(config: RigidBodyConfig): number {
    const mass = config.mass;
    const shape = config.shape;

    switch (shape.type) {
      case 'circle': {
        const r = shape.radius || 10;
        return (mass * r * r) / 2;
      }
      case 'box': {
        const w = shape.width || 10;
        const h = shape.height || 10;
        return (mass * (w * w + h * h)) / 12;
      }
      case 'capsule': {
        const r = shape.radius || 5;
        const l = shape.length || 20;
        // Approximate as rectangle + semicircles
        const rectMass = mass * l / (l + Math.PI * r);
        const circleMass = mass - rectMass;
        const rectI = (rectMass * (l * l + 4 * r * r)) / 12;
        const circleI = circleMass * r * r / 2;
        return rectI + circleI;
      }
      default:
        // Default approximation
        return mass * 100;
    }
  }

  applyForce(bodyId: string, force: PhysicsVec2, point?: PhysicsVec2): void {
    const body = this.bodies.get(bodyId);
    if (!body || body.inverseMass === 0) return;

    body.force = vec2.add(body.force, force);

    if (point) {
      const r = vec2.sub(point, body.position);
      body.torque += vec2.cross(r, force);
    }
  }

  applyImpulse(bodyId: string, impulse: PhysicsVec2, point?: PhysicsVec2): void {
    const body = this.bodies.get(bodyId);
    if (!body || body.inverseMass === 0) return;

    body.velocity = vec2.add(body.velocity, vec2.scale(impulse, body.inverseMass));

    if (point) {
      const r = vec2.sub(point, body.position);
      body.angularVelocity += body.inverseInertia * vec2.cross(r, impulse);
    }

    // Wake up if sleeping
    body.isSleeping = false;
    body.sleepTime = 0;
  }

  integrate(dt: number): void {
    for (const body of this.bodies.values()) {
      if (body.config.type === 'static' || body.config.type === 'dead') continue;
      if (body.isSleeping) continue;

      // Semi-implicit Euler integration
      // Update velocity
      body.velocity = vec2.add(
        body.velocity,
        vec2.scale(body.force, body.inverseMass * dt)
      );
      body.angularVelocity += body.torque * body.inverseInertia * dt;

      // Apply damping
      body.velocity = vec2.scale(body.velocity, 1 - body.config.linearDamping * dt);
      body.angularVelocity *= 1 - body.config.angularDamping * dt;

      // Update position
      body.position = vec2.add(body.position, vec2.scale(body.velocity, dt));
      body.angle += body.angularVelocity * dt;

      // Clear forces
      body.force = vec2.create();
      body.torque = 0;

      // Check for sleep
      if (this.config.sleepEnabled && body.config.canSleep) {
        const speed = vec2.length(body.velocity);
        const angSpeed = Math.abs(body.angularVelocity);
        if (speed < this.config.sleepVelocityThreshold && angSpeed < this.config.sleepVelocityThreshold * 0.1) {
          body.sleepTime += dt;
          if (body.sleepTime > this.config.sleepTimeThreshold) {
            body.isSleeping = true;
            body.velocity = vec2.create();
            body.angularVelocity = 0;
          }
        } else {
          body.sleepTime = 0;
        }
      }
    }
  }

  getState(): RigidBodyState[] {
    const states: RigidBodyState[] = [];
    for (const body of this.bodies.values()) {
      states.push({
        id: body.config.id,
        position: vec2.clone(body.position),
        velocity: vec2.clone(body.velocity),
        angle: body.angle,
        angularVelocity: body.angularVelocity,
        isSleeping: body.isSleeping,
        contacts: [],
      });
    }
    return states;
  }

  loadState(states: RigidBodyState[]): void {
    for (const state of states) {
      const body = this.bodies.get(state.id);
      if (body) {
        body.position = vec2.clone(state.position);
        body.velocity = vec2.clone(state.velocity);
        body.angle = state.angle;
        body.angularVelocity = state.angularVelocity;
        body.isSleeping = state.isSleeping;
      }
    }
  }
}

// =============================================================================
// COLLISION DETECTION
// =============================================================================

interface CollisionPair {
  bodyA: InternalRigidBody;
  bodyB: InternalRigidBody;
  normal: PhysicsVec2;
  depth: number;
  contactPoint: PhysicsVec2;
}

class CollisionDetector {
  detectCollisions(bodies: InternalRigidBody[]): CollisionPair[] {
    const pairs: CollisionPair[] = [];

    // Broad phase - simple N^2 for now (can optimize with spatial hash)
    for (let i = 0; i < bodies.length; i++) {
      for (let j = i + 1; j < bodies.length; j++) {
        const bodyA = bodies[i];
        const bodyB = bodies[j];

        // Skip if both static or either dead
        if (bodyA.inverseMass === 0 && bodyB.inverseMass === 0) continue;
        if (bodyA.config.type === 'dead' || bodyB.config.type === 'dead') continue;
        if (bodyA.config.response === 'none' || bodyB.config.response === 'none') continue;

        // Check collision filter
        if (!this.shouldCollide(bodyA.config.filter, bodyB.config.filter)) continue;

        // Narrow phase - shape-specific detection
        const collision = this.detectShapeCollision(bodyA, bodyB);
        if (collision) {
          pairs.push(collision);
        }
      }
    }

    return pairs;
  }

  private shouldCollide(filterA: { category: number; mask: number; group: number }, filterB: { category: number; mask: number; group: number }): boolean {
    // Group filtering
    if (filterA.group !== 0 && filterA.group === filterB.group) {
      return filterA.group > 0; // Positive = always collide, negative = never
    }

    // Category/mask filtering
    return (filterA.mask & filterB.category) !== 0 && (filterB.mask & filterA.category) !== 0;
  }

  private detectShapeCollision(bodyA: InternalRigidBody, bodyB: InternalRigidBody): CollisionPair | null {
    const shapeA = bodyA.config.shape;
    const shapeB = bodyB.config.shape;

    // Circle vs Circle
    if (shapeA.type === 'circle' && shapeB.type === 'circle') {
      return this.circleVsCircle(bodyA, bodyB);
    }

    // Circle vs Box
    if (shapeA.type === 'circle' && shapeB.type === 'box') {
      return this.circleVsBox(bodyA, bodyB);
    }
    if (shapeA.type === 'box' && shapeB.type === 'circle') {
      const result = this.circleVsBox(bodyB, bodyA);
      if (result) {
        // Swap bodies and flip normal
        return {
          ...result,
          bodyA: bodyA,
          bodyB: bodyB,
          normal: vec2.scale(result.normal, -1),
        };
      }
      return null;
    }

    // Box vs Box
    if (shapeA.type === 'box' && shapeB.type === 'box') {
      return this.boxVsBox(bodyA, bodyB);
    }

    // Fallback - treat as circles based on bounding radius
    return this.circleVsCircle(bodyA, bodyB);
  }

  private circleVsCircle(bodyA: InternalRigidBody, bodyB: InternalRigidBody): CollisionPair | null {
    const radiusA = bodyA.config.shape.radius || 10;
    const radiusB = bodyB.config.shape.radius || 10;

    const diff = vec2.sub(bodyB.position, bodyA.position);
    const distSq = vec2.lengthSq(diff);
    const minDist = radiusA + radiusB;

    if (distSq >= minDist * minDist) return null;

    const dist = Math.sqrt(distSq);
    const normal = dist > 0 ? vec2.scale(diff, 1 / dist) : { x: 1, y: 0 };
    const depth = minDist - dist;
    const contactPoint = vec2.add(bodyA.position, vec2.scale(normal, radiusA));

    return { bodyA, bodyB, normal, depth, contactPoint };
  }

  private circleVsBox(circleBody: InternalRigidBody, boxBody: InternalRigidBody): CollisionPair | null {
    const radius = circleBody.config.shape.radius || 10;
    const halfW = (boxBody.config.shape.width || 20) / 2;
    const halfH = (boxBody.config.shape.height || 20) / 2;

    // Transform circle center to box local space
    const cos = Math.cos(-boxBody.angle);
    const sin = Math.sin(-boxBody.angle);
    const diff = vec2.sub(circleBody.position, boxBody.position);
    const localCenter = {
      x: diff.x * cos - diff.y * sin,
      y: diff.x * sin + diff.y * cos,
    };

    // Find closest point on box
    const closest = {
      x: Math.max(-halfW, Math.min(halfW, localCenter.x)),
      y: Math.max(-halfH, Math.min(halfH, localCenter.y)),
    };

    // Check if inside or outside
    const inside = localCenter.x === closest.x && localCenter.y === closest.y;

    let normal: PhysicsVec2;
    let depth: number;

    if (inside) {
      // Circle center is inside box
      const dx = halfW - Math.abs(localCenter.x);
      const dy = halfH - Math.abs(localCenter.y);
      if (dx < dy) {
        closest.x = localCenter.x > 0 ? halfW : -halfW;
      } else {
        closest.y = localCenter.y > 0 ? halfH : -halfH;
      }
    }

    const localDiff = vec2.sub(localCenter, closest);
    const distSq = vec2.lengthSq(localDiff);

    if (!inside && distSq >= radius * radius) return null;

    const dist = Math.sqrt(distSq);

    // Local normal
    const localNormal = dist > 0 ? vec2.scale(localDiff, 1 / dist) : { x: 1, y: 0 };

    // Transform back to world space
    const worldNormal = {
      x: localNormal.x * Math.cos(boxBody.angle) - localNormal.y * Math.sin(boxBody.angle),
      y: localNormal.x * Math.sin(boxBody.angle) + localNormal.y * Math.cos(boxBody.angle),
    };

    if (inside) {
      depth = radius + dist;
      normal = vec2.scale(worldNormal, -1);
    } else {
      depth = radius - dist;
      normal = worldNormal;
    }

    const contactPoint = vec2.sub(circleBody.position, vec2.scale(normal, radius));

    return { bodyA: circleBody, bodyB: boxBody, normal, depth, contactPoint };
  }

  private boxVsBox(bodyA: InternalRigidBody, bodyB: InternalRigidBody): CollisionPair | null {
    // Simplified AABB check for now (ignores rotation)
    const halfWA = (bodyA.config.shape.width || 20) / 2;
    const halfHA = (bodyA.config.shape.height || 20) / 2;
    const halfWB = (bodyB.config.shape.width || 20) / 2;
    const halfHB = (bodyB.config.shape.height || 20) / 2;

    const dx = bodyB.position.x - bodyA.position.x;
    const dy = bodyB.position.y - bodyA.position.y;

    const overlapX = halfWA + halfWB - Math.abs(dx);
    const overlapY = halfHA + halfHB - Math.abs(dy);

    if (overlapX <= 0 || overlapY <= 0) return null;

    let normal: PhysicsVec2;
    let depth: number;

    if (overlapX < overlapY) {
      normal = { x: dx > 0 ? 1 : -1, y: 0 };
      depth = overlapX;
    } else {
      normal = { x: 0, y: dy > 0 ? 1 : -1 };
      depth = overlapY;
    }

    const contactPoint = vec2.add(bodyA.position, vec2.scale(normal, halfWA));

    return { bodyA, bodyB, normal, depth, contactPoint };
  }
}

// =============================================================================
// COLLISION RESOLVER
// =============================================================================

class CollisionResolver {
  private config: PhysicsSpaceConfig;

  constructor(config: PhysicsSpaceConfig) {
    this.config = config;
  }

  resolveCollisions(pairs: CollisionPair[]): ContactInfo[] {
    const contacts: ContactInfo[] = [];

    for (const pair of pairs) {
      const contact = this.resolveCollision(pair);
      if (contact) {
        contacts.push(contact);
      }
    }

    return contacts;
  }

  private resolveCollision(pair: CollisionPair): ContactInfo | null {
    const { bodyA, bodyB, normal, depth, contactPoint } = pair;

    // Check for sensor mode
    const isSensor = bodyA.config.response === 'sensor' || bodyB.config.response === 'sensor';

    // Calculate relative velocity at contact point
    const rA = vec2.sub(contactPoint, bodyA.position);
    const rB = vec2.sub(contactPoint, bodyB.position);

    const velA = vec2.add(
      bodyA.velocity,
      vec2.perpendicular(vec2.scale(rA, bodyA.angularVelocity))
    );
    const velB = vec2.add(
      bodyB.velocity,
      vec2.perpendicular(vec2.scale(rB, bodyB.angularVelocity))
    );

    const relativeVelocity = vec2.sub(velB, velA);
    const normalVelocity = vec2.dot(relativeVelocity, normal);

    // Don't resolve if velocities are separating
    if (normalVelocity > 0) return null;

    // Calculate restitution
    const restitution = Math.min(
      bodyA.config.material.restitution,
      bodyB.config.material.restitution
    );

    // Calculate effective inverse mass
    const rACrossN = vec2.cross(rA, normal);
    const rBCrossN = vec2.cross(rB, normal);
    const invMassSum =
      bodyA.inverseMass +
      bodyB.inverseMass +
      rACrossN * rACrossN * bodyA.inverseInertia +
      rBCrossN * rBCrossN * bodyB.inverseInertia;

    if (invMassSum === 0) return null;

    // Calculate impulse magnitude
    let j = -(1 + restitution) * normalVelocity;
    j /= invMassSum;

    // Apply impulse (skip if sensor)
    if (!isSensor) {
      const impulse = vec2.scale(normal, j);

      bodyA.velocity = vec2.sub(bodyA.velocity, vec2.scale(impulse, bodyA.inverseMass));
      bodyA.angularVelocity -= bodyA.inverseInertia * vec2.cross(rA, impulse);

      bodyB.velocity = vec2.add(bodyB.velocity, vec2.scale(impulse, bodyB.inverseMass));
      bodyB.angularVelocity += bodyB.inverseInertia * vec2.cross(rB, impulse);

      // Friction
      const tangent = vec2.normalize(
        vec2.sub(relativeVelocity, vec2.scale(normal, normalVelocity))
      );
      const tangentVelocity = vec2.dot(relativeVelocity, tangent);

      const friction = Math.sqrt(
        bodyA.config.material.friction * bodyB.config.material.friction
      );

      let jt = -tangentVelocity / invMassSum;
      jt = Math.max(-j * friction, Math.min(j * friction, jt)); // Coulomb's law

      const frictionImpulse = vec2.scale(tangent, jt);

      bodyA.velocity = vec2.sub(bodyA.velocity, vec2.scale(frictionImpulse, bodyA.inverseMass));
      bodyB.velocity = vec2.add(bodyB.velocity, vec2.scale(frictionImpulse, bodyB.inverseMass));

      // Position correction
      const correction = vec2.scale(
        normal,
        Math.max(depth - this.config.collisionSlop, 0) * this.config.collisionBias / invMassSum
      );

      bodyA.position = vec2.sub(bodyA.position, vec2.scale(correction, bodyA.inverseMass));
      bodyB.position = vec2.add(bodyB.position, vec2.scale(correction, bodyB.inverseMass));

      // Wake both bodies
      bodyA.isSleeping = false;
      bodyA.sleepTime = 0;
      bodyB.isSleeping = false;
      bodyB.sleepTime = 0;
    }

    return {
      bodyA: bodyA.config.id,
      bodyB: bodyB.config.id,
      point: contactPoint,
      normal,
      depth,
      impulse: j,
    };
  }
}

// =============================================================================
// SOFT BODY SIMULATOR (Verlet Integration)
// =============================================================================

interface InternalVerletParticle {
  id: string;
  position: PhysicsVec2;
  previousPosition: PhysicsVec2;
  acceleration: PhysicsVec2;
  mass: number;
  invMass: number;
  pinned: boolean;
  radius: number;
}

interface InternalVerletConstraint {
  id: string;
  particleA: string;
  particleB: string;
  restLength: number;
  stiffness: number;
  broken: boolean;
  breakThreshold?: number;
}

class SoftBodySimulator {
  private particles: Map<string, InternalVerletParticle> = new Map();
  private constraints: Map<string, InternalVerletConstraint> = new Map();
  private softBodyParticles: Map<string, string[]> = new Map(); // softBodyId -> particleIds
  private softBodyConstraints: Map<string, string[]> = new Map(); // softBodyId -> constraintIds

  addSoftBody(config: SoftBodyConfig): void {
    const particleIds: string[] = [];
    const constraintIds: string[] = [];

    // Add particles
    for (const p of config.particles) {
      const particle: InternalVerletParticle = {
        id: p.id,
        position: vec2.clone(p.position),
        previousPosition: vec2.clone(p.previousPosition),
        acceleration: vec2.clone(p.acceleration),
        mass: p.mass,
        invMass: p.pinned ? 0 : 1 / p.mass,
        pinned: p.pinned,
        radius: p.radius,
      };
      this.particles.set(p.id, particle);
      particleIds.push(p.id);
    }

    // Add constraints
    for (const c of config.constraints) {
      const constraint: InternalVerletConstraint = {
        id: c.id,
        particleA: c.particleA,
        particleB: c.particleB,
        restLength: c.restLength,
        stiffness: c.stiffness,
        broken: false,
        breakThreshold: c.breakThreshold,
      };
      this.constraints.set(c.id, constraint);
      constraintIds.push(c.id);
    }

    this.softBodyParticles.set(config.id, particleIds);
    this.softBodyConstraints.set(config.id, constraintIds);
  }

  removeSoftBody(id: string): void {
    const particleIds = this.softBodyParticles.get(id);
    const constraintIds = this.softBodyConstraints.get(id);

    if (particleIds) {
      for (const pid of particleIds) {
        this.particles.delete(pid);
      }
    }
    if (constraintIds) {
      for (const cid of constraintIds) {
        this.constraints.delete(cid);
      }
    }

    this.softBodyParticles.delete(id);
    this.softBodyConstraints.delete(id);
  }

  applyForce(particleId: string, force: PhysicsVec2): void {
    const particle = this.particles.get(particleId);
    if (particle && !particle.pinned) {
      particle.acceleration = vec2.add(particle.acceleration, vec2.scale(force, particle.invMass));
    }
  }

  applyForceToAll(force: PhysicsVec2): void {
    for (const particle of this.particles.values()) {
      if (!particle.pinned) {
        particle.acceleration = vec2.add(particle.acceleration, force);
      }
    }
  }

  integrate(dt: number, damping: number = 0.98): void {
    const dtSq = dt * dt;

    for (const particle of this.particles.values()) {
      if (particle.pinned) continue;

      // Verlet integration
      const velocity = vec2.sub(particle.position, particle.previousPosition);
      const dampedVelocity = vec2.scale(velocity, damping);

      particle.previousPosition = vec2.clone(particle.position);
      particle.position = vec2.add(
        vec2.add(particle.position, dampedVelocity),
        vec2.scale(particle.acceleration, dtSq)
      );

      // Clear acceleration
      particle.acceleration = vec2.create();
    }
  }

  solveConstraints(iterations: number): void {
    for (let i = 0; i < iterations; i++) {
      for (const constraint of this.constraints.values()) {
        if (constraint.broken) continue;

        const pA = this.particles.get(constraint.particleA);
        const pB = this.particles.get(constraint.particleB);
        if (!pA || !pB) continue;

        const diff = vec2.sub(pB.position, pA.position);
        const distance = vec2.length(diff);
        if (distance === 0) continue;

        // Check for breaking
        if (constraint.breakThreshold && distance > constraint.restLength * constraint.breakThreshold) {
          constraint.broken = true;
          continue;
        }

        const error = (distance - constraint.restLength) / distance;
        const correction = vec2.scale(diff, error * constraint.stiffness * 0.5);

        const totalMass = pA.invMass + pB.invMass;
        if (totalMass === 0) continue;

        const ratioA = pA.invMass / totalMass;
        const ratioB = pB.invMass / totalMass;

        pA.position = vec2.add(pA.position, vec2.scale(correction, ratioA));
        pB.position = vec2.sub(pB.position, vec2.scale(correction, ratioB));
      }
    }
  }

  getState(softBodyId: string): SoftBodyState | null {
    const particleIds = this.softBodyParticles.get(softBodyId);
    const constraintIds = this.softBodyConstraints.get(softBodyId);
    if (!particleIds) return null;

    const particles = particleIds.map(id => {
      const p = this.particles.get(id)!;
      return {
        id: p.id,
        position: vec2.clone(p.position),
        velocity: vec2.sub(p.position, p.previousPosition),
      };
    });

    const brokenConstraints = (constraintIds || [])
      .filter(id => this.constraints.get(id)?.broken)
      .map(id => id);

    return {
      id: softBodyId,
      particles,
      brokenConstraints,
    };
  }

  loadState(softBodyId: string, state: SoftBodyState): void {
    for (const ps of state.particles) {
      const particle = this.particles.get(ps.id);
      if (particle) {
        particle.position = vec2.clone(ps.position);
        particle.previousPosition = vec2.sub(ps.position, ps.velocity);
      }
    }

    for (const constraintId of state.brokenConstraints) {
      const constraint = this.constraints.get(constraintId);
      if (constraint) {
        constraint.broken = true;
      }
    }
  }
}

// =============================================================================
// CLOTH SIMULATOR
// =============================================================================

class ClothSimulator {
  private cloths: Map<string, {
    config: ClothConfig;
    particles: InternalVerletParticle[];
    constraints: InternalVerletConstraint[];
  }> = new Map();

  createCloth(config: ClothConfig): void {
    const particles: InternalVerletParticle[] = [];
    const constraints: InternalVerletConstraint[] = [];

    // Create particles in grid
    for (let y = 0; y < config.height; y++) {
      for (let x = 0; x < config.width; x++) {
        const index = y * config.width + x;
        const isPinned = config.pinnedParticles.includes(index);

        const pos = {
          x: config.origin.x + x * config.spacing,
          y: config.origin.y + y * config.spacing,
        };

        particles.push({
          id: `${config.id}_p_${index}`,
          position: vec2.clone(pos),
          previousPosition: vec2.clone(pos),
          acceleration: vec2.create(),
          mass: config.particleMass,
          invMass: isPinned ? 0 : 1 / config.particleMass,
          pinned: isPinned,
          radius: config.collisionRadius,
        });
      }
    }

    // Create structural constraints (horizontal and vertical)
    for (let y = 0; y < config.height; y++) {
      for (let x = 0; x < config.width; x++) {
        const index = y * config.width + x;

        // Horizontal
        if (x < config.width - 1) {
          constraints.push({
            id: `${config.id}_h_${index}`,
            particleA: particles[index].id,
            particleB: particles[index + 1].id,
            restLength: config.spacing,
            stiffness: config.structuralStiffness,
            broken: false,
            breakThreshold: config.tearThreshold || undefined,
          });
        }

        // Vertical
        if (y < config.height - 1) {
          constraints.push({
            id: `${config.id}_v_${index}`,
            particleA: particles[index].id,
            particleB: particles[index + config.width].id,
            restLength: config.spacing,
            stiffness: config.structuralStiffness,
            broken: false,
            breakThreshold: config.tearThreshold || undefined,
          });
        }
      }
    }

    // Create shear constraints (diagonal)
    if (config.shearStiffness > 0) {
      const diagLength = config.spacing * Math.SQRT2;
      for (let y = 0; y < config.height - 1; y++) {
        for (let x = 0; x < config.width - 1; x++) {
          const index = y * config.width + x;

          // Diagonal down-right
          constraints.push({
            id: `${config.id}_s1_${index}`,
            particleA: particles[index].id,
            particleB: particles[index + config.width + 1].id,
            restLength: diagLength,
            stiffness: config.shearStiffness,
            broken: false,
          });

          // Diagonal down-left
          constraints.push({
            id: `${config.id}_s2_${index}`,
            particleA: particles[index + 1].id,
            particleB: particles[index + config.width].id,
            restLength: diagLength,
            stiffness: config.shearStiffness,
            broken: false,
          });
        }
      }
    }

    // Create bend constraints (skip one)
    if (config.bendStiffness > 0) {
      const skipLength = config.spacing * 2;
      for (let y = 0; y < config.height; y++) {
        for (let x = 0; x < config.width - 2; x++) {
          const index = y * config.width + x;
          constraints.push({
            id: `${config.id}_bh_${index}`,
            particleA: particles[index].id,
            particleB: particles[index + 2].id,
            restLength: skipLength,
            stiffness: config.bendStiffness,
            broken: false,
          });
        }
      }
      for (let y = 0; y < config.height - 2; y++) {
        for (let x = 0; x < config.width; x++) {
          const index = y * config.width + x;
          constraints.push({
            id: `${config.id}_bv_${index}`,
            particleA: particles[index].id,
            particleB: particles[index + config.width * 2].id,
            restLength: skipLength,
            stiffness: config.bendStiffness,
            broken: false,
          });
        }
      }
    }

    this.cloths.set(config.id, { config, particles, constraints });
  }

  removeCloth(id: string): void {
    this.cloths.delete(id);
  }

  applyForce(clothId: string, force: PhysicsVec2): void {
    const cloth = this.cloths.get(clothId);
    if (!cloth) return;

    for (const particle of cloth.particles) {
      if (!particle.pinned) {
        particle.acceleration = vec2.add(particle.acceleration, force);
      }
    }
  }

  integrate(dt: number): void {
    const dtSq = dt * dt;

    for (const cloth of this.cloths.values()) {
      const damping = cloth.config.damping;

      for (const particle of cloth.particles) {
        if (particle.pinned) continue;

        const velocity = vec2.sub(particle.position, particle.previousPosition);
        const dampedVelocity = vec2.scale(velocity, damping);

        particle.previousPosition = vec2.clone(particle.position);
        particle.position = vec2.add(
          vec2.add(particle.position, dampedVelocity),
          vec2.scale(particle.acceleration, dtSq)
        );

        particle.acceleration = vec2.create();
      }
    }
  }

  solveConstraints(): void {
    for (const cloth of this.cloths.values()) {
      const iterations = cloth.config.iterations;

      for (let i = 0; i < iterations; i++) {
        for (const constraint of cloth.constraints) {
          if (constraint.broken) continue;

          const pA = cloth.particles.find(p => p.id === constraint.particleA);
          const pB = cloth.particles.find(p => p.id === constraint.particleB);
          if (!pA || !pB) continue;

          const diff = vec2.sub(pB.position, pA.position);
          const distance = vec2.length(diff);
          if (distance === 0) continue;

          // Check for tearing
          if (constraint.breakThreshold && distance > constraint.restLength * constraint.breakThreshold) {
            constraint.broken = true;
            continue;
          }

          const error = (distance - constraint.restLength) / distance;
          const correction = vec2.scale(diff, error * constraint.stiffness * 0.5);

          const totalMass = pA.invMass + pB.invMass;
          if (totalMass === 0) continue;

          const ratioA = pA.invMass / totalMass;
          const ratioB = pB.invMass / totalMass;

          pA.position = vec2.add(pA.position, vec2.scale(correction, ratioA));
          pB.position = vec2.sub(pB.position, vec2.scale(correction, ratioB));
        }
      }
    }
  }

  getState(clothId: string): ClothState | null {
    const cloth = this.cloths.get(clothId);
    if (!cloth) return null;

    return {
      id: clothId,
      positions: cloth.particles.map(p => vec2.clone(p.position)),
      tornConstraints: cloth.constraints
        .filter(c => c.broken)
        .map(c => {
          // Parse constraint ID to get row/col/type
          const parts = c.id.split('_');
          const type = parts[1].startsWith('h') ? 'structural' :
                       parts[1].startsWith('v') ? 'structural' :
                       parts[1].startsWith('s') ? 'shear' : 'bend';
          const index = parseInt(parts[2]);
          const col = index % cloth.config.width;
          const row = Math.floor(index / cloth.config.width);
          return { row, col, type: type as 'structural' | 'shear' | 'bend' };
        }),
    };
  }

  loadState(clothId: string, state: ClothState): void {
    const cloth = this.cloths.get(clothId);
    if (!cloth) return;

    for (let i = 0; i < state.positions.length && i < cloth.particles.length; i++) {
      cloth.particles[i].position = vec2.clone(state.positions[i]);
      cloth.particles[i].previousPosition = vec2.clone(state.positions[i]);
    }

    // Restore torn constraints
    const tornSet = new Set(state.tornConstraints.map(t => `${t.row}_${t.col}_${t.type}`));
    for (const constraint of cloth.constraints) {
      const parts = constraint.id.split('_');
      const type = parts[1].startsWith('h') || parts[1].startsWith('v') ? 'structural' :
                   parts[1].startsWith('s') ? 'shear' : 'bend';
      const index = parseInt(parts[2]);
      const col = index % cloth.config.width;
      const row = Math.floor(index / cloth.config.width);
      constraint.broken = tornSet.has(`${row}_${col}_${type}`);
    }
  }
}

// =============================================================================
// FORCE FIELD PROCESSOR
// =============================================================================

class ForceFieldProcessor {
  private forceFields: ForceField[] = [];
  private random: PhysicsRandom;

  constructor(seed: number) {
    this.random = new PhysicsRandom(seed);
  }

  setForceFields(fields: ForceField[]): void {
    this.forceFields = fields;
  }

  processForces(
    frame: number,
    bodies: InternalRigidBody[],
    applyForce: (bodyId: string, force: PhysicsVec2) => void
  ): void {
    for (const field of this.forceFields) {
      if (!field.enabled) continue;
      if (frame < field.startFrame) continue;
      if (field.endFrame >= 0 && frame > field.endFrame) continue;

      const affectedIds = field.affectedBodies && field.affectedBodies.length > 0
        ? new Set(field.affectedBodies)
        : null;

      for (const body of bodies) {
        if (body.inverseMass === 0) continue;
        if (affectedIds && !affectedIds.has(body.config.id)) continue;

        const force = this.calculateForce(field, body, frame);
        if (force) {
          applyForce(body.config.id, force);
        }
      }
    }
  }

  private calculateForce(field: ForceField, body: InternalRigidBody, frame: number): PhysicsVec2 | null {
    switch (field.type) {
      case 'gravity': {
        const gravity = this.evaluateAnimatable(field.gravity, frame);
        return vec2.scale(gravity, body.config.mass);
      }

      case 'wind': {
        const direction = this.evaluateAnimatable(field.direction, frame);
        const turbulence = this.evaluateAnimatable(field.turbulence, frame);

        // Add turbulence using simplex-like noise (simplified)
        const noiseX = Math.sin(body.position.x * field.frequency + frame * 0.1 + field.seed) * turbulence;
        const noiseY = Math.cos(body.position.y * field.frequency + frame * 0.1 + field.seed * 2) * turbulence;

        return {
          x: direction.x + noiseX,
          y: direction.y + noiseY,
        };
      }

      case 'attraction': {
        const center = this.evaluateAnimatable(field.position, frame);
        const strength = this.evaluateAnimatable(field.strength, frame);

        const diff = vec2.sub(center, body.position);
        const distSq = vec2.lengthSq(diff);
        const dist = Math.sqrt(distSq);

        if (field.radius > 0 && dist > field.radius) return null;
        if (dist < 1) return null;

        let forceMag: number;
        switch (field.falloff) {
          case 'linear':
            forceMag = strength * (field.radius > 0 ? (field.radius - dist) / field.radius : 1);
            break;
          case 'quadratic':
            forceMag = strength / distSq;
            break;
          case 'constant':
          default:
            forceMag = strength;
        }

        return vec2.scale(vec2.normalize(diff), forceMag * body.config.mass);
      }

      case 'explosion': {
        if (frame !== field.triggerFrame) return null;

        const diff = vec2.sub(body.position, field.position);
        const dist = vec2.length(diff);

        if (dist > field.radius || dist < 1) return null;

        const falloff = 1 - dist / field.radius;
        const impulse = vec2.scale(vec2.normalize(diff), field.strength * falloff);

        // Apply as impulse, not force
        body.velocity = vec2.add(body.velocity, vec2.scale(impulse, body.inverseMass));
        return null;
      }

      case 'buoyancy': {
        const surfaceLevel = this.evaluateAnimatable(field.surfaceLevel, frame);
        const submergedDepth = body.position.y - surfaceLevel;

        if (submergedDepth <= 0) return null; // Above water

        // Approximate submerged volume based on shape
        const radius = body.config.shape.radius || 10;
        const submergedRatio = Math.min(1, submergedDepth / (radius * 2));

        // Buoyancy force (upward)
        const buoyancyForce = -field.density * submergedRatio * body.config.mass * 980;

        // Drag forces
        const dragX = -field.linearDrag * body.velocity.x * submergedRatio;
        const dragY = -field.linearDrag * body.velocity.y * submergedRatio;
        const angularDrag = -field.angularDrag * body.angularVelocity * submergedRatio;

        body.angularVelocity += angularDrag;

        return {
          x: dragX,
          y: buoyancyForce + dragY,
        };
      }

      case 'vortex': {
        const center = this.evaluateAnimatable(field.position, frame);
        const strength = this.evaluateAnimatable(field.strength, frame);

        const diff = vec2.sub(body.position, center);
        const dist = vec2.length(diff);

        if (dist > field.radius || dist < 1) return null;

        const falloff = 1 - dist / field.radius;

        // Tangential force (perpendicular to radius)
        const tangent = vec2.perpendicular(vec2.normalize(diff));
        const tangentialForce = vec2.scale(tangent, strength * falloff * body.config.mass);

        // Inward force
        const inwardForce = vec2.scale(
          vec2.scale(vec2.normalize(diff), -1),
          field.inwardForce * falloff * body.config.mass
        );

        return vec2.add(tangentialForce, inwardForce);
      }

      case 'drag': {
        const speed = vec2.length(body.velocity);
        if (speed < 0.01) return null;

        const dragMag = field.linear * speed + field.quadratic * speed * speed;
        return vec2.scale(vec2.normalize(body.velocity), -dragMag);
      }

      default:
        return null;
    }
  }

  private evaluateAnimatable<T>(prop: { defaultValue?: T } | T, _frame: number): T {
    // Simplified - in production would evaluate keyframes
    if (typeof prop === 'object' && prop !== null && 'defaultValue' in prop) {
      return prop.defaultValue as T;
    }
    return prop as T;
  }
}

// =============================================================================
// MAIN PHYSICS ENGINE
// =============================================================================

interface PhysicsCheckpoint {
  frame: number;
  rigidBodyStates: RigidBodyState[];
  softBodyStates: SoftBodyState[];
  clothStates: ClothState[];
  randomState: number;
}

/**
 * Main physics engine class
 */
export class PhysicsEngine {
  private config: PhysicsSpaceConfig;
  private random: PhysicsRandom;

  private rigidBodySimulator: RigidBodySimulator;
  private collisionDetector: CollisionDetector;
  private collisionResolver: CollisionResolver;
  private softBodySimulator: SoftBodySimulator;
  private clothSimulator: ClothSimulator;
  private forceFieldProcessor: ForceFieldProcessor;

  private checkpoints: Map<number, PhysicsCheckpoint> = new Map();
  private checkpointInterval: number = 30; // Checkpoint every 30 frames

  private lastSimulatedFrame: number = -1;
  private isInitialized: boolean = false;

  constructor(config: Partial<PhysicsSpaceConfig> = {}) {
    this.config = { ...DEFAULT_SPACE_CONFIG, ...config };
    this.random = new PhysicsRandom(this.config.seed);

    this.rigidBodySimulator = new RigidBodySimulator(this.config);
    this.collisionDetector = new CollisionDetector();
    this.collisionResolver = new CollisionResolver(this.config);
    this.softBodySimulator = new SoftBodySimulator();
    this.clothSimulator = new ClothSimulator();
    this.forceFieldProcessor = new ForceFieldProcessor(this.config.seed);

    this.isInitialized = true;
  }

  // Configuration
  setConfig(config: Partial<PhysicsSpaceConfig>): void {
    this.config = { ...this.config, ...config };
    this.rigidBodySimulator = new RigidBodySimulator(this.config);
    this.collisionResolver = new CollisionResolver(this.config);
    this.clearCache();
  }

  setForceFields(fields: ForceField[]): void {
    this.forceFieldProcessor.setForceFields(fields);
    this.clearCache();
  }

  // Body management
  addRigidBody(config: RigidBodyConfig): void {
    this.rigidBodySimulator.addBody(config);
    this.clearCache();
  }

  removeRigidBody(id: string): void {
    this.rigidBodySimulator.removeBody(id);
    this.clearCache();
  }

  addSoftBody(config: SoftBodyConfig): void {
    this.softBodySimulator.addSoftBody(config);
    this.clearCache();
  }

  removeSoftBody(id: string): void {
    this.softBodySimulator.removeSoftBody(id);
    this.clearCache();
  }

  addCloth(config: ClothConfig): void {
    this.clothSimulator.createCloth(config);
    this.clearCache();
  }

  removeCloth(id: string): void {
    this.clothSimulator.removeCloth(id);
    this.clearCache();
  }

  // Simulation
  evaluateFrame(targetFrame: number): PhysicsSimulationState {
    if (!this.isInitialized) {
      throw new Error('Physics engine not initialized');
    }

    // Check if we can use cache
    if (targetFrame === this.lastSimulatedFrame) {
      return this.getState(targetFrame);
    }

    // Find nearest checkpoint
    let startFrame = 0;
    let nearestCheckpoint: PhysicsCheckpoint | null = null;

    for (const [frame, checkpoint] of this.checkpoints) {
      if (frame <= targetFrame && frame > startFrame) {
        startFrame = frame;
        nearestCheckpoint = checkpoint;
      }
    }

    // Restore from checkpoint
    if (nearestCheckpoint) {
      this.rigidBodySimulator.loadState(nearestCheckpoint.rigidBodyStates);
      // Load soft body and cloth states here...
      this.random = new PhysicsRandom(nearestCheckpoint.randomState);
    } else {
      // Start from frame 0
      this.random = new PhysicsRandom(this.config.seed);
      startFrame = 0;
    }

    // Simulate forward to target frame
    for (let frame = startFrame; frame <= targetFrame; frame++) {
      this.simulateStep(frame);

      // Save checkpoint
      if (frame % this.checkpointInterval === 0 && frame > 0 && !this.checkpoints.has(frame)) {
        this.saveCheckpoint(frame);
      }
    }

    this.lastSimulatedFrame = targetFrame;
    return this.getState(targetFrame);
  }

  private simulateStep(frame: number): void {
    const dt = this.config.timeStep;
    const bodies = this.rigidBodySimulator.getAllBodies();

    // Apply global gravity
    for (const body of bodies) {
      if (body.inverseMass > 0) {
        this.rigidBodySimulator.applyForce(
          body.config.id,
          vec2.scale(this.config.gravity, body.config.mass)
        );
      }
    }

    // Process force fields
    this.forceFieldProcessor.processForces(
      frame,
      bodies,
      (id, force) => this.rigidBodySimulator.applyForce(id, force)
    );

    // Integrate rigid bodies
    this.rigidBodySimulator.integrate(dt);

    // Detect and resolve collisions
    for (let i = 0; i < this.config.velocityIterations; i++) {
      const pairs = this.collisionDetector.detectCollisions(bodies);
      this.collisionResolver.resolveCollisions(pairs);
    }

    // Apply gravity to soft bodies and cloth
    this.softBodySimulator.applyForceToAll(this.config.gravity);
    for (const clothId of this.getClothIds()) {
      this.clothSimulator.applyForce(clothId, this.config.gravity);
    }

    // Integrate soft bodies and cloth
    this.softBodySimulator.integrate(dt);
    this.clothSimulator.integrate(dt);

    // Solve constraints
    this.softBodySimulator.solveConstraints(this.config.positionIterations);
    this.clothSimulator.solveConstraints();
  }

  private getState(frame: number): PhysicsSimulationState {
    const bodies = this.rigidBodySimulator.getAllBodies();
    const pairs = this.collisionDetector.detectCollisions(bodies);

    return {
      frame,
      rigidBodies: this.rigidBodySimulator.getState(),
      softBodies: this.getSoftBodyIds().map(id => this.softBodySimulator.getState(id)!).filter(Boolean),
      cloths: this.getClothIds().map(id => this.clothSimulator.getState(id)!).filter(Boolean),
      ragdolls: [], // TODO: Implement ragdoll state
      contacts: pairs.map(p => ({
        bodyA: p.bodyA.config.id,
        bodyB: p.bodyB.config.id,
        point: p.contactPoint,
        normal: p.normal,
        depth: p.depth,
        impulse: 0,
      })),
    };
  }

  private saveCheckpoint(frame: number): void {
    this.checkpoints.set(frame, {
      frame,
      rigidBodyStates: this.rigidBodySimulator.getState(),
      softBodyStates: this.getSoftBodyIds().map(id => this.softBodySimulator.getState(id)!).filter(Boolean),
      clothStates: this.getClothIds().map(id => this.clothSimulator.getState(id)!).filter(Boolean),
      randomState: this.config.seed + frame, // Simplified - in production, would save actual RNG state
    });
  }

  clearCache(): void {
    this.checkpoints.clear();
    this.lastSimulatedFrame = -1;
  }

  // Helpers
  private getSoftBodyIds(): string[] {
    // Would track these in production
    return [];
  }

  private getClothIds(): string[] {
    // Would track these in production
    return [];
  }

  // Keyframe export
  exportKeyframes(options: KeyframeExportOptions): ExportedKeyframes[] {
    const results: ExportedKeyframes[] = [];
    const frameData: Map<string, Array<{ frame: number; position: PhysicsVec2; angle: number }>> = new Map();

    // Collect data for each frame
    for (let frame = options.startFrame; frame <= options.endFrame; frame += options.frameStep) {
      const state = this.evaluateFrame(frame);

      for (const body of state.rigidBodies) {
        if (!frameData.has(body.id)) {
          frameData.set(body.id, []);
        }
        frameData.get(body.id)!.push({
          frame,
          position: body.position,
          angle: body.angle,
        });
      }
    }

    // Convert to keyframes
    for (const [bodyId, data] of frameData) {
      // Find layer ID for this body
      const body = this.rigidBodySimulator.getBody(bodyId);
      if (!body) continue;

      const layerId = body.config.layerId;

      if (options.properties.includes('position')) {
        const keyframes = data.map(d => ({
          frame: d.frame,
          value: d.position,
          interpolation: options.interpolation as 'linear' | 'bezier',
        }));

        // Simplify if requested
        const simplifiedKeyframes = options.simplify
          ? this.simplifyKeyframes(keyframes, options.simplifyTolerance)
          : keyframes;

        results.push({
          layerId,
          property: 'transform.position',
          keyframes: simplifiedKeyframes,
        });
      }

      if (options.properties.includes('rotation')) {
        const keyframes = data.map(d => ({
          frame: d.frame,
          value: d.angle * (180 / Math.PI), // Convert to degrees
          interpolation: options.interpolation as 'linear' | 'bezier',
        }));

        const simplifiedKeyframes = options.simplify
          ? this.simplifyKeyframes(keyframes, options.simplifyTolerance)
          : keyframes;

        results.push({
          layerId,
          property: 'transform.rotation.z',
          keyframes: simplifiedKeyframes,
        });
      }
    }

    return results;
  }

  private simplifyKeyframes<T>(
    keyframes: Array<{ frame: number; value: T; interpolation: string }>,
    tolerance: number
  ): Array<{ frame: number; value: T; interpolation: string }> {
    if (keyframes.length <= 2) return keyframes;

    // Simple Douglas-Peucker-like simplification for position keyframes
    const simplified = [keyframes[0]];
    let lastAdded = 0;

    for (let i = 1; i < keyframes.length - 1; i++) {
      const prev = keyframes[lastAdded].value;
      const curr = keyframes[i].value;
      const next = keyframes[i + 1].value;

      // Check if current point deviates significantly from line
      if (typeof curr === 'object' && 'x' in curr) {
        const p = prev as unknown as PhysicsVec2;
        const c = curr as unknown as PhysicsVec2;
        const n = next as unknown as PhysicsVec2;

        // Calculate distance from point to line
        const lineDir = vec2.sub(n, p);
        const lineLen = vec2.length(lineDir);
        if (lineLen > 0) {
          const t = Math.max(0, Math.min(1, vec2.dot(vec2.sub(c, p), lineDir) / (lineLen * lineLen)));
          const projection = vec2.add(p, vec2.scale(lineDir, t));
          const distance = vec2.distance(c, projection);

          if (distance > tolerance) {
            simplified.push(keyframes[i]);
            lastAdded = i;
          }
        }
      } else if (typeof curr === 'number') {
        // For scalar values
        const p = prev as unknown as number;
        const c = curr as unknown as number;
        const n = next as unknown as number;

        const expected = p + (n - p) * ((i - lastAdded) / (keyframes.length - 1 - lastAdded));
        if (Math.abs(c - expected) > tolerance) {
          simplified.push(keyframes[i]);
          lastAdded = i;
        }
      } else {
        simplified.push(keyframes[i]);
        lastAdded = i;
      }
    }

    simplified.push(keyframes[keyframes.length - 1]);
    return simplified;
  }

  // Cleanup
  dispose(): void {
    this.checkpoints.clear();
    this.isInitialized = false;
  }
}

// =============================================================================
// EXPORTS
// =============================================================================

export { vec2, PhysicsRandom };

export type {
  InternalRigidBody,
  InternalVerletParticle,
  InternalVerletConstraint,
  CollisionPair,
  PhysicsCheckpoint,
};
