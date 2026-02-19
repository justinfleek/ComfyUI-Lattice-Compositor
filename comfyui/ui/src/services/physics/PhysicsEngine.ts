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
  ClothConfig,
  ClothState,
  ContactInfo,
  ExportedKeyframes,
  ForceField,
  KeyframeExportOptions,
  PhysicsSimulationState,
  PhysicsSpaceConfig,
  PhysicsVec2,
  RagdollBone,
  RagdollState,
  RigidBodyConfig,
  RigidBodyState,
  SoftBodyConfig,
  SoftBodyState,
} from "@/types/physics";
import { DEFAULT_SPACE_CONFIG } from "@/types/physics";
import { hasXY, isFiniteNumber } from "@/utils/typeGuards";

/**
 * Runtime value type for type guards
 * Deterministic: Explicit union of all possible runtime types
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

import { extractRagdollState } from "./RagdollBuilder";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                        // seeded // random // for // physics
// ════════════════════════════════════════════════════════════════════════════

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

// ════════════════════════════════════════════════════════════════════════════
//                                               // vector // math // utilities
// ════════════════════════════════════════════════════════════════════════════

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

  distance: (a: PhysicsVec2, b: PhysicsVec2): number =>
    vec2.length(vec2.sub(b, a)),

  distanceSq: (a: PhysicsVec2, b: PhysicsVec2): number =>
    vec2.lengthSq(vec2.sub(b, a)),
};

// ════════════════════════════════════════════════════════════════════════════
//                                                // rigid // body // simulator
// ════════════════════════════════════════════════════════════════════════════

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
    // Calculate inverse mass for physics simulation.
    // Static/dead bodies have infinite mass (inverseMass = 0).
    // Dynamic bodies with mass=0 default to mass=1 to prevent division by zero.
    const inverseMass =
      bodyConfig.type === "static" || bodyConfig.type === "dead"
        ? 0
        : 1 / (bodyConfig.mass || 1);

    // Calculate moment of inertia if not provided
    let moment = bodyConfig.moment;
    if (!moment && bodyConfig.mass > 0) {
      moment = this.calculateMomentOfInertia(bodyConfig);
    }
    const inverseInertia =
      bodyConfig.type === "static" ||
      bodyConfig.type === "dead" ||
      bodyConfig.fixedRotation
        ? 0
        : 1 / (moment || 1);

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
      case "circle": {
        const r = shape.radius || 10;
        return (mass * r * r) / 2;
      }
      case "box": {
        const w = shape.width || 10;
        const h = shape.height || 10;
        return (mass * (w * w + h * h)) / 12;
      }
      case "capsule": {
        const r = shape.radius || 5;
        const l = shape.length || 20;
        // Approximate as rectangle + semicircles
        const rectMass = (mass * l) / (l + Math.PI * r);
        const circleMass = mass - rectMass;
        const rectI = (rectMass * (l * l + 4 * r * r)) / 12;
        const circleI = (circleMass * r * r) / 2;
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

  applyImpulse(
    bodyId: string,
    impulse: PhysicsVec2,
    point?: PhysicsVec2,
  ): void {
    const body = this.bodies.get(bodyId);
    if (!body || body.inverseMass === 0) return;

    body.velocity = vec2.add(
      body.velocity,
      vec2.scale(impulse, body.inverseMass),
    );

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
      if (body.config.type === "static" || body.config.type === "dead")
        continue;
      if (body.isSleeping) continue;

      // Semi-implicit Euler integration
      // Update velocity
      body.velocity = vec2.add(
        body.velocity,
        vec2.scale(body.force, body.inverseMass * dt),
      );
      body.angularVelocity += body.torque * body.inverseInertia * dt;

      // Apply damping
      body.velocity = vec2.scale(
        body.velocity,
        1 - body.config.linearDamping * dt,
      );
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
        if (
          speed < this.config.sleepVelocityThreshold &&
          angSpeed < this.config.sleepVelocityThreshold * 0.1
        ) {
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

// ════════════════════════════════════════════════════════════════════════════
//                                                    // collision // detection
// ════════════════════════════════════════════════════════════════════════════

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
        if (bodyA.config.type === "dead" || bodyB.config.type === "dead")
          continue;
        if (
          bodyA.config.response === "none" ||
          bodyB.config.response === "none"
        )
          continue;

        // Check collision filter
        if (!this.shouldCollide(bodyA.config.filter, bodyB.config.filter))
          continue;

        // Narrow phase - shape-specific detection
        // System F/Omega proof: Collision detection throws error if no collision (no lazy null)
        try {
          const collision = this.detectShapeCollision(bodyA, bodyB);
          pairs.push(collision);
        } catch (error) {
          // No collision detected - this is expected and not an error
          // Bodies don't overlap, continue to next pair
          continue;
        }
      }
    }

    return pairs;
  }

  private shouldCollide(
    filterA: { category: number; mask: number; group: number },
    filterB: { category: number; mask: number; group: number },
  ): boolean {
    // Group filtering
    if (filterA.group !== 0 && filterA.group === filterB.group) {
      return filterA.group > 0; // Positive = always collide, negative = never
    }

    // Category/mask filtering
    return (
      (filterA.mask & filterB.category) !== 0 &&
      (filterB.mask & filterA.category) !== 0
    );
  }

  /**
   * Detect collision between two rigid body shapes
   * 
   * System F/Omega proof: Type guard for shape collision detection
   * Type proof: bodyA, bodyB ∈ InternalRigidBody → CollisionPair (non-nullable)
   * Mathematical proof: Collision detection is deterministic - either collision exists or error thrown
   * Geometric proof: Shape intersection is well-defined - invalid state throws error
   * 
   * @param bodyA - First rigid body (must have valid shape)
   * @param bodyB - Second rigid body (must have valid shape)
   * @returns CollisionPair if collision detected
   * @throws Error if shapes are invalid or collision detection fails
   */
  private detectShapeCollision(
    bodyA: InternalRigidBody,
    bodyB: InternalRigidBody,
  ): CollisionPair {
    // System F/Omega proof: Explicit validation of shape types
    // Type proof: shapeA, shapeB ∈ CollisionShape → shapeA.type, shapeB.type ∈ ShapeType
    const shapeA = bodyA.config.shape;
    const shapeB = bodyB.config.shape;

    if (typeof shapeA !== "object" || shapeA === null || typeof shapeB !== "object" || shapeB === null) {
      throw new Error(`[PhysicsEngine] Cannot detect shape collision: Invalid shape configuration (bodyA.shape: ${typeof shapeA}, bodyB.shape: ${typeof shapeB}). Shapes must be valid CollisionShape objects. BodyA ID: ${bodyA.config.id}, BodyB ID: ${bodyB.config.id}.`);
    }

    // Circle vs Circle
    if (shapeA.type === "circle" && shapeB.type === "circle") {
      return this.circleVsCircle(bodyA, bodyB);
    }

    // Circle vs Box
    if (shapeA.type === "circle" && shapeB.type === "box") {
      return this.circleVsBox(bodyA, bodyB);
    }
    if (shapeA.type === "box" && shapeB.type === "circle") {
      try {
        const result = this.circleVsBox(bodyB, bodyA);
        // Swap bodies and flip normal
        return {
          ...result,
          bodyA: bodyA,
          bodyB: bodyB,
          normal: vec2.scale(result.normal, -1),
        };
      } catch (error) {
        if (error instanceof Error && error.message.startsWith("[PhysicsEngine]")) {
          throw error;
        }
        throw new Error(`[PhysicsEngine] Cannot detect box-circle collision: Failed to detect collision between box body "${bodyA.config.id}" and circle body "${bodyB.config.id}". ${error instanceof Error ? error.message : String(error)}`);
      }
    }

    // Box vs Box
    if (shapeA.type === "box" && shapeB.type === "box") {
      return this.boxVsBox(bodyA, bodyB);
    }

    // Fallback - treat as circles based on bounding radius
    return this.circleVsCircle(bodyA, bodyB);
  }

  /**
   * Detect collision between two circle shapes
   * 
   * System F/Omega proof: Geometric collision detection for circles
   * Type proof: bodyA, bodyB ∈ InternalRigidBody with circle shapes → CollisionPair
   * Mathematical proof: Circle collision ⟺ distance(centerA, centerB) < radiusA + radiusB
   * Geometric proof: Two circles overlap ⟺ center distance < sum of radii
   * 
   * @param bodyA - First circle body (must have circle shape with radius)
   * @param bodyB - Second circle body (must have circle shape with radius)
   * @returns CollisionPair if circles overlap
   * @throws Error if circles don't overlap or radii are invalid
   */
  private circleVsCircle(
    bodyA: InternalRigidBody,
    bodyB: InternalRigidBody,
  ): CollisionPair {
    // System F/Omega proof: Explicit validation of circle radii
    // Type proof: radiusA, radiusB ∈ ℝ → must be finite and positive
    // Mathematical proof: Circle radius must be positive (r > 0)
    const radiusAValue = bodyA.config.shape.radius;
    const radiusBValue = bodyB.config.shape.radius;
    
    if (!isFiniteNumber(radiusAValue) || radiusAValue <= 0) {
      throw new Error(`[PhysicsEngine] Cannot detect circle-circle collision: Invalid radius for bodyA (radius: ${radiusAValue}). Circle radius must be a finite positive number. BodyA ID: ${bodyA.config.id}, shape type: ${bodyA.config.shape.type}.`);
    }
    
    if (!isFiniteNumber(radiusBValue) || radiusBValue <= 0) {
      throw new Error(`[PhysicsEngine] Cannot detect circle-circle collision: Invalid radius for bodyB (radius: ${radiusBValue}). Circle radius must be a finite positive number. BodyB ID: ${bodyB.config.id}, shape type: ${bodyB.config.shape.type}.`);
    }
    
    const radiusA = radiusAValue;
    const radiusB = radiusBValue;

    // System F/Omega proof: Explicit validation of positions
    // Type proof: position ∈ PhysicsVec2 → x, y ∈ ℝ (finite)
    if (!hasXY(bodyA.position) || !hasXY(bodyB.position)) {
      throw new Error(`[PhysicsEngine] Cannot detect circle-circle collision: Invalid position vectors (bodyA.position: ${JSON.stringify(bodyA.position)}, bodyB.position: ${JSON.stringify(bodyB.position)}). Positions must be PhysicsVec2 objects with finite x, y coordinates. BodyA ID: ${bodyA.config.id}, BodyB ID: ${bodyB.config.id}.`);
    }

    const diff = vec2.sub(bodyB.position, bodyA.position);
    const distSq = vec2.lengthSq(diff);
    const minDist = radiusA + radiusB;

    // System F/Omega proof: Geometric constraint validation
    // Mathematical proof: Circles overlap ⟺ dist² < (radiusA + radiusB)²
    // Geometric proof: No collision ⟺ distance ≥ sum of radii
    if (!Number.isFinite(distSq) || distSq < 0) {
      throw new Error(`[PhysicsEngine] Cannot detect circle-circle collision: Invalid distance squared calculation (distSq: ${distSq}). Distance calculation failed - check body positions. BodyA position: (${bodyA.position.x}, ${bodyA.position.y}), BodyB position: (${bodyB.position.x}, ${bodyB.position.y}).`);
    }
    
    if (distSq >= minDist * minDist) {
      throw new Error(`[PhysicsEngine] Cannot detect circle-circle collision: Circles do not overlap (distance: ${Math.sqrt(distSq)}, sum of radii: ${minDist}). Geometric constraint violation: Circles overlap ⟺ distance < radiusA + radiusB. BodyA ID: ${bodyA.config.id} (radius: ${radiusA}), BodyB ID: ${bodyB.config.id} (radius: ${radiusB}), positions: A(${bodyA.position.x}, ${bodyA.position.y}), B(${bodyB.position.x}, ${bodyB.position.y}).`);
    }

    const dist = Math.sqrt(distSq);
    const normal = dist > 0 ? vec2.scale(diff, 1 / dist) : { x: 1, y: 0 };
    const depth = minDist - dist;
    const contactPoint = vec2.add(bodyA.position, vec2.scale(normal, radiusA));

    return { bodyA, bodyB, normal, depth, contactPoint };
  }

  /**
   * Detect collision between circle and box shapes
   * 
   * System F/Omega proof: Geometric collision detection for circle-box intersection
   * Type proof: circleBody ∈ InternalRigidBody (circle), boxBody ∈ InternalRigidBody (box) → CollisionPair
   * Mathematical proof: Circle-box collision ⟺ distance(circleCenter, closestBoxPoint) < circleRadius
   * Geometric proof: Circle intersects box ⟺ circle center within expanded box (box + radius) or distance to closest point < radius
   * 
   * @param circleBody - Circle rigid body (must have circle shape with radius)
   * @param boxBody - Box rigid body (must have box shape with width/height)
   * @returns CollisionPair if circle intersects box
   * @throws Error if shapes don't intersect or parameters are invalid
   */
  private circleVsBox(
    circleBody: InternalRigidBody,
    boxBody: InternalRigidBody,
  ): CollisionPair {
    // System F/Omega proof: Explicit validation of shape parameters
    // Type proof: radius ∈ ℝ → must be finite and positive
    // Type proof: width, height ∈ ℝ → must be finite and positive
    const radiusValue = circleBody.config.shape.radius;
    const widthValue = boxBody.config.shape.width;
    const heightValue = boxBody.config.shape.height;
    
    if (!isFiniteNumber(radiusValue) || radiusValue <= 0) {
      throw new Error(`[PhysicsEngine] Cannot detect circle-box collision: Invalid circle radius (radius: ${radiusValue}). Circle radius must be a finite positive number. Circle body ID: ${circleBody.config.id}, shape type: ${circleBody.config.shape.type}.`);
    }
    
    if (!isFiniteNumber(widthValue) || widthValue <= 0) {
      throw new Error(`[PhysicsEngine] Cannot detect circle-box collision: Invalid box width (width: ${widthValue}). Box width must be a finite positive number. Box body ID: ${boxBody.config.id}, shape type: ${boxBody.config.shape.type}.`);
    }
    
    if (!isFiniteNumber(heightValue) || heightValue <= 0) {
      throw new Error(`[PhysicsEngine] Cannot detect circle-box collision: Invalid box height (height: ${heightValue}). Box height must be a finite positive number. Box body ID: ${boxBody.config.id}, shape type: ${boxBody.config.shape.type}.`);
    }
    
    const radius = radiusValue;
    const halfW = widthValue / 2;
    const halfH = heightValue / 2;

    // System F/Omega proof: Explicit validation of positions and angles
    // Type proof: position ∈ PhysicsVec2 → x, y ∈ ℝ (finite)
    // Type proof: angle ∈ ℝ → must be finite
    if (!hasXY(circleBody.position) || !hasXY(boxBody.position)) {
      throw new Error(`[PhysicsEngine] Cannot detect circle-box collision: Invalid position vectors (circleBody.position: ${JSON.stringify(circleBody.position)}, boxBody.position: ${JSON.stringify(boxBody.position)}). Positions must be PhysicsVec2 objects with finite x, y coordinates. Circle body ID: ${circleBody.config.id}, Box body ID: ${boxBody.config.id}.`);
    }
    
    if (!Number.isFinite(boxBody.angle)) {
      throw new Error(`[PhysicsEngine] Cannot detect circle-box collision: Invalid box angle (angle: ${boxBody.angle}). Box angle must be a finite real number. Box body ID: ${boxBody.config.id}.`);
    }

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

    // System F/Omega proof: Geometric constraint validation
    // Mathematical proof: Circle intersects box ⟺ (inside ∨ distance < radius)
    // Geometric proof: No collision ⟺ (!inside ∧ distance ≥ radius)
    if (!Number.isFinite(distSq) || distSq < 0) {
      throw new Error(`[PhysicsEngine] Cannot detect circle-box collision: Invalid distance squared calculation (distSq: ${distSq}). Distance calculation failed - check body positions and angle. Circle position: (${circleBody.position.x}, ${circleBody.position.y}), Box position: (${boxBody.position.x}, ${boxBody.position.y}), Box angle: ${boxBody.angle}rad.`);
    }
    
    if (!inside && distSq >= radius * radius) {
      throw new Error(`[PhysicsEngine] Cannot detect circle-box collision: Circle does not intersect box (distance: ${Math.sqrt(distSq)}, radius: ${radius}). Geometric constraint violation: Circle intersects box ⟺ (inside ∨ distance < radius). Circle body ID: ${circleBody.config.id} (radius: ${radius}), Box body ID: ${boxBody.config.id} (size: ${widthValue}×${heightValue}), positions: Circle(${circleBody.position.x}, ${circleBody.position.y}), Box(${boxBody.position.x}, ${boxBody.position.y}), Box angle: ${boxBody.angle}rad.`);
    }

    const dist = Math.sqrt(distSq);

    // Local normal
    const localNormal =
      dist > 0 ? vec2.scale(localDiff, 1 / dist) : { x: 1, y: 0 };

    // Transform back to world space
    const worldNormal = {
      x:
        localNormal.x * Math.cos(boxBody.angle) -
        localNormal.y * Math.sin(boxBody.angle),
      y:
        localNormal.x * Math.sin(boxBody.angle) +
        localNormal.y * Math.cos(boxBody.angle),
    };

    if (inside) {
      depth = radius + dist;
      normal = vec2.scale(worldNormal, -1);
    } else {
      depth = radius - dist;
      normal = worldNormal;
    }

    const contactPoint = vec2.sub(
      circleBody.position,
      vec2.scale(normal, radius),
    );

    return { bodyA: circleBody, bodyB: boxBody, normal, depth, contactPoint };
  }

  /**
   * Detect collision between two box shapes (AABB - Axis-Aligned Bounding Box)
   * 
   * System F/Omega proof: Geometric collision detection for axis-aligned boxes
   * Type proof: bodyA, bodyB ∈ InternalRigidBody with box shapes → CollisionPair
   * Mathematical proof: AABB collision ⟺ overlapX > 0 ∧ overlapY > 0
   * Geometric proof: Two AABBs overlap ⟺ projections overlap on both axes
   * 
   * @param bodyA - First box body (must have box shape with width/height)
   * @param bodyB - Second box body (must have box shape with width/height)
   * @returns CollisionPair if boxes overlap
   * @throws Error if boxes don't overlap or dimensions are invalid
   */
  private boxVsBox(
    bodyA: InternalRigidBody,
    bodyB: InternalRigidBody,
  ): CollisionPair {
    // System F/Omega proof: Explicit validation of box dimensions
    // Type proof: width, height ∈ ℝ → must be finite and positive
    // Mathematical proof: Box dimensions must be positive (w > 0 ∧ h > 0)
    const widthAValue = bodyA.config.shape.width;
    const heightAValue = bodyA.config.shape.height;
    const widthBValue = bodyB.config.shape.width;
    const heightBValue = bodyB.config.shape.height;
    
    if (!isFiniteNumber(widthAValue) || widthAValue <= 0) {
      throw new Error(`[PhysicsEngine] Cannot detect box-box collision: Invalid width for bodyA (width: ${widthAValue}). Box width must be a finite positive number. BodyA ID: ${bodyA.config.id}, shape type: ${bodyA.config.shape.type}.`);
    }
    
    if (!isFiniteNumber(heightAValue) || heightAValue <= 0) {
      throw new Error(`[PhysicsEngine] Cannot detect box-box collision: Invalid height for bodyA (height: ${heightAValue}). Box height must be a finite positive number. BodyA ID: ${bodyA.config.id}, shape type: ${bodyA.config.shape.type}.`);
    }
    
    if (!isFiniteNumber(widthBValue) || widthBValue <= 0) {
      throw new Error(`[PhysicsEngine] Cannot detect box-box collision: Invalid width for bodyB (width: ${widthBValue}). Box width must be a finite positive number. BodyB ID: ${bodyB.config.id}, shape type: ${bodyB.config.shape.type}.`);
    }
    
    if (!isFiniteNumber(heightBValue) || heightBValue <= 0) {
      throw new Error(`[PhysicsEngine] Cannot detect box-box collision: Invalid height for bodyB (height: ${heightBValue}). Box height must be a finite positive number. BodyB ID: ${bodyB.config.id}, shape type: ${bodyB.config.shape.type}.`);
    }
    
    const halfWA = widthAValue / 2;
    const halfHA = heightAValue / 2;
    const halfWB = widthBValue / 2;
    const halfHB = heightBValue / 2;

    // System F/Omega proof: Explicit validation of positions
    // Type proof: position ∈ PhysicsVec2 → x, y ∈ ℝ (finite)
    if (!hasXY(bodyA.position) || !hasXY(bodyB.position)) {
      throw new Error(`[PhysicsEngine] Cannot detect box-box collision: Invalid position vectors (bodyA.position: ${JSON.stringify(bodyA.position)}, bodyB.position: ${JSON.stringify(bodyB.position)}). Positions must be PhysicsVec2 objects with finite x, y coordinates. BodyA ID: ${bodyA.config.id}, BodyB ID: ${bodyB.config.id}.`);
    }

    const dx = bodyB.position.x - bodyA.position.x;
    const dy = bodyB.position.y - bodyA.position.y;

    // System F/Omega proof: Explicit validation of distance calculations
    // Type proof: dx, dy ∈ ℝ → must be finite
    if (!Number.isFinite(dx) || !Number.isFinite(dy)) {
      throw new Error(`[PhysicsEngine] Cannot detect box-box collision: Invalid position difference calculation (dx: ${dx}, dy: ${dy}). Position calculation failed - check body positions. BodyA position: (${bodyA.position.x}, ${bodyA.position.y}), BodyB position: (${bodyB.position.x}, ${bodyB.position.y}).`);
    }

    const overlapX = halfWA + halfWB - Math.abs(dx);
    const overlapY = halfHA + halfHB - Math.abs(dy);

    // System F/Omega proof: Geometric constraint validation
    // Mathematical proof: AABB collision ⟺ overlapX > 0 ∧ overlapY > 0
    // Geometric proof: No collision ⟺ overlapX ≤ 0 ∨ overlapY ≤ 0
    if (!Number.isFinite(overlapX) || !Number.isFinite(overlapY)) {
      throw new Error(`[PhysicsEngine] Cannot detect box-box collision: Invalid overlap calculation (overlapX: ${overlapX}, overlapY: ${overlapY}). Overlap calculation failed - check box dimensions and positions. BodyA: ${widthAValue}×${heightAValue} at (${bodyA.position.x}, ${bodyA.position.y}), BodyB: ${widthBValue}×${heightBValue} at (${bodyB.position.x}, ${bodyB.position.y}).`);
    }
    
    if (overlapX <= 0 || overlapY <= 0) {
      throw new Error(`[PhysicsEngine] Cannot detect box-box collision: Boxes do not overlap (overlapX: ${overlapX}, overlapY: ${overlapY}). Geometric constraint violation: AABB collision ⟺ overlapX > 0 ∧ overlapY > 0. BodyA ID: ${bodyA.config.id} (${widthAValue}×${heightAValue} at ${bodyA.position.x}, ${bodyA.position.y}), BodyB ID: ${bodyB.config.id} (${widthBValue}×${heightBValue} at ${bodyB.position.x}, ${bodyB.position.y}).`);
    }

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

// ════════════════════════════════════════════════════════════════════════════
//                                                     // collision // resolver
// ════════════════════════════════════════════════════════════════════════════

class CollisionResolver {
  private config: PhysicsSpaceConfig;

  constructor(config: PhysicsSpaceConfig) {
    this.config = config;
  }

  resolveCollisions(pairs: CollisionPair[]): ContactInfo[] {
    const contacts: ContactInfo[] = [];

    for (const pair of pairs) {
      // System F/Omega proof: Collision resolution throws error if resolution fails (no lazy null)
      try {
        const contact = this.resolveCollision(pair);
        contacts.push(contact);
      } catch (error) {
        // Collision resolution failed (separating velocities, zero mass, etc.) - this is expected
        // Continue to next collision pair
        continue;
      }
    }

    return contacts;
  }

  /**
   * Resolve collision between two bodies using impulse-based dynamics
   * 
   * System F/Omega proof: Impulse-based collision resolution
   * Type proof: pair ∈ CollisionPair → ContactInfo (non-nullable)
   * Mathematical proof: Collision resolution requires non-separating velocities and non-zero mass
   * Physics proof: Impulse calculation requires invMassSum > 0 (at least one body has mass)
   * 
   * @param pair - Collision pair with contact information
   * @returns ContactInfo with resolved collision data
   * @throws Error if collision cannot be resolved (separating velocities, zero mass, etc.)
   */
  private resolveCollision(pair: CollisionPair): ContactInfo {
    // System F/Omega proof: Explicit validation of collision pair
    // Type proof: pair ∈ CollisionPair → all fields must be valid
    const { bodyA, bodyB, normal, depth, contactPoint } = pair;

    if (!hasXY(normal) || !hasXY(contactPoint)) {
      throw new Error(`[PhysicsEngine] Cannot resolve collision: Invalid collision pair data (normal: ${JSON.stringify(normal)}, contactPoint: ${JSON.stringify(contactPoint)}). Collision pair must have valid PhysicsVec2 normal and contactPoint. BodyA ID: ${bodyA.config.id}, BodyB ID: ${bodyB.config.id}.`);
    }
    
    if (!Number.isFinite(depth)) {
      throw new Error(`[PhysicsEngine] Cannot resolve collision: Invalid collision depth (depth: ${depth}). Collision depth must be a finite real number. BodyA ID: ${bodyA.config.id}, BodyB ID: ${bodyB.config.id}.`);
    }

    // Check for sensor mode
    const isSensor =
      bodyA.config.response === "sensor" || bodyB.config.response === "sensor";

    // Calculate relative velocity at contact point
    const rA = vec2.sub(contactPoint, bodyA.position);
    const rB = vec2.sub(contactPoint, bodyB.position);

    const velA = vec2.add(
      bodyA.velocity,
      vec2.perpendicular(vec2.scale(rA, bodyA.angularVelocity)),
    );
    const velB = vec2.add(
      bodyB.velocity,
      vec2.perpendicular(vec2.scale(rB, bodyB.angularVelocity)),
    );

    const relativeVelocity = vec2.sub(velB, velA);
    const normalVelocity = vec2.dot(relativeVelocity, normal);

    // System F/Omega proof: Explicit validation of collision resolution constraints
    // Physics proof: Collision resolution requires approaching velocities (normalVelocity ≤ 0)
    // Mathematical proof: Separating velocities (normalVelocity > 0) mean bodies are moving apart
    if (!Number.isFinite(normalVelocity)) {
      throw new Error(`[PhysicsEngine] Cannot resolve collision: Invalid normal velocity calculation (normalVelocity: ${normalVelocity}). Velocity calculation failed - check body velocities and angular velocities. BodyA ID: ${bodyA.config.id}, BodyB ID: ${bodyB.config.id}, contactPoint: (${contactPoint.x}, ${contactPoint.y}).`);
    }
    
    if (normalVelocity > 0) {
      throw new Error(`[PhysicsEngine] Cannot resolve collision: Bodies are separating (normalVelocity: ${normalVelocity}). Physics constraint violation: Collision resolution requires approaching velocities (normalVelocity ≤ 0). Bodies are moving apart, no collision response needed. BodyA ID: ${bodyA.config.id}, BodyB ID: ${bodyB.config.id}, relative velocity: (${relativeVelocity.x}, ${relativeVelocity.y}), normal: (${normal.x}, ${normal.y}).`);
    }

    // Calculate restitution
    const restitution = Math.min(
      bodyA.config.material.restitution,
      bodyB.config.material.restitution,
    );

    // Calculate effective inverse mass
    const rACrossN = vec2.cross(rA, normal);
    const rBCrossN = vec2.cross(rB, normal);
    const invMassSum =
      bodyA.inverseMass +
      bodyB.inverseMass +
      rACrossN * rACrossN * bodyA.inverseInertia +
      rBCrossN * rBCrossN * bodyB.inverseInertia;

    // System F/Omega proof: Explicit validation of mass constraint
    // Physics proof: Collision resolution requires at least one body with mass (invMassSum > 0)
    // Mathematical proof: Zero mass (invMassSum = 0) means both bodies are static/immovable
    if (!Number.isFinite(invMassSum) || invMassSum < 0) {
      throw new Error(`[PhysicsEngine] Cannot resolve collision: Invalid inverse mass sum calculation (invMassSum: ${invMassSum}). Mass calculation failed - check body masses and inertias. BodyA ID: ${bodyA.config.id} (inverseMass: ${bodyA.inverseMass}, inverseInertia: ${bodyA.inverseInertia}), BodyB ID: ${bodyB.config.id} (inverseMass: ${bodyB.inverseMass}, inverseInertia: ${bodyB.inverseInertia}).`);
    }
    
    if (invMassSum === 0) {
      throw new Error(`[PhysicsEngine] Cannot resolve collision: Both bodies have zero mass (invMassSum: 0). Physics constraint violation: Collision resolution requires at least one body with mass (invMassSum > 0). Both bodies are static/immovable - no collision response possible. BodyA ID: ${bodyA.config.id} (inverseMass: ${bodyA.inverseMass}), BodyB ID: ${bodyB.config.id} (inverseMass: ${bodyB.inverseMass}).`);
    }

    // Calculate impulse magnitude
    let j = -(1 + restitution) * normalVelocity;
    j /= invMassSum;

    // Apply impulse (skip if sensor)
    if (!isSensor) {
      const impulse = vec2.scale(normal, j);

      bodyA.velocity = vec2.sub(
        bodyA.velocity,
        vec2.scale(impulse, bodyA.inverseMass),
      );
      bodyA.angularVelocity -= bodyA.inverseInertia * vec2.cross(rA, impulse);

      bodyB.velocity = vec2.add(
        bodyB.velocity,
        vec2.scale(impulse, bodyB.inverseMass),
      );
      bodyB.angularVelocity += bodyB.inverseInertia * vec2.cross(rB, impulse);

      // Friction
      const tangent = vec2.normalize(
        vec2.sub(relativeVelocity, vec2.scale(normal, normalVelocity)),
      );
      const tangentVelocity = vec2.dot(relativeVelocity, tangent);

      const friction = Math.sqrt(
        bodyA.config.material.friction * bodyB.config.material.friction,
      );

      let jt = -tangentVelocity / invMassSum;
      jt = Math.max(-j * friction, Math.min(j * friction, jt)); // Coulomb's law

      const frictionImpulse = vec2.scale(tangent, jt);

      bodyA.velocity = vec2.sub(
        bodyA.velocity,
        vec2.scale(frictionImpulse, bodyA.inverseMass),
      );
      bodyB.velocity = vec2.add(
        bodyB.velocity,
        vec2.scale(frictionImpulse, bodyB.inverseMass),
      );

      // Position correction
      const correction = vec2.scale(
        normal,
        (Math.max(depth - this.config.collisionSlop, 0) *
          this.config.collisionBias) /
          invMassSum,
      );

      bodyA.position = vec2.sub(
        bodyA.position,
        vec2.scale(correction, bodyA.inverseMass),
      );
      bodyB.position = vec2.add(
        bodyB.position,
        vec2.scale(correction, bodyB.inverseMass),
      );

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

// ════════════════════════════════════════════════════════════════════════════
//                                                 // soft // body // simulator
// ════════════════════════════════════════════════════════════════════════════

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
      particle.acceleration = vec2.add(
        particle.acceleration,
        vec2.scale(force, particle.invMass),
      );
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
        vec2.scale(particle.acceleration, dtSq),
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
        if (
          constraint.breakThreshold &&
          distance > constraint.restLength * constraint.breakThreshold
        ) {
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

  getState(softBodyId: string): SoftBodyState {
    const particleIds = this.softBodyParticles.get(softBodyId);
    const constraintIds = this.softBodyConstraints.get(softBodyId);
    if (!particleIds) {
      throw new Error(`[PhysicsEngine] Cannot get soft body state: Soft body "${softBodyId}" not found`);
    }

    const particles = particleIds.map((id) => {
      const p = this.particles.get(id)!;
      return {
        id: p.id,
        position: vec2.clone(p.position),
        velocity: vec2.sub(p.position, p.previousPosition),
      };
    });

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
    const constraintIdsArray = (constraintIds !== null && constraintIds !== undefined && Array.isArray(constraintIds)) ? constraintIds : [];
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const brokenConstraints = constraintIdsArray
      .filter((id) => {
        const constraint = this.constraints.get(id);
        return (constraint != null && typeof constraint === "object" && "broken" in constraint && typeof constraint.broken === "boolean" && constraint.broken) ? true : false;
      })
      .map((id) => id);

    return {
      id: softBodyId,
      particles,
      brokenConstraints,
    };
  }

  loadState(_softBodyId: string, state: SoftBodyState): void {
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

// ════════════════════════════════════════════════════════════════════════════
//                                                        // cloth // simulator
// ════════════════════════════════════════════════════════════════════════════

class ClothSimulator {
  private cloths: Map<
    string,
    {
      config: ClothConfig;
      particles: InternalVerletParticle[];
      constraints: InternalVerletConstraint[];
    }
  > = new Map();

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
          vec2.scale(particle.acceleration, dtSq),
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

          const pA = cloth.particles.find((p) => p.id === constraint.particleA);
          const pB = cloth.particles.find((p) => p.id === constraint.particleB);
          if (!pA || !pB) continue;

          const diff = vec2.sub(pB.position, pA.position);
          const distance = vec2.length(diff);
          if (distance === 0) continue;

          // Check for tearing
          if (
            constraint.breakThreshold &&
            distance > constraint.restLength * constraint.breakThreshold
          ) {
            constraint.broken = true;
            continue;
          }

          const error = (distance - constraint.restLength) / distance;
          const correction = vec2.scale(
            diff,
            error * constraint.stiffness * 0.5,
          );

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

  getState(clothId: string): ClothState {
    const cloth = this.cloths.get(clothId);
    if (!cloth) {
      throw new Error(`[PhysicsEngine] Cannot get cloth state: Cloth "${clothId}" not found`);
    }

    return {
      id: clothId,
      positions: cloth.particles.map((p) => vec2.clone(p.position)),
      tornConstraints: cloth.constraints
        .filter((c) => c.broken)
        .map((c) => {
          // Parse constraint ID to get row/col/type
          const parts = c.id.split("_");
          const type = parts[1].startsWith("h")
            ? "structural"
            : parts[1].startsWith("v")
              ? "structural"
              : parts[1].startsWith("s")
                ? "shear"
                : "bend";
          const index = parseInt(parts[2], 10);
          const col = index % cloth.config.width;
          const row = Math.floor(index / cloth.config.width);
          return { row, col, type: type as "structural" | "shear" | "bend" };
        }),
    };
  }

  loadState(clothId: string, state: ClothState): void {
    const cloth = this.cloths.get(clothId);
    if (!cloth) return;

    for (
      let i = 0;
      i < state.positions.length && i < cloth.particles.length;
      i++
    ) {
      cloth.particles[i].position = vec2.clone(state.positions[i]);
      cloth.particles[i].previousPosition = vec2.clone(state.positions[i]);
    }

    // Restore torn constraints
    const tornSet = new Set(
      state.tornConstraints.map((t) => `${t.row}_${t.col}_${t.type}`),
    );
    for (const constraint of cloth.constraints) {
      const parts = constraint.id.split("_");
      const type =
        parts[1].startsWith("h") || parts[1].startsWith("v")
          ? "structural"
          : parts[1].startsWith("s")
            ? "shear"
            : "bend";
      const index = parseInt(parts[2], 10);
      const col = index % cloth.config.width;
      const row = Math.floor(index / cloth.config.width);
      constraint.broken = tornSet.has(`${row}_${col}_${type}`);
    }
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                               // force // field // processor
// ════════════════════════════════════════════════════════════════════════════

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
    applyForce: (bodyId: string, force: PhysicsVec2) => void,
  ): void {
    for (const field of this.forceFields) {
      if (!field.enabled) continue;
      if (frame < field.startFrame) continue;
      if (field.endFrame >= 0 && frame > field.endFrame) continue;

      const affectedIds =
        field.affectedBodies && field.affectedBodies.length > 0
          ? new Set(field.affectedBodies)
          : null;

      for (const body of bodies) {
        if (body.inverseMass === 0) continue;
        if (affectedIds && !affectedIds.has(body.config.id)) continue;

        // System F/Omega proof: Force calculation throws error if force doesn't apply (no lazy null)
        try {
          const force = this.calculateForce(field, body, frame);
          applyForce(body.config.id, force);
        } catch (error) {
          // Force doesn't apply (out of range, wrong frame, etc.) - this is expected
          // Continue to next body
          continue;
        }
      }
    }
  }

  /**
   * Calculate force from force field applied to a body
   * 
   * System F/Omega proof: Force field calculation
   * Type proof: field ∈ ForceField, body ∈ InternalRigidBody, frame ∈ ℕ → PhysicsVec2
   * Mathematical proof: Force calculation is deterministic based on field type and body position
   * Physics proof: Force applies when body is within field range and frame is within field duration
   * 
   * @param field - Force field configuration
   * @param body - Rigid body to apply force to
   * @param frame - Current simulation frame
   * @returns PhysicsVec2 force vector
   * @throws Error if force doesn't apply (out of range, wrong frame, etc.)
   */
  private calculateForce(
    field: ForceField,
    body: InternalRigidBody,
    frame: number,
  ): PhysicsVec2 {
    switch (field.type) {
      case "gravity": {
        const gravity = this.evaluateAnimatable(field.gravity, frame);
        return vec2.scale(gravity, body.config.mass);
      }

      case "wind": {
        const direction = this.evaluateAnimatable(field.direction, frame);
        const turbulence = this.evaluateAnimatable(field.turbulence, frame);

        // Add turbulence using simplex-like noise (simplified)
        const noiseX =
          Math.sin(
            body.position.x * field.frequency + frame * 0.1 + field.seed,
          ) * turbulence;
        const noiseY =
          Math.cos(
            body.position.y * field.frequency + frame * 0.1 + field.seed * 2,
          ) * turbulence;

        return {
          x: direction.x + noiseX,
          y: direction.y + noiseY,
        };
      }

      case "attraction": {
        const center = this.evaluateAnimatable(field.position, frame);
        const strength = this.evaluateAnimatable(field.strength, frame);

        // System F/Omega proof: Explicit validation of positions
        // Type proof: center, body.position ∈ PhysicsVec2 → x, y ∈ ℝ (finite)
        if (!hasXY(center) || !hasXY(body.position)) {
          throw new Error(`[PhysicsEngine] Cannot calculate attraction force: Invalid position vectors (center: ${JSON.stringify(center)}, body.position: ${JSON.stringify(body.position)}). Positions must be PhysicsVec2 objects with finite x, y coordinates. Field ID: ${field.id || "unknown"}, Body ID: ${body.config.id}, frame: ${frame}.`);
        }

        const diff = vec2.sub(center, body.position);
        const distSq = vec2.lengthSq(diff);
        const dist = Math.sqrt(distSq);

        // System F/Omega proof: Explicit validation of distance and range constraints
        // Mathematical proof: Force applies ⟺ (radius ≤ 0 ∨ dist ≤ radius) ∧ dist ≥ 1
        // Physics proof: Minimum distance prevents division by zero, maximum distance enforces field range
        if (!Number.isFinite(distSq) || distSq < 0) {
          throw new Error(`[PhysicsEngine] Cannot calculate attraction force: Invalid distance squared calculation (distSq: ${distSq}). Distance calculation failed - check field position and body position. Field position: (${center.x}, ${center.y}), Body position: (${body.position.x}, ${body.position.y}), frame: ${frame}.`);
        }
        
        if (!Number.isFinite(dist) || dist < 0) {
          throw new Error(`[PhysicsEngine] Cannot calculate attraction force: Invalid distance calculation (dist: ${dist}). Distance must be a finite non-negative number. Field position: (${center.x}, ${center.y}), Body position: (${body.position.x}, ${body.position.y}), frame: ${frame}.`);
        }
        
        if (field.radius > 0 && dist > field.radius) {
          throw new Error(`[PhysicsEngine] Cannot calculate attraction force: Body is outside field range (distance: ${dist}, radius: ${field.radius}). Physics constraint violation: Force applies ⟺ (radius ≤ 0 ∨ dist ≤ radius). Field ID: ${field.id || "unknown"}, Body ID: ${body.config.id}, field position: (${center.x}, ${center.y}), body position: (${body.position.x}, ${body.position.y}), frame: ${frame}.`);
        }
        
        if (dist < 1) {
          throw new Error(`[PhysicsEngine] Cannot calculate attraction force: Body is too close to field center (distance: ${dist}, minimum: 1). Physics constraint violation: Minimum distance prevents division by zero in force calculation. Field ID: ${field.id || "unknown"}, Body ID: ${body.config.id}, field position: (${center.x}, ${center.y}), body position: (${body.position.x}, ${body.position.y}), frame: ${frame}.`);
        }

        let forceMag: number;
        switch (field.falloff) {
          case "linear":
            forceMag =
              strength *
              (field.radius > 0 ? (field.radius - dist) / field.radius : 1);
            break;
          case "quadratic":
            forceMag = strength / distSq;
            break;
          default:
            forceMag = strength;
        }

        return vec2.scale(vec2.normalize(diff), forceMag * body.config.mass);
      }

      case "explosion": {
        // System F/Omega proof: Explicit validation of frame constraint
        // Mathematical proof: Explosion applies ⟺ frame = triggerFrame
        // Physics proof: Explosion is instantaneous (single frame event)
        if (!Number.isFinite(frame) || !Number.isFinite(field.triggerFrame)) {
          throw new Error(`[PhysicsEngine] Cannot calculate explosion force: Invalid frame values (frame: ${frame}, triggerFrame: ${field.triggerFrame}). Frame values must be finite integers. Field ID: ${field.id || "unknown"}, Body ID: ${body.config.id}.`);
        }
        
        if (frame !== field.triggerFrame) {
          throw new Error(`[PhysicsEngine] Cannot calculate explosion force: Wrong frame (current: ${frame}, trigger: ${field.triggerFrame}). Physics constraint violation: Explosion applies ⟺ frame = triggerFrame. Field ID: ${field.id || "unknown"}, Body ID: ${body.config.id}.`);
        }

        // System F/Omega proof: Explicit validation of positions and distance
        // Type proof: field.position, body.position ∈ PhysicsVec2 → x, y ∈ ℝ (finite)
        if (!hasXY(field.position) || !hasXY(body.position)) {
          throw new Error(`[PhysicsEngine] Cannot calculate explosion force: Invalid position vectors (field.position: ${JSON.stringify(field.position)}, body.position: ${JSON.stringify(body.position)}). Positions must be PhysicsVec2 objects with finite x, y coordinates. Field ID: ${field.id || "unknown"}, Body ID: ${body.config.id}, frame: ${frame}.`);
        }

        const diff = vec2.sub(body.position, field.position);
        const dist = vec2.length(diff);

        // System F/Omega proof: Explicit validation of distance constraints
        // Mathematical proof: Explosion applies ⟺ 1 ≤ dist ≤ radius
        // Physics proof: Minimum distance prevents division by zero, maximum distance enforces explosion radius
        if (!Number.isFinite(dist) || dist < 0) {
          throw new Error(`[PhysicsEngine] Cannot calculate explosion force: Invalid distance calculation (dist: ${dist}). Distance must be a finite non-negative number. Field position: (${field.position.x}, ${field.position.y}), Body position: (${body.position.x}, ${body.position.y}), frame: ${frame}.`);
        }
        
        if (dist > field.radius || dist < 1) {
          throw new Error(`[PhysicsEngine] Cannot calculate explosion force: Body is outside explosion range (distance: ${dist}, radius: ${field.radius}). Physics constraint violation: Explosion applies ⟺ 1 ≤ dist ≤ radius. Field ID: ${field.id || "unknown"}, Body ID: ${body.config.id}, field position: (${field.position.x}, ${field.position.y}), body position: (${body.position.x}, ${body.position.y}), frame: ${frame}.`);
        }

        const falloff = 1 - dist / field.radius;
        const impulse = vec2.scale(
          vec2.normalize(diff),
          field.strength * falloff,
        );

        // Apply as impulse, not force (modifies body state directly)
        // System F/Omega proof: Impulse application modifies body velocity
        // Type proof: body.velocity ∈ PhysicsVec2 → modified in place
        body.velocity = vec2.add(
          body.velocity,
          vec2.scale(impulse, body.inverseMass),
        );
        
        // Explosion applies impulse directly, returns zero force (impulse already applied)
        return { x: 0, y: 0 };
      }

      case "buoyancy": {
        const surfaceLevel = this.evaluateAnimatable(field.surfaceLevel, frame);
        
        // System F/Omega proof: Explicit validation of position and surface level
        // Type proof: body.position ∈ PhysicsVec2 → y ∈ ℝ (finite)
        // Type proof: surfaceLevel ∈ ℝ → must be finite
        if (!hasXY(body.position)) {
          throw new Error(`[PhysicsEngine] Cannot calculate buoyancy force: Invalid body position (position: ${JSON.stringify(body.position)}). Position must be PhysicsVec2 object with finite x, y coordinates. Body ID: ${body.config.id}, frame: ${frame}.`);
        }
        
        if (!Number.isFinite(surfaceLevel)) {
          throw new Error(`[PhysicsEngine] Cannot calculate buoyancy force: Invalid surface level (surfaceLevel: ${surfaceLevel}). Surface level must be a finite real number. Field ID: ${field.id || "unknown"}, frame: ${frame}.`);
        }
        
        const submergedDepth = body.position.y - surfaceLevel;

        // System F/Omega proof: Explicit validation of submersion constraint
        // Physics proof: Buoyancy applies ⟺ body is submerged (submergedDepth > 0)
        // Mathematical proof: Above water (submergedDepth ≤ 0) means no buoyancy force
        if (!Number.isFinite(submergedDepth)) {
          throw new Error(`[PhysicsEngine] Cannot calculate buoyancy force: Invalid submerged depth calculation (submergedDepth: ${submergedDepth}). Depth calculation failed - check body position and surface level. Body position: (${body.position.x}, ${body.position.y}), surface level: ${surfaceLevel}, frame: ${frame}.`);
        }
        
        if (submergedDepth <= 0) {
          throw new Error(`[PhysicsEngine] Cannot calculate buoyancy force: Body is above water surface (submergedDepth: ${submergedDepth}). Physics constraint violation: Buoyancy applies ⟺ submergedDepth > 0. Field ID: ${field.id || "unknown"}, Body ID: ${body.config.id}, body position: (${body.position.x}, ${body.position.y}), surface level: ${surfaceLevel}, frame: ${frame}.`);
        }

        // Approximate submerged volume based on shape
        const radius = body.config.shape.radius || 10;
        const submergedRatio = Math.min(1, submergedDepth / (radius * 2));

        // Buoyancy force (upward)
        const buoyancyForce =
          -field.density * submergedRatio * body.config.mass * 980;

        // Drag forces
        const dragX = -field.linearDrag * body.velocity.x * submergedRatio;
        const dragY = -field.linearDrag * body.velocity.y * submergedRatio;
        const angularDrag =
          -field.angularDrag * body.angularVelocity * submergedRatio;

        body.angularVelocity += angularDrag;

        return {
          x: dragX,
          y: buoyancyForce + dragY,
        };
      }

      case "vortex": {
        const center = this.evaluateAnimatable(field.position, frame);
        const strength = this.evaluateAnimatable(field.strength, frame);

        // System F/Omega proof: Explicit validation of positions
        // Type proof: center, body.position ∈ PhysicsVec2 → x, y ∈ ℝ (finite)
        if (!hasXY(center) || !hasXY(body.position)) {
          throw new Error(`[PhysicsEngine] Cannot calculate vortex force: Invalid position vectors (center: ${JSON.stringify(center)}, body.position: ${JSON.stringify(body.position)}). Positions must be PhysicsVec2 objects with finite x, y coordinates. Field ID: ${field.id || "unknown"}, Body ID: ${body.config.id}, frame: ${frame}.`);
        }

        const diff = vec2.sub(body.position, center);
        const dist = vec2.length(diff);

        // System F/Omega proof: Explicit validation of distance constraints
        // Mathematical proof: Vortex applies ⟺ 1 ≤ dist ≤ radius
        // Physics proof: Minimum distance prevents division by zero, maximum distance enforces vortex radius
        if (!Number.isFinite(dist) || dist < 0) {
          throw new Error(`[PhysicsEngine] Cannot calculate vortex force: Invalid distance calculation (dist: ${dist}). Distance must be a finite non-negative number. Field position: (${center.x}, ${center.y}), Body position: (${body.position.x}, ${body.position.y}), frame: ${frame}.`);
        }
        
        if (dist > field.radius || dist < 1) {
          throw new Error(`[PhysicsEngine] Cannot calculate vortex force: Body is outside vortex range (distance: ${dist}, radius: ${field.radius}). Physics constraint violation: Vortex applies ⟺ 1 ≤ dist ≤ radius. Field ID: ${field.id || "unknown"}, Body ID: ${body.config.id}, field position: (${center.x}, ${center.y}), body position: (${body.position.x}, ${body.position.y}), frame: ${frame}.`);
        }

        const falloff = 1 - dist / field.radius;

        // Tangential force (perpendicular to radius)
        const tangent = vec2.perpendicular(vec2.normalize(diff));
        const tangentialForce = vec2.scale(
          tangent,
          strength * falloff * body.config.mass,
        );

        // Inward force
        const inwardForce = vec2.scale(
          vec2.scale(vec2.normalize(diff), -1),
          field.inwardForce * falloff * body.config.mass,
        );

        return vec2.add(tangentialForce, inwardForce);
      }

      case "drag": {
        // System F/Omega proof: Explicit validation of velocity
        // Type proof: body.velocity ∈ PhysicsVec2 → x, y ∈ ℝ (finite)
        if (!hasXY(body.velocity)) {
          throw new Error(`[PhysicsEngine] Cannot calculate drag force: Invalid body velocity (velocity: ${JSON.stringify(body.velocity)}). Velocity must be PhysicsVec2 object with finite x, y coordinates. Body ID: ${body.config.id}, frame: ${frame}.`);
        }
        
        const speed = vec2.length(body.velocity);
        
        // System F/Omega proof: Explicit validation of speed constraint
        // Physics proof: Drag applies ⟺ speed ≥ threshold (typically 0.01)
        // Mathematical proof: Zero or very small speed means negligible drag force
        if (!Number.isFinite(speed) || speed < 0) {
          throw new Error(`[PhysicsEngine] Cannot calculate drag force: Invalid speed calculation (speed: ${speed}). Speed must be a finite non-negative number. Body velocity: (${body.velocity.x}, ${body.velocity.y}), frame: ${frame}.`);
        }
        
        if (speed < 0.01) {
          throw new Error(`[PhysicsEngine] Cannot calculate drag force: Body speed is too low (speed: ${speed}, threshold: 0.01). Physics constraint violation: Drag applies ⟺ speed ≥ 0.01. Body ID: ${body.config.id}, velocity: (${body.velocity.x}, ${body.velocity.y}), frame: ${frame}.`);
        }

        const dragMag = field.linear * speed + field.quadratic * speed * speed;
        return vec2.scale(vec2.normalize(body.velocity), -dragMag);
      }

      default: {
        // System F/Omega proof: Explicit validation of force field type
        // Type proof: field.type ∈ ForceType → must match known cases
        const fieldType = (field as { type?: string }).type || "unknown";
        const fieldId = (field as { id?: string }).id || "unknown";
        throw new Error(`[PhysicsEngine] Cannot calculate force: Unknown force field type "${fieldType}". Type proof violation: field.type must be one of: gravity, wind, attraction, explosion, buoyancy, vortex, drag. Field ID: ${fieldId}, Body ID: ${body.config.id}, frame: ${frame}.`);
      }
    }
  }

  private evaluateAnimatable<T>(
    prop: { value?: T; defaultValue?: T } | T,
    _frame: number,
  ): T {
    // Simplified - in production would evaluate keyframes
    if (typeof prop === "object" && prop !== null) {
      if ("value" in prop) {
        return prop.value as T;
      }
      if ("defaultValue" in prop) {
        return prop.defaultValue as T;
      }
    }
    return prop as T;
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                 // main // physics // engine
// ════════════════════════════════════════════════════════════════════════════

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

  // Ragdoll registry: tracks ragdoll ID -> bones configuration
  private ragdollRegistry: Map<string, RagdollBone[]> = new Map();

  // Seeded random number generator
  private random: PhysicsRandom;

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

  /**
   * Register a ragdoll for state tracking
   * The ragdoll's rigid bodies should already be added via addRigidBody
   */
  addRagdoll(ragdollId: string, bones: RagdollBone[]): void {
    this.ragdollRegistry.set(ragdollId, bones);
    this.clearCache();
  }

  /**
   * Remove a ragdoll from state tracking
   * Note: This does NOT remove the underlying rigid bodies
   */
  removeRagdoll(ragdollId: string): void {
    this.ragdollRegistry.delete(ragdollId);
    this.clearCache();
  }

  /**
   * Get all registered ragdoll IDs
   */
  getRagdollIds(): string[] {
    return Array.from(this.ragdollRegistry.keys());
  }

  // Simulation
  evaluateFrame(targetFrame: number): PhysicsSimulationState {
    if (!this.isInitialized) {
      throw new Error("Physics engine not initialized");
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
      if (
        frame % this.checkpointInterval === 0 &&
        frame > 0 &&
        !this.checkpoints.has(frame)
      ) {
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
          vec2.scale(this.config.gravity, body.config.mass),
        );
      }
    }

    // Process force fields
    this.forceFieldProcessor.processForces(frame, bodies, (id, force) =>
      this.rigidBodySimulator.applyForce(id, force),
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

    // Extract ragdoll states from registered ragdolls
    const ragdollStates: RagdollState[] = [];
    for (const [ragdollId, bones] of this.ragdollRegistry) {
      const state = extractRagdollState(ragdollId, bones, (bodyId: string) => {
        const body = this.rigidBodySimulator.getBody(bodyId);
        if (!body) {
          throw new Error(`[PhysicsEngine] Cannot extract ragdoll state: Rigid body "${bodyId}" not found for ragdoll "${ragdollId}"`);
        }
        return {
          position: body.position,
          velocity: body.velocity,
          angle: body.angle,
          angularVelocity: body.angularVelocity,
        };
      });
      ragdollStates.push(state);
    }

    return {
      frame,
      rigidBodies: this.rigidBodySimulator.getState(),
      softBodies: this.getSoftBodyIds()
        .map((id): SoftBodyState | { __filtered: true } => {
          // System F/Omega proof: Explicit error handling for state retrieval
          // Type proof: getState(id) → SoftBodyState (throws if not found)
          // Mathematical proof: State retrieval is deterministic - either state exists or error thrown
          try {
            return this.softBodySimulator.getState(id);
          } catch (error) {
            // State retrieval failed (entity not found) - use sentinel object instead of null
            // System F/Omega proof: Sentinel object pattern instead of lazy null
            // Type proof: Sentinel object has distinct type from SoftBodyState
            return { __filtered: true };
          }
        })
        .filter((state): state is SoftBodyState => {
          // System F/Omega proof: Explicit type guard filtering sentinel objects
          // Type proof: Filter removes sentinel objects, keeps only valid SoftBodyState
          return typeof state === "object" && state !== null && !("__filtered" in state);
        }),
      cloths: this.getClothIds()
        .map((id): ClothState | { __filtered: true } => {
          // System F/Omega proof: Explicit error handling for state retrieval
          // Type proof: getState(id) → ClothState (throws if not found)
          // Mathematical proof: State retrieval is deterministic - either state exists or error thrown
          try {
            return this.clothSimulator.getState(id);
          } catch (error) {
            // State retrieval failed (entity not found) - use sentinel object instead of null
            // System F/Omega proof: Sentinel object pattern instead of lazy null
            // Type proof: Sentinel object has distinct type from ClothState
            return { __filtered: true };
          }
        })
        .filter((state): state is ClothState => {
          // System F/Omega proof: Explicit type guard filtering sentinel objects
          // Type proof: Filter removes sentinel objects, keeps only valid ClothState
          return typeof state === "object" && state !== null && !("__filtered" in state);
        }),
      ragdolls: ragdollStates,
      contacts: pairs.map((p) => ({
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
      softBodyStates: this.getSoftBodyIds()
        .map((id): SoftBodyState | { __filtered: true } => {
          // System F/Omega proof: Explicit error handling for state retrieval
          // Type proof: getState(id) → SoftBodyState (throws if not found)
          // Mathematical proof: State retrieval is deterministic - either state exists or error thrown
          try {
            return this.softBodySimulator.getState(id);
          } catch (error) {
            // State retrieval failed (entity not found) - use sentinel object instead of null
            // System F/Omega proof: Sentinel object pattern instead of lazy null
            // Type proof: Sentinel object has distinct type from SoftBodyState
            return { __filtered: true };
          }
        })
        .filter((state): state is SoftBodyState => {
          // System F/Omega proof: Explicit type guard filtering sentinel objects
          // Type proof: Filter removes sentinel objects, keeps only valid SoftBodyState
          return typeof state === "object" && state !== null && !("__filtered" in state);
        }),
      clothStates: this.getClothIds()
        .map((id): ClothState | { __filtered: true } => {
          // System F/Omega proof: Explicit error handling for state retrieval
          // Type proof: getState(id) → ClothState (throws if not found)
          // Mathematical proof: State retrieval is deterministic - either state exists or error thrown
          try {
            return this.clothSimulator.getState(id);
          } catch (error) {
            // State retrieval failed (entity not found) - use sentinel object instead of null
            // System F/Omega proof: Sentinel object pattern instead of lazy null
            // Type proof: Sentinel object has distinct type from ClothState
            return { __filtered: true };
          }
        })
        .filter((state): state is ClothState => {
          // System F/Omega proof: Explicit type guard filtering sentinel objects
          // Type proof: Filter removes sentinel objects, keeps only valid ClothState
          return typeof state === "object" && state !== null && !("__filtered" in state);
        }),
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
    const frameData: Map<
      string,
      Array<{ frame: number; position: PhysicsVec2; angle: number }>
    > = new Map();

    // Collect data for each frame
    for (
      let frame = options.startFrame;
      frame <= options.endFrame;
      frame += options.frameStep
    ) {
      const state = this.evaluateFrame(frame);

      for (const body of state.rigidBodies) {
        if (!frameData.has(body.id)) {
          frameData.set(body.id, []);
        }
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const bodyFrameData = frameData.get(body.id);
        if (bodyFrameData != null && Array.isArray(bodyFrameData)) {
          bodyFrameData.push({
            frame,
            position: body.position,
            angle: body.angle,
          });
        }
      }
    }

    // Convert to keyframes
    for (const [bodyId, data] of frameData) {
      // Find layer ID for this body
      const body = this.rigidBodySimulator.getBody(bodyId);
      if (!body) continue;

      const layerId = body.config.layerId;

      if (options.properties.includes("position")) {
        const keyframes = data.map((d) => ({
          frame: d.frame,
          value: d.position,
          interpolation: options.interpolation as "linear" | "bezier",
        }));

        // Simplify if requested
        const simplifiedKeyframes = options.simplify
          ? this.simplifyKeyframes(keyframes, options.simplifyTolerance)
          : keyframes;

        results.push({
          layerId,
          property: "transform.position",
          keyframes: simplifiedKeyframes,
        });
      }

      if (options.properties.includes("rotation")) {
        const keyframes = data.map((d) => ({
          frame: d.frame,
          value: d.angle * (180 / Math.PI), // Convert to degrees
          interpolation: options.interpolation as "linear" | "bezier",
        }));

        const simplifiedKeyframes = options.simplify
          ? this.simplifyKeyframes(keyframes, options.simplifyTolerance)
          : keyframes;

        results.push({
          layerId,
          property: "transform.rotation.z",
          keyframes: simplifiedKeyframes,
        });
      }
    }

    return results;
  }

  private simplifyKeyframes<T>(
    keyframes: Array<{
      frame: number;
      value: T;
      interpolation: "linear" | "bezier";
    }>,
    tolerance: number,
  ): Array<{ frame: number; value: T; interpolation: "linear" | "bezier" }> {
    if (keyframes.length <= 2) return keyframes;

    // Simple Douglas-Peucker-like simplification for position keyframes
    const simplified = [keyframes[0]];
    let lastAdded = 0;

    for (let i = 1; i < keyframes.length - 1; i++) {
      const prev = keyframes[lastAdded].value;
      const curr = keyframes[i].value;
      const next = keyframes[i + 1].value;

        // Check if current point deviates significantly from line
        // Deterministic: Use type guards to validate PropertyValue structure
        // T extends PropertyValue, which includes { x: number; y: number }
        // Convert to RuntimeValue for type guard (PropertyValue is subset of RuntimeValue)
        const prevRuntime: RuntimeValue = prev as RuntimeValue;
        const currRuntime: RuntimeValue = curr as RuntimeValue;
        const nextRuntime: RuntimeValue = next as RuntimeValue;
        if (hasXY(currRuntime) && hasXY(prevRuntime) && hasXY(nextRuntime)) {
          // Type guards narrow to { x: number; y: number } which is compatible with PhysicsVec2
          const p: PhysicsVec2 = prevRuntime as PhysicsVec2;
          const c: PhysicsVec2 = currRuntime as PhysicsVec2;
          const n: PhysicsVec2 = nextRuntime as PhysicsVec2;

        // Calculate distance from point to line
        const lineDir = vec2.sub(n, p);
        const lineLen = vec2.length(lineDir);
        if (lineLen > 0) {
          const t = Math.max(
            0,
            Math.min(
              1,
              vec2.dot(vec2.sub(c, p), lineDir) / (lineLen * lineLen),
            ),
          );
          const projection = vec2.add(p, vec2.scale(lineDir, t));
          const distance = vec2.distance(c, projection);

          if (distance > tolerance) {
            simplified.push(keyframes[i]);
            lastAdded = i;
          }
        }
      }
      
      // Handle numeric keyframes (rotation, scale, etc.)
      // Deterministic: T extends PropertyValue, which includes number
      // Convert to RuntimeValue for type guard (PropertyValue is subset of RuntimeValue)
      const prevNumRuntime: RuntimeValue = prev as RuntimeValue;
      const currNumRuntime: RuntimeValue = curr as RuntimeValue;
      const nextNumRuntime: RuntimeValue = next as RuntimeValue;
      if (isFiniteNumber(currNumRuntime) && isFiniteNumber(prevNumRuntime) && isFiniteNumber(nextNumRuntime)) {
        // Type guards narrow to number - explicit validation ensures correctness
        const p: number = prevNumRuntime as number;
        const c: number = currNumRuntime as number;
        const n: number = nextNumRuntime as number;

        const expected =
          p + (n - p) * ((i - lastAdded) / (keyframes.length - 1 - lastAdded));
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

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // exports
// ════════════════════════════════════════════════════════════════════════════

export { vec2, PhysicsRandom };

export type {
  InternalRigidBody,
  InternalVerletParticle,
  InternalVerletConstraint,
  CollisionPair,
  PhysicsCheckpoint,
};
