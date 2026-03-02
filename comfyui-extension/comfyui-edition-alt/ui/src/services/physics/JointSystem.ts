/**
 * @module services/physics/JointSystem
 * @description Joint constraint system for connecting rigid bodies.
 *
 * Supports 8 joint types:
 * - Pivot: Rotation around single point (pin joint)
 * - Spring: Springy connection with stiffness/damping
 * - Distance: Fixed distance constraint
 * - Piston: Slide along axis with limits
 * - Wheel: Motor-driven rotation with suspension
 * - Weld: Rigid connection (no relative movement)
 * - Blob: Soft connection for deformable shapes
 * - Rope: One-way constraint (max distance only)
 */

import type {
  BlobJointConfig,
  DistanceJointConfig,
  JointConfig,
  PhysicsVec2,
  PistonJointConfig,
  PivotJointConfig,
  RopeJointConfig,
  SpringJointConfig,
  WeldJointConfig,
  WheelJointConfig,
} from "@/types/physics";

import { vec2 } from "./PhysicsEngine";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                             // internal // body // interface
// ════════════════════════════════════════════════════════════════════════════

interface JointBody {
  position: PhysicsVec2;
  velocity: PhysicsVec2;
  angle: number;
  angularVelocity: number;
  inverseMass: number;
  inverseInertia: number;
}

type GetBodyFn = (id: string) => JointBody | null;
type ApplyImpulseFn = (
  id: string,
  impulse: PhysicsVec2,
  point: PhysicsVec2,
) => void;

// ════════════════════════════════════════════════════════════════════════════
//                                             // joint // constraint // solver
// ════════════════════════════════════════════════════════════════════════════

/**
 * Joint constraint solver
 */
export class JointSystem {
  private joints: Map<string, JointConfig> = new Map();
  private brokenJoints: Set<string> = new Set();

  addJoint(config: JointConfig): void {
    this.joints.set(config.id, config);
  }

  removeJoint(id: string): void {
    this.joints.delete(id);
    this.brokenJoints.delete(id);
  }

  getJoint(id: string): JointConfig | undefined {
    return this.joints.get(id);
  }

  isJointBroken(id: string): boolean {
    return this.brokenJoints.has(id);
  }

  /**
   * Solve all joint constraints
   */
  solveConstraints(
    getBody: GetBodyFn,
    applyImpulse: ApplyImpulseFn,
    dt: number,
  ): void {
    for (const joint of this.joints.values()) {
      if (this.brokenJoints.has(joint.id)) continue;

      const bodyA =
        joint.bodyA === "world" ? this.getWorldBody() : getBody(joint.bodyA);
      const bodyB =
        joint.bodyB === "world" ? this.getWorldBody() : getBody(joint.bodyB);

      if (!bodyA || !bodyB) continue;

      const broken = this.solveJoint(joint, bodyA, bodyB, applyImpulse, dt);
      if (broken) {
        this.brokenJoints.add(joint.id);
      }
    }
  }

  private getWorldBody(): JointBody {
    return {
      position: { x: 0, y: 0 },
      velocity: { x: 0, y: 0 },
      angle: 0,
      angularVelocity: 0,
      inverseMass: 0,
      inverseInertia: 0,
    };
  }

  private solveJoint(
    joint: JointConfig,
    bodyA: JointBody,
    bodyB: JointBody,
    applyImpulse: ApplyImpulseFn,
    dt: number,
  ): boolean {
    switch (joint.type) {
      case "pivot":
        return this.solvePivotJoint(joint, bodyA, bodyB, applyImpulse);
      case "spring":
        return this.solveSpringJoint(joint, bodyA, bodyB, applyImpulse, dt);
      case "distance":
        return this.solveDistanceJoint(joint, bodyA, bodyB, applyImpulse);
      case "piston":
        return this.solvePistonJoint(joint, bodyA, bodyB, applyImpulse, dt);
      case "wheel":
        return this.solveWheelJoint(joint, bodyA, bodyB, applyImpulse, dt);
      case "weld":
        return this.solveWeldJoint(joint, bodyA, bodyB, applyImpulse);
      case "blob":
        return this.solveBlobJoint(joint, bodyA, bodyB, applyImpulse);
      case "rope":
        return this.solveRopeJoint(joint, bodyA, bodyB, applyImpulse);
      default:
        return false;
    }
  }

  /**
   * Pivot joint - rotation around single point
   */
  private solvePivotJoint(
    joint: PivotJointConfig,
    bodyA: JointBody,
    bodyB: JointBody,
    applyImpulse: ApplyImpulseFn,
  ): boolean {
    // Get world space anchor points
    const rA = vec2.rotate(joint.anchorA, bodyA.angle);
    const rB = vec2.rotate(joint.anchorB, bodyB.angle);

    const anchorA = vec2.add(bodyA.position, rA);
    const anchorB = vec2.add(bodyB.position, rB);

    // Position error
    const error = vec2.sub(anchorB, anchorA);
    const errorMag = vec2.length(error);

    // Check for breaking
    if (joint.maxForce && errorMag > joint.maxForce) {
      return true;
    }

    if (errorMag < 0.01) return false;

    // Calculate effective mass
    const rACrossN = vec2.cross(rA, error);
    const rBCrossN = vec2.cross(rB, error);
    const effectiveMass =
      bodyA.inverseMass +
      bodyB.inverseMass +
      rACrossN * rACrossN * bodyA.inverseInertia +
      rBCrossN * rBCrossN * bodyB.inverseInertia;

    if (effectiveMass === 0) return false;

    // Calculate impulse
    const impulse = vec2.scale(error, -1 / effectiveMass);

    // Apply impulse
    if (joint.bodyA !== "world") {
      applyImpulse(joint.bodyA, vec2.scale(impulse, -1), anchorA);
    }
    if (joint.bodyB !== "world") {
      applyImpulse(joint.bodyB, impulse, anchorB);
    }

    // Motor (if enabled)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const jointMotor = (joint != null && typeof joint === "object" && "motor" in joint && joint.motor != null && typeof joint.motor === "object") ? joint.motor : undefined;
    const motorEnabled = (jointMotor != null && typeof jointMotor === "object" && "enabled" in jointMotor && typeof jointMotor.enabled === "boolean" && jointMotor.enabled) ? true : false;
    if (motorEnabled && jointMotor !== undefined) {
      const relativeAngle = bodyB.angle - bodyA.angle;
      const motorSpeed = (typeof jointMotor.speed === "number") ? jointMotor.speed : 0;
      let targetAngularVelocity = motorSpeed;

      const motorTargetAngle = (jointMotor != null && typeof jointMotor === "object" && "targetAngle" in jointMotor && typeof jointMotor.targetAngle === "number") ? jointMotor.targetAngle : undefined;
      if (motorTargetAngle !== undefined) {
        // Servo mode
        const angleError = motorTargetAngle - relativeAngle;
        targetAngularVelocity = angleError * 5; // Simple P controller
      }

      const relativeAngularVelocity =
        bodyB.angularVelocity - bodyA.angularVelocity;
      const angularError = targetAngularVelocity - relativeAngularVelocity;

      const maxTorque = (jointMotor != null && typeof jointMotor === "object" && "maxTorque" in jointMotor && typeof jointMotor.maxTorque === "number") ? jointMotor.maxTorque : 0;
      const torqueImpulse = Math.max(
        -maxTorque,
        Math.min(maxTorque, angularError * 0.1),
      );

      // Apply angular impulse
      if (joint.bodyA !== "world" && bodyA.inverseInertia > 0) {
        bodyA.angularVelocity -= torqueImpulse * bodyA.inverseInertia;
      }
      if (joint.bodyB !== "world" && bodyB.inverseInertia > 0) {
        bodyB.angularVelocity += torqueImpulse * bodyB.inverseInertia;
      }
    }

    // Angle limits
    if (joint.limits) {
      const relativeAngle = bodyB.angle - bodyA.angle;
      if (relativeAngle < joint.limits.min) {
        const correction = (joint.limits.min - relativeAngle) * 0.1;
        if (bodyA.inverseInertia > 0) bodyA.angularVelocity -= correction;
        if (bodyB.inverseInertia > 0) bodyB.angularVelocity += correction;
      } else if (relativeAngle > joint.limits.max) {
        const correction = (relativeAngle - joint.limits.max) * 0.1;
        if (bodyA.inverseInertia > 0) bodyA.angularVelocity += correction;
        if (bodyB.inverseInertia > 0) bodyB.angularVelocity -= correction;
      }
    }

    return false;
  }

  /**
   * Spring joint - springy connection
   */
  private solveSpringJoint(
    joint: SpringJointConfig,
    bodyA: JointBody,
    bodyB: JointBody,
    applyImpulse: ApplyImpulseFn,
    dt: number,
  ): boolean {
    // Get world space anchor points
    const rA = vec2.rotate(joint.anchorA, bodyA.angle);
    const rB = vec2.rotate(joint.anchorB, bodyB.angle);

    const anchorA = vec2.add(bodyA.position, rA);
    const anchorB = vec2.add(bodyB.position, rB);

    // Calculate spring force
    const diff = vec2.sub(anchorB, anchorA);
    const distance = vec2.length(diff);

    if (distance < 0.001) return false;

    const direction = vec2.scale(diff, 1 / distance);
    const stretch = distance - joint.restLength;

    // Spring force (Hooke's law)
    const springForce = stretch * joint.stiffness;

    // Damping force
    const relativeVelocity = vec2.sub(
      vec2.add(
        bodyB.velocity,
        vec2.perpendicular(vec2.scale(rB, bodyB.angularVelocity)),
      ),
      vec2.add(
        bodyA.velocity,
        vec2.perpendicular(vec2.scale(rA, bodyA.angularVelocity)),
      ),
    );
    const dampingForce = vec2.dot(relativeVelocity, direction) * joint.damping;

    // Total force
    const totalForce = springForce + dampingForce;
    const impulse = vec2.scale(direction, totalForce * dt);

    // Check for breaking
    if (joint.maxForce && Math.abs(totalForce) > joint.maxForce) {
      return true;
    }

    // Apply impulse
    if (joint.bodyA !== "world") {
      applyImpulse(joint.bodyA, vec2.scale(impulse, -1), anchorA);
    }
    if (joint.bodyB !== "world") {
      applyImpulse(joint.bodyB, impulse, anchorB);
    }

    return false;
  }

  /**
   * Distance joint - fixed distance constraint
   */
  private solveDistanceJoint(
    joint: DistanceJointConfig,
    bodyA: JointBody,
    bodyB: JointBody,
    applyImpulse: ApplyImpulseFn,
  ): boolean {
    // Get world space anchor points
    const rA = vec2.rotate(joint.anchorA, bodyA.angle);
    const rB = vec2.rotate(joint.anchorB, bodyB.angle);

    const anchorA = vec2.add(bodyA.position, rA);
    const anchorB = vec2.add(bodyB.position, rB);

    // Calculate distance error
    const diff = vec2.sub(anchorB, anchorA);
    const distance = vec2.length(diff);

    if (distance < 0.001) return false;

    const error = distance - joint.distance;

    // Check for breaking
    if (joint.maxForce && Math.abs(error) > joint.maxForce) {
      return true;
    }

    const direction = vec2.scale(diff, 1 / distance);

    // Calculate effective mass
    const rACrossN = vec2.cross(rA, direction);
    const rBCrossN = vec2.cross(rB, direction);
    const effectiveMass =
      bodyA.inverseMass +
      bodyB.inverseMass +
      rACrossN * rACrossN * bodyA.inverseInertia +
      rBCrossN * rBCrossN * bodyB.inverseInertia;

    if (effectiveMass === 0) return false;

    // Calculate impulse
    const impulse = vec2.scale(direction, error / effectiveMass);

    // Apply impulse
    if (joint.bodyA !== "world") {
      applyImpulse(joint.bodyA, vec2.scale(impulse, -1), anchorA);
    }
    if (joint.bodyB !== "world") {
      applyImpulse(joint.bodyB, impulse, anchorB);
    }

    return false;
  }

  /**
   * Piston joint - slide along axis with limits
   */
  private solvePistonJoint(
    joint: PistonJointConfig,
    bodyA: JointBody,
    bodyB: JointBody,
    applyImpulse: ApplyImpulseFn,
    dt: number,
  ): boolean {
    // Get world space axis
    const axis = vec2.normalize(vec2.rotate(joint.axis, bodyA.angle));
    const perpAxis = vec2.perpendicular(axis);

    // Get world space anchor points
    const rA = vec2.rotate(joint.anchorA, bodyA.angle);
    const rB = vec2.rotate(joint.anchorB, bodyB.angle);

    const anchorA = vec2.add(bodyA.position, rA);
    const anchorB = vec2.add(bodyB.position, rB);

    const diff = vec2.sub(anchorB, anchorA);

    // Constrain perpendicular to axis (like pivot)
    const perpError = vec2.dot(diff, perpAxis);
    if (Math.abs(perpError) > 0.01) {
      const correction = vec2.scale(perpAxis, -perpError * 0.5);
      if (joint.bodyA !== "world") {
        applyImpulse(joint.bodyA, vec2.scale(correction, -1), anchorA);
      }
      if (joint.bodyB !== "world") {
        applyImpulse(joint.bodyB, correction, anchorB);
      }
    }

    // Check translation limits
    const translation = vec2.dot(diff, axis);
    if (joint.limits) {
      if (translation < joint.limits.min) {
        const correction = vec2.scale(
          axis,
          (joint.limits.min - translation) * 0.5,
        );
        if (joint.bodyA !== "world") {
          applyImpulse(joint.bodyA, vec2.scale(correction, -1), anchorA);
        }
        if (joint.bodyB !== "world") {
          applyImpulse(joint.bodyB, correction, anchorB);
        }
      } else if (translation > joint.limits.max) {
        const correction = vec2.scale(
          axis,
          (translation - joint.limits.max) * -0.5,
        );
        if (joint.bodyA !== "world") {
          applyImpulse(joint.bodyA, vec2.scale(correction, -1), anchorA);
        }
        if (joint.bodyB !== "world") {
          applyImpulse(joint.bodyB, correction, anchorB);
        }
      }
    }

    // Motor
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const jointMotor = (joint != null && typeof joint === "object" && "motor" in joint && joint.motor != null && typeof joint.motor === "object") ? joint.motor : undefined;
    const motorEnabled = (jointMotor != null && typeof jointMotor === "object" && "enabled" in jointMotor && typeof jointMotor.enabled === "boolean" && jointMotor.enabled) ? true : false;
    if (motorEnabled) {
      const relVel = vec2.dot(vec2.sub(bodyB.velocity, bodyA.velocity), axis);
      const motorSpeed = (jointMotor != null && typeof jointMotor === "object" && "speed" in jointMotor && typeof jointMotor.speed === "number") ? jointMotor.speed : 0;
      const motorMaxForce = (jointMotor != null && typeof jointMotor === "object" && "maxForce" in jointMotor && typeof jointMotor.maxForce === "number") ? jointMotor.maxForce : 0;
      const motorError = motorSpeed - relVel;
      const motorImpulse = Math.max(
        -motorMaxForce * dt,
        Math.min(motorMaxForce * dt, motorError * 0.5),
      );

      const impulse = vec2.scale(axis, motorImpulse);
      if (joint.bodyA !== "world") {
        applyImpulse(joint.bodyA, vec2.scale(impulse, -1), anchorA);
      }
      if (joint.bodyB !== "world") {
        applyImpulse(joint.bodyB, impulse, anchorB);
      }
    }

    return false;
  }

  /**
   * Wheel joint - motor-driven with suspension
   */
  private solveWheelJoint(
    joint: WheelJointConfig,
    bodyA: JointBody,
    bodyB: JointBody,
    applyImpulse: ApplyImpulseFn,
    dt: number,
  ): boolean {
    // Get world space axis (suspension direction)
    const axis = vec2.normalize(vec2.rotate(joint.axis, bodyA.angle));

    // Get world space anchor points
    const rA = vec2.rotate(joint.anchorA, bodyA.angle);
    const rB = vec2.rotate(joint.anchorB, bodyB.angle);

    const anchorA = vec2.add(bodyA.position, rA);
    const anchorB = vec2.add(bodyB.position, rB);

    const diff = vec2.sub(anchorB, anchorA);

    // Suspension spring (along axis)
    const suspensionOffset = vec2.dot(diff, axis);
    const suspensionVel = vec2.dot(
      vec2.sub(bodyB.velocity, bodyA.velocity),
      axis,
    );

    // Spring-damper formula
    const omega = 2 * Math.PI * joint.frequency;
    const c = 2 * joint.dampingRatio * omega;
    const springForce = omega * omega * suspensionOffset + c * suspensionVel;

    const suspensionImpulse = vec2.scale(axis, -springForce * dt);
    if (joint.bodyA !== "world") {
      applyImpulse(joint.bodyA, vec2.scale(suspensionImpulse, -1), anchorA);
    }
    if (joint.bodyB !== "world") {
      applyImpulse(joint.bodyB, suspensionImpulse, anchorB);
    }

    // Constrain perpendicular to axis
    const perpAxis = vec2.perpendicular(axis);
    const perpError = vec2.dot(diff, perpAxis);
    if (Math.abs(perpError) > 0.01) {
      const correction = vec2.scale(perpAxis, -perpError * 0.5);
      if (joint.bodyA !== "world") {
        applyImpulse(joint.bodyA, vec2.scale(correction, -1), anchorA);
      }
      if (joint.bodyB !== "world") {
        applyImpulse(joint.bodyB, correction, anchorB);
      }
    }

    // Motor (rotation)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const jointMotor = (joint != null && typeof joint === "object" && "motor" in joint && joint.motor != null && typeof joint.motor === "object") ? joint.motor : undefined;
    const motorEnabled = (jointMotor != null && typeof jointMotor === "object" && "enabled" in jointMotor && typeof jointMotor.enabled === "boolean" && jointMotor.enabled) ? true : false;
    if (motorEnabled) {
      const relativeAngularVelocity =
        bodyB.angularVelocity - bodyA.angularVelocity;
      const motorSpeed = (jointMotor != null && typeof jointMotor === "object" && "speed" in jointMotor && typeof jointMotor.speed === "number") ? jointMotor.speed : 0;
      const motorError = motorSpeed - relativeAngularVelocity;
      const maxTorque = (jointMotor != null && typeof jointMotor === "object" && "maxTorque" in jointMotor && typeof jointMotor.maxTorque === "number") ? jointMotor.maxTorque : 0;
      const torqueImpulse = Math.max(
        -maxTorque * dt,
        Math.min(maxTorque * dt, motorError * 0.5),
      );

      if (joint.bodyA !== "world" && bodyA.inverseInertia > 0) {
        bodyA.angularVelocity -= torqueImpulse * bodyA.inverseInertia;
      }
      if (joint.bodyB !== "world" && bodyB.inverseInertia > 0) {
        bodyB.angularVelocity += torqueImpulse * bodyB.inverseInertia;
      }
    }

    return false;
  }

  /**
   * Weld joint - rigid connection
   */
  private solveWeldJoint(
    joint: WeldJointConfig,
    bodyA: JointBody,
    bodyB: JointBody,
    applyImpulse: ApplyImpulseFn,
  ): boolean {
    // Position constraint (like pivot)
    const rA = vec2.rotate(joint.anchorA, bodyA.angle);
    const rB = vec2.rotate(joint.anchorB, bodyB.angle);

    const anchorA = vec2.add(bodyA.position, rA);
    const anchorB = vec2.add(bodyB.position, rB);

    const posError = vec2.sub(anchorB, anchorA);
    const posErrorMag = vec2.length(posError);

    if (posErrorMag > 0.01) {
      const effectiveMass = bodyA.inverseMass + bodyB.inverseMass;
      if (effectiveMass > 0) {
        const correction = vec2.scale(posError, 0.5 / effectiveMass);
        if (joint.bodyA !== "world") {
          applyImpulse(joint.bodyA, vec2.scale(correction, -1), anchorA);
        }
        if (joint.bodyB !== "world") {
          applyImpulse(joint.bodyB, correction, anchorB);
        }
      }
    }

    // Angle constraint
    const relativeAngle = bodyB.angle - bodyA.angle;
    const angleError = relativeAngle - joint.referenceAngle;

    if (Math.abs(angleError) > 0.01) {
      const angularCorrection = angleError * 0.5;

      if (joint.frequency && joint.frequency > 0) {
        // Soft weld - spring-like behavior
        const omega = 2 * Math.PI * joint.frequency;
        // Type proof: dampingRatio ∈ number | undefined → number (0-1 range, non-negative)
        const dampingRatio = joint.dampingRatio !== undefined && Number.isFinite(joint.dampingRatio) && joint.dampingRatio >= 0 && joint.dampingRatio <= 1
          ? joint.dampingRatio
          : 0.7;
        const c = 2 * dampingRatio * omega;

        const relAngVel = bodyB.angularVelocity - bodyA.angularVelocity;
        const torque = omega * omega * angleError + c * relAngVel;

        if (bodyA.inverseInertia > 0)
          bodyA.angularVelocity += torque * 0.5 * bodyA.inverseInertia;
        if (bodyB.inverseInertia > 0)
          bodyB.angularVelocity -= torque * 0.5 * bodyB.inverseInertia;
      } else {
        // Rigid weld
        if (bodyA.inverseInertia > 0)
          bodyA.angularVelocity += angularCorrection;
        if (bodyB.inverseInertia > 0)
          bodyB.angularVelocity -= angularCorrection;
      }
    }

    return false;
  }

  /**
   * Blob joint - soft connection
   */
  private solveBlobJoint(
    joint: BlobJointConfig,
    bodyA: JointBody,
    bodyB: JointBody,
    applyImpulse: ApplyImpulseFn,
  ): boolean {
    // Soft position constraint
    const rA = vec2.rotate(joint.anchorA, bodyA.angle);
    const rB = vec2.rotate(joint.anchorB, bodyB.angle);

    const anchorA = vec2.add(bodyA.position, rA);
    const anchorB = vec2.add(bodyB.position, rB);

    const diff = vec2.sub(anchorB, anchorA);
    const distance = vec2.length(diff);

    if (distance > 0.01) {
      // Apply soft spring force based on softness
      const stiffness = 1 / (1 + joint.softness);
      const correction = vec2.scale(diff, stiffness * 0.5);

      if (joint.bodyA !== "world") {
        applyImpulse(joint.bodyA, vec2.scale(correction, -1), anchorA);
      }
      if (joint.bodyB !== "world") {
        applyImpulse(joint.bodyB, correction, anchorB);
      }
    }

    // Pressure effect (push apart if too close)
    if (joint.pressure > 0 && distance < joint.pressure) {
      const pushForce = (joint.pressure - distance) * 0.1;
      const pushDir =
        distance > 0 ? vec2.scale(diff, 1 / distance) : { x: 1, y: 0 };
      const push = vec2.scale(pushDir, -pushForce);

      if (joint.bodyA !== "world") {
        applyImpulse(joint.bodyA, push, anchorA);
      }
      if (joint.bodyB !== "world") {
        applyImpulse(joint.bodyB, vec2.scale(push, -1), anchorB);
      }
    }

    return false;
  }

  /**
   * Rope joint - maximum distance constraint (one-way)
   */
  private solveRopeJoint(
    joint: RopeJointConfig,
    bodyA: JointBody,
    bodyB: JointBody,
    applyImpulse: ApplyImpulseFn,
  ): boolean {
    // Get world space anchor points
    const rA = vec2.rotate(joint.anchorA, bodyA.angle);
    const rB = vec2.rotate(joint.anchorB, bodyB.angle);

    const anchorA = vec2.add(bodyA.position, rA);
    const anchorB = vec2.add(bodyB.position, rB);

    // Calculate distance
    const diff = vec2.sub(anchorB, anchorA);
    const distance = vec2.length(diff);

    // Only constrain if beyond max length (rope is taut)
    if (distance <= joint.maxLength) return false;

    const error = distance - joint.maxLength;

    // Check for breaking
    if (joint.maxForce && error > joint.maxForce) {
      return true;
    }

    const direction = vec2.scale(diff, 1 / distance);

    // Calculate effective mass
    const rACrossN = vec2.cross(rA, direction);
    const rBCrossN = vec2.cross(rB, direction);
    const effectiveMass =
      bodyA.inverseMass +
      bodyB.inverseMass +
      rACrossN * rACrossN * bodyA.inverseInertia +
      rBCrossN * rBCrossN * bodyB.inverseInertia;

    if (effectiveMass === 0) return false;

    // Calculate impulse (only corrective, no push)
    const impulse = vec2.scale(direction, error / effectiveMass);

    // Apply impulse
    if (joint.bodyA !== "world") {
      applyImpulse(joint.bodyA, vec2.scale(impulse, -1), anchorA);
    }
    if (joint.bodyB !== "world") {
      applyImpulse(joint.bodyB, impulse, anchorB);
    }

    return false;
  }

  /**
   * Get all joints connecting to a body
   */
  getJointsForBody(bodyId: string): JointConfig[] {
    const result: JointConfig[] = [];
    for (const joint of this.joints.values()) {
      if (joint.bodyA === bodyId || joint.bodyB === bodyId) {
        result.push(joint);
      }
    }
    return result;
  }

  /**
   * Clear all joints
   */
  clear(): void {
    this.joints.clear();
    this.brokenJoints.clear();
  }

  /**
   * Get joint state for serialization
   */
  getState(): { id: string; broken: boolean }[] {
    return Array.from(this.joints.keys()).map((id) => ({
      id,
      broken: this.brokenJoints.has(id),
    }));
  }

  /**
   * Load joint state from serialization
   */
  loadState(states: { id: string; broken: boolean }[]): void {
    this.brokenJoints.clear();
    for (const state of states) {
      if (state.broken) {
        this.brokenJoints.add(state.id);
      }
    }
  }
}
