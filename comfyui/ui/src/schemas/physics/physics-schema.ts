/**
 * Physics Schemas
 *
 * Zod schemas for physics simulation types.
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import { finiteNumber, normalized01, positiveFinite, nonNegativeFinite } from "../layers/primitives-schema";
import {
  entityId,
  boundedArray,
  MAX_ARRAY_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Physics Enums
// ═══════════════════════════════════════════════════════════════════════════

export const BodyTypeSchema = z.enum([
  "static",
  "dynamic",
  "kinematic",
  "dormant",
  "AEmatic",
  "dead",
]);

export type BodyType = z.infer<typeof BodyTypeSchema>;

export const JointTypeSchema = z.enum([
  "pivot",
  "spring",
  "distance",
  "piston",
  "wheel",
  "weld",
  "blob",
  "rope",
]);

export type JointType = z.infer<typeof JointTypeSchema>;

export const ForceTypeSchema = z.enum([
  "gravity",
  "wind",
  "attraction",
  "explosion",
  "buoyancy",
  "vortex",
  "drag",
]);

export type ForceType = z.infer<typeof ForceTypeSchema>;

export const ShapeTypeSchema = z.enum([
  "circle",
  "box",
  "polygon",
  "capsule",
  "convex",
  "compound",
]);

export type ShapeType = z.infer<typeof ShapeTypeSchema>;

export const CollisionResponseSchema = z.enum([
  "collide",
  "sensor",
  "none",
]);

export type CollisionResponse = z.infer<typeof CollisionResponseSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Core Physics Types
// ═══════════════════════════════════════════════════════════════════════════

export const PhysicsVec2Schema = z.object({
  x: finiteNumber,
  y: finiteNumber,
}).strict();

export type PhysicsVec2 = z.infer<typeof PhysicsVec2Schema>;

export const PhysicsMaterialSchema = z.object({
  restitution: normalized01,
  friction: nonNegativeFinite.max(10), // Max reasonable friction
  surfaceVelocity: PhysicsVec2Schema.optional(),
}).strict();

export type PhysicsMaterial = z.infer<typeof PhysicsMaterialSchema>;

export const CollisionShapeSchema: z.ZodType<any> = z.lazy(() =>
  z.object({
    type: ShapeTypeSchema,
    radius: positiveFinite.max(10000).optional(),
    width: positiveFinite.max(10000).optional(),
    height: positiveFinite.max(10000).optional(),
    vertices: boundedArray(PhysicsVec2Schema, 1000).optional(), // Max 1000 vertices per polygon
    length: positiveFinite.max(10000).optional(),
    shapes: boundedArray(CollisionShapeSchema, 100).optional(), // Max 100 nested shapes
    offset: PhysicsVec2Schema.optional(),
    rotation: finiteNumber.optional(),
  }).strict().refine(
    (data) => {
      // Circle requires radius
      if (data.type === "circle" && data.radius === undefined) {
        return false;
      }
      // Box requires width and height
      if (data.type === "box" && (data.width === undefined || data.height === undefined)) {
        return false;
      }
      // Polygon requires vertices
      if (data.type === "polygon" && (!data.vertices || data.vertices.length < 3)) {
        return false;
      }
      // Capsule requires radius and length
      if (data.type === "capsule" && (data.radius === undefined || data.length === undefined)) {
        return false;
      }
      // Compound requires shapes
      if (data.type === "compound" && (!data.shapes || data.shapes.length === 0)) {
        return false;
      }
      return true;
    },
    { message: "Shape type requires appropriate properties" }
  )
);

export type CollisionShape = z.infer<typeof CollisionShapeSchema>;

export const CollisionFilterSchema = z.object({
  category: z.number().int().nonnegative().max(32), // Max 32 categories (bitmask)
  mask: z.number().int().nonnegative().max(4294967295), // Max 32-bit unsigned int
  group: z.number().int().max(32767).min(-32768), // 16-bit signed int range
}).strict();

export type CollisionFilter = z.infer<typeof CollisionFilterSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Rigid Body
// ═══════════════════════════════════════════════════════════════════════════

export const RigidBodyConfigSchema = z.object({
  id: entityId,
  layerId: entityId,
  type: BodyTypeSchema,
  mass: positiveFinite.max(1000000), // Max reasonable mass (1M kg)
  moment: positiveFinite.max(1000000000).optional(), // Max reasonable moment of inertia
  position: PhysicsVec2Schema,
  velocity: PhysicsVec2Schema.refine(
    (v) => Math.abs(v.x) < 10000 && Math.abs(v.y) < 10000,
    { message: "Velocity components must be within reasonable range" }
  ),
  angle: finiteNumber,
  angularVelocity: finiteNumber.max(1000).min(-1000), // Max reasonable angular velocity (rad/s)
  shape: CollisionShapeSchema,
  material: PhysicsMaterialSchema,
  filter: CollisionFilterSchema,
  response: CollisionResponseSchema,
  linearDamping: normalized01,
  angularDamping: normalized01,
  fixedRotation: z.boolean().optional(),
  bullet: z.boolean().optional(),
  canSleep: z.boolean(),
  sleepThreshold: positiveFinite.max(100), // Max reasonable sleep threshold
}).strict();

export type RigidBodyConfig = z.infer<typeof RigidBodyConfigSchema>;

export const ContactInfoSchema = z.object({
  bodyA: entityId,
  bodyB: entityId,
  point: PhysicsVec2Schema,
  normal: PhysicsVec2Schema.refine(
    (n) => {
      const length = Math.sqrt(n.x * n.x + n.y * n.y);
      return Math.abs(length - 1.0) < 0.01; // Normalized vector
    },
    { message: "Normal vector must be normalized" }
  ),
  depth: positiveFinite.max(10000),
}).strict().refine(
  (data) => data.bodyA !== data.bodyB,
  { message: "bodyA and bodyB must be different", path: ["bodyB"] }
);

export type ContactInfo = z.infer<typeof ContactInfoSchema>;

export const RigidBodyStateSchema = z.object({
  id: entityId,
  position: PhysicsVec2Schema,
  velocity: PhysicsVec2Schema,
  angle: finiteNumber,
  angularVelocity: finiteNumber,
  isSleeping: z.boolean(),
  contacts: boundedArray(ContactInfoSchema, 1000), // Max 1000 contacts per body
}).strict();

export type RigidBodyState = z.infer<typeof RigidBodyStateSchema>;
