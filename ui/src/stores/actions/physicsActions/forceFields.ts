/**
 * Physics Actions - Force Field Management
 *
 * Add, remove, and configure force fields including gravity.
 */

import { createGravityForce } from "@/services/physics";
import type { ForceField } from "@/types/physics";
import { storeLogger } from "@/utils/logger";
import { getPhysicsEngine } from "./engine";
import type { PhysicsStore } from "./types";

// ============================================================================
// FORCE FIELDS STORAGE
// ============================================================================

/** Track force fields locally */
const compositionForceFields = new Map<string, ForceField[]>();

// ============================================================================
// FORCE FIELD OPERATIONS
// ============================================================================

/**
 * Add a force field to the physics simulation
 */
export function addForceField(store: PhysicsStore, force: ForceField): void {
  const engine = getPhysicsEngine(store);
  const compId = store.activeCompositionId;

  // Get existing force fields for this composition
  const fields = compositionForceFields.get(compId) || [];
  const existingIndex = fields.findIndex((f) => f.id === force.id);

  if (existingIndex >= 0) {
    fields[existingIndex] = force;
  } else {
    fields.push(force);
  }

  compositionForceFields.set(compId, fields);
  engine.setForceFields(fields);
  storeLogger.info("Force field added:", force.id);
}

/**
 * Remove a force field
 */
export function removeForceField(store: PhysicsStore, forceId: string): void {
  const engine = getPhysicsEngine(store);
  const compId = store.activeCompositionId;

  const fields = compositionForceFields.get(compId) || [];
  const newFields = fields.filter((f) => f.id !== forceId);

  compositionForceFields.set(compId, newFields);
  engine.setForceFields(newFields);
  storeLogger.info("Force field removed:", forceId);
}

/**
 * Set global gravity
 */
export function setGravity(
  store: PhysicsStore,
  gravityX: number,
  gravityY: number,
): void {
  // Validate gravity values
  const safeGravityX = Number.isFinite(gravityX) ? gravityX : 0;
  const safeGravityY = Number.isFinite(gravityY) ? gravityY : 0;

  const engine = getPhysicsEngine(store);
  const compId = store.activeCompositionId;

  // Get existing force fields
  const fields = compositionForceFields.get(compId) || [];

  // Remove existing gravity force if any
  const newFields = fields.filter((f) => f.id !== "global-gravity");

  // Add new gravity force
  const gravityForce = createGravityForce("global-gravity", {
    x: safeGravityX,
    y: safeGravityY,
  });
  newFields.push(gravityForce);

  compositionForceFields.set(compId, newFields);
  engine.setForceFields(newFields);

  storeLogger.info("Gravity set to:", gravityX, gravityY);
}
