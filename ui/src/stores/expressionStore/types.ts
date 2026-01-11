/**
 * Expression Store Types
 *
 * Type definitions for expression and property driver operations.
 */

import type { Layer } from "@/types/project";
import type { PropertyDriver } from "@/services/propertyDriver";

/**
 * Interface for accessing compositor store from expression actions.
 * Uses dependency injection to avoid circular imports.
 *
 * Note: Using `any` for propertyDriverSystem because Pinia reactive proxies
 * wrap class instances and modify their type signatures. This is the same
 * pattern used in propertyDriverActions.ts.
 */
export interface ExpressionStoreAccess {
  /** Project metadata */
  project: {
    meta: { modified: string };
  };
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  /** Property driver system instance (any due to Pinia proxy) */
  propertyDriverSystem: any;
  /** Serializable driver configs */
  propertyDrivers: PropertyDriver[];
  /** Get the currently active composition */
  getActiveComp(): { currentFrame: number; settings: { fps: number; frameCount: number }; layers: Layer[] } | null;
  /** Get all layers in active composition */
  getActiveCompLayers(): Layer[];
  /** Get layer by ID */
  getLayerById(id: string): Layer | null;
  /** Get FPS from active composition */
  readonly fps: number;
  /** Get current frame */
  readonly currentFrame: number;
  /** Get frame count */
  readonly frameCount: number;
  /** Push history state */
  pushHistory(): void;
  /** Get property value at frame (for driver evaluation) */
  getPropertyValueAtFrame(layerId: string, propertyPath: string, frame: number): number | null;
  /** Evaluate property at frame with expression support (for baking) */
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  evaluatePropertyAtFrame(layerId: string, propertyPath: string, frame: number): any;
}

/**
 * State for expression store
 */
export interface ExpressionState {
  // Expression store doesn't own state - expressions are stored on keyframes
  // and drivers are stored on compositorStore.propertyDrivers
  // This is a thin wrapper that coordinates these systems
}
