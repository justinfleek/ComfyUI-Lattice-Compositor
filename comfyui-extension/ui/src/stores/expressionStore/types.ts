/**
 * Expression Store Types
 *
 * Type definitions for expression and property driver operations.
 */

import type { Layer } from "@/types/project";
import type { PropertyDriver, PropertyPath, PropertyGetter } from "@/services/propertyDriver";
import type { AudioAnalysis } from "@/services/audioFeatures";

/**
 * Structural interface for PropertyDriverSystem methods actually used.
 * This avoids Pinia reactive proxy issues by only declaring the methods we call,
 * not the full class implementation.
 */
export interface PropertyDriverSystemAccess {
  setPropertyGetter(getter: PropertyGetter): void;
  setAudioAnalysis(analysis: AudioAnalysis | null): void;
  addDriver(driver: PropertyDriver): boolean;
  removeDriver(driverId: string): void;
  updateDriver(driverId: string, updates: Partial<PropertyDriver>): void;
  evaluateLayerDrivers(
    layerId: string,
    frame: number,
    baseValues: Map<PropertyPath, number>,
  ): Map<PropertyPath, number>;
}

/**
 * Interface for accessing compositor store from expression actions.
 * Uses dependency injection to avoid circular imports.
 *
 * NOTE: propertyDriverSystem and propertyDrivers are now stored in expressionStore state,
 * not in compositorStore. Expression store methods access them via useExpressionStore().
 */
export interface ExpressionStoreAccess {
  /** Project metadata */
  project: {
    composition: { width: number; height: number };
    meta: { modified: string };
  };
  /** Get the currently active composition */
  getActiveComp(): { currentFrame: number; settings: { fps: number; frameCount: number; duration: number; width: number; height: number }; layers: Layer[] } | null;
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
  /** Get property value at frame - returns null if layer not found or property unsupported */
  getPropertyValueAtFrame(layerId: string, propertyPath: string, frame: number): number | null;
  /** Evaluate property at frame with expression support - returns array for position/scale, number for scalars */
  evaluatePropertyAtFrame(layerId: string, propertyPath: string, frame: number): number[] | number | null;
}

/**
 * State for expression store
 */
export interface ExpressionState {
  /** Property driver system instance */
  propertyDriverSystem: PropertyDriverSystemAccess | null;
  /** Serializable driver configs */
  propertyDrivers: PropertyDriver[];
}
