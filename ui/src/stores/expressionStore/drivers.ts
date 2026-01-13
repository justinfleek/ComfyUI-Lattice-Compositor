/**
 * Property Driver Actions
 *
 * Property driver system for expressions and property linking.
 */

import { interpolateProperty } from "@/services/interpolation";
import {
  createAudioDriver,
  createPropertyLink,
  type PropertyDriver,
  PropertyDriverSystem,
  type PropertyPath,
} from "@/services/propertyDriver";
import { useAudioStore } from "@/stores/audioStore";
import { useExpressionStore } from "./index";
import { useLayerStore } from "@/stores/layerStore";
import { storeLogger } from "@/utils/logger";
import type { ExpressionStoreAccess } from "./types";

// Re-export PropertyPath for consumers
export type { PropertyPath };

/**
 * Initialize the property driver system
 */
export function initializePropertyDriverSystem(
  store: ExpressionStoreAccess,
): void {
  const expressionStore = useExpressionStore();
  expressionStore.propertyDriverSystem = new PropertyDriverSystem();

  // Set up property getter that reads from store
  expressionStore.propertyDriverSystem.setPropertyGetter(
    (layerId: string, propertyPath: string, frame: number) => {
      return store.getPropertyValueAtFrame(layerId, propertyPath, frame);
    },
  );

  // Connect audio if available (from audioStore, the source of truth)
  const audioStore = useAudioStore();
  if (audioStore.audioAnalysis) {
    expressionStore.propertyDriverSystem.setAudioAnalysis(
      audioStore.audioAnalysis,
    );
  }

  // Load existing drivers
  for (const driver of expressionStore.propertyDrivers) {
    expressionStore.propertyDriverSystem.addDriver(driver);
  }
}

/**
 * Get evaluated property values for a layer with drivers applied.
 */
export function getEvaluatedLayerProperties(
  store: ExpressionStoreAccess,
  layerId: string,
  frame: number,
): Map<PropertyPath, number> {
  const expressionStore = useExpressionStore();
  if (!expressionStore.propertyDriverSystem) {
    return new Map();
  }

  // Use store's getLayerById method (ExpressionStoreAccess includes this)
  const layer = store.getLayerById(layerId);
  if (!layer) return new Map();

  // Get composition context for expressions
  const comp = store.getActiveComp?.();
  // Validate fps (nullish coalescing doesn't catch NaN)
  const fps = Number.isFinite(store.fps) && store.fps > 0 ? store.fps : 16;
  // Validate duration calculation to prevent NaN propagation
  const rawDuration = comp
    ? comp.settings.frameCount / comp.settings.fps
    : undefined;
  const duration =
    rawDuration !== undefined && Number.isFinite(rawDuration)
      ? rawDuration
      : undefined;

  // Build base values from layer properties
  const baseValues = new Map<PropertyPath, number>();

  // Position
  const pos = interpolateProperty(
    layer.transform.position,
    frame,
    fps,
    layerId,
    duration,
  ) as { x: number; y: number };
  baseValues.set("transform.position.x", pos.x);
  baseValues.set("transform.position.y", pos.y);

  // Scale
  const scale = interpolateProperty(
    layer.transform.scale,
    frame,
    fps,
    layerId,
    duration,
  ) as { x: number; y: number };
  baseValues.set("transform.scale.x", scale.x);
  baseValues.set("transform.scale.y", scale.y);

  // Rotation
  baseValues.set(
    "transform.rotation",
    interpolateProperty(
      layer.transform.rotation,
      frame,
      fps,
      layerId,
      duration,
    ),
  );

  // 3D rotations if present
  if (layer.transform.rotationX) {
    baseValues.set(
      "transform.rotationX",
      interpolateProperty(
        layer.transform.rotationX,
        frame,
        fps,
        layerId,
        duration,
      ),
    );
  }
  if (layer.transform.rotationY) {
    baseValues.set(
      "transform.rotationY",
      interpolateProperty(
        layer.transform.rotationY,
        frame,
        fps,
        layerId,
        duration,
      ),
    );
  }
  if (layer.transform.rotationZ) {
    baseValues.set(
      "transform.rotationZ",
      interpolateProperty(
        layer.transform.rotationZ,
        frame,
        fps,
        layerId,
        duration,
      ),
    );
  }

  // Opacity
  baseValues.set(
    "opacity",
    interpolateProperty(layer.opacity, frame, fps, layerId, duration),
  );

  return expressionStore.propertyDriverSystem.evaluateLayerDrivers(
    layerId,
    frame,
    baseValues,
  );
}

/**
 * Add a property driver
 * Returns false if adding would create a circular dependency
 */
export function addPropertyDriver(
  store: ExpressionStoreAccess,
  driver: PropertyDriver,
): boolean {
  const expressionStore = useExpressionStore();
  // Check for cycles before adding
  if (expressionStore.propertyDriverSystem) {
    const added = expressionStore.propertyDriverSystem.addDriver(driver);
    if (!added) {
      storeLogger.warn(
        "Cannot add property driver: would create circular dependency",
      );
      return false;
    }
  }

  expressionStore.propertyDrivers.push(driver);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
  return true;
}

/**
 * Create and add an audio-driven property driver
 */
export function createAudioPropertyDriver(
  store: ExpressionStoreAccess,
  targetLayerId: string,
  targetProperty: PropertyPath,
  audioFeature: "amplitude" | "bass" | "mid" | "high" | "rms",
  options: {
    threshold?: number;
    scale?: number;
    offset?: number;
    smoothing?: number;
  } = {},
): PropertyDriver {
  const driver = createAudioDriver(
    targetLayerId,
    targetProperty,
    audioFeature,
    options,
  );
  addPropertyDriver(store, driver);
  return driver;
}

/**
 * Create and add a property-to-property link
 * Returns null if creating would cause a circular dependency
 */
export function createPropertyLinkDriver(
  store: ExpressionStoreAccess,
  targetLayerId: string,
  targetProperty: PropertyPath,
  sourceLayerId: string,
  sourceProperty: PropertyPath,
  options: {
    scale?: number;
    offset?: number;
    blendMode?: "replace" | "add" | "multiply";
  } = {},
): PropertyDriver | null {
  const driver = createPropertyLink(
    targetLayerId,
    targetProperty,
    sourceLayerId,
    sourceProperty,
    options,
  );

  const success = addPropertyDriver(store, driver);
  if (!success) {
    return null; // Circular dependency detected
  }

  return driver;
}

/**
 * Remove a property driver
 */
export function removePropertyDriver(
  store: ExpressionStoreAccess,
  driverId: string,
): void {
  const expressionStore = useExpressionStore();
  const index = expressionStore.propertyDrivers.findIndex(
    (d: PropertyDriver) => d.id === driverId,
  );
  if (index >= 0) {
    expressionStore.propertyDrivers.splice(index, 1);
  }

  if (expressionStore.propertyDriverSystem) {
    expressionStore.propertyDriverSystem.removeDriver(driverId);
  }

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Update a property driver
 */
export function updatePropertyDriver(
  store: ExpressionStoreAccess,
  driverId: string,
  updates: Partial<PropertyDriver>,
): void {
  const expressionStore = useExpressionStore();
  const driver = expressionStore.propertyDrivers.find(
    (d: PropertyDriver) => d.id === driverId,
  );
  if (driver) {
    Object.assign(driver, updates);
  }

  if (expressionStore.propertyDriverSystem) {
    expressionStore.propertyDriverSystem.updateDriver(driverId, updates);
  }

  store.project.meta.modified = new Date().toISOString();
}

/**
 * Get all drivers for a layer
 */
export function getDriversForLayer(
  store: ExpressionStoreAccess,
  layerId: string,
): PropertyDriver[] {
  const expressionStore = useExpressionStore();
  return expressionStore.propertyDrivers.filter(
    (d: PropertyDriver) => d.targetLayerId === layerId,
  );
}

/**
 * Toggle driver enabled state
 */
export function togglePropertyDriver(
  store: ExpressionStoreAccess,
  driverId: string,
): void {
  const expressionStore = useExpressionStore();
  const driver = expressionStore.propertyDrivers.find(
    (d: PropertyDriver) => d.id === driverId,
  );
  if (driver) {
    driver.enabled = !driver.enabled;
    if (expressionStore.propertyDriverSystem) {
      expressionStore.propertyDriverSystem.updateDriver(driverId, {
        enabled: driver.enabled,
      });
    }
    store.project.meta.modified = new Date().toISOString();
  }
}
