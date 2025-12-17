/**
 * Property Driver Actions
 *
 * Property driver system for expressions and property linking.
 * Extracted from compositorStore for better maintainability.
 */

import { storeLogger } from '@/utils/logger';
import {
  PropertyDriverSystem,
  type PropertyDriver,
  type PropertyPath,
  createAudioDriver,
  createPropertyLink
} from '@/services/propertyDriver';
import type { AudioAnalysis } from '@/services/audioFeatures';
import type { AnimatableProperty } from '@/types/project';
import { interpolateProperty } from '@/services/interpolation';

export interface PropertyDriverStore {
  // State
  propertyDriverSystem: PropertyDriverSystem | null;
  propertyDrivers: PropertyDriver[];
  audioAnalysis: AudioAnalysis | null;

  // Methods the store must provide
  project: { meta: { modified: string } };
  getLayer(layerId: string): {
    transform: {
      position: AnimatableProperty<{ x: number; y: number }>;
      scale: AnimatableProperty<{ x: number; y: number }>;
      rotation: AnimatableProperty<number>;
      rotationX?: AnimatableProperty<number>;
      rotationY?: AnimatableProperty<number>;
      rotationZ?: AnimatableProperty<number>;
    };
    opacity: AnimatableProperty<number>;
  } | undefined;
  pushHistory(): void;
  getPropertyValueAtFrame(layerId: string, propertyPath: string, frame: number): number | null;
}

/**
 * Initialize the property driver system
 */
export function initializePropertyDriverSystem(store: PropertyDriverStore): void {
  store.propertyDriverSystem = new PropertyDriverSystem();

  // Set up property getter that reads from store
  store.propertyDriverSystem.setPropertyGetter((layerId, propertyPath, frame) => {
    return store.getPropertyValueAtFrame(layerId, propertyPath, frame);
  });

  // Connect audio if available
  if (store.audioAnalysis) {
    store.propertyDriverSystem.setAudioAnalysis(store.audioAnalysis);
  }

  // Load existing drivers
  for (const driver of store.propertyDrivers) {
    store.propertyDriverSystem.addDriver(driver);
  }
}

/**
 * Get evaluated property values for a layer with drivers applied
 */
export function getEvaluatedLayerProperties(
  store: PropertyDriverStore,
  layerId: string,
  frame: number
): Map<string, number> {
  if (!store.propertyDriverSystem) {
    return new Map();
  }

  const layer = store.getLayer(layerId);
  if (!layer) return new Map();

  // Build base values from layer properties
  const baseValues = new Map<string, number>();

  // Position
  const pos = interpolateProperty(layer.transform.position, frame);
  baseValues.set('transform.position.x', pos.x);
  baseValues.set('transform.position.y', pos.y);

  // Scale
  const scale = interpolateProperty(layer.transform.scale, frame);
  baseValues.set('transform.scale.x', scale.x);
  baseValues.set('transform.scale.y', scale.y);

  // Rotation
  baseValues.set('transform.rotation', interpolateProperty(layer.transform.rotation, frame));

  // 3D rotations if present
  if (layer.transform.rotationX) {
    baseValues.set('transform.rotationX', interpolateProperty(layer.transform.rotationX, frame));
  }
  if (layer.transform.rotationY) {
    baseValues.set('transform.rotationY', interpolateProperty(layer.transform.rotationY, frame));
  }
  if (layer.transform.rotationZ) {
    baseValues.set('transform.rotationZ', interpolateProperty(layer.transform.rotationZ, frame));
  }

  // Opacity
  baseValues.set('opacity', interpolateProperty(layer.opacity, frame));

  return store.propertyDriverSystem.evaluateLayerDrivers(layerId, frame, baseValues);
}

/**
 * Add a property driver
 * Returns false if adding would create a circular dependency
 */
export function addPropertyDriver(
  store: PropertyDriverStore,
  driver: PropertyDriver
): boolean {
  // Check for cycles before adding
  if (store.propertyDriverSystem) {
    const added = store.propertyDriverSystem.addDriver(driver);
    if (!added) {
      storeLogger.warn('Cannot add property driver: would create circular dependency');
      return false;
    }
  }

  store.propertyDrivers.push(driver);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
  return true;
}

/**
 * Create and add an audio-driven property driver
 */
export function createAudioPropertyDriver(
  store: PropertyDriverStore,
  targetLayerId: string,
  targetProperty: PropertyPath,
  audioFeature: 'amplitude' | 'bass' | 'mid' | 'high' | 'rms',
  options: { threshold?: number; scale?: number; offset?: number; smoothing?: number } = {}
): PropertyDriver {
  const driver = createAudioDriver(targetLayerId, targetProperty, audioFeature, options);
  addPropertyDriver(store, driver);
  return driver;
}

/**
 * Create and add a property-to-property link
 * Returns null if creating would cause a circular dependency
 */
export function createPropertyLinkDriver(
  store: PropertyDriverStore,
  targetLayerId: string,
  targetProperty: PropertyPath,
  sourceLayerId: string,
  sourceProperty: PropertyPath,
  options: { scale?: number; offset?: number; blendMode?: 'replace' | 'add' | 'multiply' } = {}
): PropertyDriver | null {
  const driver = createPropertyLink(
    targetLayerId,
    targetProperty,
    sourceLayerId,
    sourceProperty,
    options
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
  store: PropertyDriverStore,
  driverId: string
): void {
  const index = store.propertyDrivers.findIndex(d => d.id === driverId);
  if (index >= 0) {
    store.propertyDrivers.splice(index, 1);
  }

  if (store.propertyDriverSystem) {
    store.propertyDriverSystem.removeDriver(driverId);
  }

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Update a property driver
 */
export function updatePropertyDriver(
  store: PropertyDriverStore,
  driverId: string,
  updates: Partial<PropertyDriver>
): void {
  const driver = store.propertyDrivers.find(d => d.id === driverId);
  if (driver) {
    Object.assign(driver, updates);
  }

  if (store.propertyDriverSystem) {
    store.propertyDriverSystem.updateDriver(driverId, updates);
  }

  store.project.meta.modified = new Date().toISOString();
}

/**
 * Get all drivers for a layer
 */
export function getDriversForLayer(
  store: PropertyDriverStore,
  layerId: string
): PropertyDriver[] {
  return store.propertyDrivers.filter(d => d.targetLayerId === layerId);
}

/**
 * Toggle driver enabled state
 */
export function togglePropertyDriver(
  store: PropertyDriverStore,
  driverId: string
): void {
  const driver = store.propertyDrivers.find(d => d.id === driverId);
  if (driver) {
    driver.enabled = !driver.enabled;
    if (store.propertyDriverSystem) {
      store.propertyDriverSystem.updateDriver(driverId, { enabled: driver.enabled });
    }
    store.project.meta.modified = new Date().toISOString();
  }
}
