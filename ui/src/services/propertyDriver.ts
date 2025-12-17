/**
 * Property Driver System
 *
 * Links properties together - one property can drive another.
 * Supports:
 * - Property-to-property linking (Layer A position -> Layer B rotation)
 * - Audio-driven properties (amplitude -> position.x)
 * - Offset/scale transforms (gear effect, amplitude threshold triggers)
 * - Expression-like math operations
 */

import type { AudioAnalysis } from './audioFeatures';
import { getFeatureAtFrame } from './audioFeatures';
import { storeLogger } from '@/utils/logger';

// ============================================================================
// Types
// ============================================================================

export type DriverSourceType =
  | 'property'      // Another layer's property
  | 'audio'         // Audio feature
  | 'time'          // Frame/time based
  | 'expression';   // Math expression

export type PropertyPath =
  | 'transform.position.x' | 'transform.position.y' | 'transform.position.z'
  | 'transform.anchorPoint.x' | 'transform.anchorPoint.y' | 'transform.anchorPoint.z'
  | 'transform.scale.x' | 'transform.scale.y' | 'transform.scale.z'
  | 'transform.rotation' | 'transform.rotationX' | 'transform.rotationY' | 'transform.rotationZ'
  | 'opacity'
  // Spline control point properties (dynamic index)
  // Format: spline.controlPoint.{index}.{property}
  | `spline.controlPoint.${number}.x`
  | `spline.controlPoint.${number}.y`
  | `spline.controlPoint.${number}.depth`
  // Light properties
  | 'light.intensity'
  | 'light.color.r' | 'light.color.g' | 'light.color.b'
  | 'light.colorTemperature'
  | 'light.coneAngle' | 'light.penumbra' | 'light.falloff'
  | 'light.shadow.intensity' | 'light.shadow.softness' | 'light.shadow.bias'
  | 'light.poi.x' | 'light.poi.y' | 'light.poi.z'
  | 'light.areaSize.width' | 'light.areaSize.height'
  | 'light.physicalIntensity';

/**
 * Check if a property path is a spline control point property
 */
export function isSplineControlPointPath(path: string): path is PropertyPath {
  return path.startsWith('spline.controlPoint.');
}

/**
 * Check if a property path is a light property
 */
export function isLightPropertyPath(path: string): path is PropertyPath {
  return path.startsWith('light.');
}

/**
 * Parse a spline control point path into components
 * Returns null if not a valid spline control point path
 */
export function parseSplineControlPointPath(path: string): {
  index: number;
  property: 'x' | 'y' | 'depth';
} | null {
  const match = path.match(/^spline\.controlPoint\.(\d+)\.(x|y|depth)$/);
  if (!match) return null;
  return {
    index: parseInt(match[1], 10),
    property: match[2] as 'x' | 'y' | 'depth',
  };
}

/**
 * Create a spline control point property path
 */
export function createSplineControlPointPath(
  index: number,
  property: 'x' | 'y' | 'depth'
): PropertyPath {
  return `spline.controlPoint.${index}.${property}` as PropertyPath;
}

export type AudioFeatureType =
  | 'amplitude' | 'rms' | 'spectralCentroid'
  | 'sub' | 'bass' | 'lowMid' | 'mid' | 'highMid' | 'high'
  | 'onsets' | 'peaks';

export interface PropertyDriver {
  id: string;
  name: string;
  enabled: boolean;

  // Target - what property this driver affects
  targetLayerId: string;
  targetProperty: PropertyPath;

  // Source configuration
  sourceType: DriverSourceType;

  // For property source
  sourceLayerId?: string;
  sourceProperty?: PropertyPath;

  // For audio source
  audioFeature?: AudioFeatureType;
  audioThreshold?: number;      // Values below this become 0
  audioAboveThreshold?: boolean; // Only trigger when above threshold

  // Transform chain (applied in order)
  transforms: DriverTransform[];

  // How to combine with base value
  blendMode: 'replace' | 'add' | 'multiply';
  blendAmount: number;  // 0-1, for mixing with base value
}

export interface DriverTransform {
  type: 'scale' | 'offset' | 'clamp' | 'smooth' | 'invert' | 'remap' | 'threshold' | 'oscillate';

  // Scale: value * factor
  factor?: number;

  // Offset: value + amount
  amount?: number;

  // Clamp: clamp(value, min, max)
  min?: number;
  max?: number;

  // Smooth: temporal smoothing (0-1)
  smoothing?: number;

  // Remap: map from [inMin, inMax] to [outMin, outMax]
  inMin?: number;
  inMax?: number;
  outMin?: number;
  outMax?: number;

  // Threshold: value > threshold ? 1 : 0
  threshold?: number;

  // Oscillate: sin(value * frequency) * amplitude
  frequency?: number;
  amplitude?: number;
  phase?: number;
}

// ============================================================================
// Property Getter/Setter Types
// ============================================================================

export type PropertyGetter = (layerId: string, property: PropertyPath, frame: number) => number | null;
export type PropertySetter = (layerId: string, property: PropertyPath, value: number) => void;

// ============================================================================
// Driver Evaluator
// ============================================================================

export class PropertyDriverSystem {
  private drivers: Map<string, PropertyDriver> = new Map();
  private smoothedValues: Map<string, number> = new Map();
  private audioAnalysis: AudioAnalysis | null = null;
  private propertyGetter: PropertyGetter | null = null;

  constructor() {}

  /**
   * Set the audio analysis data for audio-driven properties
   */
  setAudioAnalysis(analysis: AudioAnalysis | null): void {
    this.audioAnalysis = analysis;
  }

  /**
   * Set the property getter function (provided by store/engine)
   */
  setPropertyGetter(getter: PropertyGetter): void {
    this.propertyGetter = getter;
  }

  /**
   * Add a new driver
   * Returns false if adding would create a circular dependency
   */
  addDriver(driver: PropertyDriver): boolean {
    // Check for circular dependencies before adding
    if (driver.sourceType === 'property' && driver.sourceLayerId && driver.sourceProperty) {
      if (this.wouldCreateCycle(driver)) {
        storeLogger.warn('PropertyDriverSystem: Cannot add driver: would create circular dependency');
        return false;
      }
    }

    this.drivers.set(driver.id, driver);
    this.smoothedValues.set(driver.id, 0);
    return true;
  }

  /**
   * Check if adding a driver would create a circular dependency
   */
  wouldCreateCycle(newDriver: PropertyDriver): boolean {
    if (newDriver.sourceType !== 'property') return false;
    if (!newDriver.sourceLayerId || !newDriver.sourceProperty) return false;

    // Build a dependency graph and check for cycles
    // A cycle exists if the source of the new driver ultimately depends on the target
    const visited = new Set<string>();
    const targetKey = `${newDriver.targetLayerId}:${newDriver.targetProperty}`;

    const hasCycle = (layerId: string, property: string): boolean => {
      const key = `${layerId}:${property}`;

      // If we've reached the target, we have a cycle
      if (key === targetKey) return true;

      // If already visited this node, no cycle through this path
      if (visited.has(key)) return false;
      visited.add(key);

      // Find all drivers that have this as their target
      // Then check if any of their sources lead back to our target
      for (const driver of this.drivers.values()) {
        if (driver.sourceType !== 'property') continue;
        if (driver.targetLayerId !== layerId || driver.targetProperty !== property) continue;
        if (!driver.sourceLayerId || !driver.sourceProperty) continue;

        if (hasCycle(driver.sourceLayerId, driver.sourceProperty)) {
          return true;
        }
      }

      return false;
    };

    // Check if the source of the new driver leads back to its target
    return hasCycle(newDriver.sourceLayerId, newDriver.sourceProperty);
  }

  /**
   * Remove a driver
   */
  removeDriver(id: string): void {
    this.drivers.delete(id);
    this.smoothedValues.delete(id);
  }

  /**
   * Update a driver
   */
  updateDriver(id: string, updates: Partial<PropertyDriver>): void {
    const driver = this.drivers.get(id);
    if (driver) {
      Object.assign(driver, updates);
    }
  }

  /**
   * Get a driver by ID
   */
  getDriver(id: string): PropertyDriver | undefined {
    return this.drivers.get(id);
  }

  /**
   * Get all drivers
   */
  getAllDrivers(): PropertyDriver[] {
    return Array.from(this.drivers.values());
  }

  /**
   * Get drivers for a specific target layer
   */
  getDriversForLayer(layerId: string): PropertyDriver[] {
    return Array.from(this.drivers.values()).filter(d => d.targetLayerId === layerId);
  }

  /**
   * Get drivers for a specific target property
   */
  getDriversForProperty(layerId: string, property: PropertyPath): PropertyDriver[] {
    return Array.from(this.drivers.values()).filter(
      d => d.targetLayerId === layerId && d.targetProperty === property && d.enabled
    );
  }

  /**
   * Evaluate a driver at a given frame
   */
  evaluateDriver(driver: PropertyDriver, frame: number, baseValue: number): number {
    if (!driver.enabled) return baseValue;

    // Get source value
    let value = this.getSourceValue(driver, frame);
    if (value === null) return baseValue;

    // Apply transform chain
    value = this.applyTransforms(driver, value);

    // Blend with base value
    return this.blendValue(baseValue, value, driver.blendMode, driver.blendAmount);
  }

  /**
   * Get the source value for a driver
   */
  private getSourceValue(driver: PropertyDriver, frame: number): number | null {
    switch (driver.sourceType) {
      case 'property':
        return this.getPropertySourceValue(driver, frame);

      case 'audio':
        return this.getAudioSourceValue(driver, frame);

      case 'time':
        return frame;

      default:
        return null;
    }
  }

  /**
   * Get value from another property
   */
  private getPropertySourceValue(driver: PropertyDriver, frame: number): number | null {
    if (!this.propertyGetter || !driver.sourceLayerId || !driver.sourceProperty) {
      return null;
    }
    return this.propertyGetter(driver.sourceLayerId, driver.sourceProperty, frame);
  }

  /**
   * Get value from audio analysis
   */
  private getAudioSourceValue(driver: PropertyDriver, frame: number): number | null {
    if (!this.audioAnalysis || !driver.audioFeature) {
      return null;
    }

    let value = getFeatureAtFrame(this.audioAnalysis, driver.audioFeature, frame);

    // Apply threshold if configured
    if (driver.audioThreshold !== undefined) {
      if (driver.audioAboveThreshold) {
        // Only pass through values above threshold
        value = value > driver.audioThreshold ? value : 0;
      } else {
        // Gate: set to 0 if below threshold
        value = value >= driver.audioThreshold ? value : 0;
      }
    }

    return value;
  }

  /**
   * Apply the transform chain to a value
   */
  private applyTransforms(driver: PropertyDriver, value: number): number {
    for (const transform of driver.transforms) {
      value = this.applyTransform(driver.id, transform, value);
    }
    return value;
  }

  /**
   * Apply a single transform
   */
  private applyTransform(driverId: string, transform: DriverTransform, value: number): number {
    switch (transform.type) {
      case 'scale':
        return value * (transform.factor ?? 1);

      case 'offset':
        return value + (transform.amount ?? 0);

      case 'clamp':
        return Math.max(transform.min ?? -Infinity, Math.min(transform.max ?? Infinity, value));

      case 'smooth': {
        const prevValue = this.smoothedValues.get(driverId) ?? value;
        const smoothing = transform.smoothing ?? 0.5;
        const smoothed = prevValue * smoothing + value * (1 - smoothing);
        this.smoothedValues.set(driverId, smoothed);
        return smoothed;
      }

      case 'invert':
        return 1 - value;

      case 'remap': {
        const inMin = transform.inMin ?? 0;
        const inMax = transform.inMax ?? 1;
        const outMin = transform.outMin ?? 0;
        const outMax = transform.outMax ?? 1;
        const normalized = (value - inMin) / (inMax - inMin);
        return outMin + normalized * (outMax - outMin);
      }

      case 'threshold':
        return value > (transform.threshold ?? 0.5) ? 1 : 0;

      case 'oscillate': {
        const freq = transform.frequency ?? 1;
        const amp = transform.amplitude ?? 1;
        const phase = transform.phase ?? 0;
        return Math.sin((value * freq + phase) * Math.PI * 2) * amp;
      }

      default:
        return value;
    }
  }

  /**
   * Blend driven value with base value
   */
  private blendValue(base: number, driven: number, mode: PropertyDriver['blendMode'], amount: number): number {
    let result: number;

    switch (mode) {
      case 'replace':
        result = driven;
        break;
      case 'add':
        result = base + driven;
        break;
      case 'multiply':
        result = base * driven;
        break;
      default:
        result = driven;
    }

    // Mix between base and result based on blend amount
    return base * (1 - amount) + result * amount;
  }

  /**
   * Evaluate ALL drivers for a layer at a frame
   * Returns a map of property -> driven value
   */
  evaluateLayerDrivers(
    layerId: string,
    frame: number,
    baseValues: Map<PropertyPath, number>
  ): Map<PropertyPath, number> {
    const result = new Map<PropertyPath, number>();
    const drivers = this.getDriversForLayer(layerId);

    for (const driver of drivers) {
      if (!driver.enabled) continue;

      const baseValue = baseValues.get(driver.targetProperty) ?? 0;
      const drivenValue = this.evaluateDriver(driver, frame, baseValue);

      // If multiple drivers target same property, combine them
      const existing = result.get(driver.targetProperty);
      if (existing !== undefined) {
        result.set(driver.targetProperty, existing + drivenValue - baseValue);
      } else {
        result.set(driver.targetProperty, drivenValue);
      }
    }

    return result;
  }

  /**
   * Reset smoothing state
   */
  resetSmoothing(): void {
    this.smoothedValues.clear();
  }

  /**
   * Clear all drivers
   */
  clear(): void {
    this.drivers.clear();
    this.smoothedValues.clear();
  }

  /**
   * Serialize drivers for storage
   */
  serialize(): PropertyDriver[] {
    return Array.from(this.drivers.values());
  }

  /**
   * Load drivers from serialized data
   */
  deserialize(drivers: PropertyDriver[]): void {
    this.clear();
    for (const driver of drivers) {
      this.addDriver(driver);
    }
  }
}

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Create a default property driver
 */
export function createPropertyDriver(
  targetLayerId: string,
  targetProperty: PropertyPath,
  sourceType: DriverSourceType = 'property'
): PropertyDriver {
  return {
    id: `driver_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
    name: 'New Driver',
    enabled: true,
    targetLayerId,
    targetProperty,
    sourceType,
    transforms: [],
    blendMode: 'add',
    blendAmount: 1
  };
}

/**
 * Create an audio-driven property driver
 */
export function createAudioDriver(
  targetLayerId: string,
  targetProperty: PropertyPath,
  audioFeature: AudioFeatureType,
  options: {
    threshold?: number;
    scale?: number;
    offset?: number;
    smoothing?: number;
  } = {}
): PropertyDriver {
  const driver = createPropertyDriver(targetLayerId, targetProperty, 'audio');
  driver.audioFeature = audioFeature;
  driver.audioThreshold = options.threshold ?? 0;
  driver.audioAboveThreshold = options.threshold !== undefined;

  // Add transforms based on options
  if (options.scale !== undefined && options.scale !== 1) {
    driver.transforms.push({ type: 'scale', factor: options.scale });
  }
  if (options.offset !== undefined && options.offset !== 0) {
    driver.transforms.push({ type: 'offset', amount: options.offset });
  }
  if (options.smoothing !== undefined && options.smoothing > 0) {
    driver.transforms.push({ type: 'smooth', smoothing: options.smoothing });
  }

  return driver;
}

/**
 * Create a property-to-property link
 */
export function createPropertyLink(
  targetLayerId: string,
  targetProperty: PropertyPath,
  sourceLayerId: string,
  sourceProperty: PropertyPath,
  options: {
    scale?: number;
    offset?: number;
    blendMode?: PropertyDriver['blendMode'];
  } = {}
): PropertyDriver {
  const driver = createPropertyDriver(targetLayerId, targetProperty, 'property');
  driver.sourceLayerId = sourceLayerId;
  driver.sourceProperty = sourceProperty;
  driver.blendMode = options.blendMode ?? 'add';

  if (options.scale !== undefined && options.scale !== 1) {
    driver.transforms.push({ type: 'scale', factor: options.scale });
  }
  if (options.offset !== undefined && options.offset !== 0) {
    driver.transforms.push({ type: 'offset', amount: options.offset });
  }

  return driver;
}

/**
 * Create a gear rotation effect
 * Layer B rotates based on Layer A's rotation, with offset anchor creating orbital motion
 */
export function createGearDriver(
  targetLayerId: string,
  sourceLayerId: string,
  gearRatio: number = 1,  // How many times target rotates per source rotation
  offset: number = 0       // Rotation offset in degrees
): PropertyDriver {
  const driver = createPropertyDriver(targetLayerId, 'transform.rotation', 'property');
  driver.name = 'Gear Rotation';
  driver.sourceLayerId = sourceLayerId;
  driver.sourceProperty = 'transform.rotation';
  driver.blendMode = 'replace';

  driver.transforms.push({ type: 'scale', factor: gearRatio });
  if (offset !== 0) {
    driver.transforms.push({ type: 'offset', amount: offset });
  }

  return driver;
}

/**
 * Create an audio-driven light intensity driver
 * Makes a light pulse with the music
 */
export function createAudioLightDriver(
  lightLayerId: string,
  audioFeature: AudioFeatureType = 'amplitude',
  options: {
    minIntensity?: number;
    maxIntensity?: number;
    smoothing?: number;
    threshold?: number;
  } = {}
): PropertyDriver {
  const driver = createPropertyDriver(lightLayerId, 'light.intensity', 'audio');
  driver.name = 'Audio Light Pulse';
  driver.audioFeature = audioFeature;
  driver.audioThreshold = options.threshold ?? 0;
  driver.blendMode = 'replace';

  // Remap 0-1 audio to intensity range
  const minI = options.minIntensity ?? 0.2;
  const maxI = options.maxIntensity ?? 2.0;
  driver.transforms.push({ type: 'remap', inMin: 0, inMax: 1, outMin: minI, outMax: maxI });

  if (options.smoothing !== undefined && options.smoothing > 0) {
    driver.transforms.push({ type: 'smooth', smoothing: options.smoothing });
  }

  return driver;
}

/**
 * Create an audio-driven color temperature driver
 * Shifts color temperature with audio (warm on bass, cool on high frequencies)
 */
export function createAudioColorTempDriver(
  lightLayerId: string,
  audioFeature: AudioFeatureType = 'spectralCentroid',
  options: {
    warmTemp?: number;   // Kelvin at low values (default 2700K warm)
    coolTemp?: number;   // Kelvin at high values (default 8000K cool)
    smoothing?: number;
  } = {}
): PropertyDriver {
  const driver = createPropertyDriver(lightLayerId, 'light.colorTemperature', 'audio');
  driver.name = 'Audio Color Temperature';
  driver.audioFeature = audioFeature;
  driver.blendMode = 'replace';

  // Map normalized spectral centroid to temperature range
  const warm = options.warmTemp ?? 2700;
  const cool = options.coolTemp ?? 8000;
  driver.transforms.push({ type: 'remap', inMin: 0, inMax: 1, outMin: warm, outMax: cool });

  if (options.smoothing !== undefined && options.smoothing > 0) {
    driver.transforms.push({ type: 'smooth', smoothing: options.smoothing });
  }

  return driver;
}

/**
 * Create a light that follows another layer's position
 * Useful for spotlights tracking subjects
 */
export function createLightFollowDriver(
  lightLayerId: string,
  targetLayerId: string,
  options: {
    axis?: 'poi' | 'position';  // Drive POI or light position itself
    smoothing?: number;
    offset?: { x?: number; y?: number; z?: number };
  } = {}
): PropertyDriver[] {
  const drivers: PropertyDriver[] = [];
  const axis = options.axis ?? 'poi';
  const prefix = axis === 'poi' ? 'light.poi' : 'transform.position';

  // Create drivers for x, y, z
  for (const coord of ['x', 'y', 'z'] as const) {
    const driver = createPropertyDriver(
      lightLayerId,
      `${prefix}.${coord}` as PropertyPath,
      'property'
    );
    driver.name = `Light Follow ${coord.toUpperCase()}`;
    driver.sourceLayerId = targetLayerId;
    driver.sourceProperty = `transform.position.${coord}` as PropertyPath;
    driver.blendMode = 'replace';

    // Apply offset if specified
    const offsetValue = options.offset?.[coord];
    if (offsetValue !== undefined && offsetValue !== 0) {
      driver.transforms.push({ type: 'offset', amount: offsetValue });
    }

    if (options.smoothing !== undefined && options.smoothing > 0) {
      driver.transforms.push({ type: 'smooth', smoothing: options.smoothing });
    }

    drivers.push(driver);
  }

  return drivers;
}

/**
 * Get human-readable name for a property path
 */
export function getPropertyPathDisplayName(path: PropertyPath): string {
  // Check for spline control point paths first
  const splineParsed = parseSplineControlPointPath(path);
  if (splineParsed) {
    const propName = splineParsed.property === 'x' ? 'X'
      : splineParsed.property === 'y' ? 'Y'
      : 'Depth';
    return `Control Point ${splineParsed.index} ${propName}`;
  }

  const names: Record<string, string> = {
    'transform.position.x': 'Position X',
    'transform.position.y': 'Position Y',
    'transform.position.z': 'Position Z',
    'transform.anchorPoint.x': 'Anchor Point X',
    'transform.anchorPoint.y': 'Anchor Point Y',
    'transform.anchorPoint.z': 'Anchor Point Z',
    'transform.scale.x': 'Scale X',
    'transform.scale.y': 'Scale Y',
    'transform.scale.z': 'Scale Z',
    'transform.rotation': 'Rotation',
    'transform.rotationX': 'X Rotation',
    'transform.rotationY': 'Y Rotation',
    'transform.rotationZ': 'Z Rotation',
    'opacity': 'Opacity',
    // Light properties
    'light.intensity': 'Light Intensity',
    'light.color.r': 'Light Color Red',
    'light.color.g': 'Light Color Green',
    'light.color.b': 'Light Color Blue',
    'light.colorTemperature': 'Color Temperature (K)',
    'light.coneAngle': 'Cone Angle',
    'light.penumbra': 'Penumbra',
    'light.falloff': 'Falloff',
    'light.shadow.intensity': 'Shadow Intensity',
    'light.shadow.softness': 'Shadow Softness',
    'light.shadow.bias': 'Shadow Bias',
    'light.poi.x': 'Point of Interest X',
    'light.poi.y': 'Point of Interest Y',
    'light.poi.z': 'Point of Interest Z',
    'light.areaSize.width': 'Area Light Width',
    'light.areaSize.height': 'Area Light Height',
    'light.physicalIntensity': 'Physical Intensity (lm)'
  };
  return names[path] || path;
}

/**
 * Get all available property paths (common properties available on all layers)
 */
export function getAllPropertyPaths(): PropertyPath[] {
  return [
    'transform.position.x', 'transform.position.y', 'transform.position.z',
    'transform.anchorPoint.x', 'transform.anchorPoint.y', 'transform.anchorPoint.z',
    'transform.scale.x', 'transform.scale.y', 'transform.scale.z',
    'transform.rotation', 'transform.rotationX', 'transform.rotationY', 'transform.rotationZ',
    'opacity'
  ];
}

/**
 * Get all light property paths (for light layers only)
 */
export function getLightPropertyPaths(): PropertyPath[] {
  return [
    'light.intensity',
    'light.color.r', 'light.color.g', 'light.color.b',
    'light.colorTemperature',
    'light.coneAngle', 'light.penumbra', 'light.falloff',
    'light.shadow.intensity', 'light.shadow.softness', 'light.shadow.bias',
    'light.poi.x', 'light.poi.y', 'light.poi.z',
    'light.areaSize.width', 'light.areaSize.height',
    'light.physicalIntensity'
  ];
}

/**
 * Get all property paths for a specific layer type
 */
export function getPropertyPathsForLayerType(layerType: string): PropertyPath[] {
  const commonPaths = getAllPropertyPaths();

  switch (layerType) {
    case 'light':
      return [...commonPaths, ...getLightPropertyPaths()];
    case 'spline':
      // Spline control points are dynamic, so we just return common paths
      // Individual control point paths are generated dynamically
      return commonPaths;
    default:
      return commonPaths;
  }
}

export default PropertyDriverSystem;
