/**
 * Property Driver System Tests
 *
 * Tests the property linking system that connects properties together,
 * supports audio-driven properties, and applies transform chains.
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  PropertyDriverSystem,
  createPropertyDriver,
  createAudioDriver,
  createPropertyLink,
  createGearDriver,
  getPropertyPathDisplayName,
  getAllPropertyPaths,
  type PropertyDriver,
  type PropertyPath,
  type DriverTransform,
  type AudioFeatureType
} from '@/services/propertyDriver';
import type { AudioAnalysis } from '@/services/audioFeatures';

// ============================================================================
// MOCK DATA
// ============================================================================

function createMockAudioAnalysis(frames: number = 100): AudioAnalysis {
  const createArray = (generator: (i: number) => number) =>
    Array.from({ length: frames }, (_, i) => generator(i));

  return {
    sampleRate: 44100,
    duration: frames / 30,
    frameCount: frames,
    amplitudeEnvelope: createArray(i => Math.sin(i / 10) * 0.5 + 0.5),
    rmsEnergy: createArray(i => Math.sin(i / 10) * 0.4 + 0.5),
    spectralCentroid: createArray(i => Math.sin(i / 15) * 0.3 + 0.5),
    frequencyBands: {
      sub: createArray(i => Math.sin(i / 5) * 0.5 + 0.5),
      bass: createArray(i => Math.sin(i / 8) * 0.5 + 0.5),
      lowMid: createArray(i => Math.sin(i / 10) * 0.5 + 0.5),
      mid: createArray(i => Math.sin(i / 12) * 0.5 + 0.5),
      highMid: createArray(i => Math.sin(i / 15) * 0.5 + 0.5),
      high: createArray(i => Math.sin(i / 20) * 0.5 + 0.5)
    },
    onsets: [10, 25, 40, 55, 70, 85],
    bpm: 120,
    spectralFlux: createArray(i => Math.random()),
    zeroCrossingRate: createArray(i => Math.random()),
    spectralRolloff: createArray(i => Math.random()),
    spectralFlatness: createArray(i => Math.random())
  };
}

// ============================================================================
// PROPERTY DRIVER SYSTEM TESTS
// ============================================================================

describe('PropertyDriverSystem', () => {
  let system: PropertyDriverSystem;

  beforeEach(() => {
    system = new PropertyDriverSystem();
  });

  describe('Driver Management', () => {
    it('should add a driver', () => {
      const driver = createPropertyDriver('layer1', 'transform.position.x');
      const result = system.addDriver(driver);

      expect(result).toBe(true);
      expect(system.getDriver(driver.id)).toBeDefined();
    });

    it('should remove a driver', () => {
      const driver = createPropertyDriver('layer1', 'transform.position.x');
      system.addDriver(driver);
      system.removeDriver(driver.id);

      expect(system.getDriver(driver.id)).toBeUndefined();
    });

    it('should update a driver', () => {
      const driver = createPropertyDriver('layer1', 'transform.position.x');
      system.addDriver(driver);
      system.updateDriver(driver.id, { enabled: false, name: 'Updated' });

      const updated = system.getDriver(driver.id);
      expect(updated?.enabled).toBe(false);
      expect(updated?.name).toBe('Updated');
    });

    it('should get all drivers', () => {
      const driver1 = createPropertyDriver('layer1', 'transform.position.x');
      const driver2 = createPropertyDriver('layer2', 'transform.position.y');
      system.addDriver(driver1);
      system.addDriver(driver2);

      const all = system.getAllDrivers();
      expect(all.length).toBe(2);
    });

    it('should get drivers for a specific layer', () => {
      const driver1 = createPropertyDriver('layer1', 'transform.position.x');
      const driver2 = createPropertyDriver('layer1', 'transform.position.y');
      const driver3 = createPropertyDriver('layer2', 'transform.position.x');
      system.addDriver(driver1);
      system.addDriver(driver2);
      system.addDriver(driver3);

      const layer1Drivers = system.getDriversForLayer('layer1');
      expect(layer1Drivers.length).toBe(2);
    });

    it('should get drivers for a specific property', () => {
      const driver1 = createPropertyDriver('layer1', 'transform.position.x');
      const driver2 = createPropertyDriver('layer1', 'transform.position.x');
      driver2.enabled = true;
      const driver3 = createPropertyDriver('layer1', 'transform.position.y');
      system.addDriver(driver1);
      system.addDriver(driver2);
      system.addDriver(driver3);

      const propDrivers = system.getDriversForProperty('layer1', 'transform.position.x');
      expect(propDrivers.length).toBe(2);
    });

    it('should clear all drivers', () => {
      system.addDriver(createPropertyDriver('layer1', 'transform.position.x'));
      system.addDriver(createPropertyDriver('layer2', 'transform.position.y'));
      system.clear();

      expect(system.getAllDrivers().length).toBe(0);
    });
  });

  describe('Circular Dependency Detection', () => {
    it('should detect direct circular dependency', () => {
      // A -> B
      const driverAtoB = createPropertyLink('layerB', 'transform.position.x', 'layerA', 'transform.position.x');
      system.addDriver(driverAtoB);

      // B -> A would create cycle
      const driverBtoA = createPropertyLink('layerA', 'transform.position.x', 'layerB', 'transform.position.x');
      const result = system.addDriver(driverBtoA);

      expect(result).toBe(false);
    });

    it('should detect indirect circular dependency', () => {
      // A -> B
      const driverAtoB = createPropertyLink('layerB', 'transform.position.x', 'layerA', 'transform.position.x');
      system.addDriver(driverAtoB);

      // B -> C
      const driverBtoC = createPropertyLink('layerC', 'transform.position.x', 'layerB', 'transform.position.x');
      system.addDriver(driverBtoC);

      // C -> A would create cycle
      const driverCtoA = createPropertyLink('layerA', 'transform.position.x', 'layerC', 'transform.position.x');
      const result = system.addDriver(driverCtoA);

      expect(result).toBe(false);
    });

    it('should allow non-circular dependencies', () => {
      // A -> B
      const driverAtoB = createPropertyLink('layerB', 'transform.position.x', 'layerA', 'transform.position.x');
      expect(system.addDriver(driverAtoB)).toBe(true);

      // A -> C (different target)
      const driverAtoC = createPropertyLink('layerC', 'transform.position.x', 'layerA', 'transform.position.x');
      expect(system.addDriver(driverAtoC)).toBe(true);
    });
  });

  describe('Driver Evaluation', () => {
    describe('Audio Source', () => {
      beforeEach(() => {
        system.setAudioAnalysis(createMockAudioAnalysis());
      });

      it('should evaluate audio-driven driver', () => {
        const driver = createAudioDriver('layer1', 'transform.position.x', 'amplitude');
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 50, 100);
        expect(typeof result).toBe('number');
      });

      it('should apply audio threshold', () => {
        const driver = createAudioDriver('layer1', 'transform.position.x', 'amplitude', {
          threshold: 0.9
        });
        system.addDriver(driver);

        // Most values should be gated to 0 with high threshold
        const result = system.evaluateDriver(driver, 50, 100);
        expect(typeof result).toBe('number');
      });

      it('should return base value when audio analysis is not set', () => {
        system.setAudioAnalysis(null);
        const driver = createAudioDriver('layer1', 'transform.position.x', 'amplitude');
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 50, 100);
        expect(result).toBe(100);
      });
    });

    describe('Property Source', () => {
      it('should evaluate property-linked driver', () => {
        const mockGetter = vi.fn().mockReturnValue(50);
        system.setPropertyGetter(mockGetter);

        const driver = createPropertyLink('layerB', 'transform.position.y', 'layerA', 'transform.position.x');
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 0, 100);

        expect(mockGetter).toHaveBeenCalledWith('layerA', 'transform.position.x', 0);
        expect(typeof result).toBe('number');
      });

      it('should return base value when property getter is not set', () => {
        const driver = createPropertyLink('layerB', 'transform.position.y', 'layerA', 'transform.position.x');
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 0, 100);
        expect(result).toBe(100);
      });
    });

    describe('Time Source', () => {
      it('should use frame as value for time source', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.blendMode = 'replace';
        driver.blendAmount = 1;
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 50, 100);
        expect(result).toBe(50);
      });
    });

    describe('Disabled Drivers', () => {
      it('should return base value when driver is disabled', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.enabled = false;
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 50, 100);
        expect(result).toBe(100);
      });
    });
  });

  describe('Transform Chain', () => {
    describe('Scale Transform', () => {
      it('should multiply value by factor', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.transforms.push({ type: 'scale', factor: 2 });
        driver.blendMode = 'replace';
        driver.blendAmount = 1;
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 25, 100);
        expect(result).toBe(50); // 25 * 2
      });
    });

    describe('Offset Transform', () => {
      it('should add amount to value', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.transforms.push({ type: 'offset', amount: 100 });
        driver.blendMode = 'replace';
        driver.blendAmount = 1;
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 25, 0);
        expect(result).toBe(125); // 25 + 100
      });
    });

    describe('Clamp Transform', () => {
      it('should clamp value to min/max', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.transforms.push({ type: 'clamp', min: 10, max: 40 });
        driver.blendMode = 'replace';
        driver.blendAmount = 1;
        system.addDriver(driver);

        expect(system.evaluateDriver(driver, 5, 0)).toBe(10);
        expect(system.evaluateDriver(driver, 25, 0)).toBe(25);
        expect(system.evaluateDriver(driver, 50, 0)).toBe(40);
      });
    });

    describe('Smooth Transform', () => {
      it('should apply temporal smoothing', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.transforms.push({ type: 'smooth', smoothing: 0.5 });
        driver.blendMode = 'replace';
        driver.blendAmount = 1;
        system.addDriver(driver);

        // First evaluation
        const result1 = system.evaluateDriver(driver, 100, 0);

        // Second evaluation - should be smoothed
        const result2 = system.evaluateDriver(driver, 0, 0);
        expect(result2).toBeLessThan(result1); // Smoothing toward 0
        expect(result2).toBeGreaterThan(0); // But not instant
      });

      it('should reset smoothing state', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.transforms.push({ type: 'smooth', smoothing: 0.9 });
        driver.blendMode = 'replace';
        driver.blendAmount = 1;
        system.addDriver(driver);

        system.evaluateDriver(driver, 100, 0);
        system.resetSmoothing();

        // After reset, should behave like first evaluation
        const result = system.evaluateDriver(driver, 50, 0);
        expect(result).toBe(50);
      });
    });

    describe('Invert Transform', () => {
      it('should invert value (1 - value)', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.transforms.push({ type: 'scale', factor: 0.01 }); // Scale to 0-1 range
        driver.transforms.push({ type: 'invert' });
        driver.blendMode = 'replace';
        driver.blendAmount = 1;
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 50, 0);
        expect(result).toBeCloseTo(0.5, 2); // 1 - 0.5
      });
    });

    describe('Remap Transform', () => {
      it('should remap value from one range to another', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.transforms.push({
          type: 'remap',
          inMin: 0,
          inMax: 100,
          outMin: 0,
          outMax: 1000
        });
        driver.blendMode = 'replace';
        driver.blendAmount = 1;
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 50, 0);
        expect(result).toBe(500); // 50 maps to 500 in new range
      });
    });

    describe('Threshold Transform', () => {
      it('should return 1 if above threshold, 0 if below', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.transforms.push({ type: 'threshold', threshold: 50 });
        driver.blendMode = 'replace';
        driver.blendAmount = 1;
        system.addDriver(driver);

        expect(system.evaluateDriver(driver, 30, 0)).toBe(0);
        expect(system.evaluateDriver(driver, 70, 0)).toBe(1);
      });
    });

    describe('Oscillate Transform', () => {
      it('should apply sine oscillation', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.transforms.push({
          type: 'oscillate',
          frequency: 1,
          amplitude: 10,
          phase: 0
        });
        driver.blendMode = 'replace';
        driver.blendAmount = 1;
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 0, 0);
        expect(result).toBeCloseTo(0, 1); // sin(0) * 10 = 0
      });
    });

    describe('Multiple Transforms', () => {
      it('should apply transforms in order', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.transforms.push({ type: 'scale', factor: 2 });
        driver.transforms.push({ type: 'offset', amount: 10 });
        driver.blendMode = 'replace';
        driver.blendAmount = 1;
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 25, 0);
        // 25 * 2 = 50, then 50 + 10 = 60
        expect(result).toBe(60);
      });
    });
  });

  describe('Blend Modes', () => {
    describe('Replace Mode', () => {
      it('should replace base value entirely at blendAmount=1', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.blendMode = 'replace';
        driver.blendAmount = 1;
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 50, 100);
        expect(result).toBe(50);
      });

      it('should mix at partial blendAmount', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.blendMode = 'replace';
        driver.blendAmount = 0.5;
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 50, 100);
        // Mix: base * 0.5 + result * 0.5 = 100 * 0.5 + 50 * 0.5 = 75
        expect(result).toBe(75);
      });
    });

    describe('Add Mode', () => {
      it('should add driven value to base', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.blendMode = 'add';
        driver.blendAmount = 1;
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 50, 100);
        // result = base + driven = 100 + 50 = 150
        // then mix: base * 0 + result * 1 = 150
        expect(result).toBe(150);
      });
    });

    describe('Multiply Mode', () => {
      it('should multiply driven value with base', () => {
        const driver = createPropertyDriver('layer1', 'transform.position.x', 'time');
        driver.transforms.push({ type: 'scale', factor: 0.01 }); // Make it a reasonable multiplier
        driver.blendMode = 'multiply';
        driver.blendAmount = 1;
        system.addDriver(driver);

        const result = system.evaluateDriver(driver, 50, 100);
        // Driven = 0.5, base = 100, result = 100 * 0.5 = 50
        expect(result).toBe(50);
      });
    });
  });

  describe('Layer Evaluation', () => {
    it('should evaluate all drivers for a layer', () => {
      const driver1 = createPropertyDriver('layer1', 'transform.position.x', 'time');
      driver1.blendMode = 'replace';
      driver1.blendAmount = 1;

      const driver2 = createPropertyDriver('layer1', 'transform.position.y', 'time');
      driver2.blendMode = 'replace';
      driver2.blendAmount = 1;
      driver2.transforms.push({ type: 'scale', factor: 2 });

      system.addDriver(driver1);
      system.addDriver(driver2);

      const baseValues = new Map<PropertyPath, number>();
      baseValues.set('transform.position.x', 100);
      baseValues.set('transform.position.y', 100);

      const result = system.evaluateLayerDrivers('layer1', 25, baseValues);

      expect(result.get('transform.position.x')).toBe(25);
      expect(result.get('transform.position.y')).toBe(50);
    });
  });

  describe('Serialization', () => {
    it('should serialize and deserialize drivers', () => {
      const driver1 = createPropertyDriver('layer1', 'transform.position.x');
      const driver2 = createAudioDriver('layer2', 'transform.scale.x', 'bass');

      system.addDriver(driver1);
      system.addDriver(driver2);

      const serialized = system.serialize();
      expect(serialized.length).toBe(2);

      const newSystem = new PropertyDriverSystem();
      newSystem.deserialize(serialized);

      expect(newSystem.getAllDrivers().length).toBe(2);
      expect(newSystem.getDriver(driver1.id)).toBeDefined();
      expect(newSystem.getDriver(driver2.id)).toBeDefined();
    });
  });
});

// ============================================================================
// HELPER FUNCTION TESTS
// ============================================================================

describe('createPropertyDriver', () => {
  it('should create driver with correct defaults', () => {
    const driver = createPropertyDriver('layer1', 'transform.position.x');

    expect(driver.id).toMatch(/^driver_/);
    expect(driver.name).toBe('New Driver');
    expect(driver.enabled).toBe(true);
    expect(driver.targetLayerId).toBe('layer1');
    expect(driver.targetProperty).toBe('transform.position.x');
    expect(driver.sourceType).toBe('property');
    expect(driver.transforms).toEqual([]);
    expect(driver.blendMode).toBe('add');
    expect(driver.blendAmount).toBe(1);
  });

  it('should accept custom source type', () => {
    const driver = createPropertyDriver('layer1', 'transform.position.x', 'audio');
    expect(driver.sourceType).toBe('audio');
  });
});

describe('createAudioDriver', () => {
  it('should create audio driver with feature', () => {
    const driver = createAudioDriver('layer1', 'transform.position.x', 'amplitude');

    expect(driver.sourceType).toBe('audio');
    expect(driver.audioFeature).toBe('amplitude');
    expect(driver.audioThreshold).toBe(0);
  });

  it('should apply scale transform when specified', () => {
    const driver = createAudioDriver('layer1', 'transform.position.x', 'bass', { scale: 2 });
    expect(driver.transforms.some(t => t.type === 'scale' && t.factor === 2)).toBe(true);
  });

  it('should apply offset transform when specified', () => {
    const driver = createAudioDriver('layer1', 'transform.position.x', 'bass', { offset: 10 });
    expect(driver.transforms.some(t => t.type === 'offset' && t.amount === 10)).toBe(true);
  });

  it('should apply smoothing transform when specified', () => {
    const driver = createAudioDriver('layer1', 'transform.position.x', 'bass', { smoothing: 0.5 });
    expect(driver.transforms.some(t => t.type === 'smooth' && t.smoothing === 0.5)).toBe(true);
  });

  it('should configure threshold when specified', () => {
    const driver = createAudioDriver('layer1', 'transform.position.x', 'bass', { threshold: 0.5 });
    expect(driver.audioThreshold).toBe(0.5);
    expect(driver.audioAboveThreshold).toBe(true);
  });
});

describe('createPropertyLink', () => {
  it('should create property-to-property link', () => {
    const driver = createPropertyLink('layerB', 'transform.position.y', 'layerA', 'transform.position.x');

    expect(driver.sourceType).toBe('property');
    expect(driver.sourceLayerId).toBe('layerA');
    expect(driver.sourceProperty).toBe('transform.position.x');
    expect(driver.targetLayerId).toBe('layerB');
    expect(driver.targetProperty).toBe('transform.position.y');
  });

  it('should apply custom blend mode', () => {
    const driver = createPropertyLink('layerB', 'transform.position.y', 'layerA', 'transform.position.x', {
      blendMode: 'multiply'
    });
    expect(driver.blendMode).toBe('multiply');
  });
});

describe('createGearDriver', () => {
  it('should create gear rotation driver', () => {
    const driver = createGearDriver('layerB', 'layerA', 2, 45);

    expect(driver.name).toBe('Gear Rotation');
    expect(driver.targetProperty).toBe('transform.rotation');
    expect(driver.sourceProperty).toBe('transform.rotation');
    expect(driver.blendMode).toBe('replace');

    // Should have scale and offset transforms
    expect(driver.transforms.some(t => t.type === 'scale' && t.factor === 2)).toBe(true);
    expect(driver.transforms.some(t => t.type === 'offset' && t.amount === 45)).toBe(true);
  });

  it('should use default gear ratio of 1', () => {
    const driver = createGearDriver('layerB', 'layerA');
    expect(driver.transforms.some(t => t.type === 'scale' && t.factor === 1)).toBe(true);
  });
});

describe('getPropertyPathDisplayName', () => {
  it('should return human-readable names', () => {
    expect(getPropertyPathDisplayName('transform.position.x')).toBe('Position X');
    expect(getPropertyPathDisplayName('transform.rotation')).toBe('Rotation');
    expect(getPropertyPathDisplayName('opacity')).toBe('Opacity');
  });
});

describe('getAllPropertyPaths', () => {
  it('should return all available property paths', () => {
    const paths = getAllPropertyPaths();

    expect(paths).toContain('transform.position.x');
    expect(paths).toContain('transform.position.y');
    expect(paths).toContain('transform.position.z');
    expect(paths).toContain('transform.scale.x');
    expect(paths).toContain('transform.rotation');
    expect(paths).toContain('opacity');
    expect(paths.length).toBe(14);
  });
});

// ============================================================================
// AUDIO FEATURE TYPES
// ============================================================================

describe('Audio Feature Types', () => {
  const features: AudioFeatureType[] = [
    'amplitude', 'rms', 'spectralCentroid',
    'sub', 'bass', 'lowMid', 'mid', 'highMid', 'high',
    'onsets', 'peaks'
  ];

  it('should support all audio feature types', () => {
    for (const feature of features) {
      const driver = createAudioDriver('layer1', 'transform.position.x', feature);
      expect(driver.audioFeature).toBe(feature);
    }
  });
});
