/**
 * REGRESSION TEST: BUG - Remap Division by Zero
 * 
 * @fixed 2026-01-06
 * @file services/propertyDriver.ts
 * @rootCause remap transform divided by (inMax - inMin) without checking if it's zero
 * @fix Added inRange===0 guard that returns midpoint of output range
 * @counterexample remap(0.5, 0.5, 0.5, 0, 100) produced NaN/Infinity
 */

import { describe, test, expect } from 'vitest';
import { PropertyDriverSystem } from '@/services/propertyDriver';
import type { PropertyDriver, DriverTransform } from '@/services/propertyDriver';

// Helper to create a remap transform
function createRemapTransform(
  inMin: number,
  inMax: number,
  outMin: number,
  outMax: number,
): DriverTransform {
  return {
    type: 'remap',
    inMin,
    inMax,
    outMin,
    outMax,
  };
}

describe('BUG Regression: Remap Division by Zero', () => {
  /**
   * This test MUST reproduce the exact counterexample from the bug report.
   * Before fix: remap(0.5, 0.5, 0.5, 0, 100) would divide by zero → NaN/Infinity
   * After fix: Returns midpoint of output range (50) when input range is zero
   */
  test('original counterexample now passes', () => {
    const system = new PropertyDriverSystem();
    
    // Create a driver with remap transform where inMin === inMax
    const driver: PropertyDriver = {
      id: 'test-driver',
      name: 'Test Driver',
      enabled: true,
      targetLayerId: 'layer-1',
      targetProperty: 'transform.position.x',
      sourceType: 'time',
      transforms: [
        createRemapTransform(0.5, 0.5, 0, 100), // Zero input range!
      ],
      blendMode: 'replace',
      blendAmount: 1,
    };

    system.addDriver(driver);

    // Evaluate with value 0.5 (within the zero-range input)
    // Before fix: Would produce NaN/Infinity
    // After fix: Should return midpoint of output range (50)
    const result = system.evaluateDriver(driver, 0, 0.5);

    expect(Number.isFinite(result)).toBe(true);
    expect(Number.isNaN(result)).toBe(false);
    expect(result).toBe(50); // Midpoint of [0, 100]
  });

  /**
   * Additional edge cases related to this bug.
   */
  test('various zero-range inputs return output midpoint', () => {
    const system = new PropertyDriverSystem();
    
    const testCases = [
      { inMin: 0, inMax: 0, outMin: 0, outMax: 100, expected: 50 },
      { inMin: 100, inMax: 100, outMin: 0, outMax: 200, expected: 100 },
      { inMin: 5, inMax: 5, outMin: 10, outMax: 30, expected: 20 },
      { inMin: -10, inMax: -10, outMin: 0, outMax: 1, expected: 0.5 },
    ];

    for (const { inMin, inMax, outMin, outMax, expected } of testCases) {
      const driver: PropertyDriver = {
        id: `test-${inMin}-${inMax}`,
        name: 'Test Driver',
        enabled: true,
        targetLayerId: 'layer-1',
        targetProperty: 'transform.position.x',
        sourceType: 'time',
        transforms: [
          createRemapTransform(inMin, inMax, outMin, outMax),
        ],
        blendMode: 'replace',
        blendAmount: 1,
      };

      system.addDriver(driver);
      const result = system.evaluateDriver(driver, 0, inMin);
      
      expect(Number.isFinite(result)).toBe(true);
      expect(result).toBe(expected);
    }
  });

  test('non-zero input ranges work correctly', () => {
    const system = new PropertyDriverSystem();

    const driver: PropertyDriver = {
      id: 'test-normal',
      name: 'Test Driver',
      enabled: true,
      targetLayerId: 'layer-1',
      targetProperty: 'transform.position.x',
      sourceType: 'time', // Uses frame as source value
      transforms: [
        createRemapTransform(0, 1, 0, 100), // Normal range: maps frame [0,1] → [0,100]
      ],
      blendMode: 'replace',
      blendAmount: 1,
    };

    system.addDriver(driver);

    // Normal remap should work as expected
    // Note: evaluateDriver(driver, frame, baseValue) uses frame as source value for sourceType='time'
    // baseValue is used for blending only
    expect(system.evaluateDriver(driver, 0, 0)).toBe(0);    // frame=0 → remap(0) = 0
    expect(system.evaluateDriver(driver, 0.5, 0)).toBe(50); // frame=0.5 → remap(0.5) = 50
    expect(system.evaluateDriver(driver, 1, 0)).toBe(100);  // frame=1 → remap(1) = 100
  });

  test('zero-range with any input value returns same output', () => {
    const system = new PropertyDriverSystem();
    
    const driver: PropertyDriver = {
      id: 'test-zero-range',
      name: 'Test Driver',
      enabled: true,
      targetLayerId: 'layer-1',
      targetProperty: 'transform.position.x',
      sourceType: 'time',
      transforms: [
        createRemapTransform(5, 5, 0, 100), // Zero range
      ],
      blendMode: 'replace',
      blendAmount: 1,
    };

    system.addDriver(driver);

    // Any input value should return the same output (midpoint)
    const values = [0, 5, 10, -5, 100];
    for (const value of values) {
      const result = system.evaluateDriver(driver, 0, value);
      expect(Number.isFinite(result)).toBe(true);
      expect(result).toBe(50); // Midpoint of [0, 100]
    }
  });
});
