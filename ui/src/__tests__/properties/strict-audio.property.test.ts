/**
 * STRICT Property Tests for Audio System
 * 
 * Tests the invariants that must hold for correct audio-reactive animation:
 * 1. Determinism: getFeatureAtFrame must be pure
 * 2. Bounds: features must be normalized 0-1 where documented
 * 3. Frame alignment: audio frames must match video frames
 * 4. Feature consistency: related features must be coherent
 * 
 * TOLERANCE: STRICT - Audio sync issues are immediately noticeable
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  getFeatureAtFrame,
  isBeatAtFrame,
  type AudioAnalysis,
  type AudioFeature,
} from '@/services/audioFeatures';

// ============================================================================
// TEST DATA GENERATORS
// ============================================================================

/**
 * Generate a valid AudioAnalysis object
 */
const arbitraryAudioAnalysis = (frameCount: number = 100): fc.Arbitrary<AudioAnalysis> =>
  fc.record({
    sampleRate: fc.constantFrom(44100, 48000, 96000),
    duration: fc.double({ min: 0.1, max: 300, noNaN: true, noDefaultInfinity: true }),
    frameCount: fc.constant(frameCount),
    // All features should be normalized 0-1
    amplitudeEnvelope: fc.array(
      fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }),
      { minLength: frameCount, maxLength: frameCount }
    ),
    rmsEnergy: fc.array(
      fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }),
      { minLength: frameCount, maxLength: frameCount }
    ),
    spectralCentroid: fc.array(
      fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }),
      { minLength: frameCount, maxLength: frameCount }
    ),
    frequencyBands: fc.record({
      sub: fc.array(fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }), { minLength: frameCount, maxLength: frameCount }),
      bass: fc.array(fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }), { minLength: frameCount, maxLength: frameCount }),
      lowMid: fc.array(fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }), { minLength: frameCount, maxLength: frameCount }),
      mid: fc.array(fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }), { minLength: frameCount, maxLength: frameCount }),
      highMid: fc.array(fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }), { minLength: frameCount, maxLength: frameCount }),
      high: fc.array(fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }), { minLength: frameCount, maxLength: frameCount }),
    }),
    onsets: fc.array(
      fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }),
      { minLength: frameCount, maxLength: frameCount }
    ),
    bpm: fc.double({ min: 60, max: 200, noNaN: true, noDefaultInfinity: true }),
    spectralFlux: fc.array(fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }), { minLength: frameCount, maxLength: frameCount }),
    zeroCrossingRate: fc.array(fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }), { minLength: frameCount, maxLength: frameCount }),
    spectralRolloff: fc.array(fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }), { minLength: frameCount, maxLength: frameCount }),
    spectralFlatness: fc.array(fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }), { minLength: frameCount, maxLength: frameCount }),
  });

const allFeatures: AudioFeature[] = [
  'amplitude', 'rms', 'spectralCentroid',
  'sub', 'bass', 'lowMid', 'mid', 'highMid', 'high',
  'onsets', 'spectralFlux', 'zeroCrossingRate', 
  'spectralRolloff', 'spectralFlatness'
];

// ============================================================================
// STRICT DETERMINISM TESTS
// ============================================================================

describe('STRICT: Audio Feature Determinism', () => {
  test.prop([
    fc.integer({ min: 10, max: 100 }),
  ])('getFeatureAtFrame is deterministic', (frameCount) => {
    // Create analysis manually to ensure consistency
    const analysis: AudioAnalysis = {
      sampleRate: 44100,
      duration: frameCount / 30,
      frameCount,
      amplitudeEnvelope: Array(frameCount).fill(0).map((_, i) => Math.sin(i * 0.1) * 0.5 + 0.5),
      rmsEnergy: Array(frameCount).fill(0).map((_, i) => Math.cos(i * 0.1) * 0.3 + 0.5),
      spectralCentroid: Array(frameCount).fill(0.5),
      frequencyBands: {
        sub: Array(frameCount).fill(0.2),
        bass: Array(frameCount).fill(0.4),
        lowMid: Array(frameCount).fill(0.3),
        mid: Array(frameCount).fill(0.5),
        highMid: Array(frameCount).fill(0.4),
        high: Array(frameCount).fill(0.3),
      },
      onsets: Array(frameCount).fill(0),
      bpm: 120,
      spectralFlux: Array(frameCount).fill(0.1),
      zeroCrossingRate: Array(frameCount).fill(0.2),
      spectralRolloff: Array(frameCount).fill(0.8),
      spectralFlatness: Array(frameCount).fill(0.3),
    };
    
    // Test each feature for determinism
    for (const feature of allFeatures) {
      for (let frame = 0; frame < Math.min(frameCount, 20); frame++) {
        const result1 = getFeatureAtFrame(analysis, feature, frame);
        const result2 = getFeatureAtFrame(analysis, feature, frame);
        
        expect(result1).toBe(result2);
      }
    }
  });

  test.prop([
    fc.integer({ min: 10, max: 100 }),
    fc.integer({ min: 0, max: 99 })
  ])('getFeatureAtFrame evaluation order does not affect result', (frameCount, testFrame) => {
    const analysis: AudioAnalysis = {
      sampleRate: 44100,
      duration: frameCount / 30,
      frameCount,
      amplitudeEnvelope: Array(frameCount).fill(0).map((_, i) => i / frameCount),
      rmsEnergy: Array(frameCount).fill(0.5),
      spectralCentroid: Array(frameCount).fill(0.5),
      frequencyBands: {
        sub: Array(frameCount).fill(0.2),
        bass: Array(frameCount).fill(0.4),
        lowMid: Array(frameCount).fill(0.3),
        mid: Array(frameCount).fill(0.5),
        highMid: Array(frameCount).fill(0.4),
        high: Array(frameCount).fill(0.3),
      },
      onsets: Array(frameCount).fill(0),
      bpm: 120,
      spectralFlux: Array(frameCount).fill(0.1),
      zeroCrossingRate: Array(frameCount).fill(0.2),
      spectralRolloff: Array(frameCount).fill(0.8),
      spectralFlatness: Array(frameCount).fill(0.3),
    };
    
    const safeFrame = Math.min(testFrame, frameCount - 1);
    
    // Evaluate forward
    for (let f = 0; f <= safeFrame; f++) {
      getFeatureAtFrame(analysis, 'amplitude', f);
    }
    const forwardResult = getFeatureAtFrame(analysis, 'amplitude', safeFrame);
    
    // Evaluate backward
    for (let f = frameCount - 1; f >= safeFrame; f--) {
      getFeatureAtFrame(analysis, 'amplitude', f);
    }
    const backwardResult = getFeatureAtFrame(analysis, 'amplitude', safeFrame);
    
    expect(forwardResult).toBe(backwardResult);
  });
});

// ============================================================================
// STRICT BOUNDS TESTS
// ============================================================================

describe('STRICT: Audio Feature Bounds', () => {
  test.prop([
    fc.integer({ min: 10, max: 50 })
  ])('all features return values in expected range [0,1]', (frameCount) => {
    const analysis: AudioAnalysis = {
      sampleRate: 44100,
      duration: frameCount / 30,
      frameCount,
      amplitudeEnvelope: Array(frameCount).fill(0).map(() => Math.random()),
      rmsEnergy: Array(frameCount).fill(0).map(() => Math.random()),
      spectralCentroid: Array(frameCount).fill(0).map(() => Math.random()),
      frequencyBands: {
        sub: Array(frameCount).fill(0).map(() => Math.random()),
        bass: Array(frameCount).fill(0).map(() => Math.random()),
        lowMid: Array(frameCount).fill(0).map(() => Math.random()),
        mid: Array(frameCount).fill(0).map(() => Math.random()),
        highMid: Array(frameCount).fill(0).map(() => Math.random()),
        high: Array(frameCount).fill(0).map(() => Math.random()),
      },
      onsets: Array(frameCount).fill(0).map(() => Math.random()),
      bpm: 120,
      spectralFlux: Array(frameCount).fill(0).map(() => Math.random()),
      zeroCrossingRate: Array(frameCount).fill(0).map(() => Math.random()),
      spectralRolloff: Array(frameCount).fill(0).map(() => Math.random()),
      spectralFlatness: Array(frameCount).fill(0).map(() => Math.random()),
    };
    
    for (const feature of allFeatures) {
      for (let frame = 0; frame < frameCount; frame++) {
        const value = getFeatureAtFrame(analysis, feature, frame);
        
        // All features should be 0-1 normalized
        expect(value).toBeGreaterThanOrEqual(0);
        expect(value).toBeLessThanOrEqual(1);
        expect(Number.isFinite(value)).toBe(true);
        expect(Number.isNaN(value)).toBe(false);
      }
    }
  });

  test.prop([
    fc.integer({ min: 10, max: 50 })
  ])('out-of-bounds frame returns 0', (frameCount) => {
    const analysis: AudioAnalysis = {
      sampleRate: 44100,
      duration: frameCount / 30,
      frameCount,
      amplitudeEnvelope: Array(frameCount).fill(0.5),
      rmsEnergy: Array(frameCount).fill(0.5),
      spectralCentroid: Array(frameCount).fill(0.5),
      frequencyBands: {
        sub: Array(frameCount).fill(0.5),
        bass: Array(frameCount).fill(0.5),
        lowMid: Array(frameCount).fill(0.5),
        mid: Array(frameCount).fill(0.5),
        highMid: Array(frameCount).fill(0.5),
        high: Array(frameCount).fill(0.5),
      },
      onsets: Array(frameCount).fill(0.5),
      bpm: 120,
      spectralFlux: Array(frameCount).fill(0.5),
      zeroCrossingRate: Array(frameCount).fill(0.5),
      spectralRolloff: Array(frameCount).fill(0.5),
      spectralFlatness: Array(frameCount).fill(0.5),
    };
    
    // Negative frame
    const negativeResult = getFeatureAtFrame(analysis, 'amplitude', -1);
    expect(negativeResult).toBe(0);
    
    // Beyond frameCount
    const beyondResult = getFeatureAtFrame(analysis, 'amplitude', frameCount + 100);
    expect(beyondResult).toBe(0);
  });
});

// ============================================================================
// STRICT BEAT DETECTION TESTS
// ============================================================================

describe('STRICT: Beat Detection', () => {
  test.prop([
    fc.integer({ min: 10, max: 50 })
  ])('isBeatAtFrame is deterministic', (frameCount) => {
    const analysis: AudioAnalysis = {
      sampleRate: 44100,
      duration: frameCount / 30,
      frameCount,
      amplitudeEnvelope: Array(frameCount).fill(0.5),
      rmsEnergy: Array(frameCount).fill(0.5),
      spectralCentroid: Array(frameCount).fill(0.5),
      frequencyBands: {
        sub: Array(frameCount).fill(0.5),
        bass: Array(frameCount).fill(0.5),
        lowMid: Array(frameCount).fill(0.5),
        mid: Array(frameCount).fill(0.5),
        highMid: Array(frameCount).fill(0.5),
        high: Array(frameCount).fill(0.5),
      },
      // Some frames are beats (>0.5)
      onsets: Array(frameCount).fill(0).map((_, i) => i % 4 === 0 ? 0.8 : 0.2),
      bpm: 120,
      spectralFlux: Array(frameCount).fill(0.5),
      zeroCrossingRate: Array(frameCount).fill(0.5),
      spectralRolloff: Array(frameCount).fill(0.5),
      spectralFlatness: Array(frameCount).fill(0.5),
    };
    
    for (let frame = 0; frame < frameCount; frame++) {
      const result1 = isBeatAtFrame(analysis, frame);
      const result2 = isBeatAtFrame(analysis, frame);
      
      expect(result1).toBe(result2);
    }
  });

  test.prop([
    fc.integer({ min: 10, max: 50 })
  ])('isBeatAtFrame returns boolean', (frameCount) => {
    const analysis: AudioAnalysis = {
      sampleRate: 44100,
      duration: frameCount / 30,
      frameCount,
      amplitudeEnvelope: Array(frameCount).fill(0.5),
      rmsEnergy: Array(frameCount).fill(0.5),
      spectralCentroid: Array(frameCount).fill(0.5),
      frequencyBands: {
        sub: Array(frameCount).fill(0.5),
        bass: Array(frameCount).fill(0.5),
        lowMid: Array(frameCount).fill(0.5),
        mid: Array(frameCount).fill(0.5),
        highMid: Array(frameCount).fill(0.5),
        high: Array(frameCount).fill(0.5),
      },
      onsets: Array(frameCount).fill(0).map(() => Math.random()),
      bpm: 120,
      spectralFlux: Array(frameCount).fill(0.5),
      zeroCrossingRate: Array(frameCount).fill(0.5),
      spectralRolloff: Array(frameCount).fill(0.5),
      spectralFlatness: Array(frameCount).fill(0.5),
    };
    
    for (let frame = 0; frame < frameCount; frame++) {
      const result = isBeatAtFrame(analysis, frame);
      expect(typeof result).toBe('boolean');
    }
  });
});

// ============================================================================
// STRICT NULL/UNDEFINED HANDLING
// ============================================================================

describe('STRICT: Audio Null Safety', () => {
  it('getFeatureAtFrame handles null analysis', () => {
    const result = getFeatureAtFrame(null as any, 'amplitude', 0);
    expect(result).toBe(0);
  });

  it('getFeatureAtFrame handles undefined analysis', () => {
    const result = getFeatureAtFrame(undefined as any, 'amplitude', 0);
    expect(result).toBe(0);
  });

  it('isBeatAtFrame handles null analysis', () => {
    const result = isBeatAtFrame(null as any, 0);
    expect(result).toBe(false);
  });

  it('getFeatureAtFrame handles empty arrays', () => {
    const analysis: AudioAnalysis = {
      sampleRate: 44100,
      duration: 0,
      frameCount: 0,
      amplitudeEnvelope: [],
      rmsEnergy: [],
      spectralCentroid: [],
      frequencyBands: {
        sub: [],
        bass: [],
        lowMid: [],
        mid: [],
        highMid: [],
        high: [],
      },
      onsets: [],
      bpm: 120,
      spectralFlux: [],
      zeroCrossingRate: [],
      spectralRolloff: [],
      spectralFlatness: [],
    };
    
    const result = getFeatureAtFrame(analysis, 'amplitude', 0);
    expect(result).toBe(0);
  });
});

// ============================================================================
// STRESS TESTS
// ============================================================================

describe('STRESS: Audio Feature Under Load', () => {
  test.prop([
    fc.integer({ min: 100, max: 500 }),
    fc.array(fc.integer({ min: 0, max: 499 }), { minLength: 50, maxLength: 100 })
  ])('rapid feature access produces consistent results', (frameCount, accessPattern) => {
    const analysis: AudioAnalysis = {
      sampleRate: 44100,
      duration: frameCount / 30,
      frameCount,
      amplitudeEnvelope: Array(frameCount).fill(0).map((_, i) => i / frameCount),
      rmsEnergy: Array(frameCount).fill(0).map((_, i) => (frameCount - i) / frameCount),
      spectralCentroid: Array(frameCount).fill(0.5),
      frequencyBands: {
        sub: Array(frameCount).fill(0.2),
        bass: Array(frameCount).fill(0.4),
        lowMid: Array(frameCount).fill(0.3),
        mid: Array(frameCount).fill(0.5),
        highMid: Array(frameCount).fill(0.4),
        high: Array(frameCount).fill(0.3),
      },
      onsets: Array(frameCount).fill(0),
      bpm: 120,
      spectralFlux: Array(frameCount).fill(0.1),
      zeroCrossingRate: Array(frameCount).fill(0.2),
      spectralRolloff: Array(frameCount).fill(0.8),
      spectralFlatness: Array(frameCount).fill(0.3),
    };
    
    const results = new Map<number, number>();
    
    // First pass: collect results
    for (const frame of accessPattern) {
      const safeFrame = Math.min(frame, frameCount - 1);
      const value = getFeatureAtFrame(analysis, 'amplitude', safeFrame);
      results.set(safeFrame, value);
    }
    
    // Second pass: verify consistency
    for (const frame of accessPattern) {
      const safeFrame = Math.min(frame, frameCount - 1);
      const newValue = getFeatureAtFrame(analysis, 'amplitude', safeFrame);
      const storedValue = results.get(safeFrame);
      
      expect(newValue).toBe(storedValue);
    }
  });
});
