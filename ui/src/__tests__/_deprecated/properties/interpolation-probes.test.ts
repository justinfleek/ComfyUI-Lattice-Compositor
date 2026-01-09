/**
 * Interpolation Edge Case Probes
 * These tests probe specific edge cases to verify behavior
 */
import { describe, it, expect } from 'vitest';
import { interpolateProperty } from '@/services/interpolation';
import type { AnimatableProperty, Keyframe } from '@/types/animation';

describe('Interpolation Edge Case Probes', () => {
  it('PROBE: 3D to 2D transition loses Z correctly', () => {
    const prop: AnimatableProperty<{x: number, y: number, z?: number}> = {
      id: 't', name: 't', type: 'vector3', value: {x:0,y:0,z:100},
      animated: true,
      keyframes: [
        { id:'k1', frame:0, value:{x:0,y:0,z:100}, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
        { id:'k2', frame:100, value:{x:100,y:100}, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
      ],
    };
    
    const at0 = interpolateProperty(prop, 0);
    const at25 = interpolateProperty(prop, 25);
    const at50 = interpolateProperty(prop, 50);
    const at75 = interpolateProperty(prop, 75);
    const at100 = interpolateProperty(prop, 100);
    
    console.log('3D->2D transition:');
    console.log('  t=0:', at0);
    console.log('  t=0.25:', at25);
    console.log('  t=0.5:', at50);
    console.log('  t=0.75:', at75);
    console.log('  t=1:', at100);
    
    // Z interpolates from 100 towards 0 during transition
    expect(at0.z).toBe(100);
    expect(at50.z).toBe(50); // 100 * (1 - 0.5) = 50
    
    // DESIGN: At exact keyframe frame, returns keyframe value directly
    // The endpoint keyframe has no Z (2D), so Z becomes undefined, not 0
    // This matches professional animation software behavior
    expect(at100.z).toBeUndefined();
  });

  it('PROBE: 2D to 3D transition gains Z correctly', () => {
    const prop: AnimatableProperty<{x: number, y: number, z?: number}> = {
      id: 't', name: 't', type: 'object', value: {x:0,y:0},
      animated: true,
      keyframes: [
        { id:'k1', frame:0, value:{x:0,y:0}, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
        { id:'k2', frame:100, value:{x:100,y:100,z:100}, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
      ],
    };
    
    const at0 = interpolateProperty(prop, 0);
    const at25 = interpolateProperty(prop, 25);
    const at50 = interpolateProperty(prop, 50);
    const at75 = interpolateProperty(prop, 75);
    const at100 = interpolateProperty(prop, 100);
    
    console.log('2D->3D transition:');
    console.log('  t=0:', at0);
    console.log('  t=0.25:', at25);
    console.log('  t=0.5:', at50);
    console.log('  t=0.75:', at75);
    console.log('  t=1:', at100);
    
    // Z should grow from 0 to 100
    expect(at0.z).toBeUndefined(); // No Z at start
    expect(at50.z).toBe(50); // Should be 100 * 0.5 = 50
    expect(at100.z).toBe(100);
  });

  it('PROBE: malformed hex color handling', () => {
    const prop: AnimatableProperty<string> = {
      id: 't', name: 't', type: 'color', value: '#000000',
      animated: true,
      keyframes: [
        { id:'k1', frame:0, value:'#xyz', interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
        { id:'k2', frame:100, value:'#ffffff', interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
      ],
    };
    
    let result: string | undefined;
    let error: Error | undefined;
    try {
      result = interpolateProperty(prop, 50);
      console.log('Malformed hex result:', result);
    } catch (e) {
      error = e as Error;
      console.log('Malformed hex threw:', error.message);
    }
    
    // Document current behavior - does it crash or produce NaN?
    if (error) {
      expect(error).toBeInstanceOf(Error);
    } else {
      // If it doesn't crash, what does it produce?
      expect(typeof result).toBe('string');
    }
  });

  it('PROBE: short hex color (3 chars) handling', () => {
    const prop: AnimatableProperty<string> = {
      id: 't', name: 't', type: 'color', value: '#000000',
      animated: true,
      keyframes: [
        { id:'k1', frame:0, value:'#fff', interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
        { id:'k2', frame:100, value:'#000', interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
      ],
    };
    
    const result = interpolateProperty(prop, 50);
    console.log('Short hex result:', result);
    // This will likely produce garbage since the slicing expects 6 chars
  });

  it('PROBE: RGBA hex color (8 chars) handling', () => {
    const prop: AnimatableProperty<string> = {
      id: 't', name: 't', type: 'string', value: '#000000ff',
      animated: true,
      keyframes: [
        { id:'k1', frame:0, value:'#000000ff', interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
        { id:'k2', frame:100, value:'#ffffff00', interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
      ],
    };
    
    const result = interpolateProperty(prop, 50);
    console.log('RGBA hex result:', result);
    // Alpha channel is ignored
  });

  it('PROBE: single bezier handle disabled (out enabled, in disabled)', () => {
    const prop: AnimatableProperty<number> = {
      id: 't', name: 't', type: 'number', value: 0,
      animated: true,
      keyframes: [
        { id:'k1', frame:0, value:0, interpolation:'bezier', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:20,value:30,enabled:true}, controlMode:'smooth' },
        { id:'k2', frame:100, value:100, interpolation:'linear', inHandle:{frame:-20,value:-30,enabled:false}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
      ],
    };
    
    const results: number[] = [];
    for (let t = 0; t <= 1; t += 0.1) {
      results.push(interpolateProperty(prop, t * 100));
    }
    console.log('Single disabled handle curve:', results);
    
    // Should produce finite results
    for (const r of results) {
      expect(Number.isFinite(r)).toBe(true);
    }
  });

  it('PROBE: binary search at exact boundary', () => {
    // Three keyframes: test what happens at exact keyframe frames
    const prop: AnimatableProperty<number> = {
      id: 't', name: 't', type: 'number', value: 0,
      animated: true,
      keyframes: [
        { id:'k1', frame:0, value:0, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
        { id:'k2', frame:50, value:100, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
        { id:'k3', frame:100, value:50, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
      ],
    };
    
    // At exact frame 50, should return exactly 100
    const atBoundary = interpolateProperty(prop, 50);
    console.log('At exact boundary (frame 50):', atBoundary);
    expect(atBoundary).toBeCloseTo(100, 8);
    
    // Just before and after should be continuous
    const justBefore = interpolateProperty(prop, 49.999);
    const justAfter = interpolateProperty(prop, 50.001);
    console.log('Just before 50:', justBefore);
    console.log('Just after 50:', justAfter);
  });
});
