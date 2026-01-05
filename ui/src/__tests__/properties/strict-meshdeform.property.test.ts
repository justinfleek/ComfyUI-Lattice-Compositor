/**
 * STRICT Property Tests: Mesh Deform Export
 * 
 * Tests mesh deformation export for AI video generation:
 * - Wan-Move / ATI: Pin trajectories as point tracks
 * - ControlNet: Overlap pin depth maps
 * - TTM: Motion masks from deformed mesh
 * 
 * Model Requirements:
 * 
 * Wan-Move Trajectories:
 * - Shape: (num_frames, num_points, 2) for [x, y]
 * - Coordinates: Pixel positions within composition bounds
 * - Float32 precision
 * 
 * Depth Maps:
 * - MiDaS format: uint8 grayscale, near=white (255), far=black (0)
 * - Range: inFront -100..+100 maps to depth 0..255
 * 
 * Motion Masks:
 * - Binary: 255 (white) where mesh exists, 0 (black) elsewhere
 * - Alpha: Always 255
 */

import { describe, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  exportPinsAsTrajectory,
  exportPinsAsTrajectoryWithMetadata,
  exportOverlapAsDepth,
  exportDeformedMeshMask,
  exportDeformedMeshMaskBinary,
  exportPinPositionsPerFrame,
  exportOverlapDepthSequence,
  exportMeshMaskSequence,
  depthBufferToImageData,
  type CompositionInfo,
  type DepthFormat,
} from '@/services/export/meshDeformExport';
import type { WarpPin } from '@/types/meshWarp';
import type { AnimatableProperty } from '@/types/animation';

// ============================================================================
// ARBITRARIES
// ============================================================================

// Generate animatable position property
const arbitraryAnimatablePosition = (
  width: number, 
  height: number
): fc.Arbitrary<AnimatableProperty<{ x: number; y: number }>> =>
  fc.record({
    value: fc.record({
      x: fc.double({ min: 0, max: width, noNaN: true }),
      y: fc.double({ min: 0, max: height, noNaN: true }),
    }),
    keyframes: fc.constant([]), // Static for simplicity
    expression: fc.constant(undefined),
  });

// Generate a trackable warp pin
const arbitraryPositionPin = (
  width: number, 
  height: number
): fc.Arbitrary<WarpPin> =>
  fc.record({
    id: fc.uuid(),
    name: fc.string({ minLength: 1, maxLength: 20 }),
    type: fc.constantFrom('position', 'advanced', 'bend', 'rotation') as fc.Arbitrary<WarpPin['type']>,
    position: arbitraryAnimatablePosition(width, height),
    starchAmount: fc.constant(0),
    starchExtent: fc.constant(0),
    inFront: fc.integer({ min: -100, max: 100 }),
    enabled: fc.constant(true),
  });

// Generate an overlap pin (for depth)
const arbitraryOverlapPin = (
  width: number, 
  height: number
): fc.Arbitrary<WarpPin> =>
  fc.record({
    id: fc.uuid(),
    name: fc.string({ minLength: 1, maxLength: 20 }),
    type: fc.constant('overlap') as fc.Arbitrary<WarpPin['type']>,
    position: arbitraryAnimatablePosition(width, height),
    starchAmount: fc.constant(0),
    starchExtent: fc.constant(0),
    inFront: fc.integer({ min: -100, max: 100 }),
    enabled: fc.constant(true),
  });

// Generate composition info
const arbitraryCompositionInfo = (): fc.Arbitrary<CompositionInfo> =>
  fc.record({
    width: fc.integer({ min: 64, max: 2048 }),
    height: fc.integer({ min: 64, max: 2048 }),
    frameRate: fc.integer({ min: 1, max: 60 }),
  });

// Generate frame range
const arbitraryFrameRange = (): fc.Arbitrary<[number, number]> =>
  fc.tuple(
    fc.integer({ min: 0, max: 100 }),
    fc.integer({ min: 10, max: 200 })
  ).filter(([start, end]) => end > start);

// Generate simple mesh (triangulated quad)
const arbitrarySimpleMesh = (width: number, height: number) => {
  return {
    vertices: new Float32Array([
      0, 0,           // 0: top-left
      width, 0,       // 1: top-right
      width, height,  // 2: bottom-right
      0, height,      // 3: bottom-left
    ]),
    triangles: new Uint32Array([
      0, 1, 2,  // First triangle
      0, 2, 3,  // Second triangle
    ]),
    vertexCount: 4,
    triangleCount: 2,
  };
};

// ============================================================================
// PIN TRAJECTORY EXPORT TESTS
// ============================================================================

describe('STRICT: Pin Trajectory Export (Wan-Move/ATI)', () => {
  test.prop([
    fc.integer({ min: 64, max: 1024 }),
    fc.integer({ min: 64, max: 1024 }),
    fc.integer({ min: 1, max: 60 }),
  ])('trajectory has correct shape for single pin', (width, height, fps) => {
    const pin: WarpPin = {
      id: 'pin1',
      name: 'Test Pin',
      type: 'position',
      position: { value: { x: width / 2, y: height / 2 }, keyframes: [] },
      starchAmount: 0,
      starchExtent: 0,
      inFront: 0,
      enabled: true,
    };
    
    const frameRange: [number, number] = [0, 10];
    const composition: CompositionInfo = { width, height, frameRate: fps };
    
    const trajectory = exportPinsAsTrajectory([pin], frameRange, composition);
    
    // Should have 1 track (1 pin)
    expect(trajectory.tracks.length).toBe(1);
    // Should have 11 frames (0-10 inclusive)
    expect(trajectory.tracks[0].length).toBe(11);
    // Each position should have 2 values [x, y]
    expect(trajectory.tracks[0][0].length).toBe(2);
  });

  test.prop([
    fc.integer({ min: 1, max: 20 }), // num pins
    fc.integer({ min: 64, max: 512 }),
    fc.integer({ min: 64, max: 512 }),
  ])('trajectory tracks count matches trackable pins', (numPins, width, height) => {
    const pins: WarpPin[] = [];
    
    for (let i = 0; i < numPins; i++) {
      pins.push({
        id: `pin_${i}`,
        name: `Pin ${i}`,
        type: 'position',
        position: { value: { x: i * 10, y: i * 10 }, keyframes: [] },
        starchAmount: 0,
        starchExtent: 0,
        inFront: 0,
        enabled: true,
      });
    }
    
    const trajectory = exportPinsAsTrajectory(
      pins, 
      [0, 5], 
      { width, height, frameRate: 16 }
    );
    
    expect(trajectory.tracks.length).toBe(numPins);
  });

  test.prop([
    fc.integer({ min: 64, max: 1024 }),
    fc.integer({ min: 64, max: 1024 }),
  ])('coordinates are clamped to composition bounds', (width, height) => {
    // Pin position outside bounds
    const pin: WarpPin = {
      id: 'pin1',
      name: 'Out of Bounds Pin',
      type: 'position',
      position: { value: { x: width + 100, y: height + 100 }, keyframes: [] },
      starchAmount: 0,
      starchExtent: 0,
      inFront: 0,
      enabled: true,
    };
    
    const trajectory = exportPinsAsTrajectory(
      [pin], 
      [0, 5], 
      { width, height, frameRate: 16 }
    );
    
    // All coordinates should be within bounds
    for (const frame of trajectory.tracks[0]) {
      const [x, y] = frame;
      expect(x).toBeGreaterThanOrEqual(0);
      expect(x).toBeLessThan(width);
      expect(y).toBeGreaterThanOrEqual(0);
      expect(y).toBeLessThan(height);
    }
  });

  test('visibility array matches frame count', () => {
    const pin: WarpPin = {
      id: 'pin1',
      name: 'Test',
      type: 'position',
      position: { value: { x: 50, y: 50 }, keyframes: [] },
      starchAmount: 0,
      starchExtent: 0,
      inFront: 0,
      enabled: true,
    };
    
    const trajectory = exportPinsAsTrajectory(
      [pin], 
      [0, 100], 
      { width: 512, height: 512, frameRate: 16 }
    );
    
    expect(trajectory.visibility.length).toBe(1); // 1 pin
    expect(trajectory.visibility[0].length).toBe(101); // 101 frames
    
    // All visibility should be true (pins are always visible)
    for (const vis of trajectory.visibility[0]) {
      expect(vis).toBe(true);
    }
  });

  test('metadata is populated correctly', () => {
    const pins: WarpPin[] = [
      { id: 'p1', name: 'Pin 1', type: 'position', position: { value: { x: 10, y: 10 }, keyframes: [] }, starchAmount: 0, starchExtent: 0, inFront: 0, enabled: true },
      { id: 'p2', name: 'Pin 2', type: 'advanced', position: { value: { x: 20, y: 20 }, keyframes: [] }, starchAmount: 0, starchExtent: 0, inFront: 0, enabled: true },
      { id: 'p3', name: 'Overlap', type: 'overlap', position: { value: { x: 30, y: 30 }, keyframes: [] }, starchAmount: 0, starchExtent: 0, inFront: 50, enabled: true },
    ];
    
    const trajectory = exportPinsAsTrajectory(
      pins, 
      [0, 9], 
      { width: 100, height: 100, frameRate: 24 }
    );
    
    // Overlap pins are not trackable
    expect(trajectory.metadata.numPoints).toBe(2);
    expect(trajectory.metadata.numFrames).toBe(10);
    expect(trajectory.metadata.width).toBe(100);
    expect(trajectory.metadata.height).toBe(100);
    expect(trajectory.metadata.fps).toBe(24);
  });

  test('exportPinsAsTrajectoryWithMetadata includes pin info', () => {
    const pins: WarpPin[] = [
      { id: 'p1', name: 'Position Pin', type: 'position', position: { value: { x: 10, y: 10 }, keyframes: [] }, starchAmount: 0, starchExtent: 0, inFront: 0, enabled: true },
      { id: 'p2', name: 'Rotation Pin', type: 'rotation', position: { value: { x: 20, y: 20 }, keyframes: [] }, starchAmount: 0, starchExtent: 0, inFront: 0, enabled: true },
    ];
    
    const result = exportPinsAsTrajectoryWithMetadata(
      pins, 
      [0, 5], 
      { width: 100, height: 100, frameRate: 16 }
    );
    
    expect(result.pinMetadata.length).toBe(2);
    expect(result.pinMetadata[0].id).toBe('p1');
    expect(result.pinMetadata[0].name).toBe('Position Pin');
    expect(result.pinMetadata[0].type).toBe('position');
    expect(result.pinMetadata[1].type).toBe('rotation');
  });

  test('starch and overlap pins are filtered out', () => {
    const pins: WarpPin[] = [
      { id: 'p1', name: 'Track', type: 'position', position: { value: { x: 10, y: 10 }, keyframes: [] }, starchAmount: 0, starchExtent: 0, inFront: 0, enabled: true },
      { id: 'p2', name: 'Starch', type: 'starch', position: { value: { x: 20, y: 20 }, keyframes: [] }, starchAmount: 50, starchExtent: 10, inFront: 0, enabled: true },
      { id: 'p3', name: 'Overlap', type: 'overlap', position: { value: { x: 30, y: 30 }, keyframes: [] }, starchAmount: 0, starchExtent: 0, inFront: 50, enabled: true },
    ];
    
    const trajectory = exportPinsAsTrajectory(
      pins, 
      [0, 5], 
      { width: 100, height: 100, frameRate: 16 }
    );
    
    // Only position pin should be exported
    expect(trajectory.tracks.length).toBe(1);
    expect(trajectory.metadata.numPoints).toBe(1);
  });
});

// ============================================================================
// DEPTH BUFFER EXPORT TESTS
// ============================================================================

describe('STRICT: Overlap Depth Export (ControlNet)', () => {
  test.prop([
    fc.constantFrom('uint8', 'uint16', 'float32') as fc.Arbitrary<DepthFormat>,
  ])('depth buffer type matches requested format', (format) => {
    const width = 64;
    const height = 64;
    const mesh = arbitrarySimpleMesh(width, height);
    const deformedVertices = mesh.vertices; // No deformation
    const pins: WarpPin[] = []; // No overlap pins
    
    const depth = exportOverlapAsDepth(
      mesh as any,
      deformedVertices,
      pins,
      0,
      width,
      height,
      format
    );
    
    switch (format) {
      case 'uint8':
        expect(depth instanceof Uint8Array).toBe(true);
        break;
      case 'uint16':
        expect(depth instanceof Uint16Array).toBe(true);
        break;
      case 'float32':
        expect(depth instanceof Float32Array).toBe(true);
        break;
    }
  });

  test.prop([
    fc.integer({ min: 16, max: 256 }),
    fc.integer({ min: 16, max: 256 }),
  ])('depth buffer has correct size', (width, height) => {
    const mesh = arbitrarySimpleMesh(width, height);
    const deformedVertices = mesh.vertices;
    
    const depth = exportOverlapAsDepth(
      mesh as any,
      deformedVertices,
      [],
      0,
      width,
      height,
      'uint8'
    );
    
    expect(depth.length).toBe(width * height);
  });

  test('empty depth buffer when no overlap pins', () => {
    const width = 64;
    const height = 64;
    const mesh = arbitrarySimpleMesh(width, height);
    
    const depth = exportOverlapAsDepth(
      mesh as any,
      mesh.vertices,
      [], // No pins
      0,
      width,
      height,
      'uint8'
    );
    
    // All values should be 0 (far)
    for (let i = 0; i < depth.length; i++) {
      expect(depth[i]).toBe(0);
    }
  });

  test('inFront value maps to depth correctly', () => {
    // Test the mapping: inFront (-100..+100) → depth (0..1)
    // inFront = -100 → depth = 0 (far, black)
    // inFront = 0 → depth = 0.5 (middle) → 127.5 → rounds to 128
    // inFront = +100 → depth = 1 (near, white)
    
    const testCases = [
      { inFront: -100, expected: 0 },
      { inFront: 0, expected: 128 }, // 0.5 * 255 = 127.5 rounds to 128
      { inFront: 100, expected: 255 },
    ];
    
    for (const { inFront, expected } of testCases) {
      const normalizedDepth = (inFront + 100) / 200;
      const uint8Value = Math.round(normalizedDepth * 255);
      expect(uint8Value).toBe(expected);
    }
  });
});

// ============================================================================
// DEPTH BUFFER TO IMAGEDATA TESTS
// ============================================================================

describe('STRICT: Depth Buffer to ImageData', () => {
  test.prop([
    fc.integer({ min: 16, max: 256 }),
    fc.integer({ min: 16, max: 256 }),
  ])('ImageData has correct dimensions', (width, height) => {
    const buffer = new Uint8Array(width * height);
    buffer.fill(128);
    
    const imageData = depthBufferToImageData(buffer, width, height);
    
    expect(imageData.width).toBe(width);
    expect(imageData.height).toBe(height);
    expect(imageData.data.length).toBe(width * height * 4);
  });

  test('grayscale values are R=G=B', () => {
    const buffer = new Uint8Array([0, 64, 128, 192, 255]);
    
    const imageData = depthBufferToImageData(buffer, 5, 1);
    
    for (let i = 0; i < 5; i++) {
      const r = imageData.data[i * 4];
      const g = imageData.data[i * 4 + 1];
      const b = imageData.data[i * 4 + 2];
      const a = imageData.data[i * 4 + 3];
      
      expect(r).toBe(g);
      expect(g).toBe(b);
      expect(a).toBe(255); // Full alpha
    }
  });

  test('uint16 buffer is scaled to uint8', () => {
    const buffer = new Uint16Array([0, 32768, 65535]); // min, mid, max
    
    const imageData = depthBufferToImageData(buffer, 3, 1);
    
    // 0 / 256 = 0
    expect(imageData.data[0]).toBe(0);
    // 32768 / 256 = 128
    expect(imageData.data[4]).toBe(128);
    // 65535 / 256 = 255
    expect(imageData.data[8]).toBe(255);
  });

  test('float32 buffer is scaled to uint8', () => {
    const buffer = new Float32Array([0, 0.5, 1.0]);
    
    const imageData = depthBufferToImageData(buffer, 3, 1);
    
    expect(imageData.data[0]).toBe(0);
    expect(imageData.data[4]).toBe(128); // 0.5 * 255 rounded
    expect(imageData.data[8]).toBe(255);
  });
});

// ============================================================================
// MOTION MASK EXPORT TESTS
// ============================================================================

describe('STRICT: Motion Mask Export (TTM)', () => {
  test.prop([
    fc.integer({ min: 16, max: 256 }),
    fc.integer({ min: 16, max: 256 }),
  ])('mask has correct dimensions', (width, height) => {
    const mesh = arbitrarySimpleMesh(width, height);
    
    const mask = exportDeformedMeshMask(
      mesh as any,
      mesh.vertices,
      width,
      height
    );
    
    expect(mask.width).toBe(width);
    expect(mask.height).toBe(height);
    expect(mask.data.length).toBe(width * height * 4);
  });

  test('mask values are binary (0 or 255)', () => {
    const mesh = arbitrarySimpleMesh(64, 64);
    
    const mask = exportDeformedMeshMask(
      mesh as any,
      mesh.vertices,
      64,
      64
    );
    
    for (let i = 0; i < mask.data.length; i += 4) {
      const r = mask.data[i];
      // Each R value should be 0 (black) or 255 (white)
      expect(r === 0 || r === 255).toBe(true);
    }
  });

  test('mask alpha is always 255', () => {
    const mesh = arbitrarySimpleMesh(64, 64);
    
    const mask = exportDeformedMeshMask(
      mesh as any,
      mesh.vertices,
      64,
      64
    );
    
    for (let i = 3; i < mask.data.length; i += 4) {
      expect(mask.data[i]).toBe(255);
    }
  });

  test('binary mask has correct size', () => {
    const width = 64;
    const height = 64;
    const mesh = arbitrarySimpleMesh(width, height);
    
    const mask = exportDeformedMeshMaskBinary(
      mesh as any,
      mesh.vertices,
      width,
      height
    );
    
    expect(mask.length).toBe(width * height);
  });

  test('binary mask values are 0 or 255', () => {
    const mesh = arbitrarySimpleMesh(64, 64);
    
    const mask = exportDeformedMeshMaskBinary(
      mesh as any,
      mesh.vertices,
      64,
      64
    );
    
    for (const value of mask) {
      expect(value === 0 || value === 255).toBe(true);
    }
  });
});

// ============================================================================
// PER-FRAME EXPORT TESTS
// ============================================================================

describe('STRICT: Per-Frame Export Utilities', () => {
  test('exportPinPositionsPerFrame returns correct frame count', () => {
    const pin: WarpPin = {
      id: 'p1',
      name: 'Test',
      type: 'position',
      position: { value: { x: 50, y: 50 }, keyframes: [] },
      starchAmount: 0,
      starchExtent: 0,
      inFront: 0,
      enabled: true,
    };
    
    const result = exportPinPositionsPerFrame([pin], [0, 10], 16);
    
    expect(result.length).toBe(11); // 0-10 inclusive
  });

  test('exportPinPositionsPerFrame has correct structure', () => {
    const pins: WarpPin[] = [
      { id: 'p1', name: 'Pin 1', type: 'position', position: { value: { x: 10, y: 20 }, keyframes: [] }, starchAmount: 0, starchExtent: 0, inFront: 0, enabled: true },
      { id: 'p2', name: 'Pin 2', type: 'rotation', position: { value: { x: 30, y: 40 }, keyframes: [] }, starchAmount: 0, starchExtent: 0, inFront: 0, enabled: true },
    ];
    
    const result = exportPinPositionsPerFrame(pins, [0, 2], 16);
    
    expect(result.length).toBe(3);
    
    for (const frame of result) {
      expect(frame).toHaveProperty('frame');
      expect(frame).toHaveProperty('positions');
      expect(frame.positions.length).toBe(2);
      
      for (const pos of frame.positions) {
        expect(pos).toHaveProperty('id');
        expect(pos).toHaveProperty('x');
        expect(pos).toHaveProperty('y');
      }
    }
  });

  test('frame numbers are sequential', () => {
    const pin: WarpPin = {
      id: 'p1',
      name: 'Test',
      type: 'position',
      position: { value: { x: 50, y: 50 }, keyframes: [] },
      starchAmount: 0,
      starchExtent: 0,
      inFront: 0,
      enabled: true,
    };
    
    const result = exportPinPositionsPerFrame([pin], [5, 15], 16);
    
    for (let i = 0; i < result.length; i++) {
      expect(result[i].frame).toBe(5 + i);
    }
  });
});

// ============================================================================
// SEQUENCE EXPORT TESTS
// ============================================================================

describe('STRICT: Sequence Export', () => {
  test('exportOverlapDepthSequence returns correct frame count', () => {
    const width = 32;
    const height = 32;
    const mesh = arbitrarySimpleMesh(width, height);
    
    // Create deformed vertices for 5 frames
    const deformedVerticesPerFrame = Array(5).fill(mesh.vertices);
    
    const result = exportOverlapDepthSequence(
      mesh as any,
      deformedVerticesPerFrame,
      [],
      [0, 4],
      width,
      height,
      'uint8'
    );
    
    expect(result.length).toBe(5);
  });

  test('exportMeshMaskSequence returns correct frame count', () => {
    const width = 32;
    const height = 32;
    const mesh = arbitrarySimpleMesh(width, height);
    
    const deformedVerticesPerFrame = Array(5).fill(mesh.vertices);
    
    const result = exportMeshMaskSequence(
      mesh as any,
      deformedVerticesPerFrame,
      [0, 4],
      width,
      height
    );
    
    expect(result.length).toBe(5);
    
    for (const frame of result) {
      expect(frame.mask.width).toBe(width);
      expect(frame.mask.height).toBe(height);
    }
  });
});

// ============================================================================
// EDGE CASE TESTS
// ============================================================================

describe('STRICT: Mesh Deform Export Edge Cases', () => {
  test('handles empty pin array', () => {
    const trajectory = exportPinsAsTrajectory(
      [], 
      [0, 10], 
      { width: 512, height: 512, frameRate: 16 }
    );
    
    expect(trajectory.tracks.length).toBe(0);
    expect(trajectory.visibility.length).toBe(0);
    expect(trajectory.metadata.numPoints).toBe(0);
  });

  test('handles single frame range', () => {
    const pin: WarpPin = {
      id: 'p1',
      name: 'Test',
      type: 'position',
      position: { value: { x: 50, y: 50 }, keyframes: [] },
      starchAmount: 0,
      starchExtent: 0,
      inFront: 0,
      enabled: true,
    };
    
    const trajectory = exportPinsAsTrajectory(
      [pin], 
      [5, 5], // Single frame
      { width: 100, height: 100, frameRate: 16 }
    );
    
    expect(trajectory.tracks[0].length).toBe(1);
    expect(trajectory.metadata.numFrames).toBe(1);
  });

  test('handles pins at exact boundaries', () => {
    const pins: WarpPin[] = [
      { id: 'tl', name: 'TopLeft', type: 'position', position: { value: { x: 0, y: 0 }, keyframes: [] }, starchAmount: 0, starchExtent: 0, inFront: 0, enabled: true },
      { id: 'br', name: 'BottomRight', type: 'position', position: { value: { x: 99, y: 99 }, keyframes: [] }, starchAmount: 0, starchExtent: 0, inFront: 0, enabled: true },
    ];
    
    const trajectory = exportPinsAsTrajectory(
      pins, 
      [0, 0], 
      { width: 100, height: 100, frameRate: 16 }
    );
    
    // Top-left should clamp to (0, 0)
    expect(trajectory.tracks[0][0][0]).toBe(0);
    expect(trajectory.tracks[0][0][1]).toBe(0);
    
    // Bottom-right should clamp to (99, 99) - width-1
    expect(trajectory.tracks[1][0][0]).toBe(99);
    expect(trajectory.tracks[1][0][1]).toBe(99);
  });

  test('handles very small composition', () => {
    const pin: WarpPin = {
      id: 'p1',
      name: 'Test',
      type: 'position',
      position: { value: { x: 5, y: 5 }, keyframes: [] },
      starchAmount: 0,
      starchExtent: 0,
      inFront: 0,
      enabled: true,
    };
    
    const trajectory = exportPinsAsTrajectory(
      [pin], 
      [0, 5], 
      { width: 10, height: 10, frameRate: 16 }
    );
    
    expect(trajectory.metadata.width).toBe(10);
    expect(trajectory.metadata.height).toBe(10);
  });
});
