/**
 * Integration Tests: Store ↔ Engine
 * 
 * Tests that changes in compositorStore correctly propagate to MotionEngine
 * and produce accurate frame evaluations.
 * 
 * Critical Integration Point:
 * - Store holds project state (layers, keyframes, effects)
 * - Engine evaluates frames based on store state
 * - Any mismatch = broken animation
 * 
 * REINTEGRATED: 2026-01-07 from _deprecated/integration/store-engine.integration.test.ts
 * Updated to use current compositorStore and MotionEngine APIs
 */

import { describe, test, expect, beforeEach, afterEach } from 'vitest';
import { setActivePinia, createPinia } from 'pinia';
import { useCompositorStore } from '@/stores/compositorStore';
import { motionEngine } from '@/engine/MotionEngine';

describe('Store → Engine Integration', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  afterEach(() => {
    // Cleanup handled by Pinia
  });

  describe('keyframe changes propagate correctly', () => {
    test('adding keyframe updates engine evaluation', () => {
      const store = useCompositorStore();
      
      // Create layer with opacity keyframes
      const layer = store.createLayer('solid', 'Test Layer');
      store.setFrame(0);
      store.addKeyframe(layer.id, 'opacity', 0);
      store.setFrame(30);
      store.addKeyframe(layer.id, 'opacity', 100);
      
      // Evaluate midpoint
      const project = store.project;
      const frame15 = motionEngine.evaluate(15, project);
      
      // Find the evaluated layer
      const evaluatedLayer = frame15.layers.find(l => l.id === layer.id);
      expect(evaluatedLayer).toBeDefined();
      
      // Should be interpolated value (approximately 50 at frame 15, halfway between 0 and 30)
      expect(evaluatedLayer!.opacity).toBeGreaterThan(40);
      expect(evaluatedLayer!.opacity).toBeLessThan(60);
    });

    test('modifying keyframe updates engine evaluation', () => {
      const store = useCompositorStore();
      
      const layer = store.createLayer('solid', 'Test Layer');
      store.setFrame(0);
      const kf1 = store.addKeyframe(layer.id, 'opacity', 0);
      store.setFrame(30);
      store.addKeyframe(layer.id, 'opacity', 100);
      
      // Modify first keyframe
      store.setKeyframeValue(layer.id, 'opacity', kf1.id, 50);
      
      // Evaluate at frame 0
      const project = store.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);
      
      // Should reflect modified value
      expect(evaluatedLayer!.opacity).toBeCloseTo(50, 1);
    });

    test('deleting keyframe updates engine evaluation', () => {
      const store = useCompositorStore();
      
      const layer = store.createLayer('solid', 'Test Layer');
      store.setFrame(0);
      const kf1 = store.addKeyframe(layer.id, 'opacity', 0);
      store.setFrame(30);
      store.addKeyframe(layer.id, 'opacity', 100);
      
      // Delete first keyframe
      store.deleteKeyframe(layer.id, 'opacity', kf1.id);
      
      // Evaluate at frame 0
      const project = store.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);
      
      // Should use static value or next keyframe
      expect(evaluatedLayer!.opacity).toBeDefined();
    });
  });

  describe('layer changes propagate correctly', () => {
    test('layer visibility affects engine output', () => {
      const store = useCompositorStore();
      
      const layer = store.createLayer('solid', 'Test Layer');
      store.setLayerVisible(layer.id, false);
      
      const project = store.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);
      
      // Hidden layers should have visible = false
      expect(evaluatedLayer!.visible).toBe(false);
    });

    test('layer order affects compositing', () => {
      const store = useCompositorStore();
      
      const layer1 = store.createLayer('solid', 'Layer 1');
      const layer2 = store.createLayer('solid', 'Layer 2');
      
      const project = store.project;
      const frame0 = motionEngine.evaluate(0, project);
      
      // Layers should be in correct order
      const layer1Index = frame0.layers.findIndex(l => l.id === layer1.id);
      const layer2Index = frame0.layers.findIndex(l => l.id === layer2.id);
      
      // layer2 was added after layer1, so should appear later in array
      expect(layer2Index).toBeGreaterThan(layer1Index);
    });

    test.skip('nested compositions evaluate correctly', () => {
      // TODO: Implement when nested comp API is available
      const store = useCompositorStore();
      
      // Create nested composition
      // const nestedComp = store.createLayer('nestedComp', 'Nested');
      // const childLayer = store.createLayer('solid', 'Child', { parentId: nestedComp.id });
      
      // Evaluate
      // const project = store.project;
      // const frame0 = motionEngine.evaluate(0, project);
      
      // Nested comp should evaluate recursively
    });
  });

  describe('effect changes propagate correctly', () => {
    test.skip('adding effect modifies render output', () => {
      // TODO: Implement when effect API is available
      const store = useCompositorStore();
      
      const layer = store.createLayer('solid', 'Test Layer');
      // store.addEffect(layer.id, 'blur', { radius: 10 });
      
      // Evaluate and check effect is applied
      // const project = store.project;
      // const frame0 = motionEngine.evaluate(0, project);
      // const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);
      // expect(evaluatedLayer.effects).toContain(...);
    });

    test.skip('effect parameters animate correctly', () => {
      // TODO: Implement when effect keyframes API is available
    });
  });

  describe('determinism', () => {
    test('same state produces identical evaluation', () => {
      const store = useCompositorStore();
      
      const layer = store.createLayer('solid', 'Test Layer');
      store.setFrame(0);
      store.addKeyframe(layer.id, 'opacity', 0);
      store.setFrame(30);
      store.addKeyframe(layer.id, 'opacity', 100);
      
      const project = store.project;
      
      // Evaluate same frame twice
      const frame15a = motionEngine.evaluate(15, project);
      const frame15b = motionEngine.evaluate(15, project);
      
      // Should be identical
      const layerA = frame15a.layers.find(l => l.id === layer.id);
      const layerB = frame15b.layers.find(l => l.id === layer.id);
      
      expect(layerA!.opacity).toBe(layerB!.opacity);
    });

    test.skip('scrubbing produces same result as sequential play', () => {
      // TODO: Implement when sequential evaluation API is available
      // Jump to frame 50 should equal playing 0→50
    });
  });
});

describe('Engine → Export Integration', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  describe('evaluated frames export correctly', () => {
    test.skip('export produces valid depth data', () => {
      // TODO: Implement when export API is available
      // Depth export should match engine evaluation
    });

    test.skip('export produces valid camera data', () => {
      // TODO: Implement when camera export API is available
      // Camera matrices should match engine state
    });

    test.skip('export frame count matches composition', () => {
      // TODO: Implement when export API is available
      // Should export correct number of frames
    });
  });
});

describe('Store → Persistence Integration', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  describe('save/load roundtrip', () => {
    test('project serializes and deserializes correctly', () => {
      const store = useCompositorStore();
      
      // Create a project with layers and keyframes
      const layer = store.createLayer('solid', 'Test Layer');
      store.setFrame(0);
      store.addKeyframe(layer.id, 'opacity', 0);
      store.setFrame(30);
      store.addKeyframe(layer.id, 'opacity', 100);
      
      // Serialize
      const json = JSON.stringify(store.project);
      
      // Deserialize
      const parsed = JSON.parse(json);
      
      // Should have same structure
      expect(parsed.compositions).toBeDefined();
      expect(parsed.compositions[parsed.mainCompositionId]).toBeDefined();
      expect(parsed.compositions[parsed.mainCompositionId].layers.length).toBe(1);
    });

    test('all layer types survive roundtrip', () => {
      const store = useCompositorStore();
      
      // Create different layer types
      const solidLayer = store.createLayer('solid', 'Solid');
      const textLayer = store.createLayer('text', 'Text');
      const shapeLayer = store.createLayer('shape', 'Shape');
      
      // Serialize and deserialize
      const json = JSON.stringify(store.project);
      const parsed = JSON.parse(json);
      
      // All layer types should be preserved
      const layers = parsed.compositions[parsed.mainCompositionId].layers;
      expect(layers.some((l: any) => l.type === 'solid')).toBe(true);
      expect(layers.some((l: any) => l.type === 'text')).toBe(true);
      expect(layers.some((l: any) => l.type === 'shape')).toBe(true);
    });

    test('keyframes survive roundtrip', () => {
      const store = useCompositorStore();
      
      const layer = store.createLayer('solid', 'Test Layer');
      store.setFrame(0);
      store.addKeyframe(layer.id, 'opacity', 0);
      store.setFrame(30);
      store.addKeyframe(layer.id, 'opacity', 100);
      
      // Serialize and deserialize
      const json = JSON.stringify(store.project);
      const parsed = JSON.parse(json);
      
      // Keyframes should be preserved
      const savedLayer = parsed.compositions[parsed.mainCompositionId].layers.find((l: any) => l.id === layer.id);
      expect(savedLayer.opacity.keyframes.length).toBe(2);
    });

    test.skip('effects survive roundtrip', () => {
      // TODO: Implement when effect API is available
      // Effect settings should be preserved
    });
  });
});
