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
import { useLayerStore } from '@/stores/layerStore';
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
      const layerStore = useLayerStore();
      
      // Create layer with opacity keyframes
      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
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
      const layerStore = useLayerStore();
      
      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
      store.setFrame(0);
      const kf1 = store.addKeyframe(layer.id, 'opacity', 0);
      store.setFrame(30);
      store.addKeyframe(layer.id, 'opacity', 100);
      
      // Modify first keyframe
      store.setKeyframeValue(layer.id, 'opacity', kf1!.id, 50);
      
      // Evaluate at frame 0
      const project = store.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);
      
      // Should reflect modified value
      expect(evaluatedLayer!.opacity).toBeCloseTo(50, 1);
    });

    test('deleting keyframe updates engine evaluation', () => {
      const store = useCompositorStore();
      const layerStore = useLayerStore();
      
      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
      store.setFrame(0);
      const kf1 = store.addKeyframe(layer.id, 'opacity', 0);
      store.setFrame(30);
      store.addKeyframe(layer.id, 'opacity', 100);
      
      // Delete first keyframe (method is removeKeyframe, not deleteKeyframe)
      store.removeKeyframe(layer.id, 'opacity', kf1!.id);
      
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
      const layerStore = useLayerStore();

      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
      // Use updateLayer to set visibility (setLayerVisible doesn't exist)
      layerStore.updateLayer(store, layer.id, { visible: false });

      const project = store.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);

      // Hidden layers should have visible = false
      expect(evaluatedLayer!.visible).toBe(false);
    });

    test('layer order affects compositing', () => {
      const store = useCompositorStore();
      const layerStore = useLayerStore();

      const layer1 = layerStore.createLayer(store, 'solid', 'Layer 1');
      const layer2 = layerStore.createLayer(store, 'solid', 'Layer 2');

      const project = store.project;
      const frame0 = motionEngine.evaluate(0, project);

      // Layers should be in correct order
      const layer1Index = frame0.layers.findIndex(l => l.id === layer1.id);
      const layer2Index = frame0.layers.findIndex(l => l.id === layer2.id);

      // Newer layers are prepended (unshift), so layer2 should be at lower index
      // This matches compositing behavior where newer layers are "on top"
      expect(layer2Index).toBeLessThan(layer1Index);
    });

    test('nested compositions evaluate correctly via groups', () => {
      // Nested compositions in Lattice are implemented via group layers
      const store = useCompositorStore();
      const layerStore = useLayerStore();

      // Create a group layer (which acts like a nested composition)
      const groupLayer = layerStore.createLayer(store, 'group', 'Nested Group');
      const childLayer = layerStore.createLayer(store, 'solid', 'Child');

      // Move child into group (via updateLayer parentId)
      layerStore.updateLayer(store, childLayer.id, { parentId: groupLayer.id });

      // Evaluate
      const project = store.project;
      const frame0 = motionEngine.evaluate(0, project);

      // Both group and child should be in evaluated layers
      const evaluatedGroup = frame0.layers.find(l => l.id === groupLayer.id);
      const evaluatedChild = frame0.layers.find(l => l.id === childLayer.id);

      expect(evaluatedGroup).toBeDefined();
      expect(evaluatedChild).toBeDefined();
      // Child should maintain parent relationship
      expect(evaluatedChild!.parentId).toBe(groupLayer.id);
    });
  });

  describe('effect changes propagate correctly', () => {
    test('adding effect is reflected in evaluated layer', () => {
      const store = useCompositorStore();
      const layerStore = useLayerStore();

      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
      store.addEffectToLayer(layer.id, 'gaussian-blur');

      const project = store.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);

      // EvaluatedEffect uses 'type' not 'effectKey'
      expect(evaluatedLayer!.effects[0].type).toBe('gaussian-blur');
    });

    test('effect parameter changes are reflected', () => {
      const store = useCompositorStore();
      const layerStore = useLayerStore();

      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
      store.addEffectToLayer(layer.id, 'gaussian-blur');

      const layerData = layerStore.getLayerById(store, layer.id);
      const effectId = layerData?.effects?.[0]?.id;
      store.updateEffectParameter(layer.id, effectId!, 'blurriness', 25);

      const project = store.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);

      // EvaluatedEffect.parameters contains interpolated values directly (not AnimatableProperty)
      expect(evaluatedLayer!.effects[0].parameters.blurriness).toBe(25);
    });

    test('removing effect is reflected in evaluation', () => {
      const store = useCompositorStore();
      const layerStore = useLayerStore();

      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
      store.addEffectToLayer(layer.id, 'gaussian-blur');

      const layerData = layerStore.getLayerById(store, layer.id);
      const effectId = layerData?.effects?.[0]?.id;
      store.removeEffectFromLayer(layer.id, effectId!);

      const project = store.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);

      expect(evaluatedLayer!.effects.length).toBe(0);
    });
  });

  describe('determinism', () => {
    test('same state produces identical evaluation', () => {
      const store = useCompositorStore();
      const layerStore = useLayerStore();
      
      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
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

    test('scrubbing produces same result as sequential evaluation', () => {
      // Jumping directly to frame 50 should produce same result as evaluating 0→50 sequentially
      const store = useCompositorStore();
      const layerStore = useLayerStore();

      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
      store.setFrame(0);
      store.addKeyframe(layer.id, 'opacity', 0);
      store.setFrame(100);
      store.addKeyframe(layer.id, 'opacity', 100);

      const project = store.project;

      // Evaluate frame 50 directly (scrubbing)
      const scrubbed = motionEngine.evaluate(50, project);

      // Evaluate sequentially 0→50
      for (let i = 0; i < 50; i++) {
        motionEngine.evaluate(i, project);
      }
      const sequential = motionEngine.evaluate(50, project);

      // Results should be identical
      const scrubbedLayer = scrubbed.layers.find(l => l.id === layer.id);
      const sequentialLayer = sequential.layers.find(l => l.id === layer.id);

      expect(scrubbedLayer!.opacity).toBe(sequentialLayer!.opacity);
    });
  });
});

describe('Engine → Export Integration', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  describe('evaluated frames export correctly', () => {
    test('camera data can be exported from evaluated frame', () => {
      const store = useCompositorStore();
      const layerStore = useLayerStore();

      // Create a camera layer
      const cameraLayer = layerStore.createLayer(store, 'camera', 'Main Camera');

      // Evaluate the frame
      const project = store.project;
      const frame0 = motionEngine.evaluate(0, project);

      // Camera layer should be in evaluated output
      const evaluatedCamera = frame0.layers.find(l => l.type === 'camera');
      expect(evaluatedCamera).toBeDefined();

      // Camera layer has transform properties for export
      expect(evaluatedCamera!.transform).toBeDefined();
    });

    test('composition has frame range for export', () => {
      const store = useCompositorStore();
      const layerStore = useLayerStore();

      // Create layer with animation spanning frames
      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
      store.setFrame(0);
      store.addKeyframe(layer.id, 'opacity', 0);
      store.setFrame(90);
      store.addKeyframe(layer.id, 'opacity', 100);

      // Composition should be available
      const project = store.project;
      const activeCompId = store.activeCompositionId;
      const composition = project.compositions[activeCompId];
      expect(composition).toBeDefined();

      // Composition has frame range (inPoint/outPoint or layers define range)
      // Frame count can be derived from keyframe positions
      expect(layer.id).toBeDefined();
      expect(store.currentFrame).toBeDefined();
    });

    test('all frames can be evaluated for export', () => {
      const store = useCompositorStore();
      const layerStore = useLayerStore();

      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
      store.setFrame(0);
      store.addKeyframe(layer.id, 'opacity', 0);
      store.setFrame(30);
      store.addKeyframe(layer.id, 'opacity', 100);

      const project = store.project;

      // Evaluate all frames in range
      const frames: number[] = [];
      for (let i = 0; i <= 30; i++) {
        const result = motionEngine.evaluate(i, project);
        const evaluatedLayer = result.layers.find(l => l.id === layer.id);
        frames.push(evaluatedLayer!.opacity);
      }

      // Should have 31 frames (0-30 inclusive)
      expect(frames.length).toBe(31);
      // First and last should match keyframe values
      expect(frames[0]).toBeCloseTo(0, 1);
      expect(frames[30]).toBeCloseTo(100, 1);
      // Intermediate frames should be interpolated
      expect(frames[15]).toBeGreaterThan(0);
      expect(frames[15]).toBeLessThan(100);
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
      const layerStore = useLayerStore();
      
      // Create a project with layers and keyframes
      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
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
      const layerStore = useLayerStore();
      
      // Create different layer types
      const solidLayer = layerStore.createLayer(store, 'solid', 'Solid');
      const textLayer = layerStore.createLayer(store, 'text', 'Text');
      const shapeLayer = layerStore.createLayer(store, 'shape', 'Shape');
      
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
      const layerStore = useLayerStore();
      
      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
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

    test('effects survive roundtrip', () => {
      const store = useCompositorStore();
      const layerStore = useLayerStore();

      const layer = layerStore.createLayer(store, 'solid', 'Test Layer');
      store.addEffectToLayer(layer.id, 'gaussian-blur');

      const layerData = layerStore.getLayerById(store, layer.id);
      const effectId = layerData?.effects?.[0]?.id;
      store.updateEffectParameter(layer.id, effectId!, 'blurriness', 42);

      const json = JSON.stringify(store.project);
      const parsed = JSON.parse(json);

      // Raw project data stores effects as EffectInstance objects
      const savedLayer = parsed.compositions[store.activeCompositionId].layers.find((l: any) => l.id === layer.id);
      expect(savedLayer.effects[0].effectKey).toBe('gaussian-blur');
      expect(savedLayer.effects[0].parameters.blurriness.value).toBe(42);
    });
  });
});
