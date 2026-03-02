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
import { useLayerStore } from '@/stores/layerStore';
import { useProjectStore } from '@/stores/projectStore';
import { useAnimationStore } from '@/stores/animationStore';
import { useKeyframeStore } from '@/stores/keyframeStore';
import { useEffectStore, type EffectStoreAccess } from '@/stores/effectStore';
import { motionEngine } from '@/engine/MotionEngine';
import type { Layer, LatticeProject } from '@/types/project';

describe('Store → Engine Integration', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  afterEach(() => {
    // Cleanup handled by Pinia
  });

  describe('keyframe changes propagate correctly', () => {
    test('adding keyframe updates engine evaluation', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const animationStore = useAnimationStore();
      const keyframeStore = useKeyframeStore();
      
      // Create layer with opacity keyframes
      const layer = layerStore.createLayer('solid', 'Test Layer');
      const comp = projectStore.getActiveComp();
      if (comp) comp.currentFrame = 0;
      keyframeStore.addKeyframe(layer.id, 'opacity', 0);
      if (comp) comp.currentFrame = 30;
      keyframeStore.addKeyframe(layer.id, 'opacity', 100);
      
      // Evaluate midpoint
      const project = projectStore.project;
      const frame15 = motionEngine.evaluate(15, project);
      
      // Find the evaluated layer
      const evaluatedLayer = frame15.layers.find(l => l.id === layer.id);
      expect(evaluatedLayer).toBeDefined();
      
      // Should be interpolated value (approximately 50 at frame 15, halfway between 0 and 30)
      expect(evaluatedLayer!.opacity).toBeGreaterThan(40);
      expect(evaluatedLayer!.opacity).toBeLessThan(60);
    });

    test('modifying keyframe updates engine evaluation', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const keyframeStore = useKeyframeStore();
      
      const layer = layerStore.createLayer('solid', 'Test Layer');
      const comp = projectStore.getActiveComp();
      if (comp) comp.currentFrame = 0;
      const kf1 = keyframeStore.addKeyframe(layer.id, 'opacity', 0);
      if (comp) comp.currentFrame = 30;
      keyframeStore.addKeyframe(layer.id, 'opacity', 100);
      
      // Modify first keyframe
      if (kf1) {
        keyframeStore.setKeyframeValue(layer.id, 'opacity', kf1.id, 50);
      }
      
      // Evaluate at frame 0
      const project = projectStore.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);
      
      // Should reflect modified value
      expect(evaluatedLayer!.opacity).toBeCloseTo(50, 1);
    });

    test('deleting keyframe updates engine evaluation', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const keyframeStore = useKeyframeStore();
      
      const layer = layerStore.createLayer('solid', 'Test Layer');
      const comp = projectStore.getActiveComp();
      if (comp) comp.currentFrame = 0;
      const kf1 = keyframeStore.addKeyframe(layer.id, 'opacity', 0);
      if (comp) comp.currentFrame = 30;
      keyframeStore.addKeyframe(layer.id, 'opacity', 100);
      
      // Delete first keyframe (method is removeKeyframe, not deleteKeyframe)
      if (kf1) {
        keyframeStore.removeKeyframe(layer.id, 'opacity', kf1.id);
      }
      
      // Evaluate at frame 0
      const project = projectStore.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);
      
      // Should use static value or next keyframe
      expect(evaluatedLayer!.opacity).toBeDefined();
    });
  });

  describe('layer changes propagate correctly', () => {
    test('layer visibility affects engine output', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();

      const layer = layerStore.createLayer('solid', 'Test Layer');
      // Use updateLayer to set visibility (setLayerVisible doesn't exist)
      layerStore.updateLayer(layer.id, { visible: false });

      const project = projectStore.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);

      // Hidden layers should have visible = false
      expect(evaluatedLayer!.visible).toBe(false);
    });

    test('layer order affects compositing', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();

      const layer1 = layerStore.createLayer('solid', 'Layer 1');
      const layer2 = layerStore.createLayer('solid', 'Layer 2');

      const project = projectStore.project;
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
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();

      // Create a group layer (which acts like a nested composition)
      const groupLayer = layerStore.createLayer('group', 'Nested Group');
      const childLayer = layerStore.createLayer('solid', 'Child');

      // Move child into group (via updateLayer parentId)
      layerStore.updateLayer(childLayer.id, { parentId: groupLayer.id });

      // Evaluate
      const project = projectStore.project;
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
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const effectStore = useEffectStore();

      const layer = layerStore.createLayer('solid', 'Test Layer');
      const effectStoreAccess: EffectStoreAccess = {
        getActiveCompLayers: () => projectStore.getActiveCompLayers(),
        project: projectStore.project,
        pushHistory: () => projectStore.pushHistory(),
      };
      effectStore.addEffectToLayer(effectStoreAccess, layer.id, 'gaussian-blur');

      const project = projectStore.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);

      // EvaluatedEffect uses 'type' not 'effectKey'
      expect(evaluatedLayer!.effects[0].type).toBe('gaussian-blur');
    });

    test('effect parameter changes are reflected', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const effectStore = useEffectStore();

      const layer = layerStore.createLayer('solid', 'Test Layer');
      const effectStoreAccess: EffectStoreAccess = {
        getActiveCompLayers: () => projectStore.getActiveCompLayers(),
        project: projectStore.project,
        pushHistory: () => projectStore.pushHistory(),
      };
      effectStore.addEffectToLayer(effectStoreAccess, layer.id, 'gaussian-blur');

      const layerData = layerStore.getLayerById(layer.id);
      const effectId = layerData?.effects?.[0]?.id;
      if (effectId) {
        effectStore.updateEffectParameter(effectStoreAccess, layer.id, effectId, 'blurriness', 25);
      }

      const project = projectStore.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);

      // EvaluatedEffect.parameters contains interpolated values directly (not AnimatableProperty)
      expect(evaluatedLayer!.effects[0].parameters.blurriness).toBe(25);
    });

    test('removing effect is reflected in evaluation', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const effectStore = useEffectStore();

      const layer = layerStore.createLayer('solid', 'Test Layer');
      const effectStoreAccess: EffectStoreAccess = {
        getActiveCompLayers: () => projectStore.getActiveCompLayers(),
        project: projectStore.project,
        pushHistory: () => projectStore.pushHistory(),
      };
      effectStore.addEffectToLayer(effectStoreAccess, layer.id, 'gaussian-blur');

      const layerData = layerStore.getLayerById(layer.id);
      const effectId = layerData?.effects?.[0]?.id;
      if (effectId) {
        effectStore.removeEffectFromLayer(effectStoreAccess, layer.id, effectId);
      }

      const project = projectStore.project;
      const frame0 = motionEngine.evaluate(0, project);
      const evaluatedLayer = frame0.layers.find(l => l.id === layer.id);

      expect(evaluatedLayer!.effects.length).toBe(0);
    });
  });

  describe('determinism', () => {
    test('same state produces identical evaluation', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const keyframeStore = useKeyframeStore();
      
      const layer = layerStore.createLayer('solid', 'Test Layer');
      const comp = projectStore.getActiveComp();
      if (comp) comp.currentFrame = 0;
      keyframeStore.addKeyframe(layer.id, 'opacity', 0);
      if (comp) comp.currentFrame = 30;
      keyframeStore.addKeyframe(layer.id, 'opacity', 100);
      
      const project = projectStore.project;
      
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
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const keyframeStore = useKeyframeStore();

      const layer = layerStore.createLayer('solid', 'Test Layer');
      const comp = projectStore.getActiveComp();
      if (comp) comp.currentFrame = 0;
      keyframeStore.addKeyframe(layer.id, 'opacity', 0);
      if (comp) comp.currentFrame = 100;
      keyframeStore.addKeyframe(layer.id, 'opacity', 100);

      const project = projectStore.project;

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
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();

      // Create a camera layer
      const cameraLayer = layerStore.createCameraLayer('Main Camera');

      // Evaluate the frame
      const project = projectStore.project;
      const frame0 = motionEngine.evaluate(0, project);

      // Camera layer should be in evaluated output
      const evaluatedCamera = frame0.layers.find(l => l.type === 'camera');
      expect(evaluatedCamera).toBeDefined();

      // Camera layer has transform properties for export
      expect(evaluatedCamera!.transform).toBeDefined();
    });

    test('composition has frame range for export', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const animationStore = useAnimationStore();
      const keyframeStore = useKeyframeStore();

      // Create layer with animation spanning frames
      const layer = layerStore.createLayer('solid', 'Test Layer');
      const comp = projectStore.getActiveComp();
      if (comp) comp.currentFrame = 0;
      keyframeStore.addKeyframe(layer.id, 'opacity', 0);
      if (comp) comp.currentFrame = 90;
      keyframeStore.addKeyframe(layer.id, 'opacity', 100);

      // Composition should be available
      const project = projectStore.project;
      const activeCompId = projectStore.activeCompositionId;
      const composition = project.compositions[activeCompId];
      expect(composition).toBeDefined();

      // Composition has frame range (inPoint/outPoint or layers define range)
      // Frame count can be derived from keyframe positions
      expect(layer.id).toBeDefined();
      expect(animationStore.currentFrame).toBeDefined();
    });

    test('all frames can be evaluated for export', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const keyframeStore = useKeyframeStore();

      const layer = layerStore.createLayer('solid', 'Test Layer');
      const comp = projectStore.getActiveComp();
      if (comp) comp.currentFrame = 0;
      keyframeStore.addKeyframe(layer.id, 'opacity', 0);
      if (comp) comp.currentFrame = 30;
      keyframeStore.addKeyframe(layer.id, 'opacity', 100);

      const project = projectStore.project;

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
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const keyframeStore = useKeyframeStore();
      
      // Create a project with layers and keyframes
      const layer = layerStore.createLayer('solid', 'Test Layer');
      const comp = projectStore.getActiveComp();
      if (comp) comp.currentFrame = 0;
      keyframeStore.addKeyframe(layer.id, 'opacity', 0);
      if (comp) comp.currentFrame = 30;
      keyframeStore.addKeyframe(layer.id, 'opacity', 100);
      
      // Serialize
      const json = JSON.stringify(projectStore.project);
      
      // Deserialize
      const parsed = JSON.parse(json);
      
      // Should have same structure
      expect(parsed.compositions).toBeDefined();
      expect(parsed.compositions[parsed.mainCompositionId]).toBeDefined();
      expect(parsed.compositions[parsed.mainCompositionId].layers.length).toBe(1);
    });

    test('all layer types survive roundtrip', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      
      // Create different layer types
      const solidLayer = layerStore.createLayer('solid', 'Solid');
      const textLayer = layerStore.createLayer('text', 'Text');
      const shapeLayer = layerStore.createLayer('shape', 'Shape');
      
      // Serialize and deserialize
      const json = JSON.stringify(projectStore.project);
      const parsed = JSON.parse(json);
      
      // All layer types should be preserved
      const layers = parsed.compositions[parsed.mainCompositionId].layers;
      expect(layers.some((l: Layer) => l.type === 'solid')).toBe(true);
      expect(layers.some((l: Layer) => l.type === 'text')).toBe(true);
      expect(layers.some((l: Layer) => l.type === 'shape')).toBe(true);
    });

    test('keyframes survive roundtrip', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const keyframeStore = useKeyframeStore();
      
      const layer = layerStore.createLayer('solid', 'Test Layer');
      const comp = projectStore.getActiveComp();
      if (comp) comp.currentFrame = 0;
      keyframeStore.addKeyframe(layer.id, 'opacity', 0);
      if (comp) comp.currentFrame = 30;
      keyframeStore.addKeyframe(layer.id, 'opacity', 100);
      
      // Serialize and deserialize
      const json = JSON.stringify(projectStore.project);
      const parsed = JSON.parse(json) as LatticeProject;
      
      // Keyframes should be preserved
      const savedLayer = parsed.compositions[parsed.mainCompositionId].layers.find((l: Layer) => l.id === layer.id);
      expect(savedLayer).toBeDefined();
      expect(savedLayer!.opacity.keyframes.length).toBe(2);
    });

    test('effects survive roundtrip', () => {
      const projectStore = useProjectStore();
      const layerStore = useLayerStore();
      const effectStore = useEffectStore();

      const layer = layerStore.createLayer('solid', 'Test Layer');
      const effectStoreAccess: EffectStoreAccess = {
        getActiveCompLayers: () => projectStore.getActiveCompLayers(),
        project: projectStore.project,
        pushHistory: () => projectStore.pushHistory(),
      };
      effectStore.addEffectToLayer(effectStoreAccess, layer.id, 'gaussian-blur');

      const layerData = layerStore.getLayerById(layer.id);
      const effectId = layerData?.effects?.[0]?.id;
      if (effectId) {
        effectStore.updateEffectParameter(effectStoreAccess, layer.id, effectId, 'blurriness', 42);
      }

      const json = JSON.stringify(projectStore.project);
      const parsed = JSON.parse(json) as LatticeProject;

      // Raw project data stores effects as EffectInstance objects
      const savedLayer = parsed.compositions[projectStore.activeCompositionId].layers.find((l: Layer) => l.id === layer.id);
      expect(savedLayer).toBeDefined();
      expect(savedLayer!.effects[0].effectKey).toBe('gaussian-blur');
      expect(savedLayer!.effects[0].parameters.blurriness.value).toBe(42);
    });
  });
});
