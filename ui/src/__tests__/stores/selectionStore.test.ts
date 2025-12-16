/**
 * Selection Store Tests
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { setActivePinia, createPinia } from 'pinia';
import { useSelectionStore } from '@/stores/selectionStore';

describe('SelectionStore', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  describe('initial state', () => {
    it('should start with empty selections', () => {
      const store = useSelectionStore();
      expect(store.selectedLayerIds).toEqual([]);
      expect(store.selectedKeyframeIds).toEqual([]);
      expect(store.selectedPropertyPath).toBeNull();
    });

    it('should default to select tool', () => {
      const store = useSelectionStore();
      expect(store.currentTool).toBe('select');
    });
  });

  describe('layer selection', () => {
    it('selectLayer should select a single layer', () => {
      const store = useSelectionStore();
      store.selectLayer('layer-1');
      expect(store.selectedLayerIds).toEqual(['layer-1']);
    });

    it('selectLayer should replace existing selection', () => {
      const store = useSelectionStore();
      store.selectLayer('layer-1');
      store.selectLayer('layer-2');
      expect(store.selectedLayerIds).toEqual(['layer-2']);
    });

    it('selectLayers should select multiple layers', () => {
      const store = useSelectionStore();
      store.selectLayers(['layer-1', 'layer-2', 'layer-3']);
      expect(store.selectedLayerIds).toEqual(['layer-1', 'layer-2', 'layer-3']);
    });

    it('addToSelection should add layer to existing selection', () => {
      const store = useSelectionStore();
      store.selectLayer('layer-1');
      store.addToSelection('layer-2');
      expect(store.selectedLayerIds).toEqual(['layer-1', 'layer-2']);
    });

    it('addToSelection should not duplicate layers', () => {
      const store = useSelectionStore();
      store.selectLayer('layer-1');
      store.addToSelection('layer-1');
      expect(store.selectedLayerIds).toEqual(['layer-1']);
    });

    it('removeFromSelection should remove layer', () => {
      const store = useSelectionStore();
      store.selectLayers(['layer-1', 'layer-2']);
      store.removeFromSelection('layer-1');
      expect(store.selectedLayerIds).toEqual(['layer-2']);
    });

    it('toggleLayerSelection should toggle selection state', () => {
      const store = useSelectionStore();
      store.toggleLayerSelection('layer-1');
      expect(store.selectedLayerIds).toContain('layer-1');

      store.toggleLayerSelection('layer-1');
      expect(store.selectedLayerIds).not.toContain('layer-1');
    });

    it('clearLayerSelection should clear all layers', () => {
      const store = useSelectionStore();
      store.selectLayers(['layer-1', 'layer-2']);
      store.clearLayerSelection();
      expect(store.selectedLayerIds).toEqual([]);
    });

    it('isLayerSelected should return correct state', () => {
      const store = useSelectionStore();
      store.selectLayer('layer-1');
      expect(store.isLayerSelected('layer-1')).toBe(true);
      expect(store.isLayerSelected('layer-2')).toBe(false);
    });
  });

  describe('keyframe selection', () => {
    it('selectKeyframe should select a single keyframe', () => {
      const store = useSelectionStore();
      store.selectKeyframe('kf-1');
      expect(store.selectedKeyframeIds).toEqual(['kf-1']);
    });

    it('selectKeyframes should select multiple keyframes', () => {
      const store = useSelectionStore();
      store.selectKeyframes(['kf-1', 'kf-2']);
      expect(store.selectedKeyframeIds).toEqual(['kf-1', 'kf-2']);
    });

    it('addKeyframeToSelection should add keyframe', () => {
      const store = useSelectionStore();
      store.selectKeyframe('kf-1');
      store.addKeyframeToSelection('kf-2');
      expect(store.selectedKeyframeIds).toEqual(['kf-1', 'kf-2']);
    });

    it('removeKeyframeFromSelection should remove keyframe', () => {
      const store = useSelectionStore();
      store.selectKeyframes(['kf-1', 'kf-2']);
      store.removeKeyframeFromSelection('kf-1');
      expect(store.selectedKeyframeIds).toEqual(['kf-2']);
    });

    it('toggleKeyframeSelection should toggle state', () => {
      const store = useSelectionStore();
      store.toggleKeyframeSelection('kf-1');
      expect(store.selectedKeyframeIds).toContain('kf-1');

      store.toggleKeyframeSelection('kf-1');
      expect(store.selectedKeyframeIds).not.toContain('kf-1');
    });

    it('clearKeyframeSelection should clear all keyframes', () => {
      const store = useSelectionStore();
      store.selectKeyframes(['kf-1', 'kf-2']);
      store.clearKeyframeSelection();
      expect(store.selectedKeyframeIds).toEqual([]);
    });
  });

  describe('property selection', () => {
    it('setSelectedPropertyPath should set path', () => {
      const store = useSelectionStore();
      store.setSelectedPropertyPath('transform.position');
      expect(store.selectedPropertyPath).toBe('transform.position');
    });

    it('setSelectedPropertyPath should clear with null', () => {
      const store = useSelectionStore();
      store.setSelectedPropertyPath('transform.position');
      store.setSelectedPropertyPath(null);
      expect(store.selectedPropertyPath).toBeNull();
    });
  });

  describe('tool state', () => {
    it('setTool should change current tool', () => {
      const store = useSelectionStore();
      store.setTool('pen');
      expect(store.currentTool).toBe('pen');

      store.setTool('hand');
      expect(store.currentTool).toBe('hand');
    });
  });

  describe('getters', () => {
    it('hasSelection should reflect layer selection state', () => {
      const store = useSelectionStore();
      expect(store.hasSelection).toBe(false);

      store.selectLayer('layer-1');
      expect(store.hasSelection).toBe(true);
    });

    it('hasMultipleSelected should be true for 2+ layers', () => {
      const store = useSelectionStore();
      store.selectLayer('layer-1');
      expect(store.hasMultipleSelected).toBe(false);

      store.addToSelection('layer-2');
      expect(store.hasMultipleSelected).toBe(true);
    });

    it('hasKeyframeSelection should reflect keyframe state', () => {
      const store = useSelectionStore();
      expect(store.hasKeyframeSelection).toBe(false);

      store.selectKeyframe('kf-1');
      expect(store.hasKeyframeSelection).toBe(true);
    });

    it('singleSelectedLayerId should return id when one selected', () => {
      const store = useSelectionStore();
      expect(store.singleSelectedLayerId).toBeNull();

      store.selectLayer('layer-1');
      expect(store.singleSelectedLayerId).toBe('layer-1');

      store.addToSelection('layer-2');
      expect(store.singleSelectedLayerId).toBeNull();
    });
  });

  describe('clearAll', () => {
    it('should clear all selections', () => {
      const store = useSelectionStore();
      store.selectLayers(['layer-1', 'layer-2']);
      store.selectKeyframes(['kf-1', 'kf-2']);
      store.setSelectedPropertyPath('transform.scale');

      store.clearAll();

      expect(store.selectedLayerIds).toEqual([]);
      expect(store.selectedKeyframeIds).toEqual([]);
      expect(store.selectedPropertyPath).toBeNull();
    });
  });
});
