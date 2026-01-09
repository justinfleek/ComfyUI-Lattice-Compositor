/**
 * STRICT Property Tests for Selection Store
 * 
 * Tests the invariants that must hold for selection management:
 * 1. Single select replaces selection
 * 2. Multi-select adds to selection
 * 3. Deselect removes from selection
 * 4. Clear empties selection
 * 5. No duplicates in selection
 * 
 * TOLERANCE: STRICT - Selection bugs cause confusing UI state
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import { setActivePinia, createPinia } from 'pinia';
import { useSelectionStore } from '@/stores/selectionStore';

// ============================================================================
// TEST SETUP
// ============================================================================

beforeEach(() => {
  setActivePinia(createPinia());
});

// ============================================================================
// TEST DATA GENERATORS
// ============================================================================

const arbitraryLayerId = (): fc.Arbitrary<string> =>
  fc.uuid();

const arbitraryLayerIds = (minLength = 1, maxLength = 10): fc.Arbitrary<string[]> =>
  fc.array(arbitraryLayerId(), { minLength, maxLength });

// ============================================================================
// STRICT SINGLE SELECTION TESTS
// ============================================================================

describe('STRICT: Single Selection', () => {
  test.prop([arbitraryLayerId()])('selectLayer replaces existing selection', (layerId) => {
    const store = useSelectionStore();
    
    // Pre-populate with some selection
    store.selectedLayerIds = ['old-1', 'old-2', 'old-3'];
    
    // Select new layer
    store.selectLayer(layerId);
    
    // Should have only the new layer
    expect(store.selectedLayerIds).toEqual([layerId]);
    expect(store.selectedLayerIds.length).toBe(1);
  });

  test.prop([arbitraryLayerId()])('selectLayer sets lastSelectedLayerId', (layerId) => {
    const store = useSelectionStore();
    
    store.selectLayer(layerId);
    
    expect(store.lastSelectedLayerId).toBe(layerId);
  });

  test.prop([arbitraryLayerId()])('selectLayer is idempotent', (layerId) => {
    const store = useSelectionStore();
    
    store.selectLayer(layerId);
    const firstState = [...store.selectedLayerIds];
    
    store.selectLayer(layerId);
    const secondState = [...store.selectedLayerIds];
    
    expect(firstState).toEqual(secondState);
  });
});

// ============================================================================
// STRICT MULTI SELECTION TESTS
// ============================================================================

describe('STRICT: Multi Selection', () => {
  test.prop([arbitraryLayerIds(2, 5)])('selectLayers replaces existing selection', (layerIds) => {
    const store = useSelectionStore();
    
    // Pre-populate
    store.selectedLayerIds = ['old-1', 'old-2'];
    
    store.selectLayers(layerIds);
    
    expect(store.selectedLayerIds).toEqual(layerIds);
  });

  test.prop([arbitraryLayerId(), arbitraryLayerId()])('addToSelection appends layer', (existing, newLayer) => {
    fc.pre(existing !== newLayer);
    
    const store = useSelectionStore();
    store.selectLayer(existing);
    
    store.addToSelection(newLayer);
    
    expect(store.selectedLayerIds).toContain(existing);
    expect(store.selectedLayerIds).toContain(newLayer);
    expect(store.selectedLayerIds.length).toBe(2);
  });

  test.prop([arbitraryLayerId()])('addToSelection does not duplicate', (layerId) => {
    const store = useSelectionStore();
    
    store.selectLayer(layerId);
    store.addToSelection(layerId);
    store.addToSelection(layerId);
    
    // Should still only have one
    expect(store.selectedLayerIds.length).toBe(1);
    expect(store.selectedLayerIds).toEqual([layerId]);
  });

  test.prop([arbitraryLayerIds(3, 10)])('selection never contains duplicates', (layerIds) => {
    const store = useSelectionStore();
    
    // Add all layers
    for (const id of layerIds) {
      store.addToSelection(id);
    }
    
    // Check for duplicates
    const uniqueIds = new Set(store.selectedLayerIds);
    expect(uniqueIds.size).toBe(store.selectedLayerIds.length);
  });
});

// ============================================================================
// STRICT DESELECTION TESTS
// ============================================================================

describe('STRICT: Deselection', () => {
  test.prop([arbitraryLayerIds(3, 5)])('removeFromSelection removes specific layer', (layerIds) => {
    const store = useSelectionStore();
    store.selectLayers(layerIds);
    
    const toRemove = layerIds[0];
    store.removeFromSelection(toRemove);
    
    expect(store.selectedLayerIds).not.toContain(toRemove);
    expect(store.selectedLayerIds.length).toBe(layerIds.length - 1);
  });

  test.prop([arbitraryLayerId()])('removeFromSelection on non-existent is no-op', (layerId) => {
    const store = useSelectionStore();
    store.selectedLayerIds = ['other-1', 'other-2'];
    
    const before = [...store.selectedLayerIds];
    store.removeFromSelection(layerId);
    
    expect(store.selectedLayerIds).toEqual(before);
  });

  test.prop([arbitraryLayerIds(1, 5)])('clearSelection empties selection', (layerIds) => {
    const store = useSelectionStore();
    store.selectLayers(layerIds);
    
    store.clearSelection();
    
    expect(store.selectedLayerIds).toEqual([]);
    expect(store.hasSelection).toBe(false);
  });
});

// ============================================================================
// STRICT TOGGLE TESTS
// ============================================================================

describe('STRICT: Toggle Selection', () => {
  test.prop([arbitraryLayerId()])('toggleSelection adds if not selected', (layerId) => {
    const store = useSelectionStore();
    store.selectedLayerIds = [];
    
    store.toggleSelection(layerId);
    
    expect(store.selectedLayerIds).toContain(layerId);
  });

  test.prop([arbitraryLayerId()])('toggleSelection removes if already selected', (layerId) => {
    const store = useSelectionStore();
    store.selectLayer(layerId);
    
    store.toggleSelection(layerId);
    
    expect(store.selectedLayerIds).not.toContain(layerId);
  });

  test.prop([arbitraryLayerId()])('double toggle restores original state', (layerId) => {
    const store = useSelectionStore();
    const wasSelected = store.selectedLayerIds.includes(layerId);
    
    store.toggleSelection(layerId);
    store.toggleSelection(layerId);
    
    expect(store.selectedLayerIds.includes(layerId)).toBe(wasSelected);
  });
});

// ============================================================================
// STRICT GETTER TESTS
// ============================================================================

describe('STRICT: Selection Getters', () => {
  test.prop([arbitraryLayerIds(0, 5)])('hasSelection reflects state', (layerIds) => {
    const store = useSelectionStore();
    store.selectedLayerIds = layerIds;
    
    expect(store.hasSelection).toBe(layerIds.length > 0);
  });

  test.prop([arbitraryLayerIds(0, 5)])('hasMultipleSelected reflects state', (layerIds) => {
    const store = useSelectionStore();
    store.selectedLayerIds = layerIds;
    
    expect(store.hasMultipleSelected).toBe(layerIds.length > 1);
  });

  test.prop([arbitraryLayerId()])('singleSelectedLayerId returns id when one selected', (layerId) => {
    const store = useSelectionStore();
    store.selectLayer(layerId);
    
    expect(store.singleSelectedLayerId).toBe(layerId);
  });

  test.prop([arbitraryLayerIds(2, 5)])('singleSelectedLayerId returns null when multiple selected', (layerIds) => {
    const store = useSelectionStore();
    store.selectLayers(layerIds);
    
    expect(store.singleSelectedLayerId).toBeNull();
  });

  it('singleSelectedLayerId returns null when none selected', () => {
    const store = useSelectionStore();
    store.clearSelection();
    
    expect(store.singleSelectedLayerId).toBeNull();
  });
});

// ============================================================================
// STRICT KEYFRAME SELECTION TESTS
// ============================================================================

describe('STRICT: Keyframe Selection', () => {
  test.prop([fc.array(fc.uuid(), { minLength: 1, maxLength: 5 })])('selectKeyframes replaces selection', (keyframeIds) => {
    const store = useSelectionStore();
    store.selectedKeyframeIds = ['old-kf-1', 'old-kf-2'];
    
    store.selectKeyframes(keyframeIds);
    
    expect(store.selectedKeyframeIds).toEqual(keyframeIds);
  });

  test.prop([fc.uuid()])('addKeyframeToSelection appends', (keyframeId) => {
    const store = useSelectionStore();
    store.selectedKeyframeIds = ['existing-kf'];
    
    store.addKeyframeToSelection(keyframeId);
    
    expect(store.selectedKeyframeIds).toContain(keyframeId);
    expect(store.selectedKeyframeIds).toContain('existing-kf');
  });

  test.prop([fc.uuid()])('addKeyframeToSelection prevents duplicates', (keyframeId) => {
    const store = useSelectionStore();
    
    store.addKeyframeToSelection(keyframeId);
    store.addKeyframeToSelection(keyframeId);
    store.addKeyframeToSelection(keyframeId);
    
    const count = store.selectedKeyframeIds.filter(id => id === keyframeId).length;
    expect(count).toBe(1);
  });

  it('clearKeyframeSelection empties selection', () => {
    const store = useSelectionStore();
    store.selectedKeyframeIds = ['kf-1', 'kf-2', 'kf-3'];
    
    store.clearKeyframeSelection();
    
    expect(store.selectedKeyframeIds).toEqual([]);
    expect(store.hasKeyframeSelection).toBe(false);
  });
});

// ============================================================================
// STRICT TOOL STATE TESTS
// ============================================================================

describe('STRICT: Tool State', () => {
  const validTools = ['select', 'pen', 'text', 'hand', 'zoom'] as const;

  for (const tool of validTools) {
    it(`setTool accepts '${tool}'`, () => {
      const store = useSelectionStore();
      
      store.setTool(tool);
      
      expect(store.currentTool).toBe(tool);
    });
  }

  it('tool defaults to select', () => {
    const store = useSelectionStore();
    
    expect(store.currentTool).toBe('select');
  });
});

// ============================================================================
// STRESS TESTS
// ============================================================================

describe('STRESS: Selection Under Load', () => {
  test.prop([arbitraryLayerIds(50, 100)])('handles large selections', (layerIds) => {
    const store = useSelectionStore();
    
    store.selectLayers(layerIds);
    
    expect(store.selectedLayerIds.length).toBe(layerIds.length);
    expect(store.hasSelection).toBe(true);
    expect(store.hasMultipleSelected).toBe(true);
  });

  test.prop([
    fc.array(fc.tuple(
      fc.constantFrom('select', 'add', 'remove', 'toggle', 'clear'),
      arbitraryLayerId()
    ), { minLength: 20, maxLength: 50 })
  ])('random operations maintain invariants', (operations) => {
    const store = useSelectionStore();
    
    for (const [op, layerId] of operations) {
      switch (op) {
        case 'select':
          store.selectLayer(layerId);
          break;
        case 'add':
          store.addToSelection(layerId);
          break;
        case 'remove':
          store.removeFromSelection(layerId);
          break;
        case 'toggle':
          store.toggleSelection(layerId);
          break;
        case 'clear':
          store.clearSelection();
          break;
      }
      
      // Invariant: no duplicates
      const uniqueIds = new Set(store.selectedLayerIds);
      expect(uniqueIds.size).toBe(store.selectedLayerIds.length);
      
      // Invariant: hasSelection reflects state
      expect(store.hasSelection).toBe(store.selectedLayerIds.length > 0);
    }
  });
});
