/**
 * REGRESSION TEST: BUG - Missing Undo/Redo (14 places)
 * 
 * @fixed 2026-01-06
 * @file services/ai/actionExecutor.ts
 * @rootCause 14 action executor functions were missing pushHistory() calls, breaking undo/redo
 * @fix Added pushHistory() calls to all state-modifying functions
 * @counterexample Actions like executeCreateLayer, executeDeleteLayer, etc. couldn't be undone
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { setActivePinia, createPinia } from 'pinia';
import { useCompositorStore } from '@/stores/compositorStore';
import { executeToolCall } from '@/services/ai/actionExecutor';
import type { ToolCall } from '@/services/ai/toolDefinitions';

describe('BUG Regression: Missing Undo/Redo', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  /**
   * This test MUST reproduce the exact counterexample from the bug report.
   * Before fix: Actions couldn't be undone because pushHistory() wasn't called
   * After fix: All state-modifying actions call pushHistory(), enabling undo/redo
   */
  test('original counterexample now passes - actions can be undone', async () => {
    const store = useCompositorStore();
    
    // Get initial history count
    const initialHistoryLength = store.historyStack.length;
    const initialHistoryIndex = store.historyIndex;

    // Execute an action that was missing pushHistory()
    const createLayerCall: ToolCall = {
      id: 'call-create-layer',
      name: 'createLayer',
      arguments: {
        type: 'solid',
        name: 'Test Layer',
      },
    };

    await executeToolCall(createLayerCall);

    // Verify history was updated (pushHistory was called)
    expect(store.historyStack.length).toBeGreaterThan(initialHistoryLength);
    expect(store.historyIndex).toBeGreaterThan(initialHistoryIndex);

    // Verify we can undo
    const layerCountBeforeUndo = store.getActiveCompLayers().length;
    store.undo();
    
    // Layer should be removed after undo
    expect(store.getActiveCompLayers().length).toBeLessThan(layerCountBeforeUndo);
    
    // Verify we can redo
    store.redo();
    expect(store.getActiveCompLayers().length).toBe(layerCountBeforeUndo);
  });

  /**
   * Additional edge cases related to this bug.
   */
  test('layer deletion can be undone', async () => {
    const store = useCompositorStore();
    
    // Create a layer first
    const layer = store.addLayer('solid', 'Test Layer');
    const initialHistoryLength = store.historyStack.length;

    // Delete the layer
    const deleteCall: ToolCall = {
      name: 'deleteLayer',
      arguments: {
        layerId: layer.id,
      },
    };

    await executeToolCall(deleteCall);

    // Verify history was updated
    expect(store.historyStack.length).toBeGreaterThan(initialHistoryLength);
    
    // Verify undo restores the layer
    const layerCountBeforeUndo = store.getActiveCompLayers().length;
    store.undo();
    expect(store.getActiveCompLayers().length).toBeGreaterThan(layerCountBeforeUndo);
    
    // Verify redo removes it again
    store.redo();
    expect(store.getActiveCompLayers().length).toBe(layerCountBeforeUndo);
  });

  test('layer property changes can be undone', async () => {
    const store = useCompositorStore();
    
    const layer = store.addLayer('solid', 'Test Layer');
    const initialOpacity = layer.opacity.value;
    const initialHistoryLength = store.historyStack.length;

    // Change a property
    const setPropertyCall: ToolCall = {
      name: 'setLayerProperty',
      arguments: {
        layerId: layer.id,
        propertyPath: 'opacity',
        value: 50,
      },
    };

    await executeToolCall(setPropertyCall);

    // Verify history was updated
    expect(store.historyStack.length).toBeGreaterThan(initialHistoryLength);
    
    // Verify undo restores original value
    store.undo();
    const layerAfterUndo = store.getActiveCompLayers().find(l => l.id === layer.id);
    expect(layerAfterUndo?.opacity.value).toBe(initialOpacity);
    
    // Verify redo applies change again
    store.redo();
    const layerAfterRedo = store.getActiveCompLayers().find(l => l.id === layer.id);
    expect(layerAfterRedo?.opacity.value).toBe(50);
  });

  test('keyframe addition can be undone', async () => {
    const store = useCompositorStore();
    
    const layer = store.addLayer('solid', 'Test Layer');
    const property = layer.opacity;
    const initialKeyframeCount = property.keyframes.length;
    const initialHistoryLength = store.historyStack.length;

    // Add a keyframe
    const addKeyframeCall: ToolCall = {
      id: 'call-add-keyframe',
      name: 'addKeyframe',
      arguments: {
        layerId: layer.id,
        propertyPath: 'opacity',
        frame: 10,
        value: 50,
      },
    };

    await executeToolCall(addKeyframeCall);

    // Verify history was updated
    expect(store.historyStack.length).toBeGreaterThan(initialHistoryLength);
    
    // Verify undo removes the keyframe
    store.undo();
    const layerAfterUndo = store.getActiveCompLayers().find(l => l.id === layer.id);
    expect(layerAfterUndo?.opacity.keyframes.length).toBe(initialKeyframeCount);
    
    // Verify redo adds it back
    store.redo();
    const layerAfterRedo = store.getActiveCompLayers().find(l => l.id === layer.id);
    expect(layerAfterRedo?.opacity.keyframes.length).toBeGreaterThan(initialKeyframeCount);
  });

  test('multiple actions create multiple history entries', async () => {
    const store = useCompositorStore();
    
    const initialHistoryLength = store.historyStack.length;

    // Execute multiple actions
    await executeToolCall({
      id: 'call-1',
      name: 'createLayer',
      arguments: { type: 'solid', name: 'Layer 1' },
    });

    await executeToolCall({
      id: 'call-2',
      name: 'createLayer',
      arguments: { type: 'solid', name: 'Layer 2' },
    });

    await executeToolCall({
      id: 'call-3',
      name: 'createLayer',
      arguments: { type: 'solid', name: 'Layer 3' },
    });

    // Each action should create a history entry
    expect(store.historyStack.length).toBeGreaterThanOrEqual(initialHistoryLength + 3);
    
    // Should be able to undo all three
    const layerCountAfterActions = store.getActiveCompLayers().length;
    store.undo();
    store.undo();
    store.undo();
    expect(store.getActiveCompLayers().length).toBeLessThan(layerCountAfterActions);
    
    // Should be able to redo all three
    store.redo();
    store.redo();
    store.redo();
    expect(store.getActiveCompLayers().length).toBe(layerCountAfterActions);
  });

  test('expression changes can be undone', async () => {
    const store = useCompositorStore();
    
    const layer = store.addLayer('solid', 'Test Layer');
    const initialHistoryLength = store.historyStack.length;

    // Set an expression
    const setExpressionCall: ToolCall = {
      id: 'call-set-expression',
      name: 'setExpression',
      arguments: {
        layerId: layer.id,
        propertyPath: 'opacity',
        expressionType: 'wiggle',
        params: { frequency: 2, amplitude: 10 },
      },
    };

    await executeToolCall(setExpressionCall);

    // Verify history was updated
    expect(store.historyStack.length).toBeGreaterThan(initialHistoryLength);
    
    // Verify undo removes expression
    store.undo();
    const layerAfterUndo = store.getActiveCompLayers().find(l => l.id === layer.id);
    expect(layerAfterUndo?.opacity.expression).toBeUndefined();
    
    // Verify redo restores expression
    store.redo();
    const layerAfterRedo = store.getActiveCompLayers().find(l => l.id === layer.id);
    expect(layerAfterRedo?.opacity.expression).toBeDefined();
  });
});
