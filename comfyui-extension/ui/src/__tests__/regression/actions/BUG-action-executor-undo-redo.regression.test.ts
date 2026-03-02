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
import { useProjectStore } from '@/stores/projectStore';
import { useLayerStore } from '@/stores/layerStore';
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
    const projectStore = useProjectStore();

    // Get initial history count
    const initialHistoryLength = projectStore.historyStack.length;
    const initialHistoryIndex = projectStore.historyIndex;

    // Execute an action that was missing pushHistory()
    // ToolCall uses discriminated union - args are spread, not nested under 'arguments'
    const createLayerCall: ToolCall = {
      id: 'call-create-layer',
      name: 'createLayer',
      type: 'solid',
    };

    await executeToolCall(createLayerCall);

    // Verify history was updated (pushHistory was called)
    expect(projectStore.historyStack.length).toBeGreaterThan(initialHistoryLength);
    expect(projectStore.historyIndex).toBeGreaterThan(initialHistoryIndex);

    // Verify we can undo
    const layerCountBeforeUndo = projectStore.getActiveCompLayers().length;
    projectStore.undo();

    // Layer should be removed after undo
    expect(projectStore.getActiveCompLayers().length).toBeLessThan(layerCountBeforeUndo);

    // Verify we can redo
    projectStore.redo();
    expect(projectStore.getActiveCompLayers().length).toBe(layerCountBeforeUndo);
  });

  /**
   * Additional edge cases related to this bug.
   */
  test('layer deletion can be undone', async () => {
    const projectStore = useProjectStore();
    const layerStore = useLayerStore();

    // Create a layer first
    const layer = layerStore.createLayer('solid', 'Test Layer');
    const initialHistoryLength = projectStore.historyStack.length;

    // Delete the layer - ToolCall uses discriminated union, args spread directly
    const deleteCall: ToolCall = {
      id: 'call-delete-layer',
      name: 'deleteLayer',
      layerId: layer.id,
    };

    await executeToolCall(deleteCall);

    // Verify history was updated
    expect(projectStore.historyStack.length).toBeGreaterThan(initialHistoryLength);

    // Verify undo restores the layer
    const layerCountBeforeUndo = projectStore.getActiveCompLayers().length;
    projectStore.undo();
    expect(projectStore.getActiveCompLayers().length).toBeGreaterThan(layerCountBeforeUndo);

    // Verify redo removes it again
    projectStore.redo();
    expect(projectStore.getActiveCompLayers().length).toBe(layerCountBeforeUndo);
  });

  test('layer property changes can be undone', async () => {
    const projectStore = useProjectStore();
    const layerStore = useLayerStore();

    const layer = layerStore.createLayer('solid', 'Test Layer');
    const initialOpacity = layer.opacity.value;
    const initialHistoryLength = projectStore.historyStack.length;

    // Change a property - ToolCall uses discriminated union, args spread directly
    const setPropertyCall: ToolCall = {
      id: 'call-set-property',
      name: 'setLayerProperty',
      layerId: layer.id,
      propertyPath: 'opacity',
      value: 50,
    };

    await executeToolCall(setPropertyCall);

    // Verify history was updated
    expect(projectStore.historyStack.length).toBeGreaterThan(initialHistoryLength);

    // Verify undo restores original value
    projectStore.undo();
    const layerAfterUndo = projectStore.getActiveCompLayers().find(l => l.id === layer.id);
    expect(layerAfterUndo?.opacity.value).toBe(initialOpacity);

    // Verify redo applies change again
    projectStore.redo();
    const layerAfterRedo = projectStore.getActiveCompLayers().find(l => l.id === layer.id);
    expect(layerAfterRedo?.opacity.value).toBe(50);
  });

  test('keyframe addition can be undone', async () => {
    const projectStore = useProjectStore();
    const layerStore = useLayerStore();

    const layer = layerStore.createLayer('solid', 'Test Layer');
    const property = layer.opacity;
    const initialKeyframeCount = property.keyframes.length;
    const initialHistoryLength = projectStore.historyStack.length;

    // Add a keyframe - ToolCall uses discriminated union, args spread directly
    const addKeyframeCall: ToolCall = {
      id: 'call-add-keyframe',
      name: 'addKeyframe',
      layerId: layer.id,
      propertyPath: 'opacity',
      frame: 10,
      value: 50,
    };

    await executeToolCall(addKeyframeCall);

    // Verify history was updated
    expect(projectStore.historyStack.length).toBeGreaterThan(initialHistoryLength);

    // Verify undo removes the keyframe
    projectStore.undo();
    const layerAfterUndo = projectStore.getActiveCompLayers().find(l => l.id === layer.id);
    expect(layerAfterUndo?.opacity.keyframes.length).toBe(initialKeyframeCount);

    // Verify redo adds it back
    projectStore.redo();
    const layerAfterRedo = projectStore.getActiveCompLayers().find(l => l.id === layer.id);
    expect(layerAfterRedo?.opacity.keyframes.length).toBeGreaterThan(initialKeyframeCount);
  });

  test('multiple actions create multiple history entries', async () => {
    const projectStore = useProjectStore();

    const initialHistoryLength = projectStore.historyStack.length;

    // Execute multiple actions - ToolCall uses discriminated union, args spread directly
    await executeToolCall({
      id: 'call-1',
      name: 'createLayer',
      type: 'solid',
    });

    await executeToolCall({
      id: 'call-2',
      name: 'createLayer',
      type: 'solid',
    });

    await executeToolCall({
      id: 'call-3',
      name: 'createLayer',
      type: 'solid',
    });

    // Each action should create a history entry
    expect(projectStore.historyStack.length).toBeGreaterThanOrEqual(initialHistoryLength + 3);

    // Should be able to undo all three
    const layerCountAfterActions = projectStore.getActiveCompLayers().length;
    projectStore.undo();
    projectStore.undo();
    projectStore.undo();
    expect(projectStore.getActiveCompLayers().length).toBeLessThan(layerCountAfterActions);

    // Should be able to redo all three
    projectStore.redo();
    projectStore.redo();
    projectStore.redo();
    expect(projectStore.getActiveCompLayers().length).toBe(layerCountAfterActions);
  });

  test('expression changes can be undone', async () => {
    const projectStore = useProjectStore();
    const layerStore = useLayerStore();

    const layer = layerStore.createLayer('solid', 'Test Layer');
    const initialHistoryLength = projectStore.historyStack.length;

    // Set an expression - ToolCall uses discriminated union, args spread directly
    const setExpressionCall: ToolCall = {
      id: 'call-set-expression',
      name: 'setExpression',
      layerId: layer.id,
      propertyPath: 'opacity',
      expressionType: 'wiggle',
      params: { frequency: 2, amplitude: 10 },
    };

    await executeToolCall(setExpressionCall);

    // Verify history was updated
    expect(projectStore.historyStack.length).toBeGreaterThan(initialHistoryLength);

    // Verify undo removes expression
    projectStore.undo();
    const layerAfterUndo = projectStore.getActiveCompLayers().find(l => l.id === layer.id);
    expect(layerAfterUndo?.opacity.expression).toBeUndefined();

    // Verify redo restores expression
    projectStore.redo();
    const layerAfterRedo = projectStore.getActiveCompLayers().find(l => l.id === layer.id);
    expect(layerAfterRedo?.opacity.expression).toBeDefined();
  });
});
