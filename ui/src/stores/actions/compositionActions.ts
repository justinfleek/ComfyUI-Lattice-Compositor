/**
 * Composition Actions
 *
 * Composition management including creation, deletion, navigation,
 * breadcrumb trail, and nested composition handling.
 *
 * Extracted from compositorStore.ts for modularity.
 */

import { storeLogger } from '@/utils/logger';
import { validateFps, DEFAULT_FPS } from '@/utils/fpsUtils';
import type {
  Layer,
  Composition,
  CompositionSettings,
  NestedCompData
} from '@/types/project';
import { createDefaultTransform, createAnimatableProperty } from '@/types/project';
import { useSelectionStore } from '../selectionStore';

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface CompositionStore {
  project: {
    compositions: Record<string, Composition>;
    mainCompositionId: string;
    composition: CompositionSettings; // Legacy alias
    meta: { modified: string };
  };
  activeCompositionId: string;
  openCompositionIds: string[];
  compositionBreadcrumbs: string[];
  selectedLayerIds: string[];

  // Methods the actions need to call
  getActiveComp(): Composition | null;
  switchComposition(compId: string): void;
  pushHistory(): void;
}

// ============================================================================
// COMPOSITION CRUD
// ============================================================================

/**
 * Create a new composition
 */
export function createComposition(
  store: CompositionStore,
  name: string,
  settings?: Partial<CompositionSettings>,
  isNestedComp: boolean = false
): Composition {
  const id = `comp_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

  // Get settings from active comp or use defaults
  const activeComp = store.project.compositions[store.activeCompositionId];

  // Validate fps to prevent NaN (nullish coalescing doesn't catch NaN)
  const rawFps = settings?.fps ?? activeComp?.settings.fps ?? DEFAULT_FPS;
  const validFps = validateFps(rawFps);

  const defaultSettings: CompositionSettings = {
    width: settings?.width ?? activeComp?.settings.width ?? 1024,
    height: settings?.height ?? activeComp?.settings.height ?? 1024,
    frameCount: settings?.frameCount ?? activeComp?.settings.frameCount ?? 81,
    fps: validFps,
    duration: 0,
    backgroundColor: settings?.backgroundColor ?? '#050505',
    autoResizeToContent: settings?.autoResizeToContent ?? true,
    frameBlendingEnabled: settings?.frameBlendingEnabled ?? false
  };
  defaultSettings.duration = defaultSettings.frameCount / defaultSettings.fps;

  const composition: Composition = {
    id,
    name,
    settings: defaultSettings,
    layers: [],
    currentFrame: 0,
    isNestedComp
  };

  store.project.compositions[id] = composition;

  // Open and switch to new composition
  if (!store.openCompositionIds.includes(id)) {
    store.openCompositionIds.push(id);
  }
  store.activeCompositionId = id;

  // Push history for undo/redo
  store.pushHistory();

  storeLogger.debug('Created composition:', name, id);
  return composition;
}

/**
 * Delete a composition
 */
export function deleteComposition(store: CompositionStore, compId: string): boolean {
  // Can't delete main composition
  if (compId === store.project.mainCompositionId) {
    storeLogger.warn('Cannot delete main composition');
    return false;
  }

  const comp = store.project.compositions[compId];
  if (!comp) return false;

  // Remove from compositions
  delete store.project.compositions[compId];

  // Remove from open tabs
  const openIdx = store.openCompositionIds.indexOf(compId);
  if (openIdx >= 0) {
    store.openCompositionIds.splice(openIdx, 1);
  }

  // If this was active, switch to another
  if (store.activeCompositionId === compId) {
    store.activeCompositionId = store.openCompositionIds[0] || store.project.mainCompositionId;
  }

  storeLogger.debug('Deleted composition:', compId);
  return true;
}

/**
 * Rename a composition
 */
export function renameComposition(store: CompositionStore, compId: string, newName: string): void {
  const comp = store.project.compositions[compId];
  if (comp) {
    comp.name = newName;
  }
}

/**
 * Update composition settings
 *
 * @param store - The compositor store
 * @param compId - Composition ID to update
 * @param settings - Partial settings to update (fps must be > 0 if provided)
 */
export function updateCompositionSettings(
  store: CompositionStore,
  compId: string,
  settings: Partial<CompositionSettings>
): void {
  const comp = store.project.compositions[compId];
  if (!comp) return;

  const oldFrameCount = comp.settings.frameCount;

  // Validate fps if provided to prevent division by zero
  if (settings.fps !== undefined) {
    settings.fps = validateFps(settings.fps);
  }

  // Update settings
  Object.assign(comp.settings, settings);

  // Recalculate duration (fps is guaranteed valid via validateFps)
  comp.settings.duration = comp.settings.frameCount / comp.settings.fps;

  // Extend layer outPoints if frameCount increased
  if (settings.frameCount && settings.frameCount > oldFrameCount) {
    for (const layer of comp.layers) {
      if (layer.outPoint === oldFrameCount - 1) {
        layer.outPoint = settings.frameCount - 1;
      }
    }
  }

  // Keep legacy alias in sync for main comp
  if (compId === store.project.mainCompositionId) {
    Object.assign(store.project.composition, comp.settings);
  }

  // Push history for undo/redo
  store.pushHistory();
}

/**
 * Enable frame blending for a composition
 * When enabled, layers with timeStretch or speedMap interpolate between frames
 */
export function enableFrameBlending(store: CompositionStore, compId: string): void {
  updateCompositionSettings(store, compId, { frameBlendingEnabled: true });
}

/**
 * Disable frame blending for a composition
 */
export function disableFrameBlending(store: CompositionStore, compId: string): void {
  updateCompositionSettings(store, compId, { frameBlendingEnabled: false });
}

/**
 * Toggle frame blending for a composition
 */
export function toggleFrameBlending(store: CompositionStore, compId: string): void {
  const comp = store.project.compositions[compId];
  if (!comp) return;

  const enabled = !comp.settings.frameBlendingEnabled;
  updateCompositionSettings(store, compId, { frameBlendingEnabled: enabled });
}

/**
 * Get a composition by ID
 */
export function getComposition(store: CompositionStore, compId: string): Composition | null {
  return store.project.compositions[compId] || null;
}

// ============================================================================
// TAB MANAGEMENT
// ============================================================================

/**
 * Switch to a different composition (tab)
 */
export function switchComposition(store: CompositionStore, compId: string): void {
  if (!store.project.compositions[compId]) {
    storeLogger.warn('Composition not found:', compId);
    return;
  }

  // Add to open tabs if not already
  if (!store.openCompositionIds.includes(compId)) {
    store.openCompositionIds.push(compId);
  }

  // Clear selection when switching
  const selection = useSelectionStore();
  selection.clearLayerSelection();
  selection.clearKeyframeSelection();

  store.activeCompositionId = compId;
  storeLogger.debug('Switched to composition:', compId);
}

/**
 * Close a composition tab
 */
export function closeCompositionTab(store: CompositionStore, compId: string): void {
  // Can't close if it's the only open tab
  if (store.openCompositionIds.length <= 1) {
    storeLogger.warn('Cannot close the last tab');
    return;
  }

  const idx = store.openCompositionIds.indexOf(compId);
  if (idx >= 0) {
    store.openCompositionIds.splice(idx, 1);
  }

  // If closing active, switch to another
  if (store.activeCompositionId === compId) {
    store.activeCompositionId = store.openCompositionIds[Math.max(0, idx - 1)];
  }
}

// ============================================================================
// BREADCRUMB NAVIGATION (Nested Comps)
// ============================================================================

/**
 * Enter a nested comp (e.g., double-click on nested comp layer)
 * Pushes the composition to the breadcrumb trail
 */
export function enterNestedComp(store: CompositionStore, compId: string): void {
  if (!store.project.compositions[compId]) {
    storeLogger.warn('Nested comp not found:', compId);
    return;
  }

  // Add to breadcrumb trail
  store.compositionBreadcrumbs.push(compId);

  // Switch to the composition
  switchComposition(store, compId);

  storeLogger.debug('Entered nested comp:', compId, 'breadcrumbs:', store.compositionBreadcrumbs);
}

/**
 * Navigate back one level in the breadcrumb trail
 */
export function navigateBack(store: CompositionStore): void {
  if (store.compositionBreadcrumbs.length <= 1) {
    storeLogger.warn('Already at root composition');
    return;
  }

  // Pop current and switch to previous
  store.compositionBreadcrumbs.pop();
  const prevId = store.compositionBreadcrumbs[store.compositionBreadcrumbs.length - 1];

  if (prevId) {
    switchComposition(store, prevId);
  }

  storeLogger.debug('Navigated back, breadcrumbs:', store.compositionBreadcrumbs);
}

/**
 * Navigate to a specific breadcrumb index
 * Truncates the breadcrumb trail to that point
 */
export function navigateToBreadcrumb(store: CompositionStore, index: number): void {
  // Validate index (NaN comparisons are always false, so check explicitly)
  if (!Number.isInteger(index) || index < 0 || index >= store.compositionBreadcrumbs.length) {
    return;
  }

  // Already at this breadcrumb
  if (index === store.compositionBreadcrumbs.length - 1) {
    return;
  }

  // Truncate to the selected index
  store.compositionBreadcrumbs = store.compositionBreadcrumbs.slice(0, index + 1);
  const targetId = store.compositionBreadcrumbs[index];

  if (targetId) {
    switchComposition(store, targetId);
  }

  storeLogger.debug('Navigated to breadcrumb', index, 'breadcrumbs:', store.compositionBreadcrumbs);
}

/**
 * Reset breadcrumbs to main composition (e.g., when loading a new project)
 */
export function resetBreadcrumbs(store: CompositionStore): void {
  store.compositionBreadcrumbs = [store.project.mainCompositionId];
  switchComposition(store, store.project.mainCompositionId);
}

// ============================================================================
// NESTING
// ============================================================================

/**
 * Nest selected layers into a new composition
 */
export function nestSelectedLayers(store: CompositionStore, name?: string): Composition | null {
  if (store.selectedLayerIds.length === 0) {
    storeLogger.warn('No layers selected for nesting');
    return null;
  }

  const activeComp = store.project.compositions[store.activeCompositionId];
  if (!activeComp) return null;

  // Create new composition with same settings
  const nestedComp = createComposition(
    store,
    name || 'Nested Comp',
    activeComp.settings,
    true
  );

  // Move selected layers to nested comp
  const selectedLayers = activeComp.layers.filter(l =>
    store.selectedLayerIds.includes(l.id)
  );

  // Guard against empty array (selected IDs may not exist in current comp)
  if (selectedLayers.length === 0) {
    storeLogger.warn('Selected layers not found in active composition');
    return null;
  }

  // Find earliest startFrame to normalize timing
  const earliestIn = Math.min(...selectedLayers.map(l => l.startFrame ?? l.inPoint ?? 0));

  // Move layers to nested comp and adjust timing
  for (const layer of selectedLayers) {
    // Adjust timing relative to nested comp start (update both new and legacy properties)
    const layerStart = layer.startFrame ?? layer.inPoint ?? 0;
    const layerEnd = layer.endFrame ?? layer.outPoint ?? 80;
    layer.startFrame = layerStart - earliestIn;
    layer.endFrame = layerEnd - earliestIn;
    layer.inPoint = layer.startFrame;
    layer.outPoint = layer.endFrame;

    // Remove from parent
    const idx = activeComp.layers.indexOf(layer);
    if (idx >= 0) {
      activeComp.layers.splice(idx, 1);
    }

    // Add to nested comp
    nestedComp.layers.push(layer);
  }

  // Update nested comp duration to fit layers
  const maxOut = Math.max(...nestedComp.layers.map(l => l.endFrame ?? l.outPoint ?? 80));
  nestedComp.settings.frameCount = maxOut + 1;
  nestedComp.settings.duration = nestedComp.settings.frameCount / nestedComp.settings.fps;

  // Create nested comp layer in parent composition
  const nestedEndFrame = earliestIn + nestedComp.settings.frameCount - 1;
  const nestedCompLayer: Layer = {
    id: `layer_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    name: nestedComp.name,
    type: 'nestedComp',
    visible: true,
    locked: false,
    isolate: false,
    threeD: false,
    // Timing (primary properties)
    startFrame: earliestIn,
    endFrame: nestedEndFrame,
    // Backwards compatibility aliases
    inPoint: earliestIn,
    outPoint: nestedEndFrame,
    parentId: null,
    transform: createDefaultTransform(),
    opacity: createAnimatableProperty('opacity', 100, 'number'),
    properties: [],
    effects: [],
    blendMode: 'normal',
    motionBlur: false,
    data: {
      compositionId: nestedComp.id,
      // Speed map (new naming)
      speedMapEnabled: false,
      // Backwards compatibility
      timeRemapEnabled: false,
      flattenTransform: false
    } as NestedCompData
  };

  activeComp.layers.push(nestedCompLayer);

  // Clear selection
  useSelectionStore().clearLayerSelection();

  // Switch back to parent composition
  store.activeCompositionId = activeComp.id;

  storeLogger.debug('Nested layers into:', nestedComp.name);
  return nestedComp;
}
