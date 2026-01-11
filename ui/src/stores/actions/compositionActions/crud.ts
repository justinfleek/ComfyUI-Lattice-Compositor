/**
 * Composition Actions - CRUD
 *
 * Create, read, update, delete composition operations.
 */

import type { Composition, CompositionSettings } from "@/types/project";
import { DEFAULT_FPS, validateFps } from "@/utils/fpsUtils";
import { storeLogger } from "@/utils/logger";
import type { CompositionStore } from "./types";

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
  isNestedComp: boolean = false,
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
    backgroundColor: settings?.backgroundColor ?? "#050505",
    autoResizeToContent: settings?.autoResizeToContent ?? true,
    frameBlendingEnabled: settings?.frameBlendingEnabled ?? false,
  };
  defaultSettings.duration = defaultSettings.frameCount / defaultSettings.fps;

  const composition: Composition = {
    id,
    name,
    settings: defaultSettings,
    layers: [],
    currentFrame: 0,
    isNestedComp,
  };

  store.project.compositions[id] = composition;

  // Open and switch to new composition
  if (!store.openCompositionIds.includes(id)) {
    store.openCompositionIds.push(id);
  }
  store.activeCompositionId = id;

  // Push history for undo/redo
  store.pushHistory();

  storeLogger.debug("Created composition:", name, id);
  return composition;
}

/**
 * Delete a composition
 */
export function deleteComposition(
  store: CompositionStore,
  compId: string,
): boolean {
  // Can't delete main composition
  if (compId === store.project.mainCompositionId) {
    storeLogger.warn("Cannot delete main composition");
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
    store.activeCompositionId =
      store.openCompositionIds[0] || store.project.mainCompositionId;
  }

  storeLogger.debug("Deleted composition:", compId);
  return true;
}

/**
 * Rename a composition
 */
export function renameComposition(
  store: CompositionStore,
  compId: string,
  newName: string,
): void {
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
  settings: Partial<CompositionSettings>,
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
export function enableFrameBlending(
  store: CompositionStore,
  compId: string,
): void {
  updateCompositionSettings(store, compId, { frameBlendingEnabled: true });
}

/**
 * Disable frame blending for a composition
 */
export function disableFrameBlending(
  store: CompositionStore,
  compId: string,
): void {
  updateCompositionSettings(store, compId, { frameBlendingEnabled: false });
}

/**
 * Toggle frame blending for a composition
 */
export function toggleFrameBlending(
  store: CompositionStore,
  compId: string,
): void {
  const comp = store.project.compositions[compId];
  if (!comp) return;

  const enabled = !comp.settings.frameBlendingEnabled;
  updateCompositionSettings(store, compId, { frameBlendingEnabled: enabled });
}

/**
 * Get a composition by ID
 */
export function getComposition(
  store: CompositionStore,
  compId: string,
): Composition | null {
  return store.project.compositions[compId] || null;
}
