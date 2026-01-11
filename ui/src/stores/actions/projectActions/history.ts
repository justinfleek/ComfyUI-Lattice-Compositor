/**
 * Project Actions - History Management
 *
 * Undo/redo functionality and history stack management.
 */

import { toRaw } from "vue";
import type { LatticeProject } from "@/types/project";
import type { ProjectStore } from "./types";

// ============================================================================
// CONSTANTS
// ============================================================================

const MAX_HISTORY_SIZE = 50;

// ============================================================================
// PARTICLE CACHE INVALIDATION
// ============================================================================

/**
 * Invalidate particle caches for all particle layers
 * Called after undo/redo to ensure particles reflect restored config
 */
function invalidateParticleCaches(): void {
  const engine = (window as unknown as { __latticeEngine?: {
    getLayers?: () => Array<{ clearCache?: () => void }>;
  } }).__latticeEngine;
  if (!engine) return;

  // Get all layers and clear cache for particle layers
  try {
    const layers = engine.getLayers?.() || [];
    for (const layer of layers) {
      if (layer && typeof layer.clearCache === "function") {
        layer.clearCache();
      }
    }
  } catch (_e) {
    // Silently fail if engine not fully initialized
  }
}

// ============================================================================
// HISTORY OPERATIONS
// ============================================================================

/**
 * Push current project state to history stack
 */
export function pushHistory(store: ProjectStore): void {
  // Remove any future history if we're not at the end
  if (store.historyIndex < store.historyStack.length - 1) {
    store.historyStack = store.historyStack.slice(0, store.historyIndex + 1);
  }

  // Deep clone the project using toRaw to deproxy reactive objects
  const snapshot = structuredClone(
    toRaw(store.project),
  ) as typeof store.project;
  store.historyStack.push(snapshot);
  store.historyIndex = store.historyStack.length - 1;

  // Limit history size
  if (store.historyStack.length > MAX_HISTORY_SIZE) {
    store.historyStack = store.historyStack.slice(-MAX_HISTORY_SIZE);
    store.historyIndex = store.historyStack.length - 1;
  }
}

/**
 * Undo - go back one step in history
 */
export function undo(store: ProjectStore): boolean {
  if (store.historyIndex <= 0) return false;

  store.historyIndex--;
  // Use toRaw to deproxy Pinia's reactive wrapper before cloning
  const historyEntry = toRaw(store.historyStack[store.historyIndex]);
  store.project = structuredClone(historyEntry) as LatticeProject;

  // Invalidate particle caches so they reset to restored config
  invalidateParticleCaches();

  return true;
}

/**
 * Redo - go forward one step in history
 */
export function redo(store: ProjectStore): boolean {
  if (store.historyIndex >= store.historyStack.length - 1) return false;

  store.historyIndex++;
  // Use toRaw to deproxy Pinia's reactive wrapper before cloning
  const historyEntry = toRaw(store.historyStack[store.historyIndex]);
  store.project = structuredClone(historyEntry) as LatticeProject;

  // Invalidate particle caches so they reset to restored config
  invalidateParticleCaches();

  return true;
}

/**
 * Check if undo is available
 */
export function canUndo(store: ProjectStore): boolean {
  return store.historyIndex > 0;
}

/**
 * Check if redo is available
 */
export function canRedo(store: ProjectStore): boolean {
  return store.historyIndex < store.historyStack.length - 1;
}

/**
 * Clear history stack
 */
export function clearHistory(store: ProjectStore): void {
  // Use toRaw to deproxy reactive objects before cloning
  const snapshot = structuredClone(
    toRaw(store.project),
  ) as typeof store.project;
  store.historyStack = [snapshot];
  store.historyIndex = 0;
}
