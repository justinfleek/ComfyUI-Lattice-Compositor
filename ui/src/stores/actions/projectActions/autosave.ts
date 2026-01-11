/**
 * Project Actions - Autosave Management
 *
 * Start, stop, and configure autosave functionality.
 */

import { saveProject } from "@/services/projectStorage";
import { storeLogger } from "@/utils/logger";
import type { ProjectStore } from "./types";

// ============================================================================
// AUTOSAVE TIMER MANAGEMENT
// ============================================================================

/**
 * Start autosave timer
 */
export function startAutosave(
  store: ProjectStore,
  performAutosaveFn: () => Promise<void>,
): void {
  // Don't start if already running or disabled
  if (store.autosaveTimerId !== null || !store.autosaveEnabled) {
    return;
  }

  store.autosaveTimerId = window.setInterval(
    performAutosaveFn,
    store.autosaveIntervalMs,
  );
  storeLogger.info("Autosave started with interval:", store.autosaveIntervalMs);
}

/**
 * Stop autosave timer
 */
export function stopAutosave(store: ProjectStore): void {
  if (store.autosaveTimerId !== null && store.autosaveTimerId !== undefined) {
    window.clearInterval(store.autosaveTimerId);
    store.autosaveTimerId = null;
    storeLogger.info("Autosave stopped");
  }
}

/**
 * Configure autosave settings
 */
export function configureAutosave(
  store: ProjectStore,
  options: { enabled?: boolean; intervalMs?: number },
  performAutosaveFn: () => Promise<void>,
): void {
  if (options.enabled !== undefined) {
    store.autosaveEnabled = options.enabled;
  }
  // Validate intervalMs (NaN in setInterval causes unpredictable behavior)
  if (
    options.intervalMs !== undefined &&
    Number.isFinite(options.intervalMs) &&
    options.intervalMs > 0
  ) {
    store.autosaveIntervalMs = options.intervalMs;
  }

  // Restart autosave with new settings
  stopAutosave(store);
  if (store.autosaveEnabled) {
    startAutosave(store, performAutosaveFn);
  }
}

// ============================================================================
// AUTOSAVE EXECUTION
// ============================================================================

/**
 * Perform an autosave
 */
export async function performAutosave(store: ProjectStore): Promise<void> {
  if (!store.hasUnsavedChanges) return;

  try {
    const existingProjectId = store.lastSaveProjectId || undefined;
    const result = await saveProject(store.project, existingProjectId);

    if (result.status === "success" && result.project_id) {
      store.lastSaveProjectId = result.project_id;
      store.lastSaveTime = Date.now();
      store.hasUnsavedChanges = false;
      storeLogger.info("Autosaved project:", result.project_id);
    } else {
      storeLogger.error("Autosave failed:", result.message);
    }
  } catch (error) {
    storeLogger.error("Autosave failed:", error);
  }
}

/**
 * Mark the project as having unsaved changes
 */
export function markUnsavedChanges(store: ProjectStore): void {
  store.hasUnsavedChanges = true;
}
