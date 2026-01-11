/**
 * Composition Actions - Navigation
 *
 * Tab management and breadcrumb navigation for nested compositions.
 */

import { storeLogger } from "@/utils/logger";
import { useSelectionStore } from "../../selectionStore";
import type { CompositionStore } from "./types";

// ============================================================================
// TAB MANAGEMENT
// ============================================================================

/**
 * Switch to a different composition (tab)
 */
export function switchComposition(
  store: CompositionStore,
  compId: string,
): void {
  if (!store.project.compositions[compId]) {
    storeLogger.warn("Composition not found:", compId);
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
  storeLogger.debug("Switched to composition:", compId);
}

/**
 * Close a composition tab
 */
export function closeCompositionTab(
  store: CompositionStore,
  compId: string,
): void {
  // Can't close if it's the only open tab
  if (store.openCompositionIds.length <= 1) {
    storeLogger.warn("Cannot close the last tab");
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
    storeLogger.warn("Nested comp not found:", compId);
    return;
  }

  // Add to breadcrumb trail
  store.compositionBreadcrumbs.push(compId);

  // Switch to the composition
  switchComposition(store, compId);

  storeLogger.debug(
    "Entered nested comp:",
    compId,
    "breadcrumbs:",
    store.compositionBreadcrumbs,
  );
}

/**
 * Navigate back one level in the breadcrumb trail
 */
export function navigateBack(store: CompositionStore): void {
  if (store.compositionBreadcrumbs.length <= 1) {
    storeLogger.warn("Already at root composition");
    return;
  }

  // Pop current and switch to previous
  store.compositionBreadcrumbs.pop();
  const prevId =
    store.compositionBreadcrumbs[store.compositionBreadcrumbs.length - 1];

  if (prevId) {
    switchComposition(store, prevId);
  }

  storeLogger.debug(
    "Navigated back, breadcrumbs:",
    store.compositionBreadcrumbs,
  );
}

/**
 * Navigate to a specific breadcrumb index
 * Truncates the breadcrumb trail to that point
 */
export function navigateToBreadcrumb(
  store: CompositionStore,
  index: number,
): void {
  // Validate index (NaN comparisons are always false, so check explicitly)
  if (
    !Number.isInteger(index) ||
    index < 0 ||
    index >= store.compositionBreadcrumbs.length
  ) {
    return;
  }

  // Already at this breadcrumb
  if (index === store.compositionBreadcrumbs.length - 1) {
    return;
  }

  // Truncate to the selected index
  store.compositionBreadcrumbs = store.compositionBreadcrumbs.slice(
    0,
    index + 1,
  );
  const targetId = store.compositionBreadcrumbs[index];

  if (targetId) {
    switchComposition(store, targetId);
  }

  storeLogger.debug(
    "Navigated to breadcrumb",
    index,
    "breadcrumbs:",
    store.compositionBreadcrumbs,
  );
}

/**
 * Reset breadcrumbs to main composition (e.g., when loading a new project)
 */
export function resetBreadcrumbs(store: CompositionStore): void {
  store.compositionBreadcrumbs = [store.project.mainCompositionId];
  switchComposition(store, store.project.mainCompositionId);
}
