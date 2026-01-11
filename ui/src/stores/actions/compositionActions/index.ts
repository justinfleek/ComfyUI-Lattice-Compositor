/**
 * Composition Actions
 *
 * Composition management including creation, deletion, navigation,
 * breadcrumb trail, and nested composition handling.
 *
 * MODULE STRUCTURE:
 * - types.ts: Store interface
 * - crud.ts: Composition CRUD operations
 * - navigation.ts: Tab management and breadcrumb navigation
 * - nesting.ts: Nest layers into compositions
 */

// Types
export type { CompositionStore } from "./types";

// CRUD operations
export {
  createComposition,
  deleteComposition,
  renameComposition,
  updateCompositionSettings,
  enableFrameBlending,
  disableFrameBlending,
  toggleFrameBlending,
  getComposition,
} from "./crud";

// Navigation
export {
  switchComposition,
  closeCompositionTab,
  enterNestedComp,
  navigateBack,
  navigateToBreadcrumb,
  resetBreadcrumbs,
} from "./navigation";

// Nesting
export { nestSelectedLayers } from "./nesting";
