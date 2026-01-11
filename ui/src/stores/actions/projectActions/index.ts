/**
 * Project Actions
 *
 * Project lifecycle operations: history management, serialization,
 * server persistence, and autosave functionality.
 *
 * MODULE STRUCTURE:
 * - types.ts: Store interface
 * - history.ts: Undo/redo, pushHistory
 * - serialization.ts: Import/export, load from file
 * - server.ts: Server save/load operations
 * - autosave.ts: Autosave management
 * - initialization.ts: Create/reset project
 * - assets.ts: Asset management, collect files
 */

// Types
export type { ProjectStore } from "./types";

// History operations
export {
  pushHistory,
  undo,
  redo,
  canUndo,
  canRedo,
  clearHistory,
} from "./history";

// Serialization
export {
  exportProject,
  importProject,
  loadProjectFromFile,
} from "./serialization";

// Server operations
export {
  saveProjectToServer,
  loadProjectFromServer,
  listServerProjects,
  deleteServerProject,
} from "./server";

// Autosave
export {
  startAutosave,
  stopAutosave,
  configureAutosave,
  performAutosave,
  markUnsavedChanges,
} from "./autosave";

// Project initialization
export { createDefaultProject, resetProject } from "./initialization";

// Asset management
export {
  findUsedAssetIds,
  removeUnusedAssets,
  getAssetUsageStats,
  collectFiles,
  downloadCollectedFiles,
} from "./assets";
