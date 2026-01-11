/**
 * Project Actions - Types
 *
 * Store interface for project actions.
 */

import type { LatticeProject } from "@/types/project";

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface ProjectStore {
  project: LatticeProject;
  historyStack: LatticeProject[];
  historyIndex: number;
  lastSaveProjectId: string | null;
  lastSaveTime: number | null;
  hasUnsavedChanges: boolean;
  autosaveEnabled?: boolean;
  autosaveIntervalMs?: number;
  autosaveTimerId?: number | null;
  snapConfig?: unknown; // Snapping configuration (optional)
}
