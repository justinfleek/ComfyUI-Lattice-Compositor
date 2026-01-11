/**
 * Project Actions - Initialization
 *
 * Create default projects and reset project state.
 */

import { CURRENT_SCHEMA_VERSION } from "@/services/projectMigration";
import type { LatticeProject } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { clearHistory } from "./history";
import type { ProjectStore } from "./types";

// ============================================================================
// DEFAULT PROJECT
// ============================================================================

/**
 * Create a default new project structure
 */
export function createDefaultProject(): LatticeProject {
  const mainCompId = "comp_main";

  return {
    version: "1.0.0",
    schemaVersion: CURRENT_SCHEMA_VERSION,
    meta: {
      name: "Untitled Project",
      created: new Date().toISOString(),
      modified: new Date().toISOString(),
      author: "",
    },
    // Legacy single-comp alias
    composition: {
      width: 1920,
      height: 1080,
      frameCount: 81,
      fps: 16,
      duration: 5.0625, // 81 frames at 16fps
      backgroundColor: "#1a1a1a",
      autoResizeToContent: false,
      frameBlendingEnabled: false,
    },
    // Multi-composition support
    compositions: {
      [mainCompId]: {
        id: mainCompId,
        name: "Main Comp",
        settings: {
          width: 1920,
          height: 1080,
          frameCount: 81,
          fps: 16,
          duration: 5.0625,
          backgroundColor: "#1a1a1a",
          autoResizeToContent: false,
          frameBlendingEnabled: false,
        },
        layers: [],
        currentFrame: 0,
        isNestedComp: false,
      },
    },
    mainCompositionId: mainCompId,
    layers: [], // Legacy
    currentFrame: 0,
    assets: {},
  };
}

// ============================================================================
// PROJECT RESET
// ============================================================================

/**
 * Reset project to default state
 */
export function resetProject(store: ProjectStore): void {
  store.project = createDefaultProject();
  store.lastSaveProjectId = null;
  store.lastSaveTime = 0;
  store.hasUnsavedChanges = false;
  clearHistory(store);
  storeLogger.info("Project reset to default state");
}
