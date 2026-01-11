/**
 * Project Actions - Server Operations
 *
 * Save, load, list, and delete projects on the ComfyUI backend.
 */

import { validateProjectExpressions } from "@/services/expressions/expressionValidator";
import {
  CURRENT_SCHEMA_VERSION,
  migrateProject,
  needsMigration,
} from "@/services/projectMigration";
import {
  deleteProject,
  listProjects,
  loadProject,
  saveProject,
} from "@/services/projectStorage";
import type { LatticeProject } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { validateProjectStructure } from "@/utils/security";
import type { ProjectStore } from "./types";

// ============================================================================
// SAVE
// ============================================================================

/**
 * Save project to server (ComfyUI backend)
 * @returns The project ID if successful, null otherwise
 */
export async function saveProjectToServer(
  store: ProjectStore,
  projectId?: string,
): Promise<string | null> {
  try {
    const result = await saveProject(store.project, projectId);

    if (result.status === "success" && result.project_id) {
      store.lastSaveProjectId = result.project_id;
      store.lastSaveTime = Date.now();
      store.hasUnsavedChanges = false;
      storeLogger.info("Project saved to server:", result.project_id);
      return result.project_id;
    } else {
      storeLogger.error("Failed to save project:", result.message);
      return null;
    }
  } catch (err) {
    storeLogger.error("Error saving project to server:", err);
    return null;
  }
}

// ============================================================================
// LOAD
// ============================================================================

/**
 * Load project from server (ComfyUI backend)
 * Automatically migrates older project schemas to current version
 */
export async function loadProjectFromServer(
  store: ProjectStore,
  projectId: string,
  pushHistoryFn: () => void,
): Promise<boolean> {
  try {
    const result = await loadProject(projectId);

    if (result.status === "success" && result.project) {
      let project = result.project;

      // Check if migration is needed and apply it FIRST
      // Migration transforms v1 format to v2 format
      if (needsMigration(project)) {
        const oldVersion =
          (project as unknown as { schemaVersion?: number }).schemaVersion ?? 1;
        storeLogger.info(
          `Migrating project from schema v${oldVersion} to v${CURRENT_SCHEMA_VERSION}`,
        );
        const migrationResult = migrateProject(project);
        if (migrationResult.success && migrationResult.project) {
          project = migrationResult.project as LatticeProject;
          storeLogger.info("Project migration completed successfully");
        } else {
          storeLogger.error("Project migration failed:", migrationResult.error);
          return false;
        }
      }

      // SECURITY: Validate structure AFTER migration (ensures v2 format)
      // This catches NaN/Infinity values and malformed data
      try {
        validateProjectStructure(project, `Server project '${projectId}'`);
      } catch (validationError) {
        storeLogger.error(
          "Project structure validation failed:",
          validationError,
        );
        return false;
      }

      // SECURITY: Pre-validate expressions before loading
      const validation = await validateProjectExpressions(project);
      if (!validation.valid) {
        const dangerList = validation.dangerous
          .map((d) => `  - ${d.location}: ${d.reason}`)
          .join("\n");
        storeLogger.error(
          `[SECURITY] Project contains ${validation.dangerous.length} dangerous expression(s):\n${dangerList}`,
        );
        console.warn(
          `[SECURITY] Dangerous expressions detected in project "${projectId}":\n${dangerList}\n` +
            "These expressions may contain infinite loops. Project load blocked for safety.",
        );
        return false;
      }

      if (validation.total > 0) {
        storeLogger.info(
          `[SECURITY] Validated ${validation.validated}/${validation.total} expressions (all safe)`,
        );
      }

      store.project = project;
      pushHistoryFn();
      store.lastSaveProjectId = projectId;
      store.lastSaveTime = Date.now();
      store.hasUnsavedChanges = false;
      storeLogger.info("Project loaded from server:", projectId);
      return true;
    } else {
      storeLogger.error("Failed to load project:", result.message);
      return false;
    }
  } catch (err) {
    storeLogger.error("Error loading project from server:", err);
    return false;
  }
}

// ============================================================================
// LIST / DELETE
// ============================================================================

/**
 * List all projects saved on server
 */
export async function listServerProjects(): Promise<
  Array<{ id: string; name: string; modified?: string }>
> {
  try {
    const result = await listProjects();

    if (result.status === "success" && result.projects) {
      return result.projects;
    }
    return [];
  } catch (err) {
    storeLogger.error("Error listing projects:", err);
    return [];
  }
}

/**
 * Delete a project from server
 */
export async function deleteServerProject(projectId: string): Promise<boolean> {
  try {
    const result = await deleteProject(projectId);
    return result.status === "success";
  } catch (err) {
    storeLogger.error("Error deleting project:", err);
    return false;
  }
}
