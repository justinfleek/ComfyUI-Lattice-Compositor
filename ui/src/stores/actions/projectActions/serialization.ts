/**
 * Project Actions - Serialization
 *
 * Import, export, and load projects from files.
 */

import { validateProjectExpressions } from "@/services/expressions/expressionValidator";
import {
  CURRENT_SCHEMA_VERSION,
  migrateProject,
  needsMigration,
} from "@/services/projectMigration";
import type { LatticeProject } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { validateProjectStructure } from "@/utils/security";
import type { ProjectStore } from "./types";

// ============================================================================
// EXPORT
// ============================================================================

/**
 * Export project to JSON string
 */
export function exportProject(store: ProjectStore): string {
  const project = { ...store.project };

  // Include snapConfig if available (from CompositorState)
  // This allows user snapping preferences to be preserved across save/load
  if ("snapConfig" in store && store.snapConfig) {
    (project as Record<string, unknown>).snapConfig = store.snapConfig;
  }

  return JSON.stringify(project, null, 2);
}

// ============================================================================
// IMPORT
// ============================================================================

/**
 * Import project from JSON string
 * Automatically migrates older project schemas to current version
 */
export function importProject(
  store: ProjectStore,
  json: string,
  pushHistoryFn: () => void,
): boolean {
  try {
    let project = JSON.parse(json) as LatticeProject;

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
      validateProjectStructure(project, "Imported project");
    } catch (validationError) {
      storeLogger.error(
        "Project structure validation failed:",
        validationError,
      );
      return false;
    }

    // Restore snapConfig if present in imported project
    // This preserves user snapping preferences across save/load
    const projectWithSnap = project as unknown as Record<string, unknown>;
    if (projectWithSnap.snapConfig && "snapConfig" in store) {
      try {
        (store as unknown as Record<string, unknown>).snapConfig = projectWithSnap.snapConfig;
        storeLogger.info("Restored snapConfig from imported project");
      } catch (snapError) {
        storeLogger.warn(
          "Failed to restore snapConfig, using defaults:",
          snapError,
        );
        // Continue with default snapConfig - not a fatal error
      }
    } else if ("snapConfig" in store) {
      // No snapConfig in imported project - use defaults (backwards compatibility)
      storeLogger.info("No snapConfig in imported project, using defaults");
    }

    // Remove snapConfig from project before assigning (it's not part of LatticeProject core)
    const { snapConfig: _, ...projectWithoutSnapConfig } = projectWithSnap;
    store.project = projectWithoutSnapConfig as unknown as LatticeProject;
    pushHistoryFn();
    return true;
  } catch (err) {
    storeLogger.error("Failed to import project:", err);
    return false;
  }
}

// ============================================================================
// FILE LOADING
// ============================================================================

/**
 * Load project from a File object
 * Reads the file as text and calls importProject
 *
 * @param store - The project store
 * @param file - File object (from file input or drag-drop)
 * @param pushHistoryFn - Function to push history after load
 * @returns Promise resolving to true if successful
 */
export async function loadProjectFromFile(
  store: ProjectStore,
  file: File,
  pushHistoryFn: () => void,
): Promise<boolean> {
  try {
    const json = await file.text();

    // SECURITY: Pre-validate expressions before loading
    // This catches infinite loops BEFORE they can hang the render loop
    try {
      const project = JSON.parse(json) as LatticeProject;
      const validation = await validateProjectExpressions(project);

      if (!validation.valid) {
        const dangerList = validation.dangerous
          .map((d) => `  - ${d.location}: ${d.reason}`)
          .join("\n");
        storeLogger.error(
          `[SECURITY] Project contains ${validation.dangerous.length} dangerous expression(s):\n${dangerList}`,
        );
        console.warn(
          `[SECURITY] Dangerous expressions detected in "${file.name}":\n${dangerList}\n` +
            "These expressions may contain infinite loops. Project load blocked for safety.",
        );
        return false;
      }

      if (validation.total > 0) {
        storeLogger.info(
          `[SECURITY] Validated ${validation.validated}/${validation.total} expressions (all safe)`,
        );
      }
    } catch (_parseErr) {
      // JSON parse error will be caught by importProject, let it handle
    }

    const success = importProject(store, json, pushHistoryFn);

    if (success) {
      storeLogger.info("Loaded project from file:", file.name);
    }

    return success;
  } catch (err) {
    storeLogger.error("Failed to load project from file:", err);
    return false;
  }
}
