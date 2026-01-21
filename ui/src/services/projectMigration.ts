/**
 * Project Migration Service
 *
 * Phase 10: Project Versioning Implementation
 *
 * Features:
 * - Schema versioning
 * - Automatic migration on load
 * - Migration registry
 * - Backwards compatibility
 */

import type { JSONValue } from "@/types/dataAsset";
import { createLogger } from "@/utils/logger";

const logger = createLogger("ProjectMigration");

// ============================================================================
// TYPES
// ============================================================================

/** Current schema version */
export const CURRENT_SCHEMA_VERSION = 2;

/** Minimum supported schema version for migration */
export const MIN_SUPPORTED_VERSION = 1;

/**
 * Legacy layer structure for migration
 * Contains properties that may need renaming during v1→v2 migration
 */
interface LegacyLayer {
  transform?: {
    anchorPoint?: JSONValue;
    origin?: JSONValue;
  };
  inPoint?: number;
  startFrame?: number;
  outPoint?: number;
  endFrame?: number;
  solo?: boolean;      // Renamed to isolate in v2
  isolate?: boolean;   // New name in v2
  data?: {
    timeRemapEnabled?: boolean;
    timeRemap?: JSONValue;
    speedMapEnabled?: boolean;
    speedMap?: JSONValue;
  };
}

/**
 * Legacy project structure where compositions was an array
 * Used during migration from v1 to v2
 */
interface LegacyComposition {
  id?: string;
  layers?: LegacyLayer[];
}

/**
 * Versioned project structure for migration
 * Extends LatticeProject with version metadata and legacy format support
 */
export interface VersionedProject extends Omit<import("@/types/project").LatticeProject, "compositions"> {
  /** Project schema version */
  schemaVersion: number;
  /** Project file format version (semantic) */
  version: string;
  /** Compositions - may be array (v1) or record (v2+) */
  compositions: Record<string, import("@/types/project").Composition> | LegacyComposition[];
}

export interface MigrationResult {
  /** Whether migration was successful */
  success: boolean;
  /** Original version */
  fromVersion: number;
  /** Target version */
  toVersion: number;
  /** Migrated project data */
  project?: VersionedProject;
  /** Error message if failed */
  error?: string;
  /** Warnings during migration */
  warnings: string[];
  /** Changes made during migration */
  changes: string[];
}

/**
 * Migration function type
 * Takes a project of any version and returns a migrated project
 */
export type MigrationFunction = (
  project: VersionedProject,
) => VersionedProject;

export interface Migration {
  /** Source version */
  from: number;
  /** Target version */
  to: number;
  /** Description of changes */
  description: string;
  /** Migration function */
  migrate: MigrationFunction;
}

// ============================================================================
// MIGRATIONS REGISTRY
// ============================================================================

const migrations: Migration[] = [
  // v1 -> v2: Rename anchorPoint to origin, add trade dress updates
  {
    from: 1,
    to: 2,
    description: "Rename anchorPoint to origin, update trade dress terminology",
    migrate: (project: VersionedProject): VersionedProject => {
      const migrated = JSON.parse(JSON.stringify(project)) as VersionedProject;

      // Migrate compositions
      if (Array.isArray(migrated.compositions)) {
        for (const comp of migrated.compositions) {
          if (comp.layers) {
            for (const layer of comp.layers) {
              // Rename anchorPoint to origin
              // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
              const layerTransform = (layer != null && typeof layer === "object" && "transform" in layer && layer.transform != null && typeof layer.transform === "object") ? layer.transform : undefined;
              const anchorPoint = (layerTransform != null && typeof layerTransform === "object" && "anchorPoint" in layerTransform && layerTransform.anchorPoint !== undefined) ? layerTransform.anchorPoint : undefined;
              if (anchorPoint !== undefined) {
                layerTransform.origin = anchorPoint;
                delete layerTransform.anchorPoint;
              }

              // Rename inPoint/outPoint to startFrame/endFrame
              if (layer.inPoint !== undefined) {
                layer.startFrame = layer.inPoint;
                delete layer.inPoint;
              }
              if (layer.outPoint !== undefined) {
                layer.endFrame = layer.outPoint;
                delete layer.outPoint;
              }

              // Rename timeRemap to speedMap for video layers
              const layerData = (layer != null && typeof layer === "object" && "data" in layer && layer.data != null && typeof layer.data === "object") ? layer.data : undefined;
              const timeRemapEnabled = (layerData != null && typeof layerData === "object" && "timeRemapEnabled" in layerData && layerData.timeRemapEnabled !== undefined) ? layerData.timeRemapEnabled : undefined;
              if (timeRemapEnabled !== undefined) {
                layerData.speedMapEnabled = timeRemapEnabled;
                delete layerData.timeRemapEnabled;
              }
              const timeRemap = (layerData != null && typeof layerData === "object" && "timeRemap" in layerData && layerData.timeRemap !== undefined) ? layerData.timeRemap : undefined;
              if (timeRemap !== undefined) {
                layerData.speedMap = timeRemap;
                delete layerData.timeRemap;
              }

              // Rename solo to isolate
              if (layer.solo !== undefined) {
                layer.isolate = layer.solo;
                delete layer.solo;
              }
            }
          }
        }
      }

      migrated.schemaVersion = 2;
      return migrated;
    },
  },

  // Future migrations would be added here
  // {
  //   from: 2,
  //   to: 3,
  //   description: 'Add new feature X',
  //   migrate: (project) => { ... }
  // },
];

// ============================================================================
// MIGRATION ENGINE
// ============================================================================

/**
 * Get the schema version from a project
 */
export function getProjectVersion(
  project: VersionedProject | Record<string, JSONValue>,
): number {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const schemaVersion = (project != null && typeof project === "object" && "schemaVersion" in project && typeof project.schemaVersion === "number") ? project.schemaVersion : undefined;
  if (schemaVersion !== undefined) {
    return schemaVersion;
  }

  // Legacy project without version = version 1
  return 1;
}

/**
 * Check if a project needs migration
 */
export function needsMigration(
  project: VersionedProject | Record<string, JSONValue>,
): boolean {
  const version = getProjectVersion(project);
  return version < CURRENT_SCHEMA_VERSION;
}

/**
 * Get migration path from source to target version
 */
function getMigrationPath(from: number, to: number): Migration[] {
  const path: Migration[] = [];
  let current = from;

  while (current < to) {
    const migration = migrations.find((m) => m.from === current);
    if (!migration) {
      throw new Error(`No migration found from version ${current}`);
    }
    path.push(migration);
    current = migration.to;
  }

  return path;
}

/**
 * Migrate a project to the current schema version
 */
export function migrateProject(
  project: VersionedProject | Record<string, JSONValue>,
): MigrationResult {
  const fromVersion = getProjectVersion(project);
  const toVersion = CURRENT_SCHEMA_VERSION;
  const warnings: string[] = [];
  const changes: string[] = [];

  // Check if already current
  if (fromVersion === toVersion) {
    return {
      success: true,
      fromVersion,
      toVersion,
      project,
      warnings: [],
      changes: [],
    };
  }

  // Check if version is too old - throw explicit error
  if (fromVersion < MIN_SUPPORTED_VERSION) {
    throw new Error(`[ProjectMigration] Project version ${fromVersion} is too old. Minimum supported version is ${MIN_SUPPORTED_VERSION}. Project cannot be migrated.`);
  }

  // Check if version is too new - throw explicit error
  if (fromVersion > toVersion) {
    throw new Error(`[ProjectMigration] Project version ${fromVersion} is newer than current application version ${toVersion}. Please update the application to load this project.`);
  }

  try {
    // Get migration path
    const path = getMigrationPath(fromVersion, toVersion);

    // Apply migrations in sequence
    let migrated = project;
    for (const migration of path) {
      logger.info(
        `Migrating from v${migration.from} to v${migration.to}: ${migration.description}`,
      );
      changes.push(
        `v${migration.from} → v${migration.to}: ${migration.description}`,
      );

      migrated = migration.migrate(migrated);
    }

    // Ensure schema version is set
    migrated.schemaVersion = toVersion;

    logger.info(`Migration complete: v${fromVersion} → v${toVersion}`);

    return {
      success: true,
      fromVersion,
      toVersion,
      project: migrated,
      warnings,
      changes,
    };
  } catch (error) {
    // Re-throw with context - don't silently fail
    const errorMessage = error instanceof Error ? error.message : String(error);
    throw new Error(`[ProjectMigration] Migration failed from version ${fromVersion} to ${toVersion}: ${errorMessage}. Project data may be corrupted or incompatible.`);
  }
}

/**
 * Stamp project with current version
 */
export function stampProjectVersion(
  project: Record<string, JSONValue>,
): VersionedProject {
  return {
    ...project,
    schemaVersion: CURRENT_SCHEMA_VERSION,
    version: "1.0.0", // Semantic version for display
    lastModified: new Date().toISOString(),
  };
}

/**
 * Get available migrations
 */
export function getAvailableMigrations(): Migration[] {
  return [...migrations];
}

/**
 * Get migration info for a specific version transition
 */
export function getMigrationInfo(
  from: number,
  to: number,
): Migration | undefined {
  return migrations.find((m) => m.from === from && m.to === to);
}

// ============================================================================
// EXPORTS
// ============================================================================

export default {
  CURRENT_SCHEMA_VERSION,
  MIN_SUPPORTED_VERSION,
  getProjectVersion,
  needsMigration,
  migrateProject,
  stampProjectVersion,
  getAvailableMigrations,
  getMigrationInfo,
};
