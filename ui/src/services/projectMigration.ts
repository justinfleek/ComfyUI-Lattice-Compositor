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

import { createLogger } from '@/utils/logger';

const logger = createLogger('ProjectMigration');

// ============================================================================
// TYPES
// ============================================================================

/** Current schema version */
export const CURRENT_SCHEMA_VERSION = 2;

/** Minimum supported schema version for migration */
export const MIN_SUPPORTED_VERSION = 1;

export interface VersionedProject {
  /** Project schema version */
  schemaVersion: number;
  /** Project file format version (semantic) */
  version: string;
  /** Rest of project data */
  [key: string]: any;
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

export type MigrationFunction = (project: any) => any;

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
    description: 'Rename anchorPoint to origin, update trade dress terminology',
    migrate: (project: any) => {
      const migrated = JSON.parse(JSON.stringify(project));

      // Migrate compositions
      if (migrated.compositions) {
        for (const comp of migrated.compositions) {
          if (comp.layers) {
            for (const layer of comp.layers) {
              // Rename anchorPoint to origin
              if (layer.transform?.anchorPoint !== undefined) {
                layer.transform.origin = layer.transform.anchorPoint;
                delete layer.transform.anchorPoint;
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
              if (layer.data?.timeRemapEnabled !== undefined) {
                layer.data.speedMapEnabled = layer.data.timeRemapEnabled;
                delete layer.data.timeRemapEnabled;
              }
              if (layer.data?.timeRemap !== undefined) {
                layer.data.speedMap = layer.data.timeRemap;
                delete layer.data.timeRemap;
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
export function getProjectVersion(project: any): number {
  if (typeof project?.schemaVersion === 'number') {
    return project.schemaVersion;
  }

  // Legacy project without version = version 1
  return 1;
}

/**
 * Check if a project needs migration
 */
export function needsMigration(project: any): boolean {
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
    const migration = migrations.find(m => m.from === current);
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
export function migrateProject(project: any): MigrationResult {
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

  // Check if version is too old
  if (fromVersion < MIN_SUPPORTED_VERSION) {
    return {
      success: false,
      fromVersion,
      toVersion,
      error: `Project version ${fromVersion} is too old. Minimum supported version is ${MIN_SUPPORTED_VERSION}`,
      warnings,
      changes,
    };
  }

  // Check if version is too new
  if (fromVersion > toVersion) {
    return {
      success: false,
      fromVersion,
      toVersion,
      error: `Project version ${fromVersion} is newer than current application version ${toVersion}. Please update the application.`,
      warnings,
      changes,
    };
  }

  try {
    // Get migration path
    const path = getMigrationPath(fromVersion, toVersion);

    // Apply migrations in sequence
    let migrated = project;
    for (const migration of path) {
      logger.info(`Migrating from v${migration.from} to v${migration.to}: ${migration.description}`);
      changes.push(`v${migration.from} → v${migration.to}: ${migration.description}`);

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
    logger.error('Migration failed:', error);
    return {
      success: false,
      fromVersion,
      toVersion,
      error: error instanceof Error ? error.message : 'Unknown migration error',
      warnings,
      changes,
    };
  }
}

/**
 * Validate project structure
 */
export function validateProject(project: any): { valid: boolean; errors: string[] } {
  const errors: string[] = [];

  if (!project) {
    errors.push('Project is null or undefined');
    return { valid: false, errors };
  }

  if (typeof project !== 'object') {
    errors.push('Project must be an object');
    return { valid: false, errors };
  }

  // Check required fields
  if (!project.id) {
    errors.push('Project missing required field: id');
  }

  if (!project.name) {
    errors.push('Project missing required field: name');
  }

  if (!Array.isArray(project.compositions)) {
    errors.push('Project must have compositions array');
  }

  // Validate compositions
  if (project.compositions) {
    for (let i = 0; i < project.compositions.length; i++) {
      const comp = project.compositions[i];

      if (!comp.id) {
        errors.push(`Composition ${i} missing required field: id`);
      }

      if (!comp.name) {
        errors.push(`Composition ${i} missing required field: name`);
      }

      if (typeof comp.width !== 'number' || comp.width <= 0) {
        errors.push(`Composition ${i} has invalid width`);
      }

      if (typeof comp.height !== 'number' || comp.height <= 0) {
        errors.push(`Composition ${i} has invalid height`);
      }

      if (typeof comp.frameCount !== 'number' || comp.frameCount <= 0) {
        errors.push(`Composition ${i} has invalid frameCount`);
      }
    }
  }

  return { valid: errors.length === 0, errors };
}

/**
 * Stamp project with current version
 */
export function stampProjectVersion(project: any): any {
  return {
    ...project,
    schemaVersion: CURRENT_SCHEMA_VERSION,
    version: '1.0.0',  // Semantic version for display
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
export function getMigrationInfo(from: number, to: number): Migration | undefined {
  return migrations.find(m => m.from === from && m.to === to);
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
  validateProject,
  stampProjectVersion,
  getAvailableMigrations,
  getMigrationInfo,
};
