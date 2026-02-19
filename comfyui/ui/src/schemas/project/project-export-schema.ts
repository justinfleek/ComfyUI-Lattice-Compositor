/**
 * Project Export Schema
 *
 * Zod schemas for validating project data for import/export operations.
 * Used by persistenceService.importData() for bulk project imports.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  entityId,
  jsonSerializable,
  MAX_NAME_LENGTH,
} from "../shared-validation";
import { LatticeProjectSchema } from "../project-schema";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitives
// ═══════════════════════════════════════════════════════════════════════════

const nonNegativeInt = z.number().int().nonnegative();
const positiveInt = z.number().int().positive();

// ═══════════════════════════════════════════════════════════════════════════
// Stored Project Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Stored Project
 * Project with metadata for storage/export
 */
export const StoredProjectSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  data: LatticeProjectSchema,
  thumbnail: z.string().max(10 * 1024 * 1024).optional(), // Max 10MB base64 thumbnail
  createdAt: nonNegativeInt.max(2147483647000), // Max timestamp (year 2038)
  modifiedAt: nonNegativeInt.max(2147483647000), // Max timestamp (year 2038)
  version: positiveInt.max(1000), // Max version 1000
}).strict().refine(
  (data) => {
    // modifiedAt should be >= createdAt
    return data.modifiedAt >= data.createdAt;
  },
  { message: "modifiedAt must be >= createdAt", path: ["modifiedAt"] }
);

export type StoredProject = z.infer<typeof StoredProjectSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Project Export Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Project Export Format
 * Used by importData() for bulk project imports
 * Contains array of projects and optional settings
 */
export const ProjectExportSchema = z.object({
  projects: z.array(StoredProjectSchema).max(1000), // Max 1000 projects in export
  settings: jsonSerializable.optional(), // UserSettings (JSON-serializable, validated separately in UI store)
}).strict();

export type ProjectExport = z.infer<typeof ProjectExportSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ═══════════════════════════════════════════════════════════════════════════

export function validateStoredProject(data: unknown): StoredProject {
  return StoredProjectSchema.parse(data);
}

export function safeValidateStoredProject(data: unknown) {
  return StoredProjectSchema.safeParse(data);
}

export function validateProjectExport(data: unknown): ProjectExport {
  return ProjectExportSchema.parse(data);
}

export function safeValidateProjectExport(data: unknown) {
  return ProjectExportSchema.safeParse(data);
}
