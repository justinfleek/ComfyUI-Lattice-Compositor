/**
 * Project Item Schema
 *
 * Zod schemas for validating drag-drop project items.
 * Used in TimelinePanel and ThreeCanvas drag-drop operations.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  entityId,
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ============================================================================
// Primitives
// ============================================================================

const positiveInt = z.number().int().positive();

// ============================================================================
// Project Item Type Schema
// ============================================================================

export const ProjectItemTypeSchema = z.enum([
  "composition",
  "footage",
  "solid",
  "audio",
  "folder",
]);

export type ProjectItemType = z.infer<typeof ProjectItemTypeSchema>;

// ============================================================================
// Project Item Schema
// ============================================================================

/**
 * Project item used in drag-drop operations
 */
export const ProjectItemSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: ProjectItemTypeSchema,
  width: positiveInt.max(16384).optional(), // Max 16k width
  height: positiveInt.max(16384).optional(), // Max 16k height
}).strict();

export type ProjectItem = z.infer<typeof ProjectItemSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateProjectItem(data: unknown): ProjectItem {
  return ProjectItemSchema.parse(data);
}

export function safeValidateProjectItem(data: unknown) {
  return ProjectItemSchema.safeParse(data);
}
