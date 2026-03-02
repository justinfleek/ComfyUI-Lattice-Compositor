/**
 * Recent Projects Schema
 *
 * Zod schemas for validating recent projects list stored in localStorage.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  entityId,
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitives
// ════════════════════════════════════════════════════════════════════════════

const nonNegativeInt = z.number().int().nonnegative();

// ════════════════════════════════════════════════════════════════════════════
// Recent Project Schema
// ════════════════════════════════════════════════════════════════════════════

export const RecentProjectSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  thumbnail: z.string().max(10 * 1024 * 1024).optional(), // Max 10MB base64 thumbnail
  modifiedAt: nonNegativeInt.max(2147483647000), // Max timestamp (year 2038)
}).strict();

export type RecentProject = z.infer<typeof RecentProjectSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Recent Projects Array Schema
// ════════════════════════════════════════════════════════════════════════════

export const RecentProjectsSchema = z.array(RecentProjectSchema).max(100); // Max 100 recent projects

export type RecentProjects = z.infer<typeof RecentProjectsSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ════════════════════════════════════════════════════════════════════════════

export function validateRecentProject(data: unknown): RecentProject {
  return RecentProjectSchema.parse(data);
}

export function safeValidateRecentProject(data: unknown) {
  return RecentProjectSchema.safeParse(data);
}

export function validateRecentProjects(data: unknown): RecentProjects {
  return RecentProjectsSchema.parse(data);
}

export function safeValidateRecentProjects(data: unknown) {
  return RecentProjectsSchema.safeParse(data);
}
