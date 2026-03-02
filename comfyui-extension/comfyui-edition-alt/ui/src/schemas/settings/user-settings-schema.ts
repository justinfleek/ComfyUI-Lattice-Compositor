/**
 * User Settings Schema
 *
 * Zod schemas for validating user settings stored in localStorage.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  MAX_NAME_LENGTH,
  MAX_PATH_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitives
// ════════════════════════════════════════════════════════════════════════════

const positiveInt = z.number().int().positive();
const nonNegativeInt = z.number().int().nonnegative();

// ════════════════════════════════════════════════════════════════════════════
// User Settings Schema
// ════════════════════════════════════════════════════════════════════════════

export const UserSettingsSchema = z.object({
  theme: z.enum(["dark", "light", "system"]),
  autosaveEnabled: z.boolean(),
  autosaveIntervalMs: nonNegativeInt.max(3600000), // Max 1 hour (3.6M ms)
  aiModel: z.enum(["gpt-4o", "claude-sonnet"]),
  showWelcome: z.boolean(),
  canvasBackground: z.string().max(MAX_NAME_LENGTH).trim(), // Hex color or preset name
  timelineHeight: positiveInt.max(1000), // Max 1000px timeline height
  panelLayout: z.enum(["default", "compact", "expanded"]),
  recentProjectsMax: positiveInt.max(100), // Max 100 recent projects
  keyboardShortcutsEnabled: z.boolean(),
}).strict();

export type UserSettings = z.infer<typeof UserSettingsSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ════════════════════════════════════════════════════════════════════════════

export function validateUserSettings(data: unknown): UserSettings {
  return UserSettingsSchema.parse(data);
}

export function safeValidateUserSettings(data: unknown) {
  return UserSettingsSchema.safeParse(data);
}
