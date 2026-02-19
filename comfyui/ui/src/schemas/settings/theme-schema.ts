/**
 * Theme Schema
 *
 * Zod schemas for validating theme preferences stored in localStorage.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Theme Name Schema
// ═══════════════════════════════════════════════════════════════════════════

export const ThemeNameSchema = z.enum([
  "violet",
  "ocean",
  "sunset",
  "forest",
  "ember",
  "mono",
]);

export type ThemeName = z.infer<typeof ThemeNameSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Theme State Schema
// ═══════════════════════════════════════════════════════════════════════════

export const ThemeStateSchema = z.object({
  currentTheme: ThemeNameSchema,
}).strict();

export type ThemeState = z.infer<typeof ThemeStateSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ═══════════════════════════════════════════════════════════════════════════

export function validateThemeName(data: unknown): ThemeName {
  return ThemeNameSchema.parse(data);
}

export function safeValidateThemeName(data: unknown) {
  return ThemeNameSchema.safeParse(data);
}

export function validateThemeState(data: unknown): ThemeState {
  return ThemeStateSchema.parse(data);
}

export function safeValidateThemeState(data: unknown) {
  return ThemeStateSchema.safeParse(data);
}
