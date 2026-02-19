/**
 * Settings Schema Exports
 */

export {
  UserSettingsSchema,
  validateUserSettings,
  safeValidateUserSettings,
  type UserSettings,
} from "./user-settings-schema";

export {
  RecentProjectSchema,
  RecentProjectsSchema,
  validateRecentProject,
  safeValidateRecentProject,
  validateRecentProjects,
  safeValidateRecentProjects,
  type RecentProject,
  type RecentProjects,
} from "./recent-projects-schema";

export {
  ExportTemplateSchema,
  ExportTemplateStoreSchema,
  ExportTemplateArraySchema,
  validateExportTemplate,
  safeValidateExportTemplate,
  validateExportTemplateStore,
  safeValidateExportTemplateStore,
  validateExportTemplateArray,
  safeValidateExportTemplateArray,
  type ExportTemplate,
  type ExportTemplateStore,
  type ExportTemplateArray,
} from "./export-template-schema";

export {
  RateLimitConfigSchema,
  RateLimitStatusSchema,
  StoredRateLimitsSchema,
  validateStoredRateLimits,
  safeValidateStoredRateLimits,
  type RateLimitConfig,
  type RateLimitStatus,
  type StoredRateLimits,
} from "./rate-limits-schema";

export {
  ParticlePreferencesSchema,
  RenderingBackendSchema,
  SimulationModeSchema,
  validateParticlePreferences,
  safeValidateParticlePreferences,
  type ParticlePreferences,
  type RenderingBackend,
  type SimulationMode,
} from "./particle-preferences-schema";

export {
  ThemeNameSchema,
  ThemeStateSchema,
  validateThemeName,
  safeValidateThemeName,
  validateThemeState,
  safeValidateThemeState,
  type ThemeName,
  type ThemeState,
} from "./theme-schema";

export {
  ValidationLimitsSchema,
  validateValidationLimits,
  safeValidateValidationLimits,
  type ValidationLimits,
} from "./validation-limits-schema";

export {
  SessionCountsSchema,
  AuditSessionIdSchema,
  validateSessionCounts,
  safeValidateSessionCounts,
  validateAuditSessionId,
  safeValidateAuditSessionId,
  type SessionCounts,
  type AuditSessionId,
} from "./session-storage-schema";
