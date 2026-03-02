/**
 * Shared Validation Constants and Helpers
 *
 * Common validation constraints used across all schemas.
 * Ensures consistency and prevents security issues.
 * Uses configurable limits from validationLimitsStore for power users.
 *
 * NOTE: Limits are read at schema creation time. To use updated limits,
 * schemas should be recreated or use the getter functions in refinements.
 */

import { z } from "zod";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Validation Constants (Fixed - Security Critical)
// ════════════════════════════════════════════════════════════════════════════

export const MAX_NAME_LENGTH = 200;
export const MAX_DESCRIPTION_LENGTH = 2000;
export const MAX_COMMENT_LENGTH = 5000;
export const MAX_TAG_LENGTH = 50;
export const MAX_TAGS_COUNT = 50;
export const MAX_PATH_LENGTH = 500;
export const MAX_ID_LENGTH = 200;
export const MAX_MIME_TYPE_LENGTH = 100;
export const MAX_FONT_FAMILY_LENGTH = 200;
export const MAX_FONT_STYLE_LENGTH = 100;
export const MAX_URL_LENGTH = 2048;
export const MAX_BASE64_LENGTH = 50 * 1024 * 1024; // 50MB max base64 data (security limit)
export const MAX_SHADER_LENGTH = 100000; // Max shader code length
export const MAX_FILENAME_LENGTH = 255;
export const MAX_ANIMATION_NAME_LENGTH = 100;
export const MAX_WARNING_LENGTH = 500;

// ════════════════════════════════════════════════════════════════════════════
// Configurable Limits (Default values - updated from store at runtime)
// ════════════════════════════════════════════════════════════════════════════

// Default values matching existing codebase constants
// These will be updated from validationLimitsStore when it loads
let _maxDimension = 8192;
let _maxFrameCount = 10000;
let _maxArrayLength = 100000;
let _maxParticles = 1000000;
let _maxLayers = 1000;
let _maxKeyframesPerProperty = 10000;
let _maxStringLength = 100000;
let _maxFPS = 120;

/**
 * Update limits (called from validationLimitsStore)
 */
export function updateLimits(limits: {
  maxDimension: number;
  maxFrameCount: number;
  maxArrayLength: number;
  maxParticles: number;
  maxLayers: number;
  maxKeyframesPerProperty: number;
  maxStringLength: number;
  maxFPS: number;
}): void {
  _maxDimension = limits.maxDimension;
  _maxFrameCount = limits.maxFrameCount;
  _maxArrayLength = limits.maxArrayLength;
  _maxParticles = limits.maxParticles;
  _maxLayers = limits.maxLayers;
  _maxKeyframesPerProperty = limits.maxKeyframesPerProperty;
  _maxStringLength = limits.maxStringLength;
  _maxFPS = limits.maxFPS;
}

/**
 * Initialize limits from store (call this after store is available)
 */
export function initializeLimits(): void {
  try {
    // Dynamic import to avoid circular dependency
    import("../stores/validationLimitsStore").then((module) => {
      const store = module.useValidationLimitsStore();
      const limits = store.getLimits();
      updateLimits({
        maxDimension: limits.maxDimension,
        maxFrameCount: limits.maxFrameCount,
        maxArrayLength: limits.maxArrayLength,
        maxParticles: limits.maxParticles,
        maxLayers: limits.maxLayers,
        maxKeyframesPerProperty: limits.maxKeyframesPerProperty,
        maxStringLength: limits.maxStringLength,
        maxFPS: limits.maxFPS,
      });
    });
  } catch (e) {
    console.warn("Failed to initialize validation limits:", e);
  }
}

/**
 * Get current max dimension
 */
export function getMaxDimension(): number {
  return _maxDimension;
}

/**
 * Get current max frame count
 */
export function getMaxFrameCount(): number {
  return _maxFrameCount;
}

/**
 * Get current max array length
 */
export function getMaxArrayLength(): number {
  return _maxArrayLength;
}

/**
 * Get current max particles
 */
export function getMaxParticles(): number {
  return _maxParticles;
}

/**
 * Get current max layers
 */
export function getMaxLayers(): number {
  return _maxLayers;
}

/**
 * Get current max keyframes per property
 */
export function getMaxKeyframesPerProperty(): number {
  return _maxKeyframesPerProperty;
}

/**
 * Get current max string length
 */
export function getMaxStringLength(): number {
  return _maxStringLength;
}

/**
 * Get current max FPS
 */
export function getMaxFPS(): number {
  return _maxFPS;
}

// Legacy exports for backward compatibility (use current values)
export const MAX_STRING_LENGTH = _maxStringLength;
export const MAX_ARRAY_LENGTH = _maxArrayLength;

// ════════════════════════════════════════════════════════════════════════════
// Helper Schema Factories
// ════════════════════════════════════════════════════════════════════════════

/** Non-empty string with max length and trimming */
export const nonEmptyString = (maxLength: number) =>
  z.string().min(1).max(maxLength).trim();

/** ISO 8601 datetime string */
export const iso8601DateTime = z.string().datetime();

/** Base64 or data URL string */
export const base64OrDataUrl = z.string().refine(
  (val) => {
    if (val.length > MAX_BASE64_LENGTH) return false;
    // Data URL format: data:[<mediatype>][;base64],<data>
    if (val.startsWith("data:")) {
      const commaIndex = val.indexOf(",");
      if (commaIndex === -1) return false;
      const header = val.substring(0, commaIndex);
      const data = val.substring(commaIndex + 1);
      return header.includes("base64") || data.length > 0;
    }
    // Base64 format: only base64 characters
    return /^[A-Za-z0-9+/=]+$/.test(val);
  },
  { message: "Must be valid base64 or data URL" }
);

/** Valid MIME type */
export const mimeType = z.string()
  .max(MAX_MIME_TYPE_LENGTH)
  .refine(
    (val) => /^[a-z][a-z0-9]*\/[a-z0-9][a-z0-9._-]*$/i.test(val),
    { message: "Must be valid MIME type (e.g., 'image/png', 'video/mp4')" }
  );

/** Hex color string (#RRGGBB or #RRGGBBAA) */
export const hexColor = z.string().regex(
  /^#([0-9A-Fa-f]{6}|[0-9A-Fa-f]{8})$/,
  { message: "Must be valid hex color (#RRGGBB or #RRGGBBAA)" }
);

/** Entity ID format - alphanumeric with underscores/hyphens */
export const entityId = z.string()
  .min(1)
  .max(MAX_ID_LENGTH)
  .regex(
    /^[a-zA-Z0-9_-]+$/,
    { message: "Must be valid ID format (alphanumeric, underscores, hyphens only)" }
  );

/** Property path (e.g., "data.text", "transform.position.x") */
export const propertyPath = z.string()
  .max(MAX_PATH_LENGTH)
  .regex(
    /^[a-zA-Z_$][a-zA-Z0-9_$.]*(\.[a-zA-Z_$][a-zA-Z0-9_$.]*)*$/,
    { message: "Must be valid property path (e.g., 'data.text', 'transform.position.x')" }
  );

/** Filename validation */
export const filename = z.string()
  .max(MAX_FILENAME_LENGTH)
  .refine(
    (val) => !/[<>:"|?*\x00-\x1F]/.test(val) && !val.endsWith(".") && !val.endsWith(" "),
    { message: "Must be valid filename (no invalid characters, no trailing dot/space)" }
  );

/** URL validation */
export const url = z.string()
  .max(MAX_URL_LENGTH)
  .url({ message: "Must be valid URL" });

/** Shader code validation */
export const shaderCode = z.string()
  .max(MAX_SHADER_LENGTH)
  .refine(
    (val) => {
      // Basic validation - check for dangerous patterns
      const dangerousPatterns = [
        /\beval\s*\(/,
        /\bFunction\s*\(/,
        /\brequire\s*\(/,
        /\bimport\s*\(/,
        /\bprocess\./,
        /\bfetch\s*\(/,
        /\bXMLHttpRequest\b/,
        /\bWebSocket\b/,
        /\bdocument\./,
        /\bwindow\./,
      ];
      return !dangerousPatterns.some((pattern) => pattern.test(val));
    },
    { message: "Shader code contains potentially dangerous patterns" }
  );

/** Array with max length (uses configurable limit) */
// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
export const boundedArray = <T extends z.ZodTypeAny>(schema: T, maxLength?: number) => {
  const limit = (maxLength !== null && maxLength !== undefined && typeof maxLength === "number" && Number.isFinite(maxLength) && maxLength > 0) ? maxLength : _maxArrayLength;
  return z.array(schema).max(limit);
};

/** Non-empty array */
export const nonEmptyArray = <T extends z.ZodTypeAny>(schema: T) =>
  z.array(schema).min(1);

/**
 * JSON-serializable value schema
 * Validates that a value is JSON-serializable (string, number, boolean, null, object, array)
 * Uses recursive validation to ensure nested structures are also JSON-serializable
 */
export const jsonSerializable: z.ZodTypeAny = z.lazy(() =>
  z.union([
    z.string().max(MAX_STRING_LENGTH),
    z.number().finite(),
    z.boolean(),
    z.null(),
    z.array(jsonSerializable).max(_maxArrayLength),
    z.record(z.string().max(MAX_NAME_LENGTH), jsonSerializable).refine(
      (obj) => Object.keys(obj).length <= 10000,
      { message: "Maximum 10000 keys in JSON object" }
    ),
  ])
).refine(
  (data) => {
    try {
      JSON.stringify(data);
      return true;
    } catch {
      return false;
    }
  },
  { message: "Value must be JSON-serializable" }
);

// Type export for jsonSerializable
export type JsonSerializable = z.infer<typeof jsonSerializable>;
