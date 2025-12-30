/**
 * JSON Validation and Data Hardening Service
 *
 * Provides safe JSON parsing and type guards
 * for project files, templates, and external data imports.
 */

// ============================================================
// SAFE JSON PARSING
// ============================================================

/**
 * Safely parse JSON with error handling
 */
export function safeJSONParse<T>(
  jsonString: string,
  fallback: T | null = null
): { success: true; data: T } | { success: false; error: string; data: typeof fallback } {
  try {
    const data = JSON.parse(jsonString);
    return { success: true, data };
  } catch (e) {
    const error = e instanceof Error ? e.message : 'Unknown parse error';
    console.error('[JSONValidation] Parse error:', error);
    return { success: false, error, data: fallback };
  }
}

/**
 * Safely stringify JSON with circular reference handling
 */
export function safeJSONStringify(
  data: any,
  indent: number = 2
): { success: true; json: string } | { success: false; error: string } {
  try {
    const seen = new WeakSet();
    const json = JSON.stringify(data, (key, value) => {
      if (typeof value === 'object' && value !== null) {
        if (seen.has(value)) {
          return '[Circular Reference]';
        }
        seen.add(value);
      }
      return value;
    }, indent);
    return { success: true, json };
  } catch (e) {
    const error = e instanceof Error ? e.message : 'Unknown stringify error';
    console.error('[JSONValidation] Stringify error:', error);
    return { success: false, error };
  }
}

// ============================================================
// TYPE GUARDS
// ============================================================

/**
 * Check if value is a non-null object
 */
export function isObject(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

/**
 * Check if value is a valid string
 */
export function isString(value: unknown): value is string {
  return typeof value === 'string';
}

/**
 * Check if value is a valid number (not NaN)
 */
export function isNumber(value: unknown): value is number {
  return typeof value === 'number' && !isNaN(value);
}

/**
 * Check if value is a valid array
 */
export function isArray(value: unknown): value is unknown[] {
  return Array.isArray(value);
}

/**
 * Check if value is a valid boolean
 */
export function isBoolean(value: unknown): value is boolean {
  return typeof value === 'boolean';
}

// ============================================================
// TEMPLATE VALIDATION
// ============================================================

export interface ValidationError {
  path: string;
  message: string;
  expected?: string;
  received?: string;
}

export interface ValidationResult {
  valid: boolean;
  errors: ValidationError[];
  warnings: string[];
}

/**
 * Validate Lattice Template structure (.lattice.json)
 */
export function validateLatticeTemplate(data: unknown): ValidationResult {
  const errors: ValidationError[] = [];
  const warnings: string[] = [];

  if (!isObject(data)) {
    errors.push({ path: '$', message: 'LatticeTemplate must be an object' });
    return { valid: false, errors, warnings };
  }

  const template = data as Record<string, unknown>;

  // Required fields
  if (!isString(template.formatVersion)) {
    errors.push({ path: '$.formatVersion', message: 'formatVersion must be a string' });
  }

  if (!isObject(template.templateConfig)) {
    errors.push({ path: '$.templateConfig', message: 'templateConfig must be an object' });
  } else {
    const configResult = validateTemplateConfig(template.templateConfig);
    errors.push(...configResult.errors);
    warnings.push(...configResult.warnings);
  }

  if (!isObject(template.composition)) {
    errors.push({ path: '$.composition', message: 'composition must be an object' });
  }

  if (!isArray(template.assets)) {
    errors.push({ path: '$.assets', message: 'assets must be an array' });
  }

  if (!isArray(template.fonts)) {
    errors.push({ path: '$.fonts', message: 'fonts must be an array' });
  }

  return { valid: errors.length === 0, errors, warnings };
}

/**
 * Validate template configuration
 */
export function validateTemplateConfig(data: unknown): ValidationResult {
  const errors: ValidationError[] = [];
  const warnings: string[] = [];

  if (!isObject(data)) {
    errors.push({ path: '$', message: 'TemplateConfig must be an object' });
    return { valid: false, errors, warnings };
  }

  const config = data as Record<string, unknown>;

  if (!isString(config.name) || (config.name as string).trim() === '') {
    errors.push({ path: '$.name', message: 'Template name is required' });
  }

  if (!isString(config.masterCompositionId)) {
    errors.push({ path: '$.masterCompositionId', message: 'masterCompositionId must be a string' });
  }

  if (!isArray(config.exposedProperties)) {
    errors.push({ path: '$.exposedProperties', message: 'exposedProperties must be an array' });
  }

  if (!isArray(config.groups)) {
    errors.push({ path: '$.groups', message: 'groups must be an array' });
  }

  return { valid: errors.length === 0, errors, warnings };
}

// ============================================================
// SANITIZATION
// ============================================================

/**
 * Sanitize a string to prevent XSS
 */
export function sanitizeString(str: string): string {
  return str
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#x27;');
}

/**
 * Sanitize file name for safe storage
 */
export function sanitizeFileName(name: string): string {
  return name
    .replace(/[<>:"/\\|?*]/g, '_')
    .replace(/\s+/g, '_')
    .replace(/_{2,}/g, '_')
    .substring(0, 200); // Limit length
}

/**
 * Deep clone with sanitization
 */
export function deepCloneSanitized<T>(obj: T): T {
  const result = safeJSONStringify(obj);
  if (!result.success) {
    throw new Error(`Failed to clone: ${result.error}`);
  }

  const parsed = safeJSONParse<T>(result.json);
  if (!parsed.success) {
    throw new Error(`Failed to parse clone: ${parsed.error}`);
  }

  return parsed.data;
}

// ============================================================
// EXPORTS
// ============================================================

export default {
  safeJSONParse,
  safeJSONStringify,
  sanitizeString,
  sanitizeFileName,
  deepCloneSanitized,
  isObject,
  isString,
  isNumber,
  isArray,
  isBoolean,
  validateLatticeTemplate,
  validateTemplateConfig
};
