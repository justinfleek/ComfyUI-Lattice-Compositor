/**
 * JSON Validation and Data Hardening Service
 *
 * Provides safe JSON parsing, validation, and schema checking
 * for project files, MOGRTs, and external data imports.
 */

import type { WeylProject, Composition, Layer } from '@/types/project';
import type { TemplateConfig, MOGRTPackage } from '@/types/essentialGraphics';

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
// SCHEMA VALIDATION
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
 * Validate a Weyl project structure
 */
export function validateProject(data: unknown): ValidationResult {
  const errors: ValidationError[] = [];
  const warnings: string[] = [];

  if (!isObject(data)) {
    errors.push({ path: '$', message: 'Project must be an object' });
    return { valid: false, errors, warnings };
  }

  const project = data as Record<string, unknown>;

  // Required fields
  if (!isString(project.id)) {
    errors.push({ path: '$.id', message: 'Project ID must be a string' });
  }

  if (!isString(project.name)) {
    errors.push({ path: '$.name', message: 'Project name must be a string' });
  }

  if (!isObject(project.compositions)) {
    errors.push({ path: '$.compositions', message: 'Compositions must be an object' });
  } else {
    // Validate each composition
    const compositions = project.compositions as Record<string, unknown>;
    for (const [compId, comp] of Object.entries(compositions)) {
      const compResult = validateComposition(comp, `$.compositions.${compId}`);
      errors.push(...compResult.errors);
      warnings.push(...compResult.warnings);
    }
  }

  // Optional fields with type checking
  if (project.assets !== undefined && !isObject(project.assets)) {
    warnings.push('Project assets should be an object');
  }

  if (project.version !== undefined && !isString(project.version)) {
    warnings.push('Project version should be a string');
  }

  return { valid: errors.length === 0, errors, warnings };
}

/**
 * Validate a composition structure
 */
export function validateComposition(data: unknown, basePath: string = '$'): ValidationResult {
  const errors: ValidationError[] = [];
  const warnings: string[] = [];

  if (!isObject(data)) {
    errors.push({ path: basePath, message: 'Composition must be an object' });
    return { valid: false, errors, warnings };
  }

  const comp = data as Record<string, unknown>;

  // Required fields
  const requiredStrings = ['id', 'name'];
  for (const field of requiredStrings) {
    if (!isString(comp[field])) {
      errors.push({
        path: `${basePath}.${field}`,
        message: `${field} must be a string`,
        expected: 'string',
        received: typeof comp[field]
      });
    }
  }

  const requiredNumbers = ['width', 'height', 'frameRate', 'duration', 'frameCount'];
  for (const field of requiredNumbers) {
    if (!isNumber(comp[field])) {
      errors.push({
        path: `${basePath}.${field}`,
        message: `${field} must be a number`,
        expected: 'number',
        received: typeof comp[field]
      });
    } else {
      const value = comp[field] as number;
      if (value <= 0) {
        errors.push({
          path: `${basePath}.${field}`,
          message: `${field} must be positive`,
          expected: '> 0',
          received: String(value)
        });
      }
    }
  }

  // Layers array
  if (!isArray(comp.layers)) {
    errors.push({ path: `${basePath}.layers`, message: 'layers must be an array' });
  } else {
    const layers = comp.layers as unknown[];
    for (let i = 0; i < layers.length; i++) {
      const layerResult = validateLayer(layers[i], `${basePath}.layers[${i}]`);
      errors.push(...layerResult.errors);
      warnings.push(...layerResult.warnings);
    }
  }

  return { valid: errors.length === 0, errors, warnings };
}

/**
 * Validate a layer structure
 */
export function validateLayer(data: unknown, basePath: string = '$'): ValidationResult {
  const errors: ValidationError[] = [];
  const warnings: string[] = [];

  if (!isObject(data)) {
    errors.push({ path: basePath, message: 'Layer must be an object' });
    return { valid: false, errors, warnings };
  }

  const layer = data as Record<string, unknown>;

  // Required fields
  if (!isString(layer.id)) {
    errors.push({ path: `${basePath}.id`, message: 'Layer ID must be a string' });
  }

  if (!isString(layer.name)) {
    errors.push({ path: `${basePath}.name`, message: 'Layer name must be a string' });
  }

  if (!isString(layer.type)) {
    errors.push({ path: `${basePath}.type`, message: 'Layer type must be a string' });
  } else {
    const validTypes = [
      'image', 'video', 'solid', 'null', 'text', 'spline', 'shape',
      'particle', 'camera', 'light', 'precomp', 'adjustment', 'audio',
      'procedural_matte', 'model', 'point_cloud', 'depthflow',
      'depth', 'normal', 'generated', 'group', 'path', 'control', 'matte'
    ];
    if (!validTypes.includes(layer.type as string)) {
      warnings.push(`Unknown layer type "${layer.type}" at ${basePath}.type`);
    }
  }

  // Boolean fields
  if (layer.enabled !== undefined && !isBoolean(layer.enabled)) {
    errors.push({ path: `${basePath}.enabled`, message: 'enabled must be a boolean' });
  }

  // Transform validation
  if (layer.transform !== undefined) {
    if (!isObject(layer.transform)) {
      errors.push({ path: `${basePath}.transform`, message: 'transform must be an object' });
    }
  }

  return { valid: errors.length === 0, errors, warnings };
}

/**
 * Validate MOGRT package structure
 */
export function validateMOGRT(data: unknown): ValidationResult {
  const errors: ValidationError[] = [];
  const warnings: string[] = [];

  if (!isObject(data)) {
    errors.push({ path: '$', message: 'MOGRT must be an object' });
    return { valid: false, errors, warnings };
  }

  const mogrt = data as Record<string, unknown>;

  // Required fields
  if (!isString(mogrt.formatVersion)) {
    errors.push({ path: '$.formatVersion', message: 'formatVersion must be a string' });
  }

  if (!isObject(mogrt.templateConfig)) {
    errors.push({ path: '$.templateConfig', message: 'templateConfig must be an object' });
  } else {
    const configResult = validateTemplateConfig(mogrt.templateConfig);
    errors.push(...configResult.errors);
    warnings.push(...configResult.warnings);
  }

  if (!isObject(mogrt.composition)) {
    errors.push({ path: '$.composition', message: 'composition must be an object' });
  }

  if (!isArray(mogrt.assets)) {
    errors.push({ path: '$.assets', message: 'assets must be an array' });
  }

  if (!isArray(mogrt.fonts)) {
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
// DATA REPAIR
// ============================================================

/**
 * Attempt to repair common issues in project data
 */
export function repairProject(data: unknown): { repaired: boolean; data: unknown; fixes: string[] } {
  const fixes: string[] = [];
  let repaired = false;

  if (!isObject(data)) {
    return { repaired: false, data, fixes: ['Cannot repair: not an object'] };
  }

  const project = { ...data } as Record<string, unknown>;

  // Add missing ID
  if (!project.id) {
    project.id = `project_${Date.now()}`;
    fixes.push('Added missing project ID');
    repaired = true;
  }

  // Add missing name
  if (!project.name) {
    project.name = 'Untitled Project';
    fixes.push('Added missing project name');
    repaired = true;
  }

  // Initialize missing compositions
  if (!project.compositions) {
    project.compositions = {};
    fixes.push('Initialized missing compositions object');
    repaired = true;
  }

  // Initialize missing assets
  if (!project.assets) {
    project.assets = {};
    fixes.push('Initialized missing assets object');
    repaired = true;
  }

  // Repair compositions
  if (isObject(project.compositions)) {
    const compositions = project.compositions as Record<string, unknown>;
    for (const [compId, comp] of Object.entries(compositions)) {
      if (isObject(comp)) {
        const compObj = comp as Record<string, unknown>;

        // Fix missing composition ID
        if (!compObj.id) {
          compObj.id = compId;
          fixes.push(`Fixed missing ID for composition "${compObj.name || compId}"`);
          repaired = true;
        }

        // Initialize missing layers array
        if (!compObj.layers) {
          compObj.layers = [];
          fixes.push(`Initialized missing layers for composition "${compObj.name || compId}"`);
          repaired = true;
        }

        // Repair layers
        if (isArray(compObj.layers)) {
          const layers = compObj.layers as unknown[];
          for (let i = 0; i < layers.length; i++) {
            if (isObject(layers[i])) {
              const layer = layers[i] as Record<string, unknown>;

              // Fix missing layer ID
              if (!layer.id) {
                layer.id = `layer_${Date.now()}_${i}`;
                fixes.push(`Fixed missing ID for layer "${layer.name || i}"`);
                repaired = true;
              }

              // Fix missing enabled flag
              if (layer.enabled === undefined) {
                layer.enabled = true;
                fixes.push(`Fixed missing enabled flag for layer "${layer.name || layer.id}"`);
                repaired = true;
              }
            }
          }
        }
      }
    }
  }

  return { repaired, data: project, fixes };
}

// ============================================================
// EXPORTS
// ============================================================

export default {
  safeJSONParse,
  safeJSONStringify,
  validateProject,
  validateComposition,
  validateLayer,
  validateMOGRT,
  validateTemplateConfig,
  sanitizeString,
  sanitizeFileName,
  deepCloneSanitized,
  repairProject,
  isObject,
  isString,
  isNumber,
  isArray,
  isBoolean
};
