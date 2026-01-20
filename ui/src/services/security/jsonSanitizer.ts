/**
 * JSON Sanitizer
 *
 * Security module for validating and sanitizing JSON data before processing.
 * Prevents JSON bombs, prototype pollution, and resource exhaustion attacks.
 *
 * ENTERPRISE SECURITY: This is a critical security control for ensuring Enterprise readiness.
 */

/**
 * Type representing all valid JSON values (recursive)
 */
type JSONValue =
  | string
  | number
  | boolean
  | null
  | JSONValue[]
  | { [key: string]: JSONValue };

/**
 * Type guard for JSON objects
 */
function isJSONObject(value: unknown): value is { [key: string]: JSONValue } {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

export interface JSONSanitizeOptions {
  /** Maximum nesting depth (default: 50) */
  maxDepth?: number;
  /** Maximum array length (default: 100,000) */
  maxArrayLength?: number;
  /** Maximum string length in bytes (default: 10MB) */
  maxStringLength?: number;
  /** Maximum total keys across all objects (default: 1,000,000) */
  maxTotalKeys?: number;
  /** Maximum object key length (default: 1000) */
  maxKeyLength?: number;
  /** Remove __proto__ and constructor keys (default: true) */
  removePrototypeKeys?: boolean;
  /** Remove null byte characters from strings (default: true) */
  removeNullBytes?: boolean;
}

export interface JSONSanitizeResult {
  valid: boolean;
  data: unknown;
  error?: string;
  warnings: string[];
  stats: {
    depth: number;
    totalKeys: number;
    totalArrayElements: number;
    maxStringLength: number;
    prototypeKeysRemoved: number;
  };
}

const DEFAULT_OPTIONS: Required<JSONSanitizeOptions> = {
  maxDepth: 50,
  maxArrayLength: 100_000,
  maxStringLength: 10 * 1024 * 1024, // 10MB
  maxTotalKeys: 1_000_000,
  maxKeyLength: 1000,
  removePrototypeKeys: true,
  removeNullBytes: true,
};

/**
 * Dangerous keys that could enable prototype pollution
 */
const PROTOTYPE_KEYS = new Set([
  "__proto__",
  "constructor",
  "prototype",
  "__defineGetter__",
  "__defineSetter__",
  "__lookupGetter__",
  "__lookupSetter__",
]);

/**
 * Parse and sanitize JSON string
 *
 * @param jsonString - Raw JSON string to parse
 * @param options - Sanitization options
 * @returns Sanitization result with validated data
 */
export function parseAndSanitize(
  jsonString: string,
  options: JSONSanitizeOptions = {},
): JSONSanitizeResult {
  const opts = { ...DEFAULT_OPTIONS, ...options };
  const warnings: string[] = [];
  const stats = {
    depth: 0,
    totalKeys: 0,
    totalArrayElements: 0,
    maxStringLength: 0,
    prototypeKeysRemoved: 0,
  };

  // Input validation
  if (typeof jsonString !== "string") {
    return {
      valid: false,
      data: null,
      error: "Input must be a string",
      warnings,
      stats,
    };
  }

  // Length check before parsing (prevent DoS)
  if (jsonString.length > opts.maxStringLength * 2) {
    return {
      valid: false,
      data: null,
      error: `JSON string too large: ${jsonString.length} bytes (max: ${opts.maxStringLength * 2})`,
      warnings,
      stats,
    };
  }

  // Parse JSON
  let parsed: unknown;
  try {
    parsed = JSON.parse(jsonString);
  } catch (e) {
    return {
      valid: false,
      data: null,
      error: `Invalid JSON: ${e instanceof Error ? e.message : "Parse error"}`,
      warnings,
      stats,
    };
  }

  // Sanitize the parsed data
  try {
    const sanitized = sanitizeValue(parsed, opts, stats, warnings, 0);
    return {
      valid: true,
      data: sanitized,
      warnings,
      stats,
    };
  } catch (e) {
    return {
      valid: false,
      data: null,
      error: e instanceof Error ? e.message : "Sanitization error",
      warnings,
      stats,
    };
  }
}

/**
 * Sanitize already-parsed JSON data
 *
 * @param data - Parsed JSON data
 * @param options - Sanitization options
 * @returns Sanitization result
 */
export function sanitize(
  data: unknown,
  options: JSONSanitizeOptions = {},
): JSONSanitizeResult {
  const opts = { ...DEFAULT_OPTIONS, ...options };
  const warnings: string[] = [];
  const stats = {
    depth: 0,
    totalKeys: 0,
    totalArrayElements: 0,
    maxStringLength: 0,
    prototypeKeysRemoved: 0,
  };

  try {
    const sanitized = sanitizeValue(data, opts, stats, warnings, 0);
    return {
      valid: true,
      data: sanitized,
      warnings,
      stats,
    };
  } catch (e) {
    return {
      valid: false,
      data: null,
      error: e instanceof Error ? e.message : "Sanitization error",
      warnings,
      stats,
    };
  }
}

/**
 * Recursively sanitize a value
 */
function sanitizeValue(
  value: unknown,
  opts: Required<JSONSanitizeOptions>,
  stats: JSONSanitizeResult["stats"],
  warnings: string[],
  depth: number,
): unknown {
  // Track max depth
  if (depth > stats.depth) {
    stats.depth = depth;
  }

  // Depth limit check
  if (depth > opts.maxDepth) {
    throw new Error(`Maximum nesting depth exceeded: ${opts.maxDepth} levels`);
  }

  // Null
  if (value === null) {
    return null;
  }

  // Undefined (shouldn't be in JSON, but handle it)
  if (value === undefined) {
    return undefined;
  }

  // Primitives
  const type = typeof value;

  if (type === "boolean" || type === "number") {
    // Check for NaN/Infinity (not valid JSON but could slip through)
    if (type === "number" && !Number.isFinite(value as number)) {
      warnings.push(`Non-finite number replaced with null: ${value}`);
      return null;
    }
    return value;
  }

  if (type === "string") {
    return sanitizeString(value as string, opts, stats, warnings);
  }

  // Array
  if (Array.isArray(value)) {
    return sanitizeArray(value, opts, stats, warnings, depth);
  }

  // Object
  if (type === "object") {
    return sanitizeObject(
      value as { [key: string]: JSONValue },
      opts,
      stats,
      warnings,
      depth,
    );
  }

  // Functions, symbols, etc. - remove
  warnings.push(`Unsupported type removed: ${type}`);
  return null;
}

/**
 * Sanitize a string value
 */
function sanitizeString(
  str: string,
  opts: Required<JSONSanitizeOptions>,
  stats: JSONSanitizeResult["stats"],
  warnings: string[],
): string {
  // Length check
  if (str.length > opts.maxStringLength) {
    throw new Error(
      `String exceeds maximum length: ${str.length} bytes (max: ${opts.maxStringLength})`,
    );
  }

  // Track max string length
  if (str.length > stats.maxStringLength) {
    stats.maxStringLength = str.length;
  }

  // Remove null bytes if configured
  if (opts.removeNullBytes && str.includes("\0")) {
    warnings.push("Null bytes removed from string");
    return str.replace(/\0/g, "");
  }

  return str;
}

/**
 * Sanitize an array
 */
function sanitizeArray(
  arr: unknown[],
  opts: Required<JSONSanitizeOptions>,
  stats: JSONSanitizeResult["stats"],
  warnings: string[],
  depth: number,
): unknown[] {
  // Length check
  if (arr.length > opts.maxArrayLength) {
    throw new Error(
      `Array exceeds maximum length: ${arr.length} elements (max: ${opts.maxArrayLength})`,
    );
  }

  stats.totalArrayElements += arr.length;

  // Check cumulative elements (prevent many small arrays)
  if (stats.totalArrayElements > opts.maxArrayLength * 10) {
    throw new Error(
      `Total array elements exceed limit: ${stats.totalArrayElements}`,
    );
  }

  // Sanitize each element
  const result: unknown[] = [];
  for (let i = 0; i < arr.length; i++) {
    result.push(sanitizeValue(arr[i], opts, stats, warnings, depth + 1));
  }

  return result;
}

/**
 * Sanitize an object
 */
function sanitizeObject(
  obj: { [key: string]: JSONValue },
  opts: Required<JSONSanitizeOptions>,
  stats: JSONSanitizeResult["stats"],
  warnings: string[],
  depth: number,
): { [key: string]: JSONValue } {
  const keys = Object.keys(obj);

  // Key count check
  stats.totalKeys += keys.length;
  if (stats.totalKeys > opts.maxTotalKeys) {
    throw new Error(
      `Total object keys exceed limit: ${stats.totalKeys} (max: ${opts.maxTotalKeys})`,
    );
  }

  const result: { [key: string]: JSONValue } = {};

  for (const key of keys) {
    // Key length check
    if (key.length > opts.maxKeyLength) {
      warnings.push(
        `Key truncated: ${key.slice(0, 50)}... (exceeded ${opts.maxKeyLength} chars)`,
      );
      continue; // Skip this key entirely
    }

    // Prototype pollution check
    if (opts.removePrototypeKeys && PROTOTYPE_KEYS.has(key)) {
      stats.prototypeKeysRemoved++;
      warnings.push(`Prototype pollution key removed: ${key}`);
      continue;
    }

    // Also check for prototype keys with different casing
    if (opts.removePrototypeKeys && PROTOTYPE_KEYS.has(key.toLowerCase())) {
      stats.prototypeKeysRemoved++;
      warnings.push(`Prototype pollution key removed (case variant): ${key}`);
      continue;
    }

    // Sanitize the value
    result[key] = sanitizeValue(obj[key], opts, stats, warnings, depth + 1);
  }

  return result;
}

/**
 * Quick validation without full sanitization
 * Use for fast rejection of obviously malicious input
 */
export function quickValidate(
  jsonString: string,
  options: JSONSanitizeOptions = {},
): boolean {
  const opts = { ...DEFAULT_OPTIONS, ...options };

  // Length check
  if (jsonString.length > opts.maxStringLength * 2) {
    return false;
  }

  // Quick depth check via bracket counting
  let maxBracketDepth = 0;
  let currentDepth = 0;
  for (const char of jsonString) {
    if (char === "{" || char === "[") {
      currentDepth++;
      if (currentDepth > maxBracketDepth) {
        maxBracketDepth = currentDepth;
      }
      if (currentDepth > opts.maxDepth) {
        return false;
      }
    } else if (char === "}" || char === "]") {
      currentDepth--;
    }
  }

  // Quick prototype pollution check
  if (opts.removePrototypeKeys) {
    const protoPattern = /"(__proto__|constructor|prototype)"\s*:/i;
    if (protoPattern.test(jsonString)) {
      return false;
    }
  }

  return true;
}

/**
 * Safe JSON.parse with size limits
 * Throws on invalid or oversized input
 */
export function safeParse<T = unknown>(
  jsonString: string,
  options: JSONSanitizeOptions = {},
): T {
  const result = parseAndSanitize(jsonString, options);
  if (!result.valid) {
    throw new Error(result.error || "JSON validation failed");
  }
  return result.data as T;
}

/**
 * Deep freeze an object to prevent modification
 * Use after sanitization for additional safety
 */
export function deepFreeze<T>(obj: T): T {
  if (obj === null || typeof obj !== "object") {
    return obj;
  }

  Object.freeze(obj);

  if (Array.isArray(obj)) {
    for (const item of obj) {
      deepFreeze(item);
    }
  } else {
    for (const value of Object.values(obj)) {
      deepFreeze(value);
    }
  }

  return obj;
}
