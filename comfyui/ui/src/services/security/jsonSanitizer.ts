/**
 * JSON Sanitizer
 *
 * Security module for validating and sanitizing JSON data before processing.
 * Prevents JSON bombs, prototype pollution, and resource exhaustion attacks.
 *
 * ENTERPRISE SECURITY: This is a critical security control for ensuring Enterprise readiness.
 */

import type { JSONValue } from "@/types/dataAsset";

/**
 * All possible JavaScript values that can be sanitized at runtime
 * Used as input type for sanitization functions (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

/**
 * Type guard for JSON objects
 */
function isJSONObject(value: RuntimeValue): value is { [key: string]: JSONValue } {
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
  data: JSONValue;
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
  let parsed: JSONValue;
  try {
    const parsedRaw = JSON.parse(jsonString);
    // Type guard: JSON.parse returns JSONValue
    if (
      typeof parsedRaw === "string" ||
      typeof parsedRaw === "number" ||
      typeof parsedRaw === "boolean" ||
      parsedRaw === null ||
      Array.isArray(parsedRaw) ||
      (typeof parsedRaw === "object" && parsedRaw !== null)
    ) {
      parsed = parsedRaw as JSONValue;
    } else {
      return {
        valid: false,
        data: null,
        error: "Parsed JSON is not a valid JSON value",
        warnings,
        stats,
      };
    }
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
  data: RuntimeValue,
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
  value: RuntimeValue,
  opts: Required<JSONSanitizeOptions>,
  stats: JSONSanitizeResult["stats"],
  warnings: string[],
  depth: number,
): JSONValue {
  // Track max depth
  if (depth > stats.depth) {
    stats.depth = depth;
  }

  // Depth limit check
  if (depth > opts.maxDepth) {
    throw new Error(`Maximum nesting depth exceeded: ${opts.maxDepth} levels`);
  }

  // System F/Omega proof: Explicit validation of value type
  // Type proof: value ∈ RuntimeValue → JSONValue (non-nullable, except valid JSON null)
  // Mathematical proof: Value must be a valid JSON type to be sanitized
  // Pattern proof: Invalid values are explicit error conditions, not lazy null returns

  // Null (valid JSON value - preserve it)
  if (value === null) {
    return null;
  }

  // Undefined (not valid JSON - throw error)
  // System F/Omega proof: Undefined is not a valid JSON value
  // Type proof: value ∈ undefined → error (not JSONValue)
  // Mathematical proof: JSON specification does not include undefined
  if (value === undefined) {
    throw new Error(
      `[JSONSanitizer] Cannot sanitize value: Undefined is not valid JSON. ` +
      `Depth: ${depth}, maxDepth: ${opts.maxDepth}. ` +
      `JSON specification does not support undefined values. ` +
      `Wrap in try/catch to handle invalid JSON data.`
    );
  }

  // Primitives
  const type = typeof value;

  if (type === "boolean" || type === "number") {
    // System F/Omega proof: Non-finite numbers are not valid JSON
    // Type proof: value ∈ number → number | error
    // Mathematical proof: JSON specification requires finite numbers
    if (type === "number" && !Number.isFinite(value as number)) {
      throw new Error(
        `[JSONSanitizer] Cannot sanitize value: Non-finite number is not valid JSON. ` +
        `Value: ${String(value)}, depth: ${depth}, maxDepth: ${opts.maxDepth}. ` +
        `JSON specification requires finite numbers (NaN and Infinity are not allowed). ` +
        `Wrap in try/catch to handle invalid JSON data.`
      );
    }
    return value as JSONValue;
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

  // Functions, symbols, bigint, etc. - not valid JSON
  // System F/Omega proof: Unsupported types are not valid JSON
  // Type proof: value ∈ function | symbol | bigint → error (not JSONValue)
  // Mathematical proof: JSON specification only supports null, boolean, number, string, array, object
  throw new Error(
    `[JSONSanitizer] Cannot sanitize value: Unsupported type is not valid JSON. ` +
    `Type: ${type}, depth: ${depth}, maxDepth: ${opts.maxDepth}. ` +
    `JSON specification only supports null, boolean, number, string, array, and object types. ` +
    `Functions, symbols, and bigint are not valid JSON. ` +
    `Wrap in try/catch to handle invalid JSON data.`
  );
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
  arr: JSONValue[],
  opts: Required<JSONSanitizeOptions>,
  stats: JSONSanitizeResult["stats"],
  warnings: string[],
  depth: number,
): JSONValue[] {
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
  const result: JSONValue[] = [];
  for (let i = 0; i < arr.length; i++) {
    const itemValue = arr[i] as RuntimeValue;
    result.push(sanitizeValue(itemValue, opts, stats, warnings, depth + 1));
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
export function safeParse<T extends JSONValue = JSONValue>(
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
