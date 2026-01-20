/**
 * Schema Validation Security Utilities
 *
 * SECURITY FEATURES:
 * - Prototype pollution prevention (__proto__, constructor, prototype)
 * - JSON depth limits (prevents stack overflow)
 * - JSON size limits (prevents memory exhaustion)
 * - String length limits (prevents payload attacks)
 * - Path traversal prevention
 * - Unicode normalization and sanitization
 *
 * @see docs/SECURITY_THREAT_MODEL.md for full threat analysis
 */

import type { z } from "zod";

// ============================================================================
// CONFIGURATION
// ============================================================================

export interface SafeParseOptions {
  /** Maximum JSON nesting depth (default: 100) */
  maxDepth?: number;
  /** Maximum JSON string size in bytes (default: 50MB) */
  maxSize?: number;
  /** Maximum individual string length (default: 1MB) */
  maxStringLength?: number;
  /** Maximum array length (default: 100000) */
  maxArrayLength?: number;
  /** Context name for error messages */
  context?: string;
}

const DEFAULT_OPTIONS: Required<SafeParseOptions> = {
  maxDepth: 100,
  maxSize: 50 * 1024 * 1024, // 50MB
  maxStringLength: 1024 * 1024, // 1MB
  maxArrayLength: 100000,
  context: "JSON",
};

// ============================================================================
// DANGEROUS KEYS
// ============================================================================

/**
 * Keys that can be used for prototype pollution attacks
 */
const DANGEROUS_KEYS = new Set([
  "__proto__",
  "constructor",
  "prototype",
  "__defineGetter__",
  "__defineSetter__",
  "__lookupGetter__",
  "__lookupSetter__",
]);

// ============================================================================
// SAFE JSON PARSE
// ============================================================================

export interface SafeParseResult<T> {
  success: true;
  data: T;
}

export interface SafeParseError {
  success: false;
  error: Error;
  code:
    | "PARSE_ERROR"
    | "SIZE_EXCEEDED"
    | "DEPTH_EXCEEDED"
    | "STRING_LENGTH_EXCEEDED"
    | "ARRAY_LENGTH_EXCEEDED"
    | "PROTOTYPE_POLLUTION"
    | "SCHEMA_VALIDATION"
    | "UNKNOWN";
}

export type SafeParseReturn<T> = SafeParseResult<T> | SafeParseError;

/**
 * Safely parse JSON with comprehensive security checks
 *
 * SECURITY FEATURES:
 * 1. Size limit check BEFORE parsing
 * 2. Prototype pollution prevention via reviver
 * 3. Depth tracking to prevent stack overflow
 * 4. String length limits
 * 5. Array length limits
 * 6. Schema validation via Zod
 *
 * @param json - The JSON string to parse
 * @param schema - Optional Zod schema for validation
 * @param options - Security options
 * @returns Safe parse result with typed data or detailed error
 */
export function safeJsonParse<T>(
  json: string,
  schema?: z.ZodSchema<T>,
  options: SafeParseOptions = {},
): SafeParseReturn<T> {
  const opts = { ...DEFAULT_OPTIONS, ...options };

  // 1. Size check BEFORE parsing (prevents memory exhaustion)
  if (json.length > opts.maxSize) {
    return {
      success: false,
      error: new Error(
        `${opts.context}: JSON size ${json.length} exceeds maximum ${opts.maxSize} bytes`,
      ),
      code: "SIZE_EXCEEDED",
    };
  }

  // Track depth during parsing (approximate via counting nested objects/arrays)
  let maxObservedDepth = 0;
  let currentDepth = 0;
  const depthStack: number[] = [];

  try {
    // 2. Parse with reviver for security checks
    const parsed = JSON.parse(json, (key, value) => {
      // 2a. Block prototype pollution
      if (DANGEROUS_KEYS.has(key)) {
        throw new PrototypePollutionError(
          `${opts.context}: Dangerous key '${key}' detected - potential prototype pollution attack`,
        );
      }

      // 2b. Track and limit depth
      if (typeof value === "object" && value !== null) {
        currentDepth++;
        maxObservedDepth = Math.max(maxObservedDepth, currentDepth);

        if (currentDepth > opts.maxDepth) {
          throw new DepthExceededError(
            `${opts.context}: JSON depth ${currentDepth} exceeds maximum ${opts.maxDepth}`,
          );
        }
        depthStack.push(currentDepth);
      }

      // 2c. Limit string length
      if (typeof value === "string" && value.length > opts.maxStringLength) {
        throw new StringLengthExceededError(
          `${opts.context}: String length ${value.length} exceeds maximum ${opts.maxStringLength}`,
        );
      }

      // 2d. Limit array length
      if (Array.isArray(value) && value.length > opts.maxArrayLength) {
        throw new ArrayLengthExceededError(
          `${opts.context}: Array length ${value.length} exceeds maximum ${opts.maxArrayLength}`,
        );
      }

      // Pop depth when leaving object
      if (depthStack.length > 0 && typeof value === "object" && value !== null) {
        depthStack.pop();
        currentDepth = depthStack.length > 0 ? depthStack[depthStack.length - 1] : 0;
      }

      return value;
    });

    // 3. Additional prototype pollution check on parsed result
    if (hasPrototypePollution(parsed)) {
      return {
        success: false,
        error: new Error(
          `${opts.context}: Prototype pollution detected in parsed object`,
        ),
        code: "PROTOTYPE_POLLUTION",
      };
    }

    // 4. Schema validation if provided
    if (schema) {
      const result = schema.safeParse(parsed);
      if (!result.success) {
        return {
          success: false,
          error: new Error(
            `${opts.context}: Schema validation failed - ${result.error.message}`,
          ),
          code: "SCHEMA_VALIDATION",
        };
      }
      return { success: true, data: result.data };
    }

    return { success: true, data: parsed as T };
  } catch (error) {
    if (error instanceof PrototypePollutionError) {
      return { success: false, error, code: "PROTOTYPE_POLLUTION" };
    }
    if (error instanceof DepthExceededError) {
      return { success: false, error, code: "DEPTH_EXCEEDED" };
    }
    if (error instanceof StringLengthExceededError) {
      return { success: false, error, code: "STRING_LENGTH_EXCEEDED" };
    }
    if (error instanceof ArrayLengthExceededError) {
      return { success: false, error, code: "ARRAY_LENGTH_EXCEEDED" };
    }
    return {
      success: false,
      error: error instanceof Error ? error : new Error(String(error)),
      code: "PARSE_ERROR",
    };
  }
}

// ============================================================================
// PROTOTYPE POLLUTION DETECTION
// ============================================================================

/**
 * Recursively check for prototype pollution in an object
 */
export function hasPrototypePollution(
  obj: unknown,
  visited = new WeakSet<object>(),
): boolean {
  if (typeof obj !== "object" || obj === null) {
    return false;
  }

  // Prevent infinite recursion
  if (visited.has(obj)) {
    return false;
  }
  visited.add(obj);

  // Check for dangerous keys
  if (!Array.isArray(obj)) {
    for (const key of Object.keys(obj)) {
      if (DANGEROUS_KEYS.has(key)) {
        return true;
      }
    }
  }

  // Recursively check nested objects
  for (const value of Object.values(obj)) {
    if (hasPrototypePollution(value, visited)) {
      return true;
    }
  }

  return false;
}

/**
 * Remove dangerous keys from an object (defensive sanitization)
 */
export function sanitizeObject<T>(obj: T): T {
  if (typeof obj !== "object" || obj === null) {
    return obj;
  }

  if (Array.isArray(obj)) {
    return obj.map(sanitizeObject) as T;
  }

  // Use JSONValue type for sanitized objects (recursive type from jsonSanitizer)
  type JSONValue =
    | string
    | number
    | boolean
    | null
    | JSONValue[]
    | { [key: string]: JSONValue };

  const result: { [key: string]: JSONValue } = {};
  for (const [key, value] of Object.entries(obj)) {
    if (!DANGEROUS_KEYS.has(key)) {
      result[key] = sanitizeObject(value) as JSONValue;
    }
  }
  return result as T;
}

// ============================================================================
// PATH SECURITY
// ============================================================================

/**
 * Validate and sanitize a file path to prevent traversal attacks
 *
 * @param basePath - The allowed base directory
 * @param userPath - The user-provided path (potentially malicious)
 * @returns The safe resolved path, or null if traversal detected
 */
export function sanitizePath(basePath: string, userPath: string): string | null {
  // Normalize path separators
  const normalizedBase = basePath.replace(/\\/g, "/").replace(/\/+$/, "");
  let normalizedUser = userPath.replace(/\\/g, "/");

  // Check for null bytes (can bypass checks in some systems)
  if (normalizedUser.includes("\0")) {
    console.warn("[Security] Null byte detected in path:", userPath);
    return null;
  }

  // Remove leading slashes to prevent absolute path injection
  normalizedUser = normalizedUser.replace(/^\/+/, "");

  // Check for path traversal patterns BEFORE normalization
  if (
    normalizedUser.includes("..") ||
    normalizedUser.includes("./") ||
    normalizedUser.startsWith("~")
  ) {
    console.warn("[Security] Path traversal pattern detected:", userPath);
    return null;
  }

  // Build the full path
  const fullPath = `${normalizedBase}/${normalizedUser}`;

  // Normalize the path (resolve . and ..)
  const segments = fullPath.split("/").filter((s) => s !== "" && s !== ".");
  const resolved: string[] = [];

  for (const segment of segments) {
    if (segment === "..") {
      // Going up - check if we're still within base
      if (resolved.length <= normalizedBase.split("/").filter(Boolean).length) {
        console.warn("[Security] Path traversal would escape base:", userPath);
        return null;
      }
      resolved.pop();
    } else {
      resolved.push(segment);
    }
  }

  const resolvedPath = resolved.join("/");

  // Final check: ensure resolved path starts with base
  if (!resolvedPath.startsWith(normalizedBase.replace(/^\/+/, ""))) {
    console.warn("[Security] Resolved path escapes base:", resolvedPath);
    return null;
  }

  return "/" + resolvedPath;
}

/**
 * Check if a path is safe (doesn't contain traversal patterns)
 */
export function isPathSafe(path: string): boolean {
  // Check for null bytes
  if (path.includes("\0")) {
    return false;
  }

  // Check for traversal patterns
  const traversalPatterns = [
    /\.\./,           // Parent directory
    /^~/,             // Home directory
    /^\/etc\//i,      // System config
    /^\/var\//i,      // System var
    /^\/usr\//i,      // System usr
    /^\/bin\//i,      // System bin
    /^\/sbin\//i,     // System sbin
    /^\/root\//i,     // Root home
    /^\/home\//i,     // User homes
    /^\/tmp\//i,      // Temp directory
    /^[a-z]:\\/i,     // Windows drive letters
    /^\\\\[^\\]+\\/i, // UNC paths
    /\.ssh/i,         // SSH directory
    /\.env/i,         // Environment files
    /password/i,      // Password files
    /secret/i,        // Secret files
    /credential/i,    // Credential files
    /\.git/i,         // Git directory
  ];

  for (const pattern of traversalPatterns) {
    if (pattern.test(path)) {
      return false;
    }
  }

  return true;
}

// ============================================================================
// STRING SANITIZATION
// ============================================================================

/**
 * Sanitize a string for safe display/processing
 *
 * Removes/replaces:
 * - Null bytes
 * - Unicode direction overrides (RTL/LTR attacks)
 * - Control characters
 * - Excessive whitespace
 */
export function sanitizeString(
  input: string,
  options: {
    maxLength?: number;
    allowNewlines?: boolean;
    normalizeUnicode?: boolean;
  } = {},
): string {
  const { maxLength = 10000, allowNewlines = true, normalizeUnicode = true } = options;

  let sanitized = input;

  // Remove null bytes
  sanitized = sanitized.replace(/\0/g, "");

  // Remove Unicode direction overrides (can be used to disguise malicious content)
  // U+202A-U+202E: LTR/RTL embedding and overrides
  // U+2066-U+2069: Isolate controls
  sanitized = sanitized.replace(/[\u202A-\u202E\u2066-\u2069]/g, "");

  // Remove other dangerous control characters (except newlines/tabs if allowed)
  if (allowNewlines) {
    sanitized = sanitized.replace(/[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]/g, "");
  } else {
    sanitized = sanitized.replace(/[\x00-\x1F\x7F]/g, " ");
  }

  // Normalize excessive whitespace
  sanitized = sanitized.replace(/[ \t]+/g, " ");
  if (!allowNewlines) {
    sanitized = sanitized.replace(/\s+/g, " ");
  }

  // Normalize Unicode if requested
  if (normalizeUnicode) {
    try {
      sanitized = sanitized.normalize("NFC");
    } catch {
      // If normalization fails, continue with original
    }
  }

  // Trim
  sanitized = sanitized.trim();

  // Enforce max length
  if (sanitized.length > maxLength) {
    sanitized = sanitized.slice(0, maxLength);
  }

  return sanitized;
}

/**
 * Sanitize a filename to be safe for filesystem operations
 */
export function sanitizeFilename(filename: string): string {
  let sanitized = filename;

  // Remove path separators
  sanitized = sanitized.replace(/[/\\]/g, "_");

  // Remove null bytes
  sanitized = sanitized.replace(/\0/g, "");

  // Remove shell metacharacters
  sanitized = sanitized.replace(/[;&|`$(){}[\]<>!#*?"']/g, "_");

  // Remove control characters
  sanitized = sanitized.replace(/[\x00-\x1F\x7F]/g, "");

  // Remove directory traversal attempts
  sanitized = sanitized.replace(/\.\./g, "_");

  // Don't allow hidden files (starting with .)
  if (sanitized.startsWith(".")) {
    sanitized = "_" + sanitized.slice(1);
  }

  // Limit length (most filesystems have 255 char limit)
  if (sanitized.length > 200) {
    const ext = sanitized.match(/\.[^.]+$/)?.[0] || "";
    sanitized = sanitized.slice(0, 200 - ext.length) + ext;
  }

  // Ensure filename isn't empty
  if (sanitized.length === 0 || sanitized === "_") {
    sanitized = "unnamed";
  }

  return sanitized;
}

// ============================================================================
// ERROR CLASSES
// ============================================================================

export class PrototypePollutionError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "PrototypePollutionError";
  }
}

export class DepthExceededError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "DepthExceededError";
  }
}

export class StringLengthExceededError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "StringLengthExceededError";
  }
}

export class ArrayLengthExceededError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "ArrayLengthExceededError";
  }
}

export class PathTraversalError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "PathTraversalError";
  }
}

// ============================================================================
// VALIDATION HELPERS
// ============================================================================

/**
 * Check if a value looks like a potential injection payload
 */
export function looksLikeMaliciousPayload(value: string): boolean {
  const suspiciousPatterns = [
    // Script injection
    /<script/i,
    /javascript:/i,
    /on\w+\s*=/i, // onclick=, onerror=, etc.

    // SQL injection
    /'\s*or\s+'1'\s*=\s*'1/i,
    /;\s*drop\s+table/i,
    /;\s*delete\s+from/i,

    // Command injection
    /;\s*rm\s+-rf/i,
    /\|\s*cat\s+/i,
    /`[^`]*`/, // Backtick execution

    // Path traversal
    /\.\.\//,
    /\.\.\\/, // Windows path

    // Environment variable access
    /\$\{[^}]+\}/,
    /%[A-Z_]+%/i, // Windows env vars

    // Base64 encoded payloads (heuristic)
    /^[A-Za-z0-9+/]{50,}={0,2}$/,
  ];

  for (const pattern of suspiciousPatterns) {
    if (pattern.test(value)) {
      return true;
    }
  }

  return false;
}
