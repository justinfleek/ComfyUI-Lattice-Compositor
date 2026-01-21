/**
 * Security Utilities
 *
 * Provides secure alternatives for common operations:
 * - URL validation (SSRF prevention)
 * - Cryptographically secure random values
 * - Input sanitization
 */

import type { ToolCall } from "@/services/ai/toolDefinitions";
import type { JSONValue } from "@/types/dataAsset";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for security validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

// ============================================================================
// URL VALIDATION
// ============================================================================

/**
 * Allowed URL protocols for external resources
 */
const _ALLOWED_PROTOCOLS = ["https:", "http:", "data:", "blob:"];

/**
 * Blocked hostnames (localhost, private IPs, etc.)
 * These could be used for SSRF attacks
 */
const BLOCKED_HOSTNAMES = [
  "localhost",
  "127.0.0.1",
  "0.0.0.0",
  "::1",
  // Private IP ranges are checked separately
];

/**
 * Check if a hostname is a private/internal IP address
 */
function isPrivateIP(hostname: string): boolean {
  // IPv4 private ranges
  const privateRanges = [
    /^10\./, // 10.0.0.0/8
    /^172\.(1[6-9]|2[0-9]|3[0-1])\./, // 172.16.0.0/12
    /^192\.168\./, // 192.168.0.0/16
    /^169\.254\./, // Link-local
    /^127\./, // Loopback
  ];

  return privateRanges.some((range) => range.test(hostname));
}

/**
 * Validate a URL for safe external resource loading
 *
 * @param url - The URL to validate
 * @param options - Validation options
 * @returns true if URL is safe, false otherwise
 */
export function isValidExternalURL(
  url: string,
  options: {
    allowData?: boolean;
    allowBlob?: boolean;
    allowHttp?: boolean;
  } = {},
): boolean {
  const {
    allowData = true,
    allowBlob = true,
    allowHttp = false, // Default to HTTPS only for external URLs
  } = options;

  try {
    const parsed = new URL(url);

    // Check protocol
    const allowedProtocols = ["https:"];
    if (allowHttp) allowedProtocols.push("http:");
    if (allowData) allowedProtocols.push("data:");
    if (allowBlob) allowedProtocols.push("blob:");

    if (!allowedProtocols.includes(parsed.protocol)) {
      console.warn(`[Security] Blocked URL with protocol: ${parsed.protocol}`);
      return false;
    }

    // For data: and blob: URLs, we're done checking
    if (parsed.protocol === "data:" || parsed.protocol === "blob:") {
      return true;
    }

    // Check for blocked hostnames
    if (BLOCKED_HOSTNAMES.includes(parsed.hostname.toLowerCase())) {
      console.warn(`[Security] Blocked URL with hostname: ${parsed.hostname}`);
      return false;
    }

    // Check for private IP addresses
    if (isPrivateIP(parsed.hostname)) {
      console.warn(
        `[Security] Blocked URL with private IP: ${parsed.hostname}`,
      );
      return false;
    }

    return true;
  } catch {
    // Invalid URL
    console.warn(`[Security] Invalid URL: ${url}`);
    return false;
  }
}

/**
 * Validate and sanitize a URL, throwing if invalid
 *
 * @param url - The URL to validate
 * @param context - Context for error messages (e.g., "SVG loading")
 * @param options - Validation options
 * @returns The validated URL string
 * @throws Error if URL is invalid or blocked
 */
export function validateURL(
  url: string,
  context: string = "resource loading",
  options: Parameters<typeof isValidExternalURL>[1] = {},
): string {
  if (!isValidExternalURL(url, options)) {
    throw new Error(
      `[Security] Invalid or blocked URL for ${context}: ${url.substring(0, 100)}...`,
    );
  }
  return url;
}

// ============================================================================
// CRYPTOGRAPHICALLY SECURE RANDOM
// ============================================================================

/**
 * Generate a cryptographically secure random string
 *
 * @param length - Length of the string to generate
 * @returns A random alphanumeric string
 */
export function secureRandomString(length: number = 16): string {
  const chars =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
  const array = new Uint32Array(length);
  crypto.getRandomValues(array);

  let result = "";
  for (let i = 0; i < length; i++) {
    result += chars[array[i] % chars.length];
  }
  return result;
}

/**
 * Generate a cryptographically secure random integer
 *
 * @param max - Maximum value (exclusive)
 * @returns A random integer from 0 to max-1
 */
export function secureRandomInt(max: number): number {
  const array = new Uint32Array(1);
  crypto.getRandomValues(array);
  return array[0] % max;
}

/**
 * Generate a UUID using crypto API with fallback
 */
export function secureUUID(): string {
  if (typeof crypto !== "undefined" && crypto.randomUUID) {
    return crypto.randomUUID();
  }

  // Fallback using crypto.getRandomValues (RFC 4122 version 4)
  const array = new Uint8Array(16);
  crypto.getRandomValues(array);

  // Set version (4) and variant (RFC 4122)
  array[6] = (array[6] & 0x0f) | 0x40;
  array[8] = (array[8] & 0x3f) | 0x80;

  const hex = Array.from(array, (b) => b.toString(16).padStart(2, "0")).join(
    "",
  );
  return `${hex.slice(0, 8)}-${hex.slice(8, 12)}-${hex.slice(12, 16)}-${hex.slice(16, 20)}-${hex.slice(20)}`;
}

// ============================================================================
// INPUT SANITIZATION
// ============================================================================

/**
 * Sanitize a string for safe display (prevents XSS in dynamic content)
 */
export function sanitizeHTML(input: string): string {
  const div = document.createElement("div");
  div.textContent = input;
  return div.innerHTML;
}

/**
 * Sanitize a filename to prevent directory traversal
 */
export function sanitizeFilename(filename: string): string {
  return filename
    .replace(/\.\./g, "") // Remove directory traversal
    .replace(/[<>:"/\\|?*]/g, "_") // Remove invalid characters
    .replace(/^\.+/, "") // Remove leading dots
    .trim();
}

// ============================================================================
// RUNTIME TYPE VALIDATION
// ============================================================================

/**
 * Validation error with details
 */
export class ValidationError extends Error {
  constructor(
    message: string,
    public path: string[] = [],
    public value?: JSONValue,
  ) {
    super(message);
    this.name = "ValidationError";
  }
}

/**
 * Generic object type for security utilities
 */
export interface SecurityObject {
  [key: string]: JSONValue;
}

/**
 * Validate that a value is a non-null object
 */
export function isObject(value: RuntimeValue): value is SecurityObject {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

/**
 * Validate that a value is an array
 */
export function isArray(value: RuntimeValue): value is JSONValue[] {
  return Array.isArray(value);
}

/**
 * Validate AI API response structure
 * Ensures the response has expected shape before processing
 */
export function validateAIResponse(
  response: RuntimeValue,
  context: string = "AI response",
): {
  content?: string;
  toolCalls?: Array<{
    id: string;
    name: string;
    arguments: Record<string, JSONValue>;
  }>;
} {
  if (!isObject(response)) {
    throw new ValidationError(
      `${context}: Expected object, got ${typeof response}`,
    );
  }

  const result: {
    content?: string;
    toolCalls?: Array<{
      id: string;
      name: string;
      arguments: Omit<ToolCall, "id" | "name">;
    }>;
  } = {};

  // Validate content if present
  if ("content" in response) {
    if (typeof response.content !== "string" && response.content !== null) {
      throw new ValidationError(`${context}: content must be string or null`);
    }
    result.content = response.content as string | undefined;
  }

  // Validate tool_calls / toolCalls if present
  const toolCallsKey = "tool_calls" in response ? "tool_calls" : "toolCalls";
  if (toolCallsKey in response && response[toolCallsKey] != null) {
    const toolCalls = response[toolCallsKey];
    if (!isArray(toolCalls)) {
      throw new ValidationError(`${context}: ${toolCallsKey} must be an array`);
    }

    result.toolCalls = toolCalls.map((call, i) => {
      if (!isObject(call)) {
        throw new ValidationError(
          `${context}: ${toolCallsKey}[${i}] must be an object`,
        );
      }

      const id = call.id;
      const name =
        call.name || (isObject(call.function) ? call.function.name : undefined);
      let args =
        call.arguments ||
        (isObject(call.function) ? call.function.arguments : {});

      if (typeof id !== "string") {
        throw new ValidationError(
          `${context}: ${toolCallsKey}[${i}].id must be a string`,
        );
      }
      if (typeof name !== "string") {
        throw new ValidationError(
          `${context}: ${toolCallsKey}[${i}].name must be a string`,
        );
      }

      // Parse arguments if it's a string (OpenAI format)
      if (typeof args === "string") {
        try {
          args = JSON.parse(args);
        } catch {
          throw new ValidationError(
            `${context}: ${toolCallsKey}[${i}].arguments is invalid JSON`,
          );
        }
      }

      if (!isObject(args)) {
        args = {};
      }

      return { id, name, arguments: args as Omit<ToolCall, "id" | "name"> };
    });
  }

  return result;
}

/**
 * Validate project file structure (basic validation)
 * Checks that the project has required fields before loading
 */
export function validateProjectStructure(
  data: RuntimeValue,
  context: string = "Project",
): void {
  if (!isObject(data)) {
    throw new ValidationError(
      `${context}: Expected object, got ${typeof data}`,
    );
  }

  // Check required fields
  if (!("version" in data)) {
    throw new ValidationError(`${context}: Missing required field 'version'`);
  }

  if (!("compositions" in data) && !("layers" in data)) {
    throw new ValidationError(
      `${context}: Missing required field 'compositions' or 'layers'`,
    );
  }

  // Validate compositions if present
  if ("compositions" in data && data.compositions != null) {
    if (!isObject(data.compositions)) {
      throw new ValidationError(`${context}: compositions must be an object`);
    }

    for (const [compId, comp] of Object.entries(data.compositions)) {
      if (!isObject(comp)) {
        throw new ValidationError(
          `${context}: compositions.${compId} must be an object`,
        );
      }
      if (!("settings" in comp) || !isObject(comp.settings)) {
        throw new ValidationError(
          `${context}: compositions.${compId}.settings must be an object`,
        );
      }
      if (!("layers" in comp) || !isArray(comp.layers)) {
        throw new ValidationError(
          `${context}: compositions.${compId}.layers must be an array`,
        );
      }

      // Validate numeric fields in settings
      // CompositionSettings has width, height, frameCount, fps, duration, backgroundColor, etc.
      const settings = comp.settings;
      if (
        settings.width !== undefined &&
        (!Number.isFinite(settings.width) || (settings.width as number) <= 0)
      ) {
        throw new ValidationError(
          `${context}: compositions.${compId}.settings.width must be a positive finite number`,
        );
      }
      if (
        settings.height !== undefined &&
        (!Number.isFinite(settings.height) || (settings.height as number) <= 0)
      ) {
        throw new ValidationError(
          `${context}: compositions.${compId}.settings.height must be a positive finite number`,
        );
      }
      if (
        settings.frameCount !== undefined &&
        (!Number.isFinite(settings.frameCount) ||
          (settings.frameCount as number) <= 0)
      ) {
        throw new ValidationError(
          `${context}: compositions.${compId}.settings.frameCount must be a positive finite number`,
        );
      }
      if (
        settings.fps !== undefined &&
        (!Number.isFinite(settings.fps) || (settings.fps as number) <= 0)
      ) {
        throw new ValidationError(
          `${context}: compositions.${compId}.settings.fps must be a positive finite number`,
        );
      }
    }
  }

  // Validate layers if present (legacy format)
  if ("layers" in data && data.layers != null) {
    if (!isArray(data.layers)) {
      throw new ValidationError(`${context}: layers must be an array`);
    }
  }
}

/**
 * Safely parse JSON with validation
 */
export function safeJSONParse<T extends JSONValue>(
  json: string,
  validator?: (data: JSONValue) => void,
  context: string = "JSON",
): T {
  let data: JSONValue;
  try {
    const parsed = JSON.parse(json);
    // Type guard: JSON.parse returns JSONValue
    if (
      typeof parsed === "string" ||
      typeof parsed === "number" ||
      typeof parsed === "boolean" ||
      parsed === null ||
      Array.isArray(parsed) ||
      (typeof parsed === "object" && parsed !== null)
    ) {
      data = parsed as JSONValue;
    } else {
      throw new ValidationError(`${context}: Parsed JSON is not a valid JSON value`);
    }
  } catch (e) {
    if (e instanceof ValidationError) {
      throw e;
    }
    throw new ValidationError(
      `${context}: Invalid JSON - ${e instanceof Error ? e.message : "parse error"}`,
    );
  }

  if (validator) {
    validator(data);
  }

  return data as T;
}
