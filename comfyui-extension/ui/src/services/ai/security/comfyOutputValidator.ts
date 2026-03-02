/**
 * ComfyUI Output Validator
 *
 * Validates data received from ComfyUI custom_nodes and workflows.
 * ComfyUI custom_nodes can be malicious or buggy, so we validate ALL outputs.
 *
 * SECURITY PRINCIPLE: Trust boundary at ComfyUI interface.
 * - Never trust custom_node outputs
 * - Validate before using
 * - Sanitize before rendering
 *
 * @see docs/SECURITY_THREAT_MODEL.md
 */

import { z } from "zod";
import { safeJsonParse } from "../../../utils/schemaValidation";
import { sanitizeFilename, isPathSafe } from "../../../utils/schemaValidation";
import { logAuditEntry } from "../../security/auditLog";
import type { ComfyUIWorkflow, ComfyUINode } from "@/types/export";
import type { JSONValue } from "@/types/dataAsset";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

// ============================================================================
// COMFYUI DATA SCHEMAS
// ============================================================================

/**
 * Schema for ComfyUI image output
 */
export const ComfyImageOutputSchema = z.object({
  filename: z.string().max(255),
  subfolder: z.string().max(500).optional(),
  type: z.enum(["output", "input", "temp"]).optional(),
});

/**
 * Schema for ComfyUI node execution result
 * ComfyUI node outputs can contain any JSON-serializable value
 */
export const ComfyNodeResultSchema = z.object({
  node_id: z.string(),
  output: z.record(z.union([
    z.string(),
    z.number(),
    z.boolean(),
    z.null(),
    z.array(z.union([z.string(), z.number(), z.boolean(), z.null()])),
    z.record(z.union([z.string(), z.number(), z.boolean(), z.null()])),
  ])).optional(),
  error: z.string().optional(),
});

/**
 * Schema for ComfyUI workflow execution status
 */
export const ComfyExecutionStatusSchema = z.object({
  status: z.enum(["success", "error", "queued", "running"]),
  prompt_id: z.string().optional(),
  node_errors: z.record(z.string()).optional(),
});

/**
 * Schema for ComfyUI prompt info (workflow definition)
 * ComfyUI prompts contain node definitions with JSON-serializable inputs
 */
export const ComfyPromptInfoSchema = z.object({
  prompt: z.record(z.union([
    z.string(),
    z.number(),
    z.boolean(),
    z.null(),
    z.array(z.union([z.string(), z.number(), z.boolean(), z.null()])),
    z.record(z.union([z.string(), z.number(), z.boolean(), z.null()])),
  ])),
  client_id: z.string().optional(),
  extra_data: z.record(z.union([
    z.string(),
    z.number(),
    z.boolean(),
    z.null(),
    z.array(z.union([z.string(), z.number(), z.boolean(), z.null()])),
    z.record(z.union([z.string(), z.number(), z.boolean(), z.null()])),
  ])).optional(),
});

// ============================================================================
// VALIDATION FUNCTIONS
// ============================================================================

/**
 * Validate ComfyUI image output before using
 */
export function validateComfyImageOutput(
  data: RuntimeValue,
): z.infer<typeof ComfyImageOutputSchema> | null {
  const result = ComfyImageOutputSchema.safeParse(data);

  if (!result.success) {
    logAuditEntry({
      category: "security_warning",
      severity: "warning",
      message: "Invalid ComfyUI image output received",
      metadata: {
        // System F/Omega: Convert Zod errors to AuditLogMetadata-compatible format
        // Type proof: Convert array to object with string keys for compatibility
        errorCount: result.error.errors.length,
        errorMessages: result.error.errors.map((e) => e.message).join("; "),
        errorCodes: result.error.errors.map((e) => String(e.code)).join(", "),
        errorPaths: result.error.errors.map((e) => e.path.join(".")).join("; "),
        data: String(data).slice(0, 200),
      },
    });
    throw new Error(`[ComfyOutputValidator] Invalid ComfyUI image output: ${result.error.errors.map(e => e.message).join("; ")}`);
  }

  // Additional security: sanitize filename
  const sanitizedFilename = sanitizeFilename(result.data.filename);
  if (sanitizedFilename !== result.data.filename) {
    logAuditEntry({
      category: "security_warning",
      severity: "warning",
      message: "ComfyUI image filename sanitized",
      metadata: {
        original: result.data.filename,
        sanitized: sanitizedFilename,
      },
    });
  }

  // Check for path traversal in subfolder
  if (result.data.subfolder && !isPathSafe(result.data.subfolder)) {
    logAuditEntry({
      category: "security_warning",
      severity: "critical",
      message: "Path traversal attempt in ComfyUI subfolder",
      metadata: { subfolder: result.data.subfolder },
    });
    throw new Error(`[ComfyOutputValidator] Invalid ComfyUI image output: Path traversal detected in subfolder`);
  }

  return {
    ...result.data,
    filename: sanitizedFilename,
  };
}

/**
 * Validate ComfyUI node execution result
 */
export function validateComfyNodeResult(
  data: RuntimeValue,
): z.infer<typeof ComfyNodeResultSchema> | null {
  const result = ComfyNodeResultSchema.safeParse(data);

  if (!result.success) {
    logAuditEntry({
      category: "security_warning",
      severity: "warning",
      message: "Invalid ComfyUI node result received",
      metadata: {
        // System F/Omega: Convert Zod errors to AuditLogMetadata-compatible format
        // Type proof: Convert array to object with string keys for compatibility
        errorCount: result.error.errors.length,
        errorMessages: result.error.errors.map((e) => e.message).join("; "),
        errorCodes: result.error.errors.map((e) => String(e.code)).join(", "),
        errorPaths: result.error.errors.map((e) => e.path.join(".")).join("; "),
      },
    });
    throw new Error(`[ComfyOutputValidator] Invalid ComfyUI image output: ${result.error.errors.map(e => e.message).join("; ")}`);
  }

  return result.data;
}

/**
 * Validate ComfyUI execution status
 */
export function validateComfyExecutionStatus(
  data: RuntimeValue,
): z.infer<typeof ComfyExecutionStatusSchema> | null {
  const result = ComfyExecutionStatusSchema.safeParse(data);

  if (!result.success) {
    logAuditEntry({
      category: "security_warning",
      severity: "warning",
      message: "Invalid ComfyUI execution status received",
      metadata: {
        // System F/Omega: Convert Zod errors to AuditLogMetadata-compatible format
        // Type proof: Convert array to object with string keys for compatibility
        errorCount: result.error.errors.length,
        errorMessages: result.error.errors.map((e) => e.message).join("; "),
        errorCodes: result.error.errors.map((e) => String(e.code)).join(", "),
        errorPaths: result.error.errors.map((e) => e.path.join(".")).join("; "),
      },
    });
    throw new Error(`[ComfyOutputValidator] Invalid ComfyUI image output: ${result.error.errors.map(e => e.message).join("; ")}`);
  }

  return result.data;
}

// ============================================================================
// CUSTOM NODE OUTPUT VALIDATION
// ============================================================================

/**
 * Limits for custom node outputs
 */
const CUSTOM_NODE_LIMITS = {
  maxStringLength: 100000, // 100KB per string
  maxArrayLength: 10000,
  maxObjectDepth: 20,
  maxTotalSize: 10 * 1024 * 1024, // 10MB total
};

/**
 * Validate arbitrary custom node output
 *
 * Custom nodes can return anything, so we do defensive validation:
 * - Size limits
 * - Depth limits
 * - Prototype pollution check
 * - Path traversal check in strings
 */
export function validateCustomNodeOutput(
  nodeId: string,
  nodeName: string,
  output: RuntimeValue,
): { valid: boolean; sanitized?: JSONValue; error?: string } {
  // Check if output is present
  if (output === undefined || output === null) {
    return { valid: true, sanitized: output };
  }

  // Serialize and check total size
  let serialized: string;
  try {
    serialized = JSON.stringify(output);
  } catch (error) {
    logAuditEntry({
      category: "security_warning",
      severity: "warning",
      message: `Custom node output not serializable`,
      metadata: { nodeId, nodeName, error: String(error) },
    });
    return { valid: false, error: "Output not serializable" };
  }

  if (serialized.length > CUSTOM_NODE_LIMITS.maxTotalSize) {
    logAuditEntry({
      category: "security_warning",
      severity: "warning",
      message: `Custom node output too large`,
      metadata: { nodeId, nodeName, size: serialized.length },
    });
    return { valid: false, error: `Output too large: ${serialized.length} bytes` };
  }

  // Parse with security checks
  let parsedData: JSONValue;
  try {
    const parseResult = safeJsonParse(serialized, undefined, {
      maxDepth: CUSTOM_NODE_LIMITS.maxObjectDepth,
      maxSize: CUSTOM_NODE_LIMITS.maxTotalSize,
      maxStringLength: CUSTOM_NODE_LIMITS.maxStringLength,
      maxArrayLength: CUSTOM_NODE_LIMITS.maxArrayLength,
      context: `CustomNode[${nodeName}]`,
    });
    // Type guard: ensure parseResult.data is JSONValue
    if (parseResult.success && typeof parseResult.data !== "undefined") {
      parsedData = parseResult.data as JSONValue;
    } else {
      throw new Error("Failed to parse custom node output");
    }
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : String(error);
    logAuditEntry({
      category: "security_warning",
      severity: "warning",
      message: `Custom node output validation failed`,
      metadata: {
        nodeId,
        nodeName,
        error: errorMessage,
      },
    });
    return { valid: false, error: errorMessage };
  }

  // Scan for suspicious patterns in string values
  const suspiciousStrings = findSuspiciousStrings(parsedData);
  if (suspiciousStrings.length > 0) {
    logAuditEntry({
      category: "security_warning",
      severity: "warning",
      message: `Suspicious strings in custom node output`,
      metadata: {
        nodeId,
        nodeName,
        suspiciousCount: suspiciousStrings.length,
        patterns: suspiciousStrings.slice(0, 5), // Log first 5
      },
    });
    // We allow but log - could make this configurable
  }

  return { valid: true, sanitized: parsedData };
}

/**
 * Find suspicious string patterns in an object
 */
function findSuspiciousStrings(
  obj: RuntimeValue,
  path: string = "",
  found: string[] = [],
): string[] {
  if (typeof obj === "string") {
    // Check for various suspicious patterns
    const patterns = [
      { name: "path_traversal", regex: /\.\./ },
      { name: "shell_command", regex: /;\s*(rm|del|format|wget|curl|nc)\s/i },
      { name: "script_injection", regex: /<script|javascript:/i },
      { name: "sensitive_file", regex: /\.(env|pem|key|p12|pfx)$/i },
      { name: "eval_pattern", regex: /eval\s*\(|new\s+Function\s*\(/i },
    ];

    for (const { name, regex } of patterns) {
      if (regex.test(obj)) {
        found.push(`${path}: ${name}`);
      }
    }
  } else if (Array.isArray(obj)) {
    obj.forEach((item, i) => {
      findSuspiciousStrings(item, `${path}[${i}]`, found);
    });
  } else if (typeof obj === "object" && obj !== null) {
    for (const [key, value] of Object.entries(obj)) {
      findSuspiciousStrings(value, path ? `${path}.${key}` : key, found);
    }
  }

  return found;
}

// ============================================================================
// WORKFLOW VALIDATION
// ============================================================================

/**
 * Validate a ComfyUI workflow before execution
 *
 * Checks for:
 * - Known dangerous node types
 * - Suspicious inputs
 * - External URL references
 */
export function validateComfyWorkflow(workflow: ComfyUIWorkflow): {
  safe: boolean;
  warnings: string[];
  blocked: string[];
} {
  const warnings: string[] = [];
  const blocked: string[] = [];

  // Known dangerous or risky node types
  const dangerousNodes = new Set([
    "ExecuteCode", // Direct code execution
    "PythonScript", // Python execution
    "RunBash", // Shell execution
    "SystemCommand", // System commands
    "ExternalURL", // Arbitrary URL fetching
    "WebhookNotify", // Data exfiltration
  ]);

  const riskyNodes = new Set([
    "LoadImage", // Can load from disk
    "SaveImage", // Can write to disk
    "LoadCheckpoint", // Large file loading
    "VAEDecode", // GPU intensive
    "KSampler", // GPU intensive
  ]);

  for (const [nodeId, nodeData] of Object.entries(workflow)) {
    if (!nodeData || typeof nodeData !== "object") {
      continue;
    }

    const node = nodeData as ComfyUINode;
    const classType = node.class_type;

    if (typeof classType !== "string") {
      continue;
    }

    // Block dangerous nodes
    if (dangerousNodes.has(classType)) {
      blocked.push(`Node ${nodeId}: ${classType} (code execution)`);
      continue;
    }

    // Warn about risky nodes
    if (riskyNodes.has(classType)) {
      warnings.push(`Node ${nodeId}: ${classType} (resource intensive)`);
    }

    // Check node inputs for suspicious values
    const inputs = node.inputs;
    if (inputs && typeof inputs === "object") {
      for (const [inputName, inputValue] of Object.entries(inputs)) {
        // Check for file path inputs
        if (typeof inputValue === "string") {
          if (!isPathSafe(inputValue)) {
            blocked.push(
              `Node ${nodeId}.${inputName}: suspicious path "${inputValue.slice(0, 50)}..."`,
            );
          }

          // Check for external URLs
          if (
            inputValue.startsWith("http://") ||
            inputValue.startsWith("https://")
          ) {
            warnings.push(
              `Node ${nodeId}.${inputName}: external URL "${inputValue.slice(0, 50)}..."`,
            );
          }
        }
      }
    }
  }

  // Log if anything was blocked
  if (blocked.length > 0) {
    logAuditEntry({
      category: "security_warning",
      severity: "critical",
      message: `Blocked dangerous nodes in workflow`,
      metadata: { blocked, warnings },
    });
  }

  return {
    safe: blocked.length === 0,
    warnings,
    blocked,
  };
}

// ============================================================================
// IMAGE DATA VALIDATION
// ============================================================================

/**
 * Validate image data from ComfyUI
 *
 * Checks:
 * - Valid image format
 * - Reasonable dimensions
 * - Not suspiciously large
 */
export function validateImageData(
  data: ArrayBuffer | Blob,
  options: {
    maxWidth?: number;
    maxHeight?: number;
    maxSize?: number;
    allowedFormats?: string[];
  } = {},
): Promise<{
  valid: boolean;
  error?: string;
  metadata?: { width: number; height: number; format: string };
}> {
  const {
    maxWidth = 8192,
    maxHeight = 8192,
    maxSize = 100 * 1024 * 1024, // 100MB
    allowedFormats = ["image/png", "image/jpeg", "image/webp", "image/gif"],
  } = options;

  return new Promise((resolve) => {
    // Check size
    const size = data instanceof Blob ? data.size : data.byteLength;
    if (size > maxSize) {
      resolve({ valid: false, error: `Image too large: ${size} bytes` });
      return;
    }

    // Create blob if needed
    const blob = data instanceof Blob ? data : new Blob([data]);

    // Check format via magic bytes
    const reader = new FileReader();
    reader.onload = () => {
      const arr = new Uint8Array(reader.result as ArrayBuffer);
      const format = detectImageFormat(arr);

      if (!format) {
        resolve({ valid: false, error: "Unknown image format" });
        return;
      }

      if (!allowedFormats.includes(format)) {
        resolve({ valid: false, error: `Format ${format} not allowed` });
        return;
      }

      // Load image to check dimensions
      const url = URL.createObjectURL(blob);
      const img = new Image();

      img.onload = () => {
        URL.revokeObjectURL(url);

        if (img.width > maxWidth || img.height > maxHeight) {
          resolve({
            valid: false,
            error: `Dimensions ${img.width}x${img.height} exceed maximum ${maxWidth}x${maxHeight}`,
          });
          return;
        }

        resolve({
          valid: true,
          metadata: {
            width: img.width,
            height: img.height,
            format,
          },
        });
      };

      img.onerror = () => {
        URL.revokeObjectURL(url);
        resolve({ valid: false, error: "Failed to decode image" });
      };

      img.src = url;
    };

    reader.onerror = () => {
      resolve({ valid: false, error: "Failed to read image data" });
    };

    reader.readAsArrayBuffer(blob.slice(0, 16)); // Only need first bytes for magic
  });
}

/**
 * Detect image format from magic bytes
 */
function detectImageFormat(bytes: Uint8Array): string | null {
  // PNG: 89 50 4E 47 0D 0A 1A 0A
  if (
    bytes[0] === 0x89 &&
    bytes[1] === 0x50 &&
    bytes[2] === 0x4e &&
    bytes[3] === 0x47
  ) {
    return "image/png";
  }

  // JPEG: FF D8 FF
  if (bytes[0] === 0xff && bytes[1] === 0xd8 && bytes[2] === 0xff) {
    return "image/jpeg";
  }

  // WebP: RIFF....WEBP
  if (
    bytes[0] === 0x52 &&
    bytes[1] === 0x49 &&
    bytes[2] === 0x46 &&
    bytes[3] === 0x46 &&
    bytes[8] === 0x57 &&
    bytes[9] === 0x45 &&
    bytes[10] === 0x42 &&
    bytes[11] === 0x50
  ) {
    return "image/webp";
  }

  // GIF: GIF87a or GIF89a
  if (
    bytes[0] === 0x47 &&
    bytes[1] === 0x49 &&
    bytes[2] === 0x46 &&
    bytes[3] === 0x38
  ) {
    return "image/gif";
  }

  throw new Error(`[ComfyOutputValidator] Unknown image format: first 4 bytes are ${bytes[0]}, ${bytes[1]}, ${bytes[2]}, ${bytes[3]}`);
}
