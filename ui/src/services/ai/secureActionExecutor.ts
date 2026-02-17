/**
 * Secure Action Executor
 *
 * BATTLE-HARDENED wrapper for AI tool execution:
 * - Hardened scope enforcement (default deny, time-limited elevation)
 * - Prompt injection detection with auto-lockdown
 * - Rate limiting with behavioral analysis
 * - Approval queue for dangerous operations
 * - Kill switch for active attacks
 * - Full audit logging with provenance
 *
 * SECURITY: This is the ONLY entry point for AI tool execution.
 * Never call executeToolCall directly from AI code.
 *
 * @see docs/SECURITY_THREAT_MODEL.md
 */

import type { JSONValue } from "@/types/dataAsset";
import {
  logToolCall as logToolCallAudit,
  logToolResult,
  logSecurityWarning,
  logUserConfirmation,
} from "../security/auditLog";
import { executeToolCall } from "./actionExecutor";
import {
  hardenedScopeManager,
  checkTool,
  reportInjectionDetected,
  type ToolPermission,
  type ScopeLevel,
} from "./security/hardenedScopeManager";
import {
  detectPromptInjection,
  sanitizeForLLM,
  scanForInjections,
} from "./security/promptInjectionDetector";
import type { ToolCall } from "./toolDefinitions";

// Re-export for backwards compatibility
export { hardenedScopeManager } from "./security/hardenedScopeManager";

// ============================================================================
// TYPES
// ============================================================================

export interface SecureExecutionResult {
  success: boolean;
  data?: JSONValue;
  error?: string;
  blocked?: boolean;
  requiresConfirmation?: boolean;
  confirmationId?: string;
}

export interface SecureExecutorOptions {
  /** Skip scope checks (for internal use only) */
  bypassScopeCheck?: boolean;
  /** User action that triggered this call (for audit) */
  userAction?: string;
  /** Whether user has confirmed this action */
  confirmed?: boolean;
  /** Confirmation ID if previously requested */
  confirmationId?: string;
}

// ============================================================================
// SECURE EXECUTOR
// ============================================================================

/**
 * Execute a tool call with full security checks
 *
 * BATTLE-HARDENED Security flow:
 * 1. Check kill switch
 * 2. Validate tool call structure
 * 3. Check for prompt injection (auto-lockdown on high confidence)
 * 4. Check hardened scope permissions
 * 5. Handle approval queue if required
 * 6. Execute with provenance tracking
 * 7. Log everything
 *
 * @param toolCall - The tool call to execute
 * @param options - Execution options
 * @returns Secure execution result
 */
export async function executeToolCallSecure(
  toolCall: ToolCall,
  options: SecureExecutorOptions = {},
): Promise<SecureExecutionResult> {
  const { bypassScopeCheck = false, userAction, confirmed = false, confirmationId } = options;

  // 0. Check kill switch FIRST
  if (hardenedScopeManager.isKillSwitchActive()) {
    throw new Error(`[SecureActionExecutor] 🚨 KILL SWITCH ACTIVE: All agent operations suspended. Security kill switch has been activated.`);
  }

  // 1. Validate tool call structure
  if (!toolCall || typeof toolCall.name !== "string") {
    await logSecurityWarning("Invalid tool call structure", { toolCall });
    hardenedScopeManager.recordSuspiciousActivity("invalid_tool_structure", 2);
    throw new Error(`[SecureActionExecutor] Invalid tool call structure. Tool call must have a valid "name" property. Security check failed.`);
  }

  // Extract arguments by removing 'name' and 'id' fields
  const { name, id, ...args } = toolCall;

  // Log the tool call attempt
  // Type-safe: Convert args to ToolArgsRecord (Record<string, JSONValue>)
  const argsRecord: Record<string, JSONValue> = {};
  for (const [key, value] of Object.entries(args)) {
    // Runtime type check: Ensure value is JSONValue
    if (
      typeof value === "string" ||
      typeof value === "number" ||
      typeof value === "boolean" ||
      value === null ||
      Array.isArray(value) ||
      (typeof value === "object" && value !== null)
    ) {
      argsRecord[key] = value as JSONValue;
    }
  }
  await logToolCallAudit(name, argsRecord, userAction);

  // 2. Check for prompt injection in string arguments
  if (args && typeof args === "object") {
    const stringArgs: Record<string, string | undefined> = {};
    for (const [key, value] of Object.entries(args)) {
      if (typeof value === "string") {
        stringArgs[key] = value;
      }
    }

    const injections = scanForInjections(stringArgs);
    if (injections.length > 0) {
      const highConfidence = injections.filter((i) => i.confidence === "high");

      // System F/Omega: Convert detections to AuditLogMetadata-compatible format
      // Type proof: AuditLogMetadata allows { [key: string]: string | number | boolean | null | undefined }
      // Convert array to object with string keys for compatibility
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
      const detectionsObj: Record<string, string | null> = {};
      injections.forEach((injection, index) => {
        const type = (typeof injection.type === "string" && injection.type.length > 0) ? injection.type : null;
        detectionsObj[`detection_${index}_type`] = type;
        detectionsObj[`detection_${index}_confidence`] = injection.confidence;
        const location = (typeof injection.location === "string" && injection.location.length > 0) ? injection.location : null;
        detectionsObj[`detection_${index}_location`] = location;
      });
      await logSecurityWarning(
        `Prompt injection detected in tool call ${name}`,
        {
          detectionCount: injections.length,
          highConfidenceCount: highConfidence.length,
          ...detectionsObj,
        },
      );

      // HARDENED: Report to scope manager (affects suspicion score)
      for (const injection of injections) {
        const severity = injection.confidence === "high" ? 5 : injection.confidence === "medium" ? 2 : 1;
        reportInjectionDetected(`${injection.type}: ${injection.details || "unknown"}`);
      }

      // Block high-confidence injections
      if (highConfidence.length > 0) {
        // HARDENED: Auto-downgrade to readonly on injection
        hardenedScopeManager.autoDowngrade("High-confidence injection detected");

        throw new Error(`[SecureActionExecutor] Blocked: prompt injection detected (${highConfidence[0].type}). High-confidence security threat detected and blocked.`);
      }

      // Medium/low: sanitize and continue with caution
      console.warn(
        `[Security] Medium/low confidence injection in ${name}, sanitizing`,
      );

      // Sanitize string values in args
      // Extract arguments from ToolCall by removing 'name' and 'id'
      const { name: toolName, id, ...toolArgs } = toolCall;
      for (const [key, value] of Object.entries(toolArgs)) {
        if (typeof value === "string") {
          // Type-safe assignment - sanitize string values
          (toolArgs as Record<string, JSONValue>)[key] = sanitizeForLLM(value);
        }
      }
      // Reconstruct toolCall with sanitized args
      Object.assign(toolCall, toolArgs);
    }
  }

  // 3. Check hardened scope permissions (unless bypassed for approved calls)
  if (!bypassScopeCheck) {
    // Type-safe: Convert args to Record<string, JSONValue>
    const argsForCheck: Record<string, JSONValue> = {};
    for (const [key, value] of Object.entries(args)) {
      if (
        typeof value === "string" ||
        typeof value === "number" ||
        typeof value === "boolean" ||
        value === null ||
        Array.isArray(value) ||
        (typeof value === "object" && value !== null)
      ) {
        argsForCheck[key] = value as JSONValue;
      }
    }
    const permission = checkTool(name, argsForCheck);

    if (!permission.allowed) {
      // Don't reveal scope details to potential attacker
      if (permission.requiresApproval) {
        // For approval-required tools, we need to return structured response for UI
        // But we'll throw an error that includes the approval context
        const approvalError = new Error(`[SecureActionExecutor] Tool '${name}' requires user approval. User confirmation required before execution.`);
        (approvalError as Error & { requiresConfirmation: boolean; confirmationId?: string }).requiresConfirmation = true;
        (approvalError as Error & { confirmationId?: string }).confirmationId = permission.approvalId;
        throw approvalError;
      }
      throw new Error(`[SecureActionExecutor] Tool '${name}' not available. Tool is blocked by security scope restrictions.`);
    }
  }

  // 4. Handle confirmation for previously queued operations
  if (confirmationId && !confirmed) {
    const approval = hardenedScopeManager.approveOperation(confirmationId);
    if (!approval) {
      throw new Error(`[SecureActionExecutor] Approval expired or invalid. Confirmation ID "${confirmationId}" is no longer valid.`);
    }
    // Continue with approved operation
  }

  // 5. Execute the tool call
  try {
    const result = await executeToolCall(toolCall);

    await logToolResult(name, true, "Tool executed successfully", {
      resultType: typeof result,
      scope: hardenedScopeManager.getSessionInfo().scope,
    });

    return {
      success: true,
      data: result,
    };
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : String(error);

    await logToolResult(name, false, errorMessage);

    // Certain errors might indicate attack
    if (errorMessage.includes("prototype") || errorMessage.includes("__proto__")) {
      hardenedScopeManager.recordSuspiciousActivity("prototype_error", 3, errorMessage);
    }

    // Re-throw the error - it's already explicit and debuggable
    throw error;
  }
}

/**
 * Execute multiple tool calls with security checks
 * Stops on first failure unless continueOnError is true
 */
export async function executeToolCallsBatch(
  toolCalls: ToolCall[],
  options: SecureExecutorOptions & { continueOnError?: boolean } = {},
): Promise<SecureExecutionResult[]> {
  const results: SecureExecutionResult[] = [];
  const { continueOnError = false, ...execOptions } = options;

  for (const toolCall of toolCalls) {
    try {
      const result = await executeToolCallSecure(toolCall, execOptions);
      results.push(result);
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : String(error);
      const errorResult: SecureExecutionResult = {
        success: false,
        error: errorMessage,
        blocked: errorMessage.includes("blocked") || errorMessage.includes("KILL SWITCH") || errorMessage.includes("not available"),
      };
      results.push(errorResult);

      // Stop on failure unless continueOnError
      if (!continueOnError) {
        throw error; // Re-throw to propagate the error
      }
    }
  }

  return results;
}

/**
 * Confirm a pending tool call (from UI approval dialog)
 */
export async function confirmPendingToolCall(
  confirmationId: string,
  approved: boolean,
): Promise<SecureExecutionResult> {
  await logUserConfirmation(`confirmation:${confirmationId}`, approved);

  if (!approved) {
    hardenedScopeManager.denyOperation(confirmationId);
    throw new Error(`[SecureActionExecutor] User declined the action. Confirmation ID "${confirmationId}" was denied by user.`);
  }

  const pending = hardenedScopeManager.approveOperation(confirmationId);
  if (!pending) {
    throw new Error(`[SecureActionExecutor] Approval expired or invalid. Confirmation ID "${confirmationId}" is no longer valid.`);
  }

  // Execute with bypass since we've already confirmed
  // Reconstruct ToolCall from stored name and arguments
  const toolCall = {
    id: confirmationId,
    name: pending.toolName,
    ...pending.arguments,
  } as ToolCall;
  return executeToolCallSecure(toolCall, { confirmed: true, bypassScopeCheck: true });
}

// ============================================================================
// SCOPE MANAGEMENT (using hardened manager)
// ============================================================================

/**
 * Get current scope level
 */
export function getCurrentScope(): ScopeLevel {
  return hardenedScopeManager.getSessionInfo().scope;
}

/**
 * Get full session info for UI
 */
export function getSessionInfo() {
  return hardenedScopeManager.getSessionInfo();
}

/**
 * Request scope elevation (returns request for UI)
 */
export function requestScopeElevation(
  targetScope: ScopeLevel,
  reason: string,
) {
  return hardenedScopeManager.requestElevation(targetScope, reason);
}

/**
 * Grant scope elevation (ONLY call from trusted UI)
 */
export function grantScopeElevation(
  targetScope: ScopeLevel,
  reason: string,
) {
  return hardenedScopeManager.grantElevation(targetScope, reason);
}

/**
 * Revoke scope elevation (return to readonly)
 */
export function revokeScopeElevation(reason?: string) {
  hardenedScopeManager.revokeElevation(reason);
}

/**
 * Start new agent session (call between conversations)
 */
export function startNewAgentSession() {
  hardenedScopeManager.startNewSession();
}

/**
 * Check if a tool would be allowed (without executing)
 */
export function wouldToolBeAllowed(
  toolName: string,
  args?: Record<string, JSONValue>,
): ToolPermission {
  return checkTool(toolName, args);
}

/**
 * Get list of available tools at current scope
 */
export function getAvailableTools(): string[] {
  return hardenedScopeManager.getAvailableTools();
}

/**
 * Get pending approvals for UI
 */
export function getPendingApprovals() {
  return hardenedScopeManager.getPendingApprovals();
}

/**
 * Approve a pending operation (ONLY from trusted UI)
 */
export function approveOperation(approvalId: string) {
  return hardenedScopeManager.approveOperation(approvalId);
}

/**
 * Deny a pending operation
 */
export function denyOperation(approvalId: string) {
  return hardenedScopeManager.denyOperation(approvalId);
}

/**
 * KILL SWITCH: Suspend all agent operations immediately
 */
export function activateKillSwitch(reason: string) {
  hardenedScopeManager.activateKillSwitch(reason);
}

/**
 * Deactivate kill switch (requires explicit user action)
 */
export function deactivateKillSwitch() {
  hardenedScopeManager.deactivateKillSwitch();
}

/**
 * Check if kill switch is active
 */
export function isKillSwitchActive(): boolean {
  return hardenedScopeManager.isKillSwitchActive();
}
