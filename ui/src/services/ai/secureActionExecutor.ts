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
  data?: unknown;
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
    return {
      success: false,
      error: "🚨 KILL SWITCH ACTIVE: All agent operations suspended",
      blocked: true,
    };
  }

  // 1. Validate tool call structure
  if (!toolCall || typeof toolCall.name !== "string") {
    await logSecurityWarning("Invalid tool call structure", { toolCall });
    hardenedScopeManager.recordSuspiciousActivity("invalid_tool_structure", 2);
    return {
      success: false,
      error: "Invalid tool call structure",
      blocked: true,
    };
  }

  // Extract arguments by removing 'name' and 'id' fields
  const { name, id, ...args } = toolCall;

  // Log the tool call attempt
  await logToolCallAudit(name, args, userAction);

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

      await logSecurityWarning(
        `Prompt injection detected in tool call ${name}`,
        {
          detectionCount: injections.length,
          highConfidenceCount: highConfidence.length,
          detections: injections.map((i) => ({
            type: i.type,
            confidence: i.confidence,
            location: i.location,
          })),
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

        return {
          success: false,
          error: `Blocked: prompt injection detected (${highConfidence[0].type})`,
          blocked: true,
        };
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
          (toolArgs as Record<string, unknown>)[key] = sanitizeForLLM(value);
        }
      }
      // Reconstruct toolCall with sanitized args
      Object.assign(toolCall, toolArgs);
    }
  }

  // 3. Check hardened scope permissions (unless bypassed for approved calls)
  if (!bypassScopeCheck) {
    const permission = checkTool(name, args);

    if (!permission.allowed) {
      // Don't reveal scope details to potential attacker
      return {
        success: false,
        error: permission.requiresApproval
          ? `Tool '${name}' requires user approval`
          : `Tool '${name}' not available`,
        blocked: !permission.requiresApproval,
        requiresConfirmation: permission.requiresApproval,
        confirmationId: permission.approvalId,
      };
    }
  }

  // 4. Handle confirmation for previously queued operations
  if (confirmationId && !confirmed) {
    const approval = hardenedScopeManager.approveOperation(confirmationId);
    if (!approval) {
      return {
        success: false,
        error: "Approval expired or invalid",
        blocked: true,
      };
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

    return {
      success: false,
      error: errorMessage,
    };
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
    const result = await executeToolCallSecure(toolCall, execOptions);
    results.push(result);

    // Stop on failure unless continueOnError
    if (!result.success && !continueOnError) {
      break;
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
    return {
      success: false,
      error: "User declined the action",
      blocked: true,
    };
  }

  const pending = hardenedScopeManager.approveOperation(confirmationId);
  if (!pending) {
    return {
      success: false,
      error: "Approval expired or invalid",
      blocked: true,
    };
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
  args?: Record<string, unknown>,
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
