/**
 * LLM Agent Scope Manager
 *
 * Implements DEFAULT DENY security model for LLM tool execution:
 * - All tools denied by default unless explicitly allowed
 * - Scopes define what operations are permitted
 * - Rate limiting per scope
 * - Confirmation requirements for destructive operations
 *
 * SECURITY PRINCIPLE: Defense in depth
 * Even if prompt injection succeeds, scope limits the damage.
 *
 * @see docs/SECURITY_THREAT_MODEL.md
 */

import { logAuditEntry } from "../../security/auditLog";

// ============================================================================
// TYPES
// ============================================================================

/**
 * Tool risk classification
 */
export type ToolRisk = "read" | "create" | "modify" | "delete" | "system" | "network";

/**
 * Defines what an LLM agent can do within a scope
 */
export interface AgentScope {
  /** Unique identifier for this scope */
  name: string;

  /** Human-readable description */
  description: string;

  /**
   * Tools explicitly ALLOWED in this scope
   * Use "*" to allow all tools (dangerous!)
   */
  allowedTools: Set<string>;

  /**
   * Tools explicitly DENIED in this scope (overrides allowedTools)
   * Use "*" to deny all by default
   */
  deniedTools: Set<string>;

  /**
   * File system access level
   * - "none": No file access
   * - "project-only": Only files within project directory
   * - "read-only": Can read files but not write
   * - "full": Full file access (dangerous!)
   */
  fileAccess: "none" | "project-only" | "read-only" | "full";

  /**
   * Allowed directories for file operations (relative to project root)
   */
  allowedPaths: string[];

  /** Can create new layers */
  canCreateLayers: boolean;

  /** Can delete existing layers */
  canDeleteLayers: boolean;

  /** Maximum layers that can be created in one operation */
  maxLayersPerOperation: number;

  /** Can modify expression code */
  canModifyExpressions: boolean;

  /** Can export projects */
  canExport: boolean;

  /** Maximum keyframes per operation */
  maxKeyframesPerOperation: number;

  /** Maximum operations per minute (rate limit) */
  maxOperationsPerMinute: number;

  /**
   * Tools that require user confirmation before execution
   */
  requireConfirmationFor: Set<string>;

  /**
   * Custom validation function for tool calls
   */
  customValidator?: (toolName: string, args: Record<string, unknown>) => boolean;
}

/**
 * Result of checking tool permission
 */
export interface ScopeCheckResult {
  allowed: boolean;
  reason?: string;
  requiresConfirmation?: boolean;
}

// ============================================================================
// SCOPE PRESETS
// ============================================================================

/**
 * Predefined scopes for common use cases
 *
 * SECURITY: "readonly" is the DEFAULT scope
 */
export const SCOPE_PRESETS: Record<string, AgentScope> = {
  /**
   * READONLY: Most restrictive, safe for untrusted prompts
   * Can only query state, cannot modify anything
   */
  readonly: {
    name: "readonly",
    description: "Read-only access - can query but not modify",
    allowedTools: new Set([
      "getProjectState",
      "getLayerInfo",
      "getLayerById",
      "listLayers",
      "getSelectedLayers",
      "getCompositionSettings",
      "getCurrentFrame",
      "getKeyframeAt",
      "getExpression",
    ]),
    deniedTools: new Set(["*"]), // Deny everything else
    fileAccess: "none",
    allowedPaths: [],
    canCreateLayers: false,
    canDeleteLayers: false,
    maxLayersPerOperation: 0,
    canModifyExpressions: false,
    canExport: false,
    maxKeyframesPerOperation: 0,
    maxOperationsPerMinute: 100,
    requireConfirmationFor: new Set(),
  },

  /**
   * LIMITED: Can create and modify, but cannot delete or access files
   * Good for guided creation workflows
   */
  limited: {
    name: "limited",
    description: "Limited access - can create and modify, cannot delete",
    allowedTools: new Set([
      // Read operations
      "getProjectState",
      "getLayerInfo",
      "getLayerById",
      "listLayers",
      "getSelectedLayers",
      "getCompositionSettings",
      "getCurrentFrame",
      "getKeyframeAt",
      "getExpression",
      // Create operations
      "createLayer",
      "createTextLayer",
      "createShapeLayer",
      "createSolidLayer",
      "duplicateLayer",
      // Modify operations
      "setLayerProperty",
      "setKeyframe",
      "setLayerName",
      "setLayerParent",
      "moveLayer",
      "selectLayer",
      "deselectAll",
    ]),
    deniedTools: new Set([
      "deleteLayer",
      "deleteAllLayers",
      "deleteKeyframe",
      "deleteAllKeyframes",
      "readFile",
      "writeFile",
      "executeExpression",
      "runCommand",
      "decomposeImage",
      "vectorizeImage",
    ]),
    fileAccess: "none",
    allowedPaths: [],
    canCreateLayers: true,
    canDeleteLayers: false,
    maxLayersPerOperation: 10,
    canModifyExpressions: false,
    canExport: false,
    maxKeyframesPerOperation: 100,
    maxOperationsPerMinute: 50,
    requireConfirmationFor: new Set(["createLayer", "duplicateLayer"]),
  },

  /**
   * STANDARD: Normal operation level for trusted use
   * Can create, modify, delete with confirmations
   */
  standard: {
    name: "standard",
    description: "Standard access - full editing with confirmations for destructive ops",
    allowedTools: new Set([
      // Read operations
      "getProjectState",
      "getLayerInfo",
      "getLayerById",
      "listLayers",
      "getSelectedLayers",
      "getCompositionSettings",
      "getCurrentFrame",
      "getKeyframeAt",
      "getExpression",
      // Create operations
      "createLayer",
      "createTextLayer",
      "createShapeLayer",
      "createSolidLayer",
      "createCameraLayer",
      "createLightLayer",
      "duplicateLayer",
      // Modify operations
      "setLayerProperty",
      "setKeyframe",
      "setLayerName",
      "setLayerParent",
      "moveLayer",
      "selectLayer",
      "deselectAll",
      "setExpression",
      // Delete operations (require confirmation)
      "deleteLayer",
      "deleteKeyframe",
      // Export (require confirmation)
      "exportProject",
    ]),
    deniedTools: new Set([
      "deleteAllLayers",
      "deleteAllKeyframes",
      "readFile",
      "writeFile",
      "runCommand",
      "decomposeImage",
      "vectorizeImage",
    ]),
    fileAccess: "project-only",
    allowedPaths: ["assets", "exports"],
    canCreateLayers: true,
    canDeleteLayers: true,
    maxLayersPerOperation: 50,
    canModifyExpressions: true,
    canExport: true,
    maxKeyframesPerOperation: 500,
    maxOperationsPerMinute: 30,
    requireConfirmationFor: new Set([
      "deleteLayer",
      "deleteKeyframe",
      "exportProject",
      "setExpression",
    ]),
  },

  /**
   * FULL: Maximum access - for explicit user grant only
   * WARNING: Only enable with explicit user consent!
   */
  full: {
    name: "full",
    description: "Full access - all operations enabled (requires explicit user grant)",
    allowedTools: new Set(["*"]),
    deniedTools: new Set(), // Nothing denied
    fileAccess: "project-only",
    allowedPaths: ["assets", "exports", "cache"],
    canCreateLayers: true,
    canDeleteLayers: true,
    maxLayersPerOperation: 100,
    canModifyExpressions: true,
    canExport: true,
    maxKeyframesPerOperation: 1000,
    maxOperationsPerMinute: 20,
    requireConfirmationFor: new Set([
      "deleteAllLayers",
      "deleteAllKeyframes",
      "writeFile",
      "decomposeImage",
      "vectorizeImage",
    ]),
  },
};

// ============================================================================
// SCOPE MANAGER CLASS
// ============================================================================

/**
 * Manages LLM agent scopes and enforces security policies
 */
export class ScopeManager {
  private currentScope: AgentScope;
  private operationCounts: Map<string, { count: number; resetAt: number }> = new Map();
  private pendingConfirmations: Map<string, { toolName: string; args: Record<string, unknown>; timestamp: number }> = new Map();

  /**
   * Create a new scope manager
   * @param scope - Initial scope (defaults to READONLY for safety)
   */
  constructor(scope: AgentScope = SCOPE_PRESETS.readonly) {
    this.currentScope = scope;
    console.log(`[ScopeManager] Initialized with scope: ${scope.name}`);
  }

  /**
   * Get the current scope
   */
  getScope(): AgentScope {
    return this.currentScope;
  }

  /**
   * Change the current scope
   * @param scope - New scope to apply
   */
  setScope(scope: AgentScope): void {
    const oldScope = this.currentScope.name;
    this.currentScope = scope;
    console.log(`[ScopeManager] Scope changed: ${oldScope} -> ${scope.name}`);

    // Log scope change for audit
    logAuditEntry({
      category: "security_warning",
      severity: "info",
      message: `Scope changed from ${oldScope} to ${scope.name}`,
      metadata: { newScope: scope.name, oldScope },
    });
  }

  /**
   * Set scope by preset name
   * @param presetName - Name of the preset ("readonly", "limited", "standard", "full")
   */
  setScopePreset(presetName: keyof typeof SCOPE_PRESETS): void {
    const preset = SCOPE_PRESETS[presetName];
    if (!preset) {
      console.error(`[ScopeManager] Unknown scope preset: ${presetName}`);
      return;
    }
    this.setScope(preset);
  }

  /**
   * Check if a tool is allowed in the current scope
   */
  checkToolAllowed(toolName: string, args?: Record<string, unknown>): ScopeCheckResult {
    const scope = this.currentScope;

    // 1. Check explicit denial FIRST (overrides allow)
    if (scope.deniedTools.has(toolName) || (scope.deniedTools.has("*") && !scope.allowedTools.has(toolName))) {
      return {
        allowed: false,
        reason: `Tool '${toolName}' is denied in scope '${scope.name}'`,
      };
    }

    // 2. Check explicit allowance
    if (!scope.allowedTools.has(toolName) && !scope.allowedTools.has("*")) {
      return {
        allowed: false,
        reason: `Tool '${toolName}' is not allowed in scope '${scope.name}'`,
      };
    }

    // 3. Check rate limits
    const rateCheck = this.checkRateLimit(toolName);
    if (!rateCheck.allowed) {
      return rateCheck;
    }

    // 4. Check custom validator if present
    if (scope.customValidator && args) {
      if (!scope.customValidator(toolName, args)) {
        return {
          allowed: false,
          reason: `Tool '${toolName}' failed custom validation in scope '${scope.name}'`,
        };
      }
    }

    // 5. Check specific capability restrictions
    const capabilityCheck = this.checkCapabilityRestrictions(toolName, args);
    if (!capabilityCheck.allowed) {
      return capabilityCheck;
    }

    // 6. Check if confirmation is required
    const requiresConfirmation = scope.requireConfirmationFor.has(toolName);

    return {
      allowed: true,
      requiresConfirmation,
    };
  }

  /**
   * Check rate limit for a tool
   */
  private checkRateLimit(toolName: string): ScopeCheckResult {
    const now = Date.now();
    const key = `${this.currentScope.name}:${toolName}`;
    const record = this.operationCounts.get(key);

    if (!record || record.resetAt < now) {
      // Start new rate limit window
      this.operationCounts.set(key, { count: 1, resetAt: now + 60000 });
      return { allowed: true };
    }

    if (record.count >= this.currentScope.maxOperationsPerMinute) {
      return {
        allowed: false,
        reason: `Rate limit exceeded for '${toolName}': ${record.count}/${this.currentScope.maxOperationsPerMinute} per minute`,
      };
    }

    record.count++;
    return { allowed: true };
  }

  /**
   * Check capability-specific restrictions
   */
  private checkCapabilityRestrictions(
    toolName: string,
    args?: Record<string, unknown>,
  ): ScopeCheckResult {
    const scope = this.currentScope;

    // Layer creation check
    if (toolName.includes("create") && toolName.includes("Layer")) {
      if (!scope.canCreateLayers) {
        return {
          allowed: false,
          reason: `Layer creation not allowed in scope '${scope.name}'`,
        };
      }
    }

    // Layer deletion check
    if (toolName.includes("delete") && toolName.includes("Layer")) {
      if (!scope.canDeleteLayers) {
        return {
          allowed: false,
          reason: `Layer deletion not allowed in scope '${scope.name}'`,
        };
      }
    }

    // Expression modification check
    if (toolName === "setExpression" || toolName === "executeExpression") {
      if (!scope.canModifyExpressions) {
        return {
          allowed: false,
          reason: `Expression modification not allowed in scope '${scope.name}'`,
        };
      }
    }

    // Export check
    if (toolName.includes("export")) {
      if (!scope.canExport) {
        return {
          allowed: false,
          reason: `Export not allowed in scope '${scope.name}'`,
        };
      }
    }

    // File access check
    if (toolName === "readFile" || toolName === "writeFile") {
      if (scope.fileAccess === "none") {
        return {
          allowed: false,
          reason: `File access not allowed in scope '${scope.name}'`,
        };
      }

      if (toolName === "writeFile" && scope.fileAccess === "read-only") {
        return {
          allowed: false,
          reason: `Write access not allowed in scope '${scope.name}'`,
        };
      }

      // Check path if provided
      if (args?.path && typeof args.path === "string") {
        if (!this.isPathAllowed(args.path)) {
          return {
            allowed: false,
            reason: `Path '${args.path}' not allowed in scope '${scope.name}'`,
          };
        }
      }
    }

    // Keyframe count check
    if (args?.keyframes && Array.isArray(args.keyframes)) {
      if (args.keyframes.length > scope.maxKeyframesPerOperation) {
        return {
          allowed: false,
          reason: `Too many keyframes (${args.keyframes.length} > ${scope.maxKeyframesPerOperation}) for scope '${scope.name}'`,
        };
      }
    }

    return { allowed: true };
  }

  /**
   * Check if a file path is allowed in current scope
   */
  private isPathAllowed(path: string): boolean {
    const scope = this.currentScope;

    if (scope.fileAccess === "none") {
      return false;
    }

    // Normalize path
    const normalizedPath = path.replace(/\\/g, "/").toLowerCase();

    // Check for path traversal
    if (normalizedPath.includes("..")) {
      return false;
    }

    // Check against allowed paths
    if (scope.allowedPaths.length > 0) {
      return scope.allowedPaths.some((allowed) =>
        normalizedPath.startsWith(allowed.toLowerCase()),
      );
    }

    return scope.fileAccess === "full";
  }

  /**
   * Check if a tool requires confirmation
   */
  requiresConfirmation(toolName: string): boolean {
    return this.currentScope.requireConfirmationFor.has(toolName);
  }

  /**
   * Request confirmation for a tool call
   * Returns a confirmation ID that must be used to confirm
   */
  requestConfirmation(
    toolName: string,
    args: Record<string, unknown>,
  ): string {
    const confirmationId = `confirm-${Date.now()}-${Math.random().toString(36).slice(2)}`;
    this.pendingConfirmations.set(confirmationId, {
      toolName,
      args,
      timestamp: Date.now(),
    });
    return confirmationId;
  }

  /**
   * Confirm a pending tool call
   */
  confirmToolCall(confirmationId: string): { toolName: string; args: Record<string, unknown> } | null {
    const pending = this.pendingConfirmations.get(confirmationId);
    if (!pending) {
      return null;
    }

    // Check if confirmation is still valid (5 minute timeout)
    if (Date.now() - pending.timestamp > 5 * 60 * 1000) {
      this.pendingConfirmations.delete(confirmationId);
      return null;
    }

    this.pendingConfirmations.delete(confirmationId);
    return { toolName: pending.toolName, args: pending.args };
  }

  /**
   * Cancel a pending confirmation
   */
  cancelConfirmation(confirmationId: string): boolean {
    return this.pendingConfirmations.delete(confirmationId);
  }

  /**
   * Clear expired confirmations
   */
  cleanupExpiredConfirmations(): void {
    const now = Date.now();
    const expiry = 5 * 60 * 1000; // 5 minutes

    for (const [id, pending] of this.pendingConfirmations) {
      if (now - pending.timestamp > expiry) {
        this.pendingConfirmations.delete(id);
      }
    }
  }

  /**
   * Get statistics about current rate limits
   */
  getRateLimitStats(): Record<string, { count: number; limit: number; resetsIn: number }> {
    const now = Date.now();
    const stats: Record<string, { count: number; limit: number; resetsIn: number }> = {};

    for (const [key, record] of this.operationCounts) {
      if (record.resetAt > now) {
        stats[key] = {
          count: record.count,
          limit: this.currentScope.maxOperationsPerMinute,
          resetsIn: record.resetAt - now,
        };
      }
    }

    return stats;
  }
}

// ============================================================================
// SINGLETON INSTANCE
// ============================================================================

/**
 * Global scope manager instance
 * Initialize with readonly scope for safety
 */
export const scopeManager = new ScopeManager(SCOPE_PRESETS.readonly);

// ============================================================================
// CONVENIENCE FUNCTIONS
// ============================================================================

/**
 * Quick check if a tool is allowed
 */
export function isToolAllowed(toolName: string, args?: Record<string, unknown>): boolean {
  return scopeManager.checkToolAllowed(toolName, args).allowed;
}

/**
 * Get the current scope name
 */
export function getCurrentScopeName(): string {
  return scopeManager.getScope().name;
}

/**
 * Elevate scope with user consent
 * @param targetScope - Scope to elevate to
 * @param reason - Why elevation is needed
 */
export function requestScopeElevation(
  targetScope: keyof typeof SCOPE_PRESETS,
  reason: string,
): { requiresConsent: true; targetScope: string; reason: string } {
  console.log(`[ScopeManager] Scope elevation requested: ${scopeManager.getScope().name} -> ${targetScope}`);
  console.log(`[ScopeManager] Reason: ${reason}`);

  return {
    requiresConsent: true,
    targetScope,
    reason,
  };
}
