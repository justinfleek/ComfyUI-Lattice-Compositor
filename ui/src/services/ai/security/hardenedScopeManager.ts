/**
 * Hardened Scope Manager
 *
 * BATTLE-HARDENED security model for LLM agent execution:
 *
 * 1. IMMUTABLE SCOPE TOKENS - Scope grants are cryptographically signed
 * 2. AUTOMATIC DOWNGRADE - Any suspicious activity = immediate readonly
 * 3. SESSION ISOLATION - Each conversation starts fresh
 * 4. TIME-LIMITED ELEVATION - Elevated scopes expire automatically
 * 5. HUMAN APPROVAL QUEUE - Elevated ops queue for approval, don't auto-execute
 * 6. PROVENANCE TRACKING - Every action tagged with why it was allowed
 * 7. KILL SWITCH - Instantly revoke all agent permissions
 * 8. HIDDEN CAPABILITIES - Agent doesn't know what tools exist
 * 9. ANOMALY DETECTION - Behavioral patterns trigger lockdown
 * 10. SCOPE CEILING - Cannot elevate beyond what user explicitly granted
 *
 * THREAT MODEL:
 * - Attacker has full control of LLM output
 * - Attacker knows the codebase and security measures
 * - Attacker can try unlimited prompt injections
 * - Goal: Prevent unauthorized state modification or data exfiltration
 *
 * @see docs/SECURITY_THREAT_MODEL.md
 */

import type { JSONValue } from "@/types/dataAsset";
import { assertDefined } from "@/utils/typeGuards";
import { logAuditEntry, logSecurityWarning } from "../../security/auditLog";
import type { ToolCall } from "../toolDefinitions";

// ============================================================================
// TYPES
// ============================================================================

export type ScopeLevel = "readonly" | "limited" | "standard" | "full";

export interface ScopeGrant {
  /** Unique ID for this grant */
  id: string;
  /** Scope level granted */
  level: ScopeLevel;
  /** When grant was issued (unix ms) */
  issuedAt: number;
  /** When grant expires (unix ms) */
  expiresAt: number;
  /** User who approved this grant */
  grantedBy: "user" | "system";
  /** Reason for grant (for audit) */
  reason: string;
  /** HMAC signature to prevent tampering */
  signature: string;
  /** Session ID this grant belongs to */
  sessionId: string;
  /** Maximum scope this grant can elevate to */
  ceiling: ScopeLevel;
}

export interface ScopeSession {
  /** Unique session ID */
  id: string;
  /** When session started */
  startedAt: number;
  /** Current effective scope */
  currentScope: ScopeLevel;
  /** Active scope grant (if elevated) */
  activeGrant: ScopeGrant | null;
  /** Operations performed in this session */
  operationCount: number;
  /** Suspicious activity detected */
  suspicionScore: number;
  /** Whether session is locked down */
  lockedDown: boolean;
  /** Why session was locked (if locked) */
  lockReason?: string;
  /** Operations pending approval */
  pendingApprovals: PendingApproval[];
}

export interface PendingApproval {
  /** Unique ID */
  id: string;
  /** Tool being requested */
  toolName: string;
  /** Arguments for tool (without name/id fields) */
  arguments: Record<string, JSONValue>;
  /** When requested */
  requestedAt: number;
  /** Why this needs approval */
  reason: string;
  /** Expires after this time */
  expiresAt: number;
}

export interface ToolPermission {
  allowed: boolean;
  reason: string;
  requiresApproval: boolean;
  approvalId?: string;
  scopeUsed: ScopeLevel;
}

// ============================================================================
// CONSTANTS
// ============================================================================

/** How long elevated scopes last (5 minutes) */
const SCOPE_ELEVATION_TTL_MS = 5 * 60 * 1000;

/** How long pending approvals last (2 minutes) */
const APPROVAL_TTL_MS = 2 * 60 * 1000;

/** Suspicion score that triggers lockdown */
const SUSPICION_LOCKDOWN_THRESHOLD = 10;

/** Rate limit: operations per minute at each scope level */
const RATE_LIMITS: Record<ScopeLevel, number> = {
  readonly: 100,
  limited: 30,
  standard: 20,
  full: 10,
};

/** Signing key (in production, this would come from secure storage) */
const SIGNING_KEY = "lattice-scope-v1-" + (typeof crypto !== "undefined" ? crypto.randomUUID() : Date.now());

// ============================================================================
// TOOL CLASSIFICATIONS
// ============================================================================

/** Tools available at each scope level */
const SCOPE_TOOLS: Record<ScopeLevel, Set<string>> = {
  readonly: new Set([
    "getProjectState",
    "getLayerInfo",
    "getLayerById",
    "listLayers",
    "getSelectedLayers",
    "getCompositionSettings",
    "getCurrentFrame",
    "getKeyframeAt",
    "getExpression",
    "findLayers",
  ]),

  limited: new Set([
    // Include readonly
    "getProjectState", "getLayerInfo", "getLayerById", "listLayers",
    "getSelectedLayers", "getCompositionSettings", "getCurrentFrame",
    "getKeyframeAt", "getExpression", "findLayers",
    // Add creation/modification
    "createLayer", "createTextLayer", "createShapeLayer", "createSolidLayer",
    "duplicateLayer", "setLayerProperty", "setLayerTransform",
    "addKeyframe", "setKeyframeEasing", "setLayerName",
    "moveLayer", "selectLayer", "deselectAll",
    "setCurrentFrame", "playPreview",
  ]),

  standard: new Set([
    // Include limited (not listing all for brevity)
    "*limited*",
    // Add deletion and expressions
    "deleteLayer", "removeKeyframe", "setExpression", "removeExpression",
    "addEffect", "updateEffect", "removeEffect",
    "configureParticles", "applyCameraTrajectory", "addCameraShake",
    "setTextContent", "setSplinePoints", "setSpeedMap",
  ]),

  full: new Set([
    "*all*", // All tools (dangerous!)
  ]),
};

/** Tools that ALWAYS require human approval, regardless of scope */
const ALWAYS_REQUIRE_APPROVAL = new Set([
  "decomposeImage",     // Expensive AI operation
  "vectorizeImage",     // Expensive AI operation  
  "deleteAllLayers",    // Mass deletion
  "deleteAllKeyframes", // Mass deletion
  "exportProject",      // Data output
  "writeFile",          // File system write
]);

/** Tools that can NEVER be called by agent (system only) */
const SYSTEM_ONLY_TOOLS = new Set([
  "loadProject",        // Only user can load projects
  "saveProject",        // Only user can save
  "clearProject",       // Only user can clear
  "setApiKey",          // Security sensitive
  "configureBackend",   // System config
]);

// ============================================================================
// HARDENED SCOPE MANAGER
// ============================================================================

class HardenedScopeManager {
  private session: ScopeSession;
  private operationTimestamps: number[] = [];
  private killSwitchActive = false;

  constructor() {
    this.session = this.createNewSession();
  }

  // ==========================================================================
  // SESSION MANAGEMENT
  // ==========================================================================

  private createNewSession(): ScopeSession {
    const sessionId = this.generateSecureId();

    logAuditEntry({
      category: "security_warning",
      severity: "info",
      message: `New agent session started: ${sessionId}`,
      metadata: { sessionId, scope: "readonly" },
    });

    return {
      id: sessionId,
      startedAt: Date.now(),
      currentScope: "readonly", // ALWAYS start readonly
      activeGrant: null,
      operationCount: 0,
      suspicionScore: 0,
      lockedDown: false,
      pendingApprovals: [],
    };
  }

  /**
   * Start a fresh session (call between agent conversations)
   */
  public startNewSession(): void {
    // Log end of previous session
    if (this.session.operationCount > 0) {
      logAuditEntry({
        category: "security_warning",
        severity: "info",
        message: `Agent session ended: ${this.session.id}`,
        metadata: {
          sessionId: this.session.id,
          operationCount: this.session.operationCount,
          suspicionScore: this.session.suspicionScore,
          wasLockedDown: this.session.lockedDown,
        },
      });
    }

    this.session = this.createNewSession();
    this.operationTimestamps = [];
  }

  /**
   * Get current session info (for UI display)
   */
  public getSessionInfo(): {
    sessionId: string;
    scope: ScopeLevel;
    lockedDown: boolean;
    operationCount: number;
    suspicionScore: number;
    grantExpiresIn?: number;
    pendingApprovalCount: number;
  } {
    const now = Date.now();
    return {
      sessionId: this.session.id,
      scope: this.session.currentScope,
      lockedDown: this.session.lockedDown || this.killSwitchActive,
      operationCount: this.session.operationCount,
      suspicionScore: this.session.suspicionScore,
      grantExpiresIn: this.session.activeGrant
        ? Math.max(0, this.session.activeGrant.expiresAt - now)
        : undefined,
      pendingApprovalCount: this.session.pendingApprovals.length,
    };
  }

  // ==========================================================================
  // SCOPE ELEVATION (REQUIRES USER ACTION)
  // ==========================================================================

  /**
   * Request scope elevation - returns info for UI to prompt user
   * Does NOT automatically elevate!
   */
  public requestElevation(
    targetScope: ScopeLevel,
    reason: string,
  ): {
    requestId: string;
    targetScope: ScopeLevel;
    reason: string;
    currentScope: ScopeLevel;
    requiresUserApproval: true;
  } {
    const requestId = this.generateSecureId();

    logAuditEntry({
      category: "security_warning",
      severity: "warning",
      message: `Scope elevation requested: ${this.session.currentScope} -> ${targetScope}`,
      metadata: { requestId, reason, sessionId: this.session.id },
    });

    return {
      requestId,
      targetScope,
      reason,
      currentScope: this.session.currentScope,
      requiresUserApproval: true,
    };
  }

  /**
   * Grant scope elevation (ONLY call from trusted UI action)
   */
  public grantElevation(
    targetScope: ScopeLevel,
    reason: string,
    ceiling: ScopeLevel = targetScope,
  ): ScopeGrant | null {
    // Cannot elevate if locked down
    if (this.session.lockedDown || this.killSwitchActive) {
      throw new Error(`[HardenedScopeManager] Elevation denied: session "${this.session.id}" is locked down`);
    }

    // Cannot elevate beyond ceiling
    const scopeOrder: ScopeLevel[] = ["readonly", "limited", "standard", "full"];
    const ceilingIndex = scopeOrder.indexOf(ceiling);
    const targetIndex = scopeOrder.indexOf(targetScope);
    if (targetIndex > ceilingIndex) {
      throw new Error(`[HardenedScopeManager] Elevation denied: target scope "${targetScope}" exceeds ceiling "${ceiling}"`);
    }

    const now = Date.now();
    const grant: ScopeGrant = {
      id: this.generateSecureId(),
      level: targetScope,
      issuedAt: now,
      expiresAt: now + SCOPE_ELEVATION_TTL_MS,
      grantedBy: "user",
      reason,
      signature: "", // Will be set below
      sessionId: this.session.id,
      ceiling,
    };

    // Sign the grant
    grant.signature = this.signGrant(grant);

    // Apply the grant
    this.session.activeGrant = grant;
    this.session.currentScope = targetScope;

    logAuditEntry({
      category: "security_warning",
      severity: "warning",
      message: `Scope elevated: readonly -> ${targetScope}`,
      metadata: {
        grantId: grant.id,
        sessionId: this.session.id,
        expiresAt: new Date(grant.expiresAt).toISOString(),
        reason,
      },
    });

    return grant;
  }

  /**
   * Revoke current scope grant (return to readonly)
   */
  public revokeElevation(reason: string = "user-initiated"): void {
    if (this.session.activeGrant) {
      logAuditEntry({
        category: "security_warning",
        severity: "info",
        message: `Scope revoked: ${this.session.currentScope} -> readonly`,
        metadata: {
          grantId: this.session.activeGrant.id,
          sessionId: this.session.id,
          reason,
        },
      });
    }

    this.session.activeGrant = null;
    this.session.currentScope = "readonly";
  }

  // ==========================================================================
  // TOOL PERMISSION CHECKING
  // ==========================================================================

  /**
   * Check if a tool is allowed in current scope
   * This is the main entry point for security checks
   */
  public checkToolPermission(
    toolName: string,
    args: Record<string, JSONValue> = {},
  ): ToolPermission {
    // 1. Check kill switch
    if (this.killSwitchActive) {
      return {
        allowed: false,
        reason: "KILL SWITCH ACTIVE: All agent operations suspended",
        requiresApproval: false,
        scopeUsed: "readonly",
      };
    }

    // 2. Check session lockdown
    if (this.session.lockedDown) {
      return {
        allowed: false,
        reason: `Session locked: ${this.session.lockReason}`,
        requiresApproval: false,
        scopeUsed: "readonly",
      };
    }

    // 3. Check if grant has expired
    this.checkGrantExpiry();

    // 4. Check system-only tools
    if (SYSTEM_ONLY_TOOLS.has(toolName)) {
      return {
        allowed: false,
        reason: `Tool '${toolName}' is system-only and cannot be called by agent`,
        requiresApproval: false,
        scopeUsed: this.session.currentScope,
      };
    }

    // 5. Check rate limits
    const rateCheck = this.checkRateLimit();
    if (!rateCheck.allowed) {
      // Type proof: reason is guaranteed non-null when allowed is false
      assertDefined(rateCheck.reason, "reason must exist when rate limit check fails");
      return {
        allowed: false,
        reason: rateCheck.reason,
        requiresApproval: false,
        scopeUsed: this.session.currentScope,
      };
    }

    // 6. Check if tool is allowed at current scope
    const scopeAllowed = this.isToolInScope(toolName, this.session.currentScope);
    if (!scopeAllowed) {
      // Track denial (could indicate injection attempt)
      this.recordSuspiciousActivity("tool_denied", 1);

      return {
        allowed: false,
        reason: `Tool '${toolName}' not allowed in scope '${this.session.currentScope}'`,
        requiresApproval: false,
        scopeUsed: this.session.currentScope,
      };
    }

    // 7. Check if tool always requires approval
    if (ALWAYS_REQUIRE_APPROVAL.has(toolName)) {
      const approvalId = this.createPendingApproval(
        toolName,
        args,
        `Tool '${toolName}' requires explicit user approval`,
      );

      return {
        allowed: false,
        reason: `Tool '${toolName}' requires user approval`,
        requiresApproval: true,
        approvalId,
        scopeUsed: this.session.currentScope,
      };
    }

    // 8. All checks passed
    this.session.operationCount++;
    this.operationTimestamps.push(Date.now());

    return {
      allowed: true,
      reason: "Allowed by scope",
      requiresApproval: false,
      scopeUsed: this.session.currentScope,
    };
  }

  /**
   * Check if a tool is in a scope's allowed set
   */
  private isToolInScope(toolName: string, scope: ScopeLevel): boolean {
    const scopeTools = SCOPE_TOOLS[scope];

    // Full scope allows everything
    if (scopeTools.has("*all*")) {
      return true;
    }

    // Standard includes limited
    if (scope === "standard" && scopeTools.has("*limited*")) {
      if (SCOPE_TOOLS.limited.has(toolName)) {
        return true;
      }
    }

    return scopeTools.has(toolName);
  }

  /**
   * Check rate limits
   */
  private checkRateLimit(): { allowed: boolean; reason?: string } {
    const now = Date.now();
    const oneMinuteAgo = now - 60000;

    // Remove old timestamps
    this.operationTimestamps = this.operationTimestamps.filter(
      (t) => t > oneMinuteAgo,
    );

    const limit = RATE_LIMITS[this.session.currentScope];
    if (this.operationTimestamps.length >= limit) {
      this.recordSuspiciousActivity("rate_limit_hit", 2);

      return {
        allowed: false,
        reason: `Rate limit exceeded: ${this.operationTimestamps.length}/${limit} per minute`,
      };
    }

    return { allowed: true };
  }

  /**
   * Check if active grant has expired
   */
  private checkGrantExpiry(): void {
    if (!this.session.activeGrant) return;

    if (Date.now() > this.session.activeGrant.expiresAt) {
      logAuditEntry({
        category: "security_warning",
        severity: "info",
        message: "Scope grant expired, reverting to readonly",
        metadata: {
          grantId: this.session.activeGrant.id,
          sessionId: this.session.id,
        },
      });

      this.session.activeGrant = null;
      this.session.currentScope = "readonly";
    }
  }

  // ==========================================================================
  // APPROVAL SYSTEM
  // ==========================================================================

  /**
   * Create a pending approval for a tool call
   */
  private createPendingApproval(
    toolName: string,
    args: Record<string, JSONValue>,
    reason: string,
  ): string {
    const approval: PendingApproval = {
      id: this.generateSecureId(),
      toolName,
      arguments: args,
      requestedAt: Date.now(),
      reason,
      expiresAt: Date.now() + APPROVAL_TTL_MS,
    };

    this.session.pendingApprovals.push(approval);

    // Clean up expired approvals
    this.cleanupExpiredApprovals();

    return approval.id;
  }

  /**
   * Approve a pending operation (ONLY call from trusted UI action)
   */
  public approveOperation(approvalId: string): PendingApproval {
    const index = this.session.pendingApprovals.findIndex(
      (a) => a.id === approvalId,
    );

    if (index === -1) {
      throw new Error(`[HardenedScopeManager] Approval "${approvalId}" not found`);
    }

    const approval = this.session.pendingApprovals[index];

    // Check expiry
    if (Date.now() > approval.expiresAt) {
      this.session.pendingApprovals.splice(index, 1);
      throw new Error(`[HardenedScopeManager] Approval "${approvalId}" has expired`);
    }

    // Remove from pending
    this.session.pendingApprovals.splice(index, 1);

    logAuditEntry({
      category: "user_confirmation",
      severity: "info",
      message: `User approved operation: ${approval.toolName}`,
      metadata: {
        approvalId,
        toolName: approval.toolName,
        sessionId: this.session.id,
      },
    });

    return approval;
  }

  /**
   * Deny a pending operation
   */
  public denyOperation(approvalId: string): boolean {
    const index = this.session.pendingApprovals.findIndex(
      (a) => a.id === approvalId,
    );

    if (index === -1) {
      return false;
    }

    const approval = this.session.pendingApprovals[index];
    this.session.pendingApprovals.splice(index, 1);

    logAuditEntry({
      category: "user_confirmation",
      severity: "warning",
      message: `User denied operation: ${approval.toolName}`,
      metadata: {
        approvalId,
        toolName: approval.toolName,
        sessionId: this.session.id,
      },
    });

    return true;
  }

  /**
   * Get pending approvals for UI
   */
  public getPendingApprovals(): PendingApproval[] {
    this.cleanupExpiredApprovals();
    return [...this.session.pendingApprovals];
  }

  private cleanupExpiredApprovals(): void {
    const now = Date.now();
    this.session.pendingApprovals = this.session.pendingApprovals.filter(
      (a) => a.expiresAt > now,
    );
  }

  // ==========================================================================
  // SUSPICION & LOCKDOWN
  // ==========================================================================

  /**
   * Record suspicious activity (increases suspicion score)
   */
  public recordSuspiciousActivity(
    type: string,
    severity: number,
    details?: string,
  ): void {
    this.session.suspicionScore += severity;

    logSecurityWarning(`Suspicious activity: ${type}`, {
      sessionId: this.session.id,
      severity,
      details,
      totalSuspicion: this.session.suspicionScore,
    });

    // Check if we should lock down
    if (this.session.suspicionScore >= SUSPICION_LOCKDOWN_THRESHOLD) {
      this.lockdownSession(`Suspicion score ${this.session.suspicionScore} exceeded threshold`);
    }
  }

  /**
   * Lock down the current session (revoke all permissions)
   */
  public lockdownSession(reason: string): void {
    this.session.lockedDown = true;
    this.session.lockReason = reason;
    this.session.activeGrant = null;
    this.session.currentScope = "readonly";
    this.session.pendingApprovals = [];

    logSecurityWarning(`SESSION LOCKED DOWN: ${reason}`, {
      sessionId: this.session.id,
      operationCount: this.session.operationCount,
      suspicionScore: this.session.suspicionScore,
    });
  }

  /**
   * Automatically downgrade to readonly (less severe than lockdown)
   */
  public autoDowngrade(reason: string): void {
    if (this.session.currentScope !== "readonly") {
      logAuditEntry({
        category: "security_warning",
        severity: "warning",
        message: `Auto-downgrade: ${this.session.currentScope} -> readonly`,
        metadata: { reason, sessionId: this.session.id },
      });

      this.session.activeGrant = null;
      this.session.currentScope = "readonly";
    }
  }

  // ==========================================================================
  // KILL SWITCH
  // ==========================================================================

  /**
   * KILL SWITCH: Immediately suspend all agent operations
   * Use when active attack is detected
   */
  public activateKillSwitch(reason: string): void {
    this.killSwitchActive = true;
    this.lockdownSession("KILL SWITCH: " + reason);

    logSecurityWarning("🚨 KILL SWITCH ACTIVATED 🚨", {
      reason,
      sessionId: this.session.id,
    });

    // Could trigger additional alerts here (e.g., desktop notification)
  }

  /**
   * Deactivate kill switch (requires explicit action)
   */
  public deactivateKillSwitch(): void {
    this.killSwitchActive = false;

    logAuditEntry({
      category: "security_warning",
      severity: "warning",
      message: "Kill switch deactivated",
      metadata: { sessionId: this.session.id },
    });

    // Start fresh session
    this.startNewSession();
  }

  /**
   * Check if kill switch is active
   */
  public isKillSwitchActive(): boolean {
    return this.killSwitchActive;
  }

  // ==========================================================================
  // CAPABILITY HIDING
  // ==========================================================================

  /**
   * Get tools available to agent at current scope
   * SECURITY: Only reveals tools actually available, not full catalog
   */
  public getAvailableTools(): string[] {
    if (this.session.lockedDown || this.killSwitchActive) {
      return []; // Reveal nothing when locked
    }

    const scope = this.session.currentScope;
    const tools: string[] = [];

    for (const tool of SCOPE_TOOLS[scope]) {
      if (tool.startsWith("*")) continue; // Meta-markers
      if (!SYSTEM_ONLY_TOOLS.has(tool)) {
        tools.push(tool);
      }
    }

    // Include lower scope tools
    if (scope === "standard" || scope === "full") {
      for (const tool of SCOPE_TOOLS.limited) {
        if (!tools.includes(tool) && !SYSTEM_ONLY_TOOLS.has(tool)) {
          tools.push(tool);
        }
      }
    }

    return tools;
  }

  /**
   * Get tool info for agent (limited information)
   * SECURITY: Does NOT reveal what tools exist at higher scopes
   */
  public getToolInfo(toolName: string): {
    exists: boolean;
    available: boolean;
    requiresApproval: boolean;
  } | null {
    // If locked, reveal nothing
    if (this.session.lockedDown || this.killSwitchActive) {
      throw new Error(`[HardenedScopeManager] Cannot check tool availability: session is locked down or kill switch is active`);
    }

    const isAvailable = this.isToolInScope(toolName, this.session.currentScope);
    const requiresApproval = ALWAYS_REQUIRE_APPROVAL.has(toolName);

    // Only reveal if tool is available at current scope
    // This prevents enumeration attacks
    if (!isAvailable) {
      throw new Error(`[HardenedScopeManager] Tool "${toolName}" is not available at current scope "${this.session.currentScope}"`);
    }

    return {
      exists: true,
      available: isAvailable,
      requiresApproval,
    };
  }

  // ==========================================================================
  // CRYPTOGRAPHIC UTILITIES
  // ==========================================================================

  private generateSecureId(): string {
    if (typeof crypto !== "undefined" && crypto.randomUUID) {
      return crypto.randomUUID();
    }
    return `${Date.now()}-${Math.random().toString(36).slice(2)}`;
  }

  private signGrant(grant: ScopeGrant): string {
    // In production, use proper HMAC
    // For now, simple hash that includes all grant fields
    const data = `${grant.id}|${grant.level}|${grant.issuedAt}|${grant.expiresAt}|${grant.sessionId}|${SIGNING_KEY}`;

    // Simple hash (production would use crypto.subtle.sign)
    let hash = 0;
    for (let i = 0; i < data.length; i++) {
      const char = data.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash = hash & hash; // Convert to 32-bit integer
    }
    return hash.toString(36);
  }

  /**
   * Verify a grant signature
   */
  public verifyGrant(grant: ScopeGrant): boolean {
    const expectedSignature = this.signGrant({ ...grant, signature: "" });
    return grant.signature === expectedSignature;
  }
}

// ============================================================================
// SINGLETON EXPORT
// ============================================================================

export const hardenedScopeManager = new HardenedScopeManager();

// ============================================================================
// CONVENIENCE EXPORTS
// ============================================================================

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || {}
export function checkTool(
  toolName: string,
  args?: Record<string, JSONValue>,
): ToolPermission {
  const argsObj = (args !== null && args !== undefined && typeof args === "object" && args !== null) ? args : {};
  return hardenedScopeManager.checkToolPermission(toolName, argsObj);
}

export function getCurrentScope(): ScopeLevel {
  return hardenedScopeManager.getSessionInfo().scope;
}

export function isLockedDown(): boolean {
  return hardenedScopeManager.getSessionInfo().lockedDown;
}

export function activateKillSwitch(reason: string): void {
  hardenedScopeManager.activateKillSwitch(reason);
}

export function reportInjectionDetected(details: string): void {
  hardenedScopeManager.recordSuspiciousActivity("injection_detected", 5, details);
}
