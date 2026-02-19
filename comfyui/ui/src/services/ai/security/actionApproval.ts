/**
 * Action Approval System
 *
 * Approval gate system that requires explicit user approval for ALL agent actions.
 * Default deny pattern: No actions execute without approval.
 *
 * SECURITY: This is the primary defense against unauthorized agent actions.
 * Every agent action must be reviewed and approved by the user before execution.
 *
 * Architecture:
 * 1. Agent plans actions (with reasoning)
 * 2. Actions are queued for approval
 * 3. User reviews action plan
 * 4. User approves/denies/modifies scope
 * 5. Approved actions execute
 */

import type { JSONValue } from "@/types/dataAsset";
import type { ToolCall } from "../toolDefinitions";
import { logAuditEntry, logUserConfirmation, type AuditLogMetadata } from "../../security/auditLog";
import { uuid5, UUID5_NAMESPACES } from "@/utils/uuid5";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

export interface ActionPlan {
  /** Unique plan ID */
  id: string;
  /** Session ID */
  sessionId: string;
  /** User instruction that triggered this plan */
  userInstruction: string;
  /** Agent reasoning for this plan */
  reasoning: string;
  /** Planned actions */
  actions: PlannedAction[];
  /** When plan was created */
  createdAt: number;
  /** When plan expires */
  expiresAt: number;
  /** Current status */
  status: "pending" | "approved" | "denied" | "expired";
  /** When plan was approved/denied */
  decidedAt?: number;
  /** Who decided (user/system) */
  decidedBy?: "user" | "system";
  /** Additional metadata */
  metadata?: Record<string, JSONValue>;
}

export interface PlannedAction {
  /** Unique action ID */
  id: string;
  /** Tool call */
  toolCall: ToolCall;
  /** Reasoning for this specific action */
  reasoning: string;
  /** Whether this action requires approval */
  requiresApproval: boolean;
  /** Scope required for this action */
  requiredScope?: string;
}

export interface ApprovalDecision {
  /** Plan ID */
  planId: string;
  /** Whether plan was approved */
  approved: boolean;
  /** Which actions were approved (if partial) */
  approvedActionIds?: string[];
  /** Modified scope (if user changed scope) */
  modifiedScope?: string;
  /** User comment */
  comment?: string;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                                // constants
// ═══════════════════════════════════════════════════════════════════════════

/** How long action plans last before expiring (5 minutes) */
const ACTION_PLAN_TTL_MS = 5 * 60 * 1000;

// ═══════════════════════════════════════════════════════════════════════════
//                                            // action // approval // manager
// ═══════════════════════════════════════════════════════════════════════════

class ActionApprovalManager {
  private plans: Map<string, ActionPlan> = new Map();
  private sessionPlans: Map<string, string[]> = new Map(); // sessionId -> planIds[]

  /**
   * Create an action plan for user review
   * This is called BEFORE any actions execute
   */
  public createActionPlan(
    sessionId: string,
    userInstruction: string,
    reasoning: string,
    toolCalls: ToolCall[],
    actionReasonings: string[] = [],
  ): ActionPlan {
    const now = Date.now();
    const planId = uuid5(`plan-${sessionId}-${now}`, UUID5_NAMESPACES.OID);

    const actions: PlannedAction[] = toolCalls.map((call, index) => ({
      id: uuid5(`action-${planId}-${index}`, UUID5_NAMESPACES.OID),
      toolCall: call,
      reasoning: actionReasonings[index] || `Execute ${call.name} to fulfill user request`,
      requiresApproval: true, // ALL actions require approval by default
      requiredScope: undefined, // Will be determined by scope manager
    }));

    const plan: ActionPlan = {
      id: planId,
      sessionId,
      userInstruction,
      reasoning,
      actions,
      createdAt: now,
      expiresAt: now + ACTION_PLAN_TTL_MS,
      status: "pending",
    };

    this.plans.set(planId, plan);

    // Track by session
    if (!this.sessionPlans.has(sessionId)) {
      this.sessionPlans.set(sessionId, []);
    }
    this.sessionPlans.get(sessionId)!.push(planId);

    logAuditEntry({
      category: "security_warning",
      severity: "info",
      message: `Action plan created: ${planId} (${actions.length} actions)`,
      metadata: {
        planId,
        sessionId,
        actionCount: actions.length,
        userInstruction: userInstruction.substring(0, 100),
        reasoning: reasoning.substring(0, 200),
      },
    });

    return plan;
  }

  /**
   * Get action plan by ID
   */
  public getActionPlan(planId: string): ActionPlan | null {
    const plan = this.plans.get(planId);
    if (!plan) return null;

    // Check expiry
    if (Date.now() > plan.expiresAt && plan.status === "pending") {
      plan.status = "expired";
      plan.decidedAt = Date.now();
      plan.decidedBy = "system";
    }

    return plan;
  }

  /**
   * Get pending action plans for a session
   */
  public getPendingPlans(sessionId: string): ActionPlan[] {
    const planIds = this.sessionPlans.get(sessionId) || [];
    const plans = planIds
      .map((id) => this.plans.get(id))
      .filter((p): p is ActionPlan => p !== undefined && p.status === "pending");

    // Check expiry
    const now = Date.now();
    for (const plan of plans) {
      if (now > plan.expiresAt) {
        plan.status = "expired";
        plan.decidedAt = now;
        plan.decidedBy = "system";
      }
    }

    return plans.filter((p) => p.status === "pending");
  }

  /**
   * Approve an action plan
   * Returns approved actions that can be executed
   */
  public approvePlan(decision: ApprovalDecision): PlannedAction[] {
    const plan = this.plans.get(decision.planId);
    if (!plan) {
      throw new Error(`[ActionApproval] Plan "${decision.planId}" not found`);
    }

    if (plan.status !== "pending") {
      throw new Error(`[ActionApproval] Plan "${decision.planId}" is not pending (status: ${plan.status})`);
    }

    if (Date.now() > plan.expiresAt) {
      plan.status = "expired";
      plan.decidedAt = Date.now();
      plan.decidedBy = "system";
      throw new Error(`[ActionApproval] Plan "${decision.planId}" has expired`);
    }

    plan.status = decision.approved ? "approved" : "denied";
    plan.decidedAt = Date.now();
    plan.decidedBy = "user";

    if (decision.modifiedScope) {
      // Store modified scope for execution
      plan.metadata = { ...plan.metadata, modifiedScope: decision.modifiedScope };
    }

    logUserConfirmation(`plan:${decision.planId}`, decision.approved);
    logAuditEntry({
      category: "user_confirmation",
      severity: decision.approved ? "info" : "warning",
      message: `Action plan ${decision.approved ? "APPROVED" : "DENIED"}: ${decision.planId}`,
      metadata: {
        planId: decision.planId,
        sessionId: plan.sessionId,
        actionCount: plan.actions.length,
        approvedActionCount: decision.approvedActionIds?.length || plan.actions.length,
        comment: decision.comment,
      },
    });

    if (!decision.approved) {
      return [];
    }

    // Return approved actions
    // Deterministic: Explicit null check before accessing property
    if (decision.approvedActionIds) {
      // Partial approval
      // Type guard ensures approvedActionIds is defined here
      const approvedIds = decision.approvedActionIds;
      return plan.actions.filter((a) => approvedIds.includes(a.id));
    }

    // Full approval
    return plan.actions;
  }

  /**
   * Deny an action plan
   */
  public denyPlan(planId: string, reason?: string): void {
    const plan = this.plans.get(planId);
    if (!plan) {
      throw new Error(`[ActionApproval] Plan "${planId}" not found`);
    }

    plan.status = "denied";
    plan.decidedAt = Date.now();
    plan.decidedBy = "user";

    logUserConfirmation(`plan:${planId}`, false);
    logAuditEntry({
      category: "user_confirmation",
      severity: "warning",
      message: `Action plan DENIED: ${planId}`,
      metadata: {
        planId,
        sessionId: plan.sessionId,
        reason,
      },
    });
  }

  /**
   * Check if an action plan exists and is approved
   */
  public isPlanApproved(planId: string): boolean {
    const plan = this.plans.get(planId);
    if (!plan) return false;

    if (plan.status === "approved") {
      // Check expiry
      if (Date.now() > plan.expiresAt) {
        plan.status = "expired";
        return false;
      }
      return true;
    }

    return false;
  }

  /**
   * Get all plans for a session (for UI display)
   */
  public getSessionPlans(sessionId: string): ActionPlan[] {
    const planIds = this.sessionPlans.get(sessionId) || [];
    return planIds
      .map((id) => this.plans.get(id))
      .filter((p): p is ActionPlan => p !== undefined);
  }

  /**
   * Cleanup expired plans
   */
  public cleanupExpiredPlans(): void {
    const now = Date.now();
    for (const plan of this.plans.values()) {
      if (plan.status === "pending" && now > plan.expiresAt) {
        plan.status = "expired";
        plan.decidedAt = now;
        plan.decidedBy = "system";
      }
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // singleton // export
// ═══════════════════════════════════════════════════════════════════════════

export const actionApproval = new ActionApprovalManager();
