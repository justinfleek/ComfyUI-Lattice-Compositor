/**
 * Agent Rollback System
 *
 * Agent-specific rollback that tracks agent actions separately from user actions.
 * Enables rolling back all agent actions from a session independently of user undo/redo.
 *
 * SECURITY: This allows users to undo agent mistakes without losing their own work.
 *
 * Architecture:
 * 1. Track all agent actions separately
 * 2. Store project state snapshots before each agent action
 * 3. Enable rollback to any point before agent actions
 * 4. Preserve user actions, only rollback agent actions
 */

import type { LatticeProject } from "@/types/project";
import { useProjectStore } from "@/stores/projectStore";
import { logAuditEntry } from "../../security/auditLog";
import { uuid5, UUID5_NAMESPACES } from "@/utils/uuid5";

// ============================================================================
// TYPES
// ============================================================================

export interface AgentAction {
  /** Unique action ID */
  id: string;
  /** Session ID */
  sessionId: string;
  /** Sandbox ID (if executed in sandbox) */
  sandboxId?: string;
  /** Tool name */
  toolName: string;
  /** Tool arguments */
  arguments: Record<string, unknown>;
  /** When action was executed */
  executedAt: number;
  /** Project state BEFORE this action */
  stateBefore: LatticeProject;
  /** Project state AFTER this action */
  stateAfter: LatticeProject;
  /** Whether action succeeded */
  success: boolean;
  /** Reasoning for this action */
  reasoning?: string;
}

export interface RollbackPoint {
  /** Point ID */
  id: string;
  /** Session ID */
  sessionId: string;
  /** Project state at this point */
  projectState: LatticeProject;
  /** When this point was created */
  timestamp: number;
  /** Actions that happened after this point */
  actionsAfter: string[]; // Action IDs
}

// ============================================================================
// AGENT ROLLBACK MANAGER
// ============================================================================

class AgentRollbackManager {
  private actions: Map<string, AgentAction> = new Map();
  private sessionActions: Map<string, string[]> = new Map(); // sessionId -> actionIds[]
  private rollbackPoints: Map<string, RollbackPoint> = new Map();
  private sessionRollbackPoints: Map<string, string[]> = new Map(); // sessionId -> pointIds[]

  /**
   * Record an agent action (called BEFORE execution)
   */
  public recordActionBefore(
    sessionId: string,
    toolName: string,
    args: Record<string, unknown>,
    sandboxId?: string,
    reasoning?: string,
  ): string {
    const projectStore = useProjectStore();
    const stateBefore = structuredClone(projectStore.project) as LatticeProject;

    const actionId = uuid5(`agent-action-${sessionId}-${Date.now()}`, UUID5_NAMESPACES.OID);

    // Store will be updated after execution
    const action: AgentAction = {
      id: actionId,
      sessionId,
      sandboxId,
      toolName,
      arguments: args,
      executedAt: Date.now(),
      stateBefore,
      stateAfter: structuredClone(stateBefore) as LatticeProject, // Will be updated
      success: false, // Will be updated
      reasoning,
    };

    this.actions.set(actionId, action);

    // Track by session
    if (!this.sessionActions.has(sessionId)) {
      this.sessionActions.set(sessionId, []);
    }
    this.sessionActions.get(sessionId)!.push(actionId);

    return actionId;
  }

  /**
   * Update action after execution
   */
  public recordActionAfter(
    actionId: string,
    success: boolean,
  ): void {
    const action = this.actions.get(actionId);
    if (!action) {
      throw new Error(`[AgentRollback] Action "${actionId}" not found`);
    }

    const projectStore = useProjectStore();
    action.stateAfter = structuredClone(projectStore.project) as LatticeProject;
    action.success = success;
  }

  /**
   * Create a rollback point (snapshot of current state)
   */
  public createRollbackPoint(sessionId: string): string {
    const projectStore = useProjectStore();
    const pointId = uuid5(`rollback-point-${sessionId}-${Date.now()}`, UUID5_NAMESPACES.OID);

    const point: RollbackPoint = {
      id: pointId,
      sessionId,
      projectState: structuredClone(projectStore.project) as LatticeProject,
      timestamp: Date.now(),
      actionsAfter: [],
    };

    this.rollbackPoints.set(pointId, point);

    // Track by session
    if (!this.sessionRollbackPoints.has(sessionId)) {
      this.sessionRollbackPoints.set(sessionId, []);
    }
    this.sessionRollbackPoints.get(sessionId)!.push(pointId);

    // Update actionsAfter for all previous points
    const sessionActions = this.sessionActions.get(sessionId) || [];
    for (const prevPoint of this.sessionRollbackPoints.get(sessionId) || []) {
      if (prevPoint !== pointId) {
        const prevPointObj = this.rollbackPoints.get(prevPoint);
        if (prevPointObj) {
          prevPointObj.actionsAfter = sessionActions.filter(
            (aid) => {
              const action = this.actions.get(aid);
              return action && action.executedAt > prevPointObj.timestamp;
            },
          );
        }
      }
    }

    return pointId;
  }

  /**
   * Rollback all agent actions from a session
   * This restores the project to the state before any agent actions
   */
  public rollbackSession(sessionId: string): void {
    const sessionActions = this.sessionActions.get(sessionId) || [];
    if (sessionActions.length === 0) {
      return; // Nothing to rollback
    }

    // Find the earliest action
    let earliestAction: AgentAction | null = null;
    for (const actionId of sessionActions) {
      const action = this.actions.get(actionId);
      if (action && (!earliestAction || action.executedAt < earliestAction.executedAt)) {
        earliestAction = action;
      }
    }

    if (!earliestAction) {
      return;
    }

    // Restore to state before first agent action
    const projectStore = useProjectStore();
    projectStore.project = structuredClone(earliestAction.stateBefore) as LatticeProject;
    projectStore.pushHistory();

    logAuditEntry({
      category: "security_warning",
      severity: "info",
      message: `Agent session rolled back: ${sessionId}`,
      metadata: {
        sessionId,
        actionCount: sessionActions.length,
        rolledBackTo: new Date(earliestAction.executedAt).toISOString(),
      },
    });
  }

  /**
   * Rollback to a specific rollback point
   */
  public rollbackToPoint(pointId: string): void {
    const point = this.rollbackPoints.get(pointId);
    if (!point) {
      throw new Error(`[AgentRollback] Rollback point "${pointId}" not found`);
    }

    const projectStore = useProjectStore();
    projectStore.project = structuredClone(point.projectState) as LatticeProject;
    projectStore.pushHistory();

    logAuditEntry({
      category: "security_warning",
      severity: "info",
      message: `Rolled back to point: ${pointId}`,
      metadata: {
        pointId,
        sessionId: point.sessionId,
        timestamp: new Date(point.timestamp).toISOString(),
      },
    });
  }

  /**
   * Rollback a specific agent action
   */
  public rollbackAction(actionId: string): void {
    const action = this.actions.get(actionId);
    if (!action) {
      throw new Error(`[AgentRollback] Action "${actionId}" not found`);
    }

    const projectStore = useProjectStore();
    projectStore.project = structuredClone(action.stateBefore) as LatticeProject;
    projectStore.pushHistory();

    logAuditEntry({
      category: "security_warning",
      severity: "info",
      message: `Rolled back agent action: ${actionId}`,
      metadata: {
        actionId,
        sessionId: action.sessionId,
        toolName: action.toolName,
      },
    });
  }

  /**
   * Get all agent actions for a session
   */
  public getSessionActions(sessionId: string): AgentAction[] {
    const actionIds = this.sessionActions.get(sessionId) || [];
    return actionIds
      .map((id) => this.actions.get(id))
      .filter((a): a is AgentAction => a !== undefined)
      .sort((a, b) => a.executedAt - b.executedAt);
  }

  /**
   * Get rollback points for a session
   */
  public getSessionRollbackPoints(sessionId: string): RollbackPoint[] {
    const pointIds = this.sessionRollbackPoints.get(sessionId) || [];
    return pointIds
      .map((id) => this.rollbackPoints.get(id))
      .filter((p): p is RollbackPoint => p !== undefined)
      .sort((a, b) => a.timestamp - b.timestamp);
  }

  /**
   * Clear session data (for cleanup)
   */
  public clearSession(sessionId: string): void {
    const actionIds = this.sessionActions.get(sessionId) || [];
    for (const id of actionIds) {
      this.actions.delete(id);
    }
    this.sessionActions.delete(sessionId);

    const pointIds = this.sessionRollbackPoints.get(sessionId) || [];
    for (const id of pointIds) {
      this.rollbackPoints.delete(id);
    }
    this.sessionRollbackPoints.delete(sessionId);
  }
}

// ============================================================================
// SINGLETON EXPORT
// ============================================================================

export const agentRollback = new AgentRollbackManager();
