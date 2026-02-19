/**
 * Agent Sandbox
 *
 * Sandboxed execution environment for AI agent actions.
 * Agent actions execute in isolated environment, changes staged before commit.
 * This allows user to review staged changes before committing to main store.
 *
 * SECURITY: This prevents agents from directly modifying the main store.
 * All changes are staged and require explicit user approval before commit.
 *
 * Architecture:
 * 1. Agent actions execute in sandbox (isolated project state)
 * 2. Changes are staged (not applied to main store)
 * 3. User reviews staged changes
 * 4. User commits or rolls back sandbox state
 * 5. Rollback sandbox independently of main store undo/redo
 */

import type { LatticeProject } from "@/types/project";
import { useProjectStore } from "@/stores/projectStore";
import { logAuditEntry } from "../../security/auditLog";
import { uuid5, UUID5_NAMESPACES } from "@/utils/uuid5";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

export interface SandboxState {
  /** Unique sandbox ID */
  id: string;
  /** Session ID this sandbox belongs to */
  sessionId: string;
  /** When sandbox was created */
  createdAt: number;
  /** Base project state (snapshot when sandbox was created) */
  baseState: LatticeProject;
  /** Current sandbox state (with staged changes) */
  currentState: LatticeProject;
  /** List of actions performed in sandbox */
  actions: SandboxAction[];
  /** Whether sandbox has been committed */
  committed: boolean;
  /** When sandbox was committed (if committed) */
  committedAt?: number;
}

export interface SandboxAction {
  /** Unique action ID */
  id: string;
  /** Tool name that was executed */
  toolName: string;
  /** Tool arguments */
  arguments: Record<string, unknown>;
  /** When action was executed */
  executedAt: number;
  /** Result of action */
  result: unknown;
  /** Whether action succeeded */
  success: boolean;
  /** Reasoning for this action (from agent) */
  reasoning?: string;
}

export interface SandboxDiff {
  /** Layers added */
  layersAdded: string[];
  /** Layers removed */
  layersRemoved: string[];
  /** Layers modified */
  layersModified: string[];
  /** Properties changed */
  propertiesChanged: Array<{
    layerId: string;
    propertyPath: string;
    oldValue: unknown;
    newValue: unknown;
  }>;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                        // sandbox // manager
// ════════════════════════════════════════════════════════════════════════════

class AgentSandbox {
  private sandboxes: Map<string, SandboxState> = new Map();
  private activeSandboxId: string | null = null;

  /**
   * Create a new sandbox for agent execution
   * Takes a snapshot of current project state as base
   */
  public createSandbox(sessionId: string): SandboxState {
    const projectStore = useProjectStore();
    const baseState = structuredClone(projectStore.project) as LatticeProject;

    const sandbox: SandboxState = {
      id: uuid5(`sandbox-${sessionId}-${Date.now()}`, UUID5_NAMESPACES.OID),
      sessionId,
      createdAt: Date.now(),
      baseState,
      currentState: structuredClone(baseState) as LatticeProject,
      actions: [],
      committed: false,
    };

    this.sandboxes.set(sandbox.id, sandbox);
    this.activeSandboxId = sandbox.id;

    logAuditEntry({
      category: "security_warning",
      severity: "info",
      message: `Agent sandbox created: ${sandbox.id}`,
      metadata: {
        sandboxId: sandbox.id,
        sessionId,
        layerCount: baseState.compositions?.[Object.keys(baseState.compositions)[0]]?.layers?.length || 0,
      },
    });

    return sandbox;
  }

  /**
   * Get active sandbox
   */
  public getActiveSandbox(): SandboxState | null {
    if (!this.activeSandboxId) return null;
    return this.sandboxes.get(this.activeSandboxId) || null;
  }

  /**
   * Get sandbox by ID
   */
  public getSandbox(sandboxId: string): SandboxState | null {
    return this.sandboxes.get(sandboxId) || null;
  }

  /**
   * Record an action in the sandbox
   */
  public recordAction(
    sandboxId: string,
    toolName: string,
    args: Record<string, unknown>,
    result: unknown,
    success: boolean,
    reasoning?: string,
  ): void {
    const sandbox = this.sandboxes.get(sandboxId);
    if (!sandbox) {
      throw new Error(`[AgentSandbox] Sandbox "${sandboxId}" not found`);
    }

    if (sandbox.committed) {
      throw new Error(`[AgentSandbox] Cannot record action: sandbox "${sandboxId}" has been committed`);
    }

    const action: SandboxAction = {
      id: uuid5(`action-${sandboxId}-${sandbox.actions.length}`, UUID5_NAMESPACES.OID),
      toolName,
      arguments: args,
      executedAt: Date.now(),
      result,
      success,
      reasoning,
    };

    sandbox.actions.push(action);

    // Update current state (this is where sandboxed execution happens)
    // The actual state update is done by the action executor in sandbox mode
    // This just records what happened
  }

  /**
   * Update sandbox state (called by action executor in sandbox mode)
   */
  public updateSandboxState(sandboxId: string, newState: LatticeProject): void {
    const sandbox = this.sandboxes.get(sandboxId);
    if (!sandbox) {
      throw new Error(`[AgentSandbox] Sandbox "${sandboxId}" not found`);
    }

    if (sandbox.committed) {
      throw new Error(`[AgentSandbox] Cannot update state: sandbox "${sandboxId}" has been committed`);
    }

    sandbox.currentState = structuredClone(newState) as LatticeProject;
  }

  /**
   * Get diff between base state and current sandbox state
   */
  public getSandboxDiff(sandboxId: string): SandboxDiff {
    const sandbox = this.sandboxes.get(sandboxId);
    if (!sandbox) {
      throw new Error(`[AgentSandbox] Sandbox "${sandboxId}" not found`);
    }

    const baseLayers = sandbox.baseState.compositions?.[Object.keys(sandbox.baseState.compositions)[0]]?.layers || [];
    const currentLayers = sandbox.currentState.compositions?.[Object.keys(sandbox.currentState.compositions)[0]]?.layers || [];

    const baseLayerIds = new Set(baseLayers.map((l) => l.id));
    const currentLayerIds = new Set(currentLayers.map((l) => l.id));

    const layersAdded = currentLayers
      .filter((l) => !baseLayerIds.has(l.id))
      .map((l) => l.id);
    const layersRemoved = baseLayers
      .filter((l) => !currentLayerIds.has(l.id))
      .map((l) => l.id);
    const layersModified: string[] = [];

    // Check for modified layers
    for (const currentLayer of currentLayers) {
      if (baseLayerIds.has(currentLayer.id)) {
        const baseLayer = baseLayers.find((l) => l.id === currentLayer.id);
        if (baseLayer && JSON.stringify(baseLayer) !== JSON.stringify(currentLayer)) {
          layersModified.push(currentLayer.id);
        }
      }
    }

    //                                                                      // todo
    const propertiesChanged: SandboxDiff["propertiesChanged"] = [];

    return {
      layersAdded,
      layersRemoved,
      layersModified,
      propertiesChanged,
    };
  }

  /**
   * Commit sandbox changes to main store
   * This applies all staged changes to the actual project
   */
  public commitSandbox(sandboxId: string): void {
    const sandbox = this.sandboxes.get(sandboxId);
    if (!sandbox) {
      throw new Error(`[AgentSandbox] Sandbox "${sandboxId}" not found`);
    }

    if (sandbox.committed) {
      throw new Error(`[AgentSandbox] Sandbox "${sandboxId}" has already been committed`);
    }

    const projectStore = useProjectStore();

    // Apply sandbox state to main store
    projectStore.project = structuredClone(sandbox.currentState) as LatticeProject;
    projectStore.pushHistory();

    sandbox.committed = true;
    sandbox.committedAt = Date.now();

    const diff = this.getSandboxDiff(sandboxId);
    logAuditEntry({
      category: "security_warning",
      severity: "info",
      message: `Agent sandbox committed: ${sandboxId}`,
      metadata: {
        sandboxId,
        sessionId: sandbox.sessionId,
        actionCount: sandbox.actions.length,
        layersAdded: diff.layersAdded.length,
        layersRemoved: diff.layersRemoved.length,
        layersModified: diff.layersModified.length,
      },
    });

    // Clear active sandbox
    if (this.activeSandboxId === sandboxId) {
      this.activeSandboxId = null;
    }
  }

  /**
   * Rollback sandbox (discard all staged changes)
   * This does NOT affect the main store
   */
  public rollbackSandbox(sandboxId: string): void {
    const sandbox = this.sandboxes.get(sandboxId);
    if (!sandbox) {
      throw new Error(`[AgentSandbox] Sandbox "${sandboxId}" not found`);
    }

    if (sandbox.committed) {
      throw new Error(`[AgentSandbox] Cannot rollback committed sandbox "${sandboxId}"`);
    }

    // Reset to base state
    sandbox.currentState = structuredClone(sandbox.baseState) as LatticeProject;
    sandbox.actions = [];

    logAuditEntry({
      category: "security_warning",
      severity: "info",
      message: `Agent sandbox rolled back: ${sandboxId}`,
      metadata: {
        sandboxId,
        sessionId: sandbox.sessionId,
        actionCount: sandbox.actions.length,
      },
    });

    // Clear active sandbox
    if (this.activeSandboxId === sandboxId) {
      this.activeSandboxId = null;
    }
  }

  /**
   * Close sandbox (cleanup, but keep for audit)
   */
  public closeSandbox(sandboxId: string): void {
    const sandbox = this.sandboxes.get(sandboxId);
    if (!sandbox) {
      return;
    }

    if (!sandbox.committed) {
      // Auto-rollback uncommitted sandboxes
      this.rollbackSandbox(sandboxId);
    }

    if (this.activeSandboxId === sandboxId) {
      this.activeSandboxId = null;
    }

    // Keep sandbox in map for audit (could prune old ones later)
  }

  /**
   * Get all sandboxes for a session
   */
  public getSessionSandboxes(sessionId: string): SandboxState[] {
    return Array.from(this.sandboxes.values()).filter(
      (s) => s.sessionId === sessionId,
    );
  }

  /**
   * Get all actions in a sandbox
   */
  public getSandboxActions(sandboxId: string): SandboxAction[] {
    const sandbox = this.sandboxes.get(sandboxId);
    if (!sandbox) {
      return [];
    }
    return [...sandbox.actions];
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                       // singleton // export
// ════════════════════════════════════════════════════════════════════════════

export const agentSandbox = new AgentSandbox();
