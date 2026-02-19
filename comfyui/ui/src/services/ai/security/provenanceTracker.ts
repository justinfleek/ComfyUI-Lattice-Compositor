/**
 * Provenance Tracker
 *
 * Tracks the decision chain for agent actions:
 * - User instruction → Agent reasoning → Tool calls → Results
 *
 * This enables:
 * - Query "why did agent do X?"
 * - Export provenance data for analysis
 * - Link to audit log entries
 * - Full decision chain visibility
 *
 * SECURITY: This is critical for understanding agent behavior
 * and detecting prompt injection or manipulation attempts.
 */

import type { JSONValue } from "@/types/dataAsset";
import { logAuditEntry } from "../../security/auditLog";
import { uuid5, UUID5_NAMESPACES } from "@/utils/uuid5";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

export interface ProvenanceEntry {
  /** Unique provenance ID */
  id: string;
  /** Session ID */
  sessionId: string;
  /** When this decision was made */
  timestamp: number;
  /** User instruction that triggered this */
  userInstruction: string;
  /** Agent reasoning for this decision */
  reasoning: string;
  /** Tool calls made as part of this decision */
  toolCalls: Array<{
    id: string;
    name: string;
    arguments: Record<string, JSONValue>;
    reasoning?: string; // Why this specific tool call
  }>;
  /** Results of tool calls */
  results: Array<{
    toolCallId: string;
    success: boolean;
    result?: unknown;
    error?: string;
  }>;
  /** Link to audit log entry ID */
  auditLogId?: number;
  /** Additional context */
  metadata?: Record<string, JSONValue>;
}

export interface ProvenanceQuery {
  /** Filter by session ID */
  sessionId?: string;
  /** Filter by tool name */
  toolName?: string;
  /** Start timestamp */
  startTime?: number;
  /** End timestamp */
  endTime?: number;
  /** Maximum entries */
  limit?: number;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                    // provenance // tracker
// ═══════════════════════════════════════════════════════════════════════════

class ProvenanceTracker {
  private entries: Map<string, ProvenanceEntry> = new Map();
  private sessionEntries: Map<string, string[]> = new Map(); // sessionId -> entryIds[]

  /**
   * Record a decision chain
   */
  public recordDecision(
    sessionId: string,
    userInstruction: string,
    reasoning: string,
    toolCalls: Array<{
      id: string;
      name: string;
      arguments: Record<string, JSONValue>;
      reasoning?: string;
    }>,
    results: Array<{
      toolCallId: string;
      success: boolean;
      result?: unknown;
      error?: string;
    }>,
    metadata?: Record<string, JSONValue>,
  ): string {
    const entry: ProvenanceEntry = {
      id: uuid5(`provenance-${sessionId}-${Date.now()}`, UUID5_NAMESPACES.OID),
      sessionId,
      timestamp: Date.now(),
      userInstruction,
      reasoning,
      toolCalls,
      results,
      metadata,
    };

    this.entries.set(entry.id, entry);

    // Track by session
    if (!this.sessionEntries.has(sessionId)) {
      this.sessionEntries.set(sessionId, []);
    }
    this.sessionEntries.get(sessionId)!.push(entry.id);

    // Log to audit log
    logAuditEntry({
      category: "security_warning",
      severity: "info",
      message: `Provenance recorded: ${toolCalls.length} tool call(s)`,
      metadata: {
        provenanceId: entry.id,
        sessionId,
        toolCallCount: toolCalls.length,
        userInstruction: userInstruction.substring(0, 100), // Truncate for metadata
        reasoning: reasoning.substring(0, 200), // Truncate for metadata
      },
    }).then(() => {
      // Link audit log entry back to provenance
      // Note: This is async, so we can't get the audit log ID immediately
      // In production, we'd query the audit log to find the matching entry
    });

    return entry.id;
  }

  /**
   * Query provenance entries
   */
  public queryProvenance(query: ProvenanceQuery = {}): ProvenanceEntry[] {
    let entries = Array.from(this.entries.values());

    // Filter by session
    if (query.sessionId) {
      entries = entries.filter((e) => e.sessionId === query.sessionId);
    }

    // Filter by tool name
    if (query.toolName) {
      entries = entries.filter((e) =>
        e.toolCalls.some((tc) => tc.name === query.toolName),
      );
    }

    // Filter by time range
    // Deterministic: Explicit null checks before accessing properties
    if (query.startTime !== undefined && query.startTime !== null) {
      const startTime = query.startTime;
      entries = entries.filter((e) => e.timestamp >= startTime);
    }
    if (query.endTime !== undefined && query.endTime !== null) {
      const endTime = query.endTime;
      entries = entries.filter((e) => e.timestamp <= endTime);
    }

    // Sort by timestamp (newest first)
    entries.sort((a, b) => b.timestamp - a.timestamp);

    // Apply limit
    if (query.limit && query.limit > 0) {
      entries = entries.slice(0, query.limit);
    }

    return entries;
  }

  /**
   * Get provenance for a specific decision
   */
  public getProvenance(provenanceId: string): ProvenanceEntry | null {
    return this.entries.get(provenanceId) || null;
  }

  /**
   * Query "why did agent do X?"
   * Returns the reasoning chain that led to a specific tool call
   */
  public queryWhy(
    toolCallId: string,
    sessionId?: string,
  ): ProvenanceEntry | null {
    let entries = Array.from(this.entries.values());

    if (sessionId) {
      entries = entries.filter((e) => e.sessionId === sessionId);
    }

    // Find entry that contains this tool call
    for (const entry of entries) {
      if (entry.toolCalls.some((tc) => tc.id === toolCallId)) {
        return entry;
      }
    }

    return null;
  }

  /**
   * Get all provenance for a session
   */
  public getSessionProvenance(sessionId: string): ProvenanceEntry[] {
    const entryIds = this.sessionEntries.get(sessionId) || [];
    return entryIds
      .map((id) => this.entries.get(id))
      .filter((e): e is ProvenanceEntry => e !== undefined);
  }

  /**
   * Export provenance data for analysis
   */
  public exportProvenance(query?: ProvenanceQuery): string {
    const entries = this.queryProvenance(query || {});
    return JSON.stringify(
      {
        exportedAt: new Date().toISOString(),
        entryCount: entries.length,
        entries,
      },
      null,
      2,
    );
  }

  /**
   * Clear provenance for a session (for cleanup)
   */
  public clearSessionProvenance(sessionId: string): void {
    const entryIds = this.sessionEntries.get(sessionId) || [];
    for (const id of entryIds) {
      this.entries.delete(id);
    }
    this.sessionEntries.delete(sessionId);
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // singleton // export
// ═══════════════════════════════════════════════════════════════════════════

export const provenanceTracker = new ProvenanceTracker();
