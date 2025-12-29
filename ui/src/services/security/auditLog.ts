/**
 * Security Audit Log Service
 *
 * Persistent audit logging for LLM tool calls and security events.
 * Uses IndexedDB for persistence across page refreshes.
 *
 * SECURITY: This log is critical for:
 * - Investigating prompt injection attacks
 * - Tracking resource abuse
 * - Compliance and forensics
 *
 * @see AUDIT/SECURITY_ARCHITECTURE.md
 */

// ============================================================================
// Types
// ============================================================================

export interface AuditLogEntry {
  /** Unique entry ID (auto-generated) */
  id?: number;
  /** ISO timestamp */
  timestamp: string;
  /** Event category */
  category: 'tool_call' | 'tool_result' | 'rate_limit' | 'vram_check' | 'user_confirmation' | 'security_warning' | 'error';
  /** Event severity */
  severity: 'info' | 'warning' | 'error' | 'critical';
  /** Tool name (for tool events) */
  toolName?: string;
  /** Tool arguments (sanitized) */
  toolArguments?: Record<string, unknown>;
  /** Result or error message */
  message: string;
  /** Success/failure for tool calls */
  success?: boolean;
  /** Session ID (persists across page loads within session) */
  sessionId: string;
  /** User action that triggered this (if known) */
  userAction?: string;
  /** Additional context */
  metadata?: Record<string, unknown>;
}

export interface AuditLogQuery {
  /** Filter by category */
  category?: AuditLogEntry['category'];
  /** Filter by severity */
  severity?: AuditLogEntry['severity'];
  /** Filter by tool name */
  toolName?: string;
  /** Filter by session ID */
  sessionId?: string;
  /** Start timestamp (ISO) */
  startTime?: string;
  /** End timestamp (ISO) */
  endTime?: string;
  /** Maximum entries to return */
  limit?: number;
  /** Offset for pagination */
  offset?: number;
}

export interface AuditLogStats {
  totalEntries: number;
  byCategory: Record<string, number>;
  bySeverity: Record<string, number>;
  byToolName: Record<string, number>;
  oldestEntry: string | null;
  newestEntry: string | null;
}

// ============================================================================
// Constants
// ============================================================================

const DB_NAME = 'LatticeSecurityAudit';
const DB_VERSION = 1;
const STORE_NAME = 'auditLog';

/** Maximum entries to keep (auto-prune oldest) */
const MAX_ENTRIES = 10000;

/** Maximum age of entries in days (auto-prune older) */
const MAX_AGE_DAYS = 30;

// ============================================================================
// Session Management
// ============================================================================

let currentSessionId: string | null = null;

/**
 * Get or create session ID.
 * Session ID persists in sessionStorage (cleared on browser close).
 */
function getSessionId(): string {
  if (currentSessionId) return currentSessionId;

  const stored = sessionStorage.getItem('lattice_audit_session_id');
  if (stored) {
    currentSessionId = stored;
    return stored;
  }

  // Generate new session ID
  currentSessionId = `session_${Date.now()}_${Math.random().toString(36).substring(2, 9)}`;
  sessionStorage.setItem('lattice_audit_session_id', currentSessionId);
  return currentSessionId;
}

// ============================================================================
// IndexedDB Setup
// ============================================================================

let dbPromise: Promise<IDBDatabase> | null = null;

function openDatabase(): Promise<IDBDatabase> {
  if (dbPromise) return dbPromise;

  dbPromise = new Promise((resolve, reject) => {
    const request = indexedDB.open(DB_NAME, DB_VERSION);

    request.onerror = () => {
      console.error('[SECURITY AUDIT] Failed to open IndexedDB:', request.error);
      reject(request.error);
    };

    request.onsuccess = () => {
      resolve(request.result);
    };

    request.onupgradeneeded = (event) => {
      const db = (event.target as IDBOpenDBRequest).result;

      // Create audit log store with indexes
      if (!db.objectStoreNames.contains(STORE_NAME)) {
        const store = db.createObjectStore(STORE_NAME, {
          keyPath: 'id',
          autoIncrement: true,
        });

        // Indexes for efficient querying
        store.createIndex('timestamp', 'timestamp', { unique: false });
        store.createIndex('category', 'category', { unique: false });
        store.createIndex('severity', 'severity', { unique: false });
        store.createIndex('toolName', 'toolName', { unique: false });
        store.createIndex('sessionId', 'sessionId', { unique: false });
        store.createIndex('category_timestamp', ['category', 'timestamp'], { unique: false });
      }
    };
  });

  return dbPromise;
}

// ============================================================================
// Core Logging Functions
// ============================================================================

/**
 * Log an audit entry to IndexedDB.
 *
 * SECURITY: This function is intentionally fire-and-forget.
 * Logging failures should never block the main application.
 */
export async function logAuditEntry(
  entry: Omit<AuditLogEntry, 'id' | 'timestamp' | 'sessionId'>
): Promise<void> {
  try {
    const db = await openDatabase();
    const transaction = db.transaction(STORE_NAME, 'readwrite');
    const store = transaction.objectStore(STORE_NAME);

    const fullEntry: AuditLogEntry = {
      ...entry,
      timestamp: new Date().toISOString(),
      sessionId: getSessionId(),
    };

    // Also log to console for immediate visibility
    const consoleMethod = entry.severity === 'error' || entry.severity === 'critical'
      ? console.error
      : entry.severity === 'warning'
        ? console.warn
        : console.log;
    consoleMethod(`[SECURITY AUDIT] [${entry.category}] ${entry.message}`, entry.toolArguments || '');

    store.add(fullEntry);

    // Auto-prune if needed (async, don't wait)
    pruneOldEntries().catch(err => console.warn('[SECURITY AUDIT] Prune failed:', err));

  } catch (error) {
    // Never throw from audit logging - just warn
    console.warn('[SECURITY AUDIT] Failed to log entry:', error);
  }
}

/**
 * Log an LLM tool call.
 */
export async function logToolCall(
  toolName: string,
  toolArguments: Record<string, unknown>,
  userAction?: string
): Promise<void> {
  await logAuditEntry({
    category: 'tool_call',
    severity: 'info',
    toolName,
    toolArguments: sanitizeArguments(toolArguments),
    message: `Tool call: ${toolName}`,
    userAction,
  });
}

/**
 * Log an LLM tool result.
 */
export async function logToolResult(
  toolName: string,
  success: boolean,
  message: string,
  metadata?: Record<string, unknown>
): Promise<void> {
  await logAuditEntry({
    category: 'tool_result',
    severity: success ? 'info' : 'warning',
    toolName,
    success,
    message,
    metadata,
  });
}

/**
 * Log a rate limit event.
 */
export async function logRateLimit(
  toolName: string,
  currentCount: number,
  maxCount: number
): Promise<void> {
  await logAuditEntry({
    category: 'rate_limit',
    severity: 'warning',
    toolName,
    message: `Rate limit reached for ${toolName}: ${currentCount}/${maxCount}`,
    metadata: { currentCount, maxCount },
  });
}

/**
 * Log a VRAM check result.
 */
export async function logVRAMCheck(
  toolName: string,
  passed: boolean,
  required: number,
  available: number
): Promise<void> {
  await logAuditEntry({
    category: 'vram_check',
    severity: passed ? 'info' : 'warning',
    toolName,
    success: passed,
    message: passed
      ? `VRAM check passed for ${toolName}: ${required}MB required, ${available}MB available`
      : `VRAM check FAILED for ${toolName}: ${required}MB required, only ${available}MB available`,
    metadata: { required, available },
  });
}

/**
 * Log a user confirmation event.
 */
export async function logUserConfirmation(
  toolName: string,
  confirmed: boolean
): Promise<void> {
  await logAuditEntry({
    category: 'user_confirmation',
    severity: confirmed ? 'info' : 'warning',
    toolName,
    success: confirmed,
    message: confirmed
      ? `User APPROVED ${toolName}`
      : `User DECLINED ${toolName}`,
  });
}

/**
 * Log a security warning (potential attack detected).
 */
export async function logSecurityWarning(
  message: string,
  metadata?: Record<string, unknown>
): Promise<void> {
  await logAuditEntry({
    category: 'security_warning',
    severity: 'critical',
    message: `SECURITY WARNING: ${message}`,
    metadata,
  });
}

// ============================================================================
// Query Functions
// ============================================================================

/**
 * Query audit log entries.
 */
export async function queryAuditLog(query: AuditLogQuery = {}): Promise<AuditLogEntry[]> {
  try {
    const db = await openDatabase();
    const transaction = db.transaction(STORE_NAME, 'readonly');
    const store = transaction.objectStore(STORE_NAME);

    return new Promise((resolve, reject) => {
      const entries: AuditLogEntry[] = [];
      let cursor: IDBRequest<IDBCursorWithValue | null>;

      // Use appropriate index based on query
      if (query.category) {
        const index = store.index('category');
        cursor = index.openCursor(IDBKeyRange.only(query.category), 'prev');
      } else if (query.sessionId) {
        const index = store.index('sessionId');
        cursor = index.openCursor(IDBKeyRange.only(query.sessionId), 'prev');
      } else {
        const index = store.index('timestamp');
        cursor = index.openCursor(null, 'prev'); // Newest first
      }

      const limit = query.limit ?? 100;
      const offset = query.offset ?? 0;
      let skipped = 0;

      cursor.onsuccess = () => {
        const result = cursor.result;
        if (!result || entries.length >= limit) {
          resolve(entries);
          return;
        }

        const entry = result.value as AuditLogEntry;

        // Apply filters
        if (query.severity && entry.severity !== query.severity) {
          result.continue();
          return;
        }
        if (query.toolName && entry.toolName !== query.toolName) {
          result.continue();
          return;
        }
        if (query.startTime && entry.timestamp < query.startTime) {
          result.continue();
          return;
        }
        if (query.endTime && entry.timestamp > query.endTime) {
          result.continue();
          return;
        }

        // Apply offset
        if (skipped < offset) {
          skipped++;
          result.continue();
          return;
        }

        entries.push(entry);
        result.continue();
      };

      cursor.onerror = () => reject(cursor.error);
    });
  } catch (error) {
    console.warn('[SECURITY AUDIT] Query failed:', error);
    return [];
  }
}

/**
 * Get audit log statistics.
 */
export async function getAuditStats(): Promise<AuditLogStats> {
  try {
    const db = await openDatabase();
    const transaction = db.transaction(STORE_NAME, 'readonly');
    const store = transaction.objectStore(STORE_NAME);

    return new Promise((resolve, reject) => {
      const stats: AuditLogStats = {
        totalEntries: 0,
        byCategory: {},
        bySeverity: {},
        byToolName: {},
        oldestEntry: null,
        newestEntry: null,
      };

      const countRequest = store.count();
      countRequest.onsuccess = () => {
        stats.totalEntries = countRequest.result;
      };

      const cursor = store.openCursor();
      cursor.onsuccess = () => {
        const result = cursor.result;
        if (!result) {
          resolve(stats);
          return;
        }

        const entry = result.value as AuditLogEntry;

        // Track by category
        stats.byCategory[entry.category] = (stats.byCategory[entry.category] || 0) + 1;

        // Track by severity
        stats.bySeverity[entry.severity] = (stats.bySeverity[entry.severity] || 0) + 1;

        // Track by tool name
        if (entry.toolName) {
          stats.byToolName[entry.toolName] = (stats.byToolName[entry.toolName] || 0) + 1;
        }

        // Track oldest/newest
        if (!stats.oldestEntry || entry.timestamp < stats.oldestEntry) {
          stats.oldestEntry = entry.timestamp;
        }
        if (!stats.newestEntry || entry.timestamp > stats.newestEntry) {
          stats.newestEntry = entry.timestamp;
        }

        result.continue();
      };

      cursor.onerror = () => reject(cursor.error);
    });
  } catch (error) {
    console.warn('[SECURITY AUDIT] Stats query failed:', error);
    return {
      totalEntries: 0,
      byCategory: {},
      bySeverity: {},
      byToolName: {},
      oldestEntry: null,
      newestEntry: null,
    };
  }
}

/**
 * Export audit log as JSON (for investigation).
 */
export async function exportAuditLog(query?: AuditLogQuery): Promise<string> {
  const entries = await queryAuditLog({ ...query, limit: MAX_ENTRIES });
  const stats = await getAuditStats();

  const export_data = {
    exportedAt: new Date().toISOString(),
    sessionId: getSessionId(),
    stats,
    entries,
  };

  return JSON.stringify(export_data, null, 2);
}

/**
 * Download audit log as file.
 */
export async function downloadAuditLog(query?: AuditLogQuery): Promise<void> {
  const json = await exportAuditLog(query);
  const blob = new Blob([json], { type: 'application/json' });
  const url = URL.createObjectURL(blob);

  const a = document.createElement('a');
  a.href = url;
  a.download = `lattice-security-audit-${new Date().toISOString().split('T')[0]}.json`;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}

// ============================================================================
// Maintenance Functions
// ============================================================================

/**
 * Prune old entries to prevent unbounded growth.
 */
async function pruneOldEntries(): Promise<number> {
  try {
    const db = await openDatabase();
    const transaction = db.transaction(STORE_NAME, 'readwrite');
    const store = transaction.objectStore(STORE_NAME);

    // Check count first
    const countRequest = store.count();

    return new Promise((resolve, reject) => {
      countRequest.onsuccess = async () => {
        const count = countRequest.result;
        let deleted = 0;

        // Prune if over max entries
        if (count > MAX_ENTRIES) {
          const toDelete = count - MAX_ENTRIES;
          const index = store.index('timestamp');
          const cursor = index.openCursor(); // Oldest first

          cursor.onsuccess = () => {
            const result = cursor.result;
            if (!result || deleted >= toDelete) {
              console.log(`[SECURITY AUDIT] Pruned ${deleted} old entries`);
              resolve(deleted);
              return;
            }

            store.delete(result.primaryKey);
            deleted++;
            result.continue();
          };

          cursor.onerror = () => reject(cursor.error);
        } else {
          // Prune by age
          const cutoff = new Date();
          cutoff.setDate(cutoff.getDate() - MAX_AGE_DAYS);
          const cutoffStr = cutoff.toISOString();

          const index = store.index('timestamp');
          const range = IDBKeyRange.upperBound(cutoffStr);
          const cursor = index.openCursor(range);

          cursor.onsuccess = () => {
            const result = cursor.result;
            if (!result) {
              if (deleted > 0) {
                console.log(`[SECURITY AUDIT] Pruned ${deleted} entries older than ${MAX_AGE_DAYS} days`);
              }
              resolve(deleted);
              return;
            }

            store.delete(result.primaryKey);
            deleted++;
            result.continue();
          };

          cursor.onerror = () => reject(cursor.error);
        }
      };

      countRequest.onerror = () => reject(countRequest.error);
    });
  } catch (error) {
    console.warn('[SECURITY AUDIT] Prune failed:', error);
    return 0;
  }
}

/**
 * Clear all audit log entries.
 * SECURITY: Requires explicit confirmation, logged as security event.
 */
export async function clearAuditLog(confirmationCode: string): Promise<boolean> {
  // Require specific confirmation code to prevent accidental clearing
  if (confirmationCode !== 'CLEAR_AUDIT_LOG') {
    console.warn('[SECURITY AUDIT] Clear rejected: invalid confirmation code');
    return false;
  }

  try {
    // Log the clear action BEFORE clearing
    await logAuditEntry({
      category: 'security_warning',
      severity: 'critical',
      message: 'Audit log cleared by user action',
      metadata: { clearedAt: new Date().toISOString() },
    });

    const db = await openDatabase();
    const transaction = db.transaction(STORE_NAME, 'readwrite');
    const store = transaction.objectStore(STORE_NAME);

    return new Promise((resolve, reject) => {
      const request = store.clear();
      request.onsuccess = () => {
        console.log('[SECURITY AUDIT] Audit log cleared');
        resolve(true);
      };
      request.onerror = () => reject(request.error);
    });
  } catch (error) {
    console.error('[SECURITY AUDIT] Clear failed:', error);
    return false;
  }
}

// ============================================================================
// Helpers
// ============================================================================

/**
 * Sanitize tool arguments for logging.
 * Removes potentially sensitive data, truncates long strings.
 */
function sanitizeArguments(args: Record<string, unknown>): Record<string, unknown> {
  const sanitized: Record<string, unknown> = {};

  for (const [key, value] of Object.entries(args)) {
    // Skip potentially sensitive keys
    if (key.toLowerCase().includes('password') ||
        key.toLowerCase().includes('secret') ||
        key.toLowerCase().includes('token') ||
        key.toLowerCase().includes('key')) {
      sanitized[key] = '[REDACTED]';
      continue;
    }

    // Truncate long strings
    if (typeof value === 'string' && value.length > 500) {
      sanitized[key] = value.substring(0, 500) + '...[truncated]';
      continue;
    }

    // Truncate data URLs
    if (typeof value === 'string' && value.startsWith('data:')) {
      sanitized[key] = value.substring(0, 50) + '...[data URL truncated]';
      continue;
    }

    sanitized[key] = value;
  }

  return sanitized;
}
