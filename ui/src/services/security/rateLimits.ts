/**
 * Persistent Rate Limits Service
 *
 * Stores rate limit counters in localStorage so they survive page refresh.
 * Implements per-day limits with automatic daily reset.
 *
 * SECURITY: Prevents abuse via:
 * - Persistent counters (survive page refresh)
 * - Per-day limits (reset at midnight UTC)
 * - Per-tool tracking
 * - Explicit user action required to reset
 *
 * @see AUDIT/SECURITY_ARCHITECTURE.md
 */

import { logRateLimit, logSecurityWarning } from "./auditLog";
import { isFiniteNumber, safeNonNegativeDefault } from "@/utils/typeGuards";

// ============================================================================
// Types
// ============================================================================

export interface RateLimitConfig {
  /** Tool name */
  toolName: string;
  /** Maximum calls per day */
  maxPerDay: number;
  /** Maximum calls per session (optional, more restrictive) */
  maxPerSession?: number;
  /** VRAM cost in MB (for budget tracking) */
  vramCostMB?: number;
}

export interface RateLimitStatus {
  /** Tool name */
  toolName: string;
  /** Calls today */
  callsToday: number;
  /** Max calls per day */
  maxPerDay: number;
  /** Calls this session */
  callsThisSession: number;
  /** Max calls per session (if set) */
  maxPerSession?: number;
  /** Whether more calls are allowed */
  canCall: boolean;
  /** Reason if blocked */
  blockedReason?: string;
  /** When daily limit resets (ISO timestamp) */
  resetsAt: string;
  /** Time until reset (human readable) */
  resetsIn: string;
}

interface StoredRateLimits {
  /** Date string (YYYY-MM-DD UTC) */
  date: string;
  /** Tool call counts */
  counts: Record<string, number>;
  /** Last reset timestamp */
  lastReset: string;
}

// ============================================================================
// Constants
// ============================================================================

const STORAGE_KEY = "lattice_rate_limits";
const SESSION_KEY = "lattice_session_counts";

/**
 * Default rate limits for high-risk tools.
 * These can be overridden by calling setRateLimitConfig().
 */
const DEFAULT_LIMITS: Record<string, RateLimitConfig> = {
  decomposeImage: {
    toolName: "decomposeImage",
    maxPerDay: 10, // Max 10 decompositions per day
    maxPerSession: 3, // Max 3 per session without explicit reset
    vramCostMB: 28800,
  },
  vectorizeImage: {
    toolName: "vectorizeImage",
    maxPerDay: 20, // Max 20 vectorizations per day
    maxPerSession: 5, // Max 5 per session
    vramCostMB: 4000,
  },
};

// ============================================================================
// State
// ============================================================================

/** Custom limits (override defaults) */
const customLimits: Record<string, RateLimitConfig> = {};

/** Session counts (in-memory, cleared on page refresh) */
let sessionCounts: Record<string, number> = {};

// ============================================================================
// Storage Functions
// ============================================================================

/**
 * Get current UTC date string (YYYY-MM-DD).
 */
function getCurrentDateUTC(): string {
  return new Date().toISOString().split("T")[0];
}

/**
 * Get tomorrow midnight UTC as ISO string.
 */
function getTomorrowMidnightUTC(): string {
  const tomorrow = new Date();
  tomorrow.setUTCDate(tomorrow.getUTCDate() + 1);
  tomorrow.setUTCHours(0, 0, 0, 0);
  return tomorrow.toISOString();
}

/**
 * Get human-readable time until reset.
 */
function getTimeUntilReset(): string {
  const now = new Date();
  const tomorrow = new Date();
  tomorrow.setUTCDate(tomorrow.getUTCDate() + 1);
  tomorrow.setUTCHours(0, 0, 0, 0);

  const diffMs = tomorrow.getTime() - now.getTime();
  const hours = Math.floor(diffMs / (1000 * 60 * 60));
  const minutes = Math.floor((diffMs % (1000 * 60 * 60)) / (1000 * 60));

  if (hours > 0) {
    return `${hours}h ${minutes}m`;
  }
  return `${minutes}m`;
}

/**
 * Load rate limits from localStorage.
 * Auto-resets if date has changed.
 */
function loadStoredLimits(): StoredRateLimits {
  try {
    const stored = localStorage.getItem(STORAGE_KEY);
    if (stored) {
      const data = JSON.parse(stored) as StoredRateLimits;

      // Check if we need to reset (new day)
      const today = getCurrentDateUTC();
      if (data.date !== today) {
        console.log("[SECURITY] Daily rate limits reset (new day)");
        return {
          date: today,
          counts: {},
          lastReset: new Date().toISOString(),
        };
      }

      return data;
    }
  } catch (error) {
    console.warn("[SECURITY] Failed to load rate limits:", error);
  }

  // Default: fresh state
  return {
    date: getCurrentDateUTC(),
    counts: {},
    lastReset: new Date().toISOString(),
  };
}

/**
 * Save rate limits to localStorage.
 */
function saveStoredLimits(limits: StoredRateLimits): void {
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(limits));
  } catch (error) {
    console.warn("[SECURITY] Failed to save rate limits:", error);
  }
}

/**
 * Load session counts from sessionStorage.
 */
function loadSessionCounts(): Record<string, number> {
  try {
    const stored = sessionStorage.getItem(SESSION_KEY);
    if (stored) {
      return JSON.parse(stored);
    }
  } catch (error) {
    console.warn("[SECURITY] Failed to load session counts:", error);
  }
  return {};
}

/**
 * Save session counts to sessionStorage.
 */
function saveSessionCounts(): void {
  try {
    sessionStorage.setItem(SESSION_KEY, JSON.stringify(sessionCounts));
  } catch (error) {
    console.warn("[SECURITY] Failed to save session counts:", error);
  }
}

// Initialize session counts
sessionCounts = loadSessionCounts();

// ============================================================================
// Public API
// ============================================================================

/**
 * Check if a tool call is allowed under rate limits.
 * Does NOT increment counters - call recordToolCall() after successful execution.
 */
export function checkRateLimit(toolName: string): RateLimitStatus {
  const config = customLimits[toolName] || DEFAULT_LIMITS[toolName];

  if (!config) {
    // No limits configured for this tool
    // Type proof: sessionCounts[toolName] ∈ number | undefined → number (≥ 0, count)
    const sessionCount = safeNonNegativeDefault(
      sessionCounts[toolName],
      0,
      "sessionCounts[toolName]",
    );
    return {
      toolName,
      callsToday: 0,
      maxPerDay: Infinity,
      callsThisSession: sessionCount,
      canCall: true,
      resetsAt: getTomorrowMidnightUTC(),
      resetsIn: getTimeUntilReset(),
    };
  }

  const stored = loadStoredLimits();
  // Type proof: stored.counts[toolName] ∈ number | undefined → number (≥ 0, count)
  const callsToday = safeNonNegativeDefault(
    stored.counts[toolName],
    0,
    "stored.counts[toolName]",
  );
  const callsThisSession = safeNonNegativeDefault(
    sessionCounts[toolName],
    0,
    "sessionCounts[toolName]",
  );

  // Check daily limit
  if (callsToday >= config.maxPerDay) {
    return {
      toolName,
      callsToday,
      maxPerDay: config.maxPerDay,
      callsThisSession,
      maxPerSession: config.maxPerSession,
      canCall: false,
      blockedReason: `Daily limit reached (${callsToday}/${config.maxPerDay}). Resets in ${getTimeUntilReset()}.`,
      resetsAt: getTomorrowMidnightUTC(),
      resetsIn: getTimeUntilReset(),
    };
  }

  // Check session limit (if configured)
  if (config.maxPerSession && callsThisSession >= config.maxPerSession) {
    return {
      toolName,
      callsToday,
      maxPerDay: config.maxPerDay,
      callsThisSession,
      maxPerSession: config.maxPerSession,
      canCall: false,
      blockedReason: `Session limit reached (${callsThisSession}/${config.maxPerSession}). Use resetSessionLimit('${toolName}') to continue.`,
      resetsAt: getTomorrowMidnightUTC(),
      resetsIn: getTimeUntilReset(),
    };
  }

  return {
    toolName,
    callsToday,
    maxPerDay: config.maxPerDay,
    callsThisSession,
    maxPerSession: config.maxPerSession,
    canCall: true,
    resetsAt: getTomorrowMidnightUTC(),
    resetsIn: getTimeUntilReset(),
  };
}

/**
 * Record a tool call (increment counters).
 * Call this AFTER successful execution.
 */
export async function recordToolCall(toolName: string): Promise<void> {
  // Increment daily count
  // Type proof: stored.counts[toolName] ∈ number | undefined → number (≥ 0, count)
  const stored = loadStoredLimits();
  const currentDailyCount = safeNonNegativeDefault(
    stored.counts[toolName],
    0,
    "stored.counts[toolName]",
  );
  stored.counts[toolName] = currentDailyCount + 1;
  saveStoredLimits(stored);

  // Increment session count
  // Type proof: sessionCounts[toolName] ∈ number | undefined → number (≥ 0, count)
  const currentSessionCount = safeNonNegativeDefault(
    sessionCounts[toolName],
    0,
    "sessionCounts[toolName]",
  );
  sessionCounts[toolName] = currentSessionCount + 1;
  saveSessionCounts();

  const config = customLimits[toolName] || DEFAULT_LIMITS[toolName];
  const newStatus = checkRateLimit(toolName);

  // Type proof: number | undefined → proper conditional formatting
  // Construct log message based on whether session limit exists
  const sessionInfo = isFiniteNumber(newStatus.maxPerSession) && newStatus.maxPerSession > 0
    ? `session: ${newStatus.callsThisSession}/${newStatus.maxPerSession}`
    : `session: ${newStatus.callsThisSession}`;
  console.log(
    `[SECURITY] Rate limit recorded: ${toolName} ` +
      `(today: ${newStatus.callsToday}/${newStatus.maxPerDay}, ` +
      `${sessionInfo})`,
  );

  // Log if approaching limits
  if (config && newStatus.callsToday >= config.maxPerDay * 0.8) {
    await logRateLimit(toolName, newStatus.callsToday, config.maxPerDay);
  }
}

/**
 * Reset session limit for a specific tool.
 * Requires user action - logs the reset.
 */
export async function resetSessionLimit(toolName: string): Promise<void> {
  // Type proof: sessionCounts[toolName] ∈ number | undefined → number (≥ 0, count)
  const oldCount = safeNonNegativeDefault(
    sessionCounts[toolName],
    0,
    "sessionCounts[toolName]",
  );
  sessionCounts[toolName] = 0;
  saveSessionCounts();

  console.log(
    `[SECURITY] Session limit reset for ${toolName} (was: ${oldCount})`,
  );
  await logSecurityWarning(`Session limit reset by user: ${toolName}`, {
    toolName,
    previousCount: oldCount,
  });
}

/**
 * Reset ALL session limits.
 * Requires explicit confirmation.
 */
export async function resetAllSessionLimits(
  confirmationCode: string,
): Promise<boolean> {
  if (confirmationCode !== "RESET_SESSION_LIMITS") {
    console.warn("[SECURITY] Reset rejected: invalid confirmation code");
    return false;
  }

  const oldCounts = { ...sessionCounts };
  sessionCounts = {};
  saveSessionCounts();

  console.log("[SECURITY] All session limits reset");
  await logSecurityWarning("All session limits reset by user", {
    previousCounts: oldCounts,
  });

  return true;
}

/**
 * Get status for all rate-limited tools.
 */
export function getAllRateLimitStatus(): RateLimitStatus[] {
  const allTools = new Set([
    ...Object.keys(DEFAULT_LIMITS),
    ...Object.keys(customLimits),
  ]);

  return Array.from(allTools).map((toolName) => checkRateLimit(toolName));
}

/**
 * Set custom rate limit configuration.
 * Overrides defaults for specific tools.
 */
export function setRateLimitConfig(config: RateLimitConfig): void {
  customLimits[config.toolName] = config;
  console.log(
    `[SECURITY] Rate limit configured for ${config.toolName}:`,
    config,
  );
}

/**
 * Get remaining calls for a tool.
 */
export function getRemainingCalls(toolName: string): {
  remainingToday: number;
  remainingSession: number;
} {
  const status = checkRateLimit(toolName);

  return {
    remainingToday: Math.max(0, status.maxPerDay - status.callsToday),
    remainingSession: status.maxPerSession
      ? Math.max(0, status.maxPerSession - status.callsThisSession)
      : Infinity,
  };
}

/**
 * Check if any rate limits are close to being reached.
 */
export function checkRateLimitWarnings(): {
  toolName: string;
  message: string;
  severity: "warning" | "critical";
}[] {
  const warnings: {
    toolName: string;
    message: string;
    severity: "warning" | "critical";
  }[] = [];

  for (const status of getAllRateLimitStatus()) {
    const config =
      customLimits[status.toolName] || DEFAULT_LIMITS[status.toolName];
    if (!config) continue;

    const dailyPercent = status.callsToday / status.maxPerDay;

    if (dailyPercent >= 1) {
      warnings.push({
        toolName: status.toolName,
        message: `Daily limit reached for ${status.toolName}. Resets in ${status.resetsIn}.`,
        severity: "critical",
      });
    } else if (dailyPercent >= 0.8) {
      warnings.push({
        toolName: status.toolName,
        message: `${status.toolName}: ${status.callsToday}/${status.maxPerDay} daily calls used.`,
        severity: "warning",
      });
    }

    if (status.maxPerSession) {
      if (status.callsThisSession >= status.maxPerSession) {
        warnings.push({
          toolName: status.toolName,
          message: `Session limit reached for ${status.toolName}. Manual reset required.`,
          severity: "critical",
        });
      }
    }
  }

  return warnings;
}
