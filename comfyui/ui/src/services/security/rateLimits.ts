/**
 * Frontend Rate Limit Awareness for Lattice Compositor
 *
 * Client-side rate limit tracking and UI hints.
 * Backend rate limiting is authoritative; this provides user feedback.
 */

export interface RateLimitInfo {
  tool_name: string;
  remaining: number;
  limit: number;
  reset_at: number; // Unix timestamp
}

export interface RateLimitStats {
  total_requests: number;
  allowed_requests: number;
  denied_requests: number;
  last_denied?: number; // Unix timestamp
}

export interface RateLimitStatus {
  toolName: string;
  callsToday: number;
  maxPerDay: number;
  callsThisSession: number;
  maxPerSession?: number;
  canCall: boolean;
  blockedReason?: string;
  resetsAt?: number;
  resetsIn?: number;
}

/**
 * Store rate limit information from API responses
 */
class RateLimitStore {
  private limits: Map<string, RateLimitInfo> = new Map();
  private stats: Map<string, RateLimitStats> = new Map();

  /**
   * Update rate limit info from API response headers
   */
  updateFromHeaders(
    tool_name: string,
    headers: Headers | Record<string, string>
  ): void {
    const getHeader = (name: string): string | null => {
      if (headers instanceof Headers) {
        return headers.get(name);
      }
      return headers[name] || null;
    };

    const remaining = getHeader("X-RateLimit-Remaining");
    const limit = getHeader("X-RateLimit-Limit");
    const reset = getHeader("X-RateLimit-Reset");

    if (remaining && limit && reset) {
      this.limits.set(tool_name, {
        tool_name,
        remaining: parseInt(remaining, 10),
        limit: parseInt(limit, 10),
        reset_at: parseInt(reset, 10),
      });
    }
  }

  /**
   * Get rate limit info for a tool
   */
  getLimit(tool_name: string): RateLimitInfo | null {
    return this.limits.get(tool_name) || null;
  }

  /**
   * Update stats from API response
   */
  updateStats(tool_name: string, allowed: boolean): void {
    const current = this.stats.get(tool_name) || {
      total_requests: 0,
      allowed_requests: 0,
      denied_requests: 0,
    };

    current.total_requests++;
    if (allowed) {
      current.allowed_requests++;
    } else {
      current.denied_requests++;
      current.last_denied = Date.now();
    }

    this.stats.set(tool_name, current);
  }

  /**
   * Get stats for a tool
   */
  getStats(tool_name: string): RateLimitStats | null {
    return this.stats.get(tool_name) || null;
  }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// RATE LIMIT TRACKING (for AI agent)
// ═══════════════════════════════════════════════════════════════════════════

const store = new RateLimitStore();

// Default limits for high-risk tools
const DEFAULT_LIMITS: Record<string, { maxPerDay: number; maxPerSession?: number }> = {
  decomposeImage: { maxPerDay: 10, maxPerSession: 2 },
  vectorizeImage: { maxPerDay: 20, maxPerSession: 5 },
};

// Session tracking (survives page refresh via sessionStorage)
const SESSION_KEY = "lattice_rate_limit_session";

interface SessionCounts {
  [toolName: string]: number;
}

function getSessionCounts(): SessionCounts {
  try {
    const stored = sessionStorage.getItem(SESSION_KEY);
    if (stored) {
      return JSON.parse(stored) as SessionCounts;
    }
  } catch (error) {
    console.warn("[RateLimits] Failed to load session counts:", error);
  }
  return {};
}

function saveSessionCounts(counts: SessionCounts): void {
  try {
    sessionStorage.setItem(SESSION_KEY, JSON.stringify(counts));
  } catch (error) {
    console.warn("[RateLimits] Failed to save session counts:", error);
  }
}

// Daily tracking (survives page refresh via localStorage)
const DAILY_KEY_PREFIX = "lattice_rate_limit_daily_";

function getDailyKey(toolName: string): string {
  return `${DAILY_KEY_PREFIX}${toolName}`;
}

function getDailyCount(toolName: string): number {
  try {
    const key = getDailyKey(toolName);
    const stored = localStorage.getItem(key);
    if (stored) {
      const data = JSON.parse(stored) as { count: number; date: string };
      // Check if it's today's date
      const today = new Date().toISOString().split("T")[0];
      if (data.date === today) {
        return data.count;
      }
    }
  } catch (error) {
    console.warn("[RateLimits] Failed to load daily count:", error);
  }
  return 0;
}

function incrementDailyCount(toolName: string): void {
  try {
    const key = getDailyKey(toolName);
    const today = new Date().toISOString().split("T")[0];
    const current = getDailyCount(toolName);
    localStorage.setItem(key, JSON.stringify({ count: current + 1, date: today }));
  } catch (error) {
    console.warn("[RateLimits] Failed to save daily count:", error);
  }
}

/**
 * Check if a tool call is allowed under rate limits
 */
export function checkRateLimit(toolName: string): RateLimitStatus {
  const config = DEFAULT_LIMITS[toolName] || { maxPerDay: 100, maxPerSession: undefined };
  const callsToday = getDailyCount(toolName);
  const sessionCounts = getSessionCounts();
  const callsThisSession = sessionCounts[toolName] || 0;

  // Check daily limit
  if (callsToday >= config.maxPerDay) {
    return {
      toolName,
      callsToday,
      maxPerDay: config.maxPerDay,
      callsThisSession,
      maxPerSession: config.maxPerSession,
      canCall: false,
      blockedReason: `Daily limit reached (${callsToday}/${config.maxPerDay}). Resets at midnight UTC.`,
    };
  }

  // Check session limit
  if (config.maxPerSession !== undefined && callsThisSession >= config.maxPerSession) {
    return {
      toolName,
      callsToday,
      maxPerDay: config.maxPerDay,
      callsThisSession,
      maxPerSession: config.maxPerSession,
      canCall: false,
      blockedReason: `Session limit reached (${callsThisSession}/${config.maxPerSession}).`,
    };
  }

  return {
    toolName,
    callsToday,
    maxPerDay: config.maxPerDay,
    callsThisSession,
    maxPerSession: config.maxPerSession,
    canCall: true,
  };
}

/**
 * Record a tool call (increment counters)
 */
export async function recordToolCall(toolName: string): Promise<void> {
  incrementDailyCount(toolName);
  const sessionCounts = getSessionCounts();
  sessionCounts[toolName] = (sessionCounts[toolName] || 0) + 1;
  saveSessionCounts(sessionCounts);
}

/**
 * Reset session limit for a tool
 */
export function resetSessionLimit(toolName: string): void {
  const sessionCounts = getSessionCounts();
  delete sessionCounts[toolName];
  saveSessionCounts(sessionCounts);
}

/**
 * Get rate limit store instance
 */
export function getRateLimitStore(): RateLimitStore {
  return store;
}
