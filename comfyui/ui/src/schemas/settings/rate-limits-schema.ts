/**
 * Rate Limits Schema
 *
 * Zod schemas for validating rate limit data stored in localStorage/sessionStorage.
 * Low priority - only affects rate limiting, not security critical.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ============================================================================
// Primitives
// ============================================================================

const nonNegativeInt = z.number().int().nonnegative();
const positiveFinite = z.number().finite().positive();

// ============================================================================
// Rate Limit Config Schema
// ============================================================================

export const RateLimitConfigSchema = z.object({
  toolName: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  maxPerDay: positiveFinite.max(100000), // Max 100k calls per day
  maxPerSession: positiveFinite.max(10000).optional(), // Max 10k calls per session
  vramCostMB: positiveFinite.max(1000000).optional(), // Max 1TB VRAM cost
}).strict();

export type RateLimitConfig = z.infer<typeof RateLimitConfigSchema>;

// ============================================================================
// Rate Limit Status Schema
// ============================================================================

export const RateLimitStatusSchema = z.object({
  toolName: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  callsToday: nonNegativeInt.max(100000), // Max 100k calls today
  maxPerDay: positiveFinite.max(100000), // Max 100k calls per day
  callsThisSession: nonNegativeInt.max(10000), // Max 10k calls this session
  maxPerSession: positiveFinite.max(10000).optional(), // Max 10k calls per session
  canCall: z.boolean(),
  blockedReason: z.string().max(500).trim().optional(),
  resetsAt: z.string().datetime(), // ISO timestamp
  resetsIn: z.string().max(100).trim(), // Human readable
}).strict().refine(
  (data) => {
    // callsToday should be <= maxPerDay
    return data.callsToday <= data.maxPerDay;
  },
  { message: "callsToday must be <= maxPerDay", path: ["callsToday"] }
).refine(
  (data) => {
    // callsThisSession should be <= maxPerSession if set
    if (data.maxPerSession !== undefined) {
      return data.callsThisSession <= data.maxPerSession;
    }
    return true;
  },
  { message: "callsThisSession must be <= maxPerSession", path: ["callsThisSession"] }
);

export type RateLimitStatus = z.infer<typeof RateLimitStatusSchema>;

// ============================================================================
// Stored Rate Limits Schema
// ============================================================================

/**
 * Rate limits stored in localStorage
 */
export const StoredRateLimitsSchema = z.object({
  date: z.string().regex(/^\d{4}-\d{2}-\d{2}$/), // YYYY-MM-DD format
  counts: z.record(z.string().max(MAX_NAME_LENGTH), nonNegativeInt.max(100000)).refine(
    (counts) => Object.keys(counts).length <= 1000,
    { message: "Maximum 1000 rate limit keys" }
  ),
  lastReset: z.string().datetime(), // ISO timestamp
}).strict();

export type StoredRateLimits = z.infer<typeof StoredRateLimitsSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateStoredRateLimits(data: unknown): StoredRateLimits {
  return StoredRateLimitsSchema.parse(data);
}

export function safeValidateStoredRateLimits(data: unknown) {
  return StoredRateLimitsSchema.safeParse(data);
}
