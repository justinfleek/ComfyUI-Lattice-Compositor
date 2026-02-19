/**
 * Session Storage Schema
 *
 * Zod schemas for validating data stored in sessionStorage.
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

// ============================================================================
// Session Counts Schema
// ============================================================================

/**
 * Session counts stored in sessionStorage for rate limiting
 */
export const SessionCountsSchema = z.record(
  z.string().max(MAX_NAME_LENGTH).trim(),
  nonNegativeInt.max(100000) // Max 100k calls per session
).refine(
  (counts) => Object.keys(counts).length <= 1000,
  { message: "Maximum 1000 session count keys" }
);

export type SessionCounts = z.infer<typeof SessionCountsSchema>;

// ============================================================================
// Audit Session ID Schema
// ============================================================================

/**
 * Audit session ID stored in sessionStorage
 */
export const AuditSessionIdSchema = z.string().uuid();

export type AuditSessionId = z.infer<typeof AuditSessionIdSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateSessionCounts(data: unknown): SessionCounts {
  return SessionCountsSchema.parse(data);
}

export function safeValidateSessionCounts(data: unknown) {
  return SessionCountsSchema.safeParse(data);
}

export function validateAuditSessionId(data: unknown): AuditSessionId {
  return AuditSessionIdSchema.parse(data);
}

export function safeValidateAuditSessionId(data: unknown) {
  return AuditSessionIdSchema.safeParse(data);
}
