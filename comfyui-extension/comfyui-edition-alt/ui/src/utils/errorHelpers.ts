/**
 * Error Helper Utilities
 *
 * Standardized error message formatting across the codebase.
 * Provides consistent error context and helpful debugging information.
 */

/**
 * Create a contextual error with standard format:
 * [Context] Action failed: Reason. How to fix.
 *
 * @param context - The module/component context (e.g., "ModelExport", "DataImport")
 * @param action - What action was being performed (e.g., "WanMove export", "JSON parsing")
 * @param reason - Why it failed (e.g., "No animated layers found", "Invalid JSON syntax")
 * @param fix - Optional suggestion on how to fix the issue
 */
export function createContextualError(
  context: string,
  action: string,
  reason: string,
  fix?: string,
): Error {
  const message = `[${context}] ${action} failed: ${reason}.${fix ? ` ${fix}` : ""}`;
  return new Error(message);
}

/**
 * Create a validation error for field/value mismatches
 *
 * @param field - The field name that failed validation
 * @param value - The actual value received
 * @param expected - What was expected (e.g., "positive number", "array", "function")
 */
export function createValidationError(
  field: string,
  value: unknown,
  expected: string,
): Error {
  return createContextualError(
    "Validation",
    `Field "${field}" validation`,
    `got ${typeof value} (${JSON.stringify(value)}), expected ${expected}`,
    `Provide a valid ${expected} value for ${field}`,
  );
}
