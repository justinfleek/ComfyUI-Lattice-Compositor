/**
 * Type Utilities
 *
 * Reusable type-safe utility functions for object manipulation.
 */

/**
 * Type-safe omit - removes specified keys from object.
 * Returns new object with proper Omit<T, K> type inference.
 *
 * @example
 * const config = omitKeys(runtimeEmitter, ['accumulator', 'burstTimer', 'velocity'] as const);
 * // TypeScript infers: Omit<RuntimeEmitter, 'accumulator' | 'burstTimer' | 'velocity'>
 */
export function omitKeys<T extends object, K extends keyof T>(
  obj: T,
  keys: readonly K[],
): Omit<T, K> {
  const result = { ...obj } as Record<string, unknown>;
  for (const key of keys) {
    delete result[key as string];
  }
  return result as Omit<T, K>;
}
