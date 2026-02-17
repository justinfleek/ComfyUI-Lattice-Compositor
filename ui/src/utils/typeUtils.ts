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
  // Create a copy and delete specified keys
  const result = { ...obj } as Partial<T>;
  for (const key of keys) {
    delete result[key];
  }
  return result as Omit<T, K>;
}
