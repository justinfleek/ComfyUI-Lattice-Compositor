/**
 * Retry Utility
 *
 * Implements exponential backoff retry logic for async operations.
 * Useful for handling transient failures in network requests, API calls, etc.
 *
 * SECURITY: Prevents cascading failures by retrying transient errors.
 */

export interface RetryOptions {
  /** Maximum number of retry attempts (default: 3) */
  maxAttempts?: number;
  /** Initial delay in milliseconds (default: 1000) */
  initialDelay?: number;
  /** Maximum delay in milliseconds (default: 10000) */
  maxDelay?: number;
  /** Multiplier for exponential backoff (default: 2) */
  multiplier?: number;
  /** Function to determine if error is retryable (default: all errors are retryable) */
  isRetryable?: (error: unknown) => boolean;
  /** Optional callback before each retry */
  onRetry?: (attempt: number, error: unknown) => void;
}

const DEFAULT_OPTIONS: Required<Omit<RetryOptions, "isRetryable" | "onRetry">> = {
  maxAttempts: 3,
  initialDelay: 1000,
  maxDelay: 10000,
  multiplier: 2,
};

/**
 * Sleep for specified milliseconds
 */
function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

/**
 * Calculate delay for exponential backoff
 */
function calculateDelay(
  attempt: number,
  initialDelay: number,
  maxDelay: number,
  multiplier: number,
): number {
  const delay = initialDelay * Math.pow(multiplier, attempt);
  return Math.min(delay, maxDelay);
}

/**
 * Retry an async operation with exponential backoff
 *
 * @param fn - Async function to retry
 * @param options - Retry configuration options
 * @returns Result of the function if successful
 * @throws Last error if all retries fail
 *
 * @example
 * ```typescript
 * const result = await retry(
 *   () => fetch('/api/data'),
 *   { maxAttempts: 5, initialDelay: 500 }
 * );
 * ```
 */
export async function retry<T>(
  fn: () => Promise<T>,
  options: RetryOptions = {},
): Promise<T> {
  const {
    maxAttempts = DEFAULT_OPTIONS.maxAttempts,
    initialDelay = DEFAULT_OPTIONS.initialDelay,
    maxDelay = DEFAULT_OPTIONS.maxDelay,
    multiplier = DEFAULT_OPTIONS.multiplier,
    isRetryable = () => true,
    onRetry,
  } = options;

  let lastError: unknown;

  for (let attempt = 0; attempt < maxAttempts; attempt++) {
    try {
      return await fn();
    } catch (error) {
      lastError = error;

      // Check if error is retryable
      if (!isRetryable(error)) {
        throw error;
      }

      // Don't retry on last attempt
      if (attempt === maxAttempts - 1) {
        throw error;
      }

      // Calculate delay and wait
      const delay = calculateDelay(attempt, initialDelay, maxDelay, multiplier);
      await sleep(delay);

      // Call retry callback if provided
      if (onRetry) {
        onRetry(attempt + 1, error);
      }
    }
  }

  // This should never be reached, but TypeScript needs it
  throw lastError;
}

/**
 * Retry with custom retry condition
 *
 * @example
 * ```typescript
 * // Only retry on network errors
 * const result = await retryIf(
 *   () => fetch('/api/data'),
 *   (error) => error instanceof TypeError && error.message.includes('network'),
 *   { maxAttempts: 3 }
 * );
 * ```
 */
export async function retryIf<T>(
  fn: () => Promise<T>,
  condition: (error: unknown) => boolean,
  options: Omit<RetryOptions, "isRetryable"> = {},
): Promise<T> {
  return retry(fn, { ...options, isRetryable: condition });
}

/**
 * Retry with fixed delay (no exponential backoff)
 */
export async function retryWithFixedDelay<T>(
  fn: () => Promise<T>,
  delay: number,
  maxAttempts: number = 3,
): Promise<T> {
  return retry(fn, {
    maxAttempts,
    initialDelay: delay,
    maxDelay: delay,
    multiplier: 1,
  });
}
