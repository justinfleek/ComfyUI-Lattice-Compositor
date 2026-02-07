/**
 * Debounce and Throttle Utilities
 *
 * Control function execution frequency for performance optimization.
 * - Debounce: Delay execution until after a period of inactivity
 * - Throttle: Limit execution to at most once per time period
 */

/**
 * Debounce a function - delays execution until after a period of inactivity
 *
 * @param fn - Function to debounce
 * @param delay - Delay in milliseconds
 * @param immediate - If true, execute immediately on first call
 * @returns Debounced function
 *
 * @example
 * ```typescript
 * const debouncedSearch = debounce((query: string) => {
 *   searchAPI(query);
 * }, 300);
 *
 * // User types "hello" quickly
 * debouncedSearch('h'); // Cancelled
 * debouncedSearch('he'); // Cancelled
 * debouncedSearch('hel'); // Cancelled
 * debouncedSearch('hell'); // Cancelled
 * debouncedSearch('hello'); // Executes after 300ms of no calls
 * ```
 */
export function debounce<T extends (...args: unknown[]) => unknown>(
  fn: T,
  delay: number,
  immediate: boolean = false,
): (...args: Parameters<T>) => void {
  let timeoutId: ReturnType<typeof setTimeout> | null = null;
  let hasCalled = false;

  return function (this: unknown, ...args: Parameters<T>): void {
    const callNow = immediate && !hasCalled;

    if (timeoutId !== null) {
      clearTimeout(timeoutId);
    }

    timeoutId = setTimeout(() => {
      timeoutId = null;
      hasCalled = false;
      if (!immediate) {
        fn.apply(this, args);
      }
    }, delay);

    if (callNow) {
      hasCalled = true;
      fn.apply(this, args);
    }
  };
}

/**
 * Throttle a function - limits execution to at most once per time period
 *
 * @param fn - Function to throttle
 * @param delay - Minimum time between executions in milliseconds
 * @returns Throttled function
 *
 * @example
 * ```typescript
 * const throttledScroll = throttle(() => {
 *   updateScrollPosition();
 * }, 100);
 *
 * // User scrolls rapidly
 * throttledScroll(); // Executes immediately
 * throttledScroll(); // Ignored (within 100ms)
 * throttledScroll(); // Ignored (within 100ms)
 * // After 100ms...
 * throttledScroll(); // Executes
 * ```
 */
export function throttle<T extends (...args: unknown[]) => unknown>(
  fn: T,
  delay: number,
): (...args: Parameters<T>) => void {
  let lastCall = 0;
  let timeoutId: ReturnType<typeof setTimeout> | null = null;

  return function (this: unknown, ...args: Parameters<T>): void {
    const now = Date.now();
    const timeSinceLastCall = now - lastCall;

    if (timeSinceLastCall >= delay) {
      // Enough time has passed, execute immediately
      lastCall = now;
      fn.apply(this, args);
    } else {
      // Schedule execution for when delay period ends
      if (timeoutId !== null) {
        clearTimeout(timeoutId);
      }

      timeoutId = setTimeout(() => {
        lastCall = Date.now();
        timeoutId = null;
        fn.apply(this, args);
      }, delay - timeSinceLastCall);
    }
  };
}

/**
 * Debounce with leading edge execution
 * Executes immediately on first call, then debounces subsequent calls
 */
export function debounceLeading<T extends (...args: unknown[]) => unknown>(
  fn: T,
  delay: number,
): (...args: Parameters<T>) => void {
  return debounce(fn, delay, true);
}

/**
 * Throttle with leading edge execution
 * Executes immediately, then throttles subsequent calls
 */
export function throttleLeading<T extends (...args: unknown[]) => unknown>(
  fn: T,
  delay: number,
): (...args: Parameters<T>) => void {
  let lastCall = 0;

  return function (this: unknown, ...args: Parameters<T>): void {
    const now = Date.now();
    if (now - lastCall >= delay) {
      lastCall = now;
      fn.apply(this, args);
    }
  };
}
