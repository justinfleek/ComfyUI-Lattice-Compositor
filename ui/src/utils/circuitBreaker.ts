/**
 * Circuit Breaker Utility
 *
 * Implements circuit breaker pattern to prevent cascading failures.
 * When a service is failing, the circuit breaker "opens" and stops
 * making requests until the service recovers.
 *
 * SECURITY: Prevents cascading failures and resource exhaustion.
 */

export type CircuitState = "closed" | "open" | "half-open";

export interface CircuitBreakerOptions {
  /** Number of failures before opening circuit (default: 5) */
  failureThreshold?: number;
  /** Time in milliseconds before attempting to close circuit (default: 60000) */
  resetTimeout?: number;
  /** Time window in milliseconds for counting failures (default: 60000) */
  monitoringWindow?: number;
  /** Optional callback when circuit opens */
  onOpen?: () => void;
  /** Optional callback when circuit closes */
  onClose?: () => void;
  /** Optional callback when circuit half-opens */
  onHalfOpen?: () => void;
}

const DEFAULT_OPTIONS: Required<
  Omit<CircuitBreakerOptions, "onOpen" | "onClose" | "onHalfOpen">
> = {
  failureThreshold: 5,
  resetTimeout: 60000, // 1 minute
  monitoringWindow: 60000, // 1 minute
};

interface FailureRecord {
  timestamp: number;
}

/**
 * Circuit Breaker class
 *
 * @example
 * ```typescript
 * const breaker = new CircuitBreaker(
 *   () => fetch('/api/data'),
 *   { failureThreshold: 3, resetTimeout: 30000 }
 * );
 *
 * try {
 *   const result = await breaker.execute();
 * } catch (error) {
 *   if (breaker.state === 'open') {
 *     // Circuit is open, service is down
 *   }
 * }
 * ```
 */
export class CircuitBreaker<T> {
  private state: CircuitState = "closed";
  private failures: FailureRecord[] = [];
  private nextAttempt: number = 0;
  private readonly options: Required<
    Omit<CircuitBreakerOptions, "onOpen" | "onClose" | "onHalfOpen">
  >;
  private readonly onOpen?: () => void;
  private readonly onClose?: () => void;
  private readonly onHalfOpen?: () => void;

  constructor(
    private readonly fn: () => Promise<T>,
    options: CircuitBreakerOptions = {},
  ) {
    this.options = {
      failureThreshold: options.failureThreshold ?? DEFAULT_OPTIONS.failureThreshold,
      resetTimeout: options.resetTimeout ?? DEFAULT_OPTIONS.resetTimeout,
      monitoringWindow:
        options.monitoringWindow ?? DEFAULT_OPTIONS.monitoringWindow,
    };
    this.onOpen = options.onOpen;
    this.onClose = options.onClose;
    this.onHalfOpen = options.onHalfOpen;
  }

  /**
   * Get current circuit state
   */
  get currentState(): CircuitState {
    this.updateState();
    return this.state;
  }

  /**
   * Check if circuit is open (blocking requests)
   */
  get isOpen(): boolean {
    return this.currentState === "open";
  }

  /**
   * Check if circuit is closed (allowing requests)
   */
  get isClosed(): boolean {
    return this.currentState === "closed";
  }

  /**
   * Check if circuit is half-open (testing recovery)
   */
  get isHalfOpen(): boolean {
    return this.currentState === "half-open";
  }

  /**
   * Update circuit state based on current conditions
   */
  private updateState(): void {
    const now = Date.now();

    // Clean old failures outside monitoring window
    this.failures = this.failures.filter(
      (f) => now - f.timestamp < this.options.monitoringWindow,
    );

    switch (this.state) {
      case "closed":
        // Check if we've exceeded failure threshold
        if (this.failures.length >= this.options.failureThreshold) {
          this.state = "open";
          this.nextAttempt = now + this.options.resetTimeout;
          this.onOpen?.();
        }
        break;

      case "open":
        // Check if reset timeout has passed
        if (now >= this.nextAttempt) {
          this.state = "half-open";
          this.onHalfOpen?.();
        }
        break;

      case "half-open":
        // Stay in half-open until success or failure
        break;
    }
  }

  /**
   * Record a failure
   */
  private recordFailure(): void {
    this.failures.push({ timestamp: Date.now() });
  }

  /**
   * Record a success (reset failures)
   */
  private recordSuccess(): void {
    if (this.state === "half-open") {
      this.state = "closed";
      this.failures = [];
      this.onClose?.();
    } else {
      // Clean old failures but keep recent ones
      const now = Date.now();
      this.failures = this.failures.filter(
        (f) => now - f.timestamp < this.options.monitoringWindow,
      );
    }
  }

  /**
   * Execute the function with circuit breaker protection
   *
   * @throws Error if circuit is open or function fails
   */
  async execute(): Promise<T> {
    this.updateState();

    if (this.state === "open") {
      throw new Error(
        `Circuit breaker is OPEN. Service unavailable. Retry after ${new Date(this.nextAttempt).toISOString()}`,
      );
    }

    try {
      const result = await this.fn();
      this.recordSuccess();
      return result;
    } catch (error) {
      this.recordFailure();
      this.updateState();
      throw error;
    }
  }

  /**
   * Reset circuit breaker to closed state
   */
  reset(): void {
    this.state = "closed";
    this.failures = [];
    this.nextAttempt = 0;
    this.onClose?.();
  }

  /**
   * Get failure count in current monitoring window
   */
  getFailureCount(): number {
    this.updateState();
    return this.failures.length;
  }
}

/**
 * Create a circuit breaker instance
 *
 * @example
 * ```typescript
 * const breaker = createCircuitBreaker(
 *   () => apiCall(),
 *   { failureThreshold: 3 }
 * );
 * ```
 */
export function createCircuitBreaker<T>(
  fn: () => Promise<T>,
  options?: CircuitBreakerOptions,
): CircuitBreaker<T> {
  return new CircuitBreaker(fn, options);
}
