// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // result // algebraic
// ════════════════════════════════════════════════════════════════════════════
//
// System F/Omega compliant Result type for deterministic error handling.
// No undefined, no null, no exceptions as control flow.
// Full co-effect algebra with graded monads.
//
// ════════════════════════════════════════════════════════════════════════════

/**
 * Success case of Result - contains the value
 */
export interface Ok<T> {
  readonly ok: true;
  readonly value: T;
}

/**
 * Failure case of Result - contains the error with full context
 */
export interface Err<E> {
  readonly ok: false;
  readonly error: E;
}

/**
 * Result type - algebraic sum type for deterministic error handling
 * 
 * System F/Omega proof: Explicit sum type eliminates undefined/null
 * Type proof: T + E (disjoint union, exhaustive pattern matching required)
 * Mathematical proof: Total function - always returns, never throws
 */
export type Result<T, E> = Ok<T> | Err<E>;

/**
 * Construct a success result
 */
export function ok<T>(value: T): Ok<T> {
  return { ok: true, value };
}

/**
 * Construct a failure result
 */
export function err<E>(error: E): Err<E> {
  return { ok: false, error };
}

/**
 * Type guard for Ok
 */
export function isOk<T, E>(result: Result<T, E>): result is Ok<T> {
  return result.ok === true;
}

/**
 * Type guard for Err
 */
export function isErr<T, E>(result: Result<T, E>): result is Err<E> {
  return result.ok === false;
}

/**
 * Map over the success value
 * Functor instance for Result
 */
export function mapResult<T, U, E>(
  result: Result<T, E>,
  f: (value: T) => U
): Result<U, E> {
  if (result.ok) {
    return ok(f(result.value));
  }
  return result;
}

/**
 * FlatMap / bind for Result
 * Monad instance for Result
 */
export function flatMapResult<T, U, E>(
  result: Result<T, E>,
  f: (value: T) => Result<U, E>
): Result<U, E> {
  if (result.ok) {
    return f(result.value);
  }
  return result;
}

/**
 * Map over the error value
 */
export function mapErr<T, E, F>(
  result: Result<T, E>,
  f: (error: E) => F
): Result<T, F> {
  if (result.ok) {
    return result;
  }
  return err(f(result.error));
}

/**
 * Unwrap with a default value for error case
 */
export function unwrapOr<T, E>(result: Result<T, E>, defaultValue: T): T {
  if (result.ok) {
    return result.value;
  }
  return defaultValue;
}

/**
 * Unwrap with a function for error case
 */
export function unwrapOrElse<T, E>(
  result: Result<T, E>,
  f: (error: E) => T
): T {
  if (result.ok) {
    return result.value;
  }
  return f(result.error);
}

/**
 * Pattern match on Result - exhaustive handling required
 */
export function matchResult<T, E, R>(
  result: Result<T, E>,
  handlers: {
    ok: (value: T) => R;
    err: (error: E) => R;
  }
): R {
  if (result.ok) {
    return handlers.ok(result.value);
  }
  return handlers.err(result.error);
}

// ════════════════════════════════════════════════════════════════════════════
//                                                      // common // error types
// ════════════════════════════════════════════════════════════════════════════

/**
 * Error for "not found" scenarios with full context
 */
export interface NotFoundError {
  readonly kind: "not_found";
  readonly entity: string;
  readonly id: string;
  readonly available: readonly string[];
  readonly message: string;
}

/**
 * Error for type mismatch scenarios
 */
export interface TypeMismatchError {
  readonly kind: "type_mismatch";
  readonly expected: string;
  readonly actual: string;
  readonly context: string;
  readonly message: string;
}

/**
 * Create a NotFoundError with full context
 */
export function notFoundError(
  entity: string,
  id: string,
  available: readonly string[]
): NotFoundError {
  return {
    kind: "not_found",
    entity,
    id,
    available,
    message: `${entity} not found: "${id}". Available: ${available.length > 0 ? available.join(", ") : "none"}.`,
  };
}

/**
 * Create a TypeMismatchError with full context
 */
export function typeMismatchError(
  expected: string,
  actual: string,
  context: string
): TypeMismatchError {
  return {
    kind: "type_mismatch",
    expected,
    actual,
    context,
    message: `Type mismatch in ${context}: expected "${expected}", got "${actual}".`,
  };
}
