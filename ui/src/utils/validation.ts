// ============================================================================
// INPUT VALIDATION UTILITIES
// ============================================================================
// Runtime validation for input boundaries (AI commands, file imports, user input)
// These functions ACTUALLY CHECK values at runtime, not just assert types.
// ============================================================================

/**
 * Validation result - either success with typed value, or failure with error message
 */
export type ValidationResult<T> =
  | { ok: true; value: T }
  | { ok: false; error: string };

/**
 * Helper to create success result
 */
export function ok<T>(value: T): ValidationResult<T> {
  return { ok: true, value };
}

/**
 * Helper to create failure result
 */
export function fail<T>(error: string): ValidationResult<T> {
  return { ok: false, error };
}

// ============================================================================
// PRIMITIVE VALIDATORS
// ============================================================================

/**
 * Validate that value is a string
 */
export function validateString(
  value: unknown,
  name: string,
  options: { minLength?: number; maxLength?: number; allowEmpty?: boolean } = {},
): ValidationResult<string> {
  if (typeof value !== "string") {
    return fail(`${name} must be a string, got ${typeof value}`);
  }
  if (!options.allowEmpty && value.length === 0) {
    return fail(`${name} cannot be empty`);
  }
  if (options.minLength !== undefined && value.length < options.minLength) {
    return fail(`${name} must be at least ${options.minLength} characters`);
  }
  if (options.maxLength !== undefined && value.length > options.maxLength) {
    return fail(`${name} must be at most ${options.maxLength} characters`);
  }
  return ok(value);
}

/**
 * Validate that value is a finite number (not NaN, not Infinity)
 */
export function validateFiniteNumber(
  value: unknown,
  name: string,
  options: { min?: number; max?: number; allowNaN?: boolean } = {},
): ValidationResult<number> {
  const num = typeof value === "number" ? value : Number(value);

  if (Number.isNaN(num)) {
    if (options.allowNaN) return ok(num);
    return fail(`${name} must be a valid number, got NaN`);
  }

  if (!Number.isFinite(num)) {
    return fail(`${name} must be a finite number, got ${value}`);
  }

  if (options.min !== undefined && num < options.min) {
    return fail(`${name} must be >= ${options.min}, got ${num}`);
  }

  if (options.max !== undefined && num > options.max) {
    return fail(`${name} must be <= ${options.max}, got ${num}`);
  }

  return ok(num);
}

/**
 * Validate that value is an integer
 */
export function validateInteger(
  value: unknown,
  name: string,
  options: { min?: number; max?: number } = {},
): ValidationResult<number> {
  const result = validateFiniteNumber(value, name, options);
  if (!result.ok) return result;

  if (!Number.isInteger(result.value)) {
    return fail(`${name} must be an integer, got ${result.value}`);
  }

  return result;
}

/**
 * Validate that value is a boolean
 */
export function validateBoolean(
  value: unknown,
  name: string,
): ValidationResult<boolean> {
  if (typeof value !== "boolean") {
    return fail(`${name} must be a boolean, got ${typeof value}`);
  }
  return ok(value);
}

/**
 * Validate that value is one of allowed values
 */
export function validateEnum<T extends string>(
  value: unknown,
  name: string,
  allowed: readonly T[],
): ValidationResult<T> {
  if (typeof value !== "string") {
    return fail(`${name} must be a string, got ${typeof value}`);
  }
  if (!allowed.includes(value as T)) {
    return fail(`${name} must be one of [${allowed.join(", ")}], got "${value}"`);
  }
  return ok(value as T);
}

// ============================================================================
// ARRAY VALIDATORS
// ============================================================================

/**
 * Validate that value is an array
 */
export function validateArray<T>(
  value: unknown,
  name: string,
  itemValidator: (item: unknown, index: number) => ValidationResult<T>,
  options: { minLength?: number; maxLength?: number } = {},
): ValidationResult<T[]> {
  if (!Array.isArray(value)) {
    return fail(`${name} must be an array, got ${typeof value}`);
  }

  if (options.minLength !== undefined && value.length < options.minLength) {
    return fail(`${name} must have at least ${options.minLength} items`);
  }

  if (options.maxLength !== undefined && value.length > options.maxLength) {
    return fail(`${name} must have at most ${options.maxLength} items`);
  }

  const result: T[] = [];
  for (let i = 0; i < value.length; i++) {
    const itemResult = itemValidator(value[i], i);
    if (!itemResult.ok) {
      return fail(`${name}[${i}]: ${itemResult.error}`);
    }
    result.push(itemResult.value);
  }

  return ok(result);
}

/**
 * Validate array of finite numbers
 */
export function validateNumberArray(
  value: unknown,
  name: string,
  options: {
    minLength?: number;
    maxLength?: number;
    min?: number;
    max?: number;
  } = {},
): ValidationResult<number[]> {
  return validateArray(
    value,
    name,
    (item, i) =>
      validateFiniteNumber(item, `item ${i}`, {
        min: options.min,
        max: options.max,
      }),
    { minLength: options.minLength, maxLength: options.maxLength },
  );
}

// ============================================================================
// OBJECT VALIDATORS
// ============================================================================

/**
 * Validate that value is a non-null object
 */
export function validateObject(
  value: unknown,
  name: string,
): ValidationResult<Record<string, unknown>> {
  if (typeof value !== "object" || value === null) {
    return fail(
      `${name} must be an object, got ${value === null ? "null" : typeof value}`,
    );
  }
  return ok(value as Record<string, unknown>);
}

/**
 * Validate a Vec2 (x, y coordinates)
 */
export function validateVec2(
  value: unknown,
  name: string,
): ValidationResult<{ x: number; y: number }> {
  const objResult = validateObject(value, name);
  if (!objResult.ok) return objResult;

  const obj = objResult.value;
  const x = validateFiniteNumber(obj.x, `${name}.x`);
  if (!x.ok) return x;

  const y = validateFiniteNumber(obj.y, `${name}.y`);
  if (!y.ok) return y;

  return ok({ x: x.value, y: y.value });
}

/**
 * Validate a Vec3 (x, y, z coordinates)
 */
export function validateVec3(
  value: unknown,
  name: string,
  options: { allowMissingZ?: boolean } = {},
): ValidationResult<{ x: number; y: number; z: number }> {
  const objResult = validateObject(value, name);
  if (!objResult.ok) return objResult;

  const obj = objResult.value;
  const x = validateFiniteNumber(obj.x, `${name}.x`);
  if (!x.ok) return x;

  const y = validateFiniteNumber(obj.y, `${name}.y`);
  if (!y.ok) return y;

  let z: number;
  if (obj.z === undefined && options.allowMissingZ) {
    z = 0;
  } else {
    const zResult = validateFiniteNumber(obj.z, `${name}.z`);
    if (!zResult.ok) return zResult;
    z = zResult.value;
  }

  return ok({ x: x.value, y: y.value, z });
}

/**
 * Validate a color object (r, g, b, optional a)
 */
export function validateColor(
  value: unknown,
  name: string,
): ValidationResult<{ r: number; g: number; b: number; a?: number }> {
  const objResult = validateObject(value, name);
  if (!objResult.ok) return objResult;

  const obj = objResult.value;
  const r = validateFiniteNumber(obj.r, `${name}.r`, { min: 0, max: 255 });
  if (!r.ok) return r;

  const g = validateFiniteNumber(obj.g, `${name}.g`, { min: 0, max: 255 });
  if (!g.ok) return g;

  const b = validateFiniteNumber(obj.b, `${name}.b`, { min: 0, max: 255 });
  if (!b.ok) return b;

  if (obj.a !== undefined) {
    const a = validateFiniteNumber(obj.a, `${name}.a`, { min: 0, max: 1 });
    if (!a.ok) return a;
    return ok({ r: r.value, g: g.value, b: b.value, a: a.value });
  }

  return ok({ r: r.value, g: g.value, b: b.value });
}

// ============================================================================
// OPTIONAL VALIDATORS
// ============================================================================

/**
 * Make a validator optional - returns undefined if value is undefined/null
 */
export function optional<T>(
  validator: (value: unknown, name: string) => ValidationResult<T>,
): (value: unknown, name: string) => ValidationResult<T | undefined> {
  return (value, name) => {
    if (value === undefined || value === null) {
      return ok(undefined);
    }
    return validator(value, name);
  };
}

/**
 * Provide a default value if undefined
 */
export function withDefault<T>(
  validator: (value: unknown, name: string) => ValidationResult<T>,
  defaultValue: T,
): (value: unknown, name: string) => ValidationResult<T> {
  return (value, name) => {
    if (value === undefined || value === null) {
      return ok(defaultValue);
    }
    return validator(value, name);
  };
}

// ============================================================================
// COMPOSITION HELPERS
// ============================================================================

/**
 * Validate all fields of an object schema
 * Returns typed object if all validations pass
 */
export function validateSchema<T extends Record<string, unknown>>(
  value: unknown,
  name: string,
  schema: {
    [K in keyof T]: (value: unknown, name: string) => ValidationResult<T[K]>;
  },
): ValidationResult<T> {
  const objResult = validateObject(value, name);
  if (!objResult.ok) return objResult;

  const obj = objResult.value;
  const result: Partial<T> = {};

  for (const key of Object.keys(schema) as (keyof T)[]) {
    const fieldValidator = schema[key];
    const fieldResult = fieldValidator(
      obj[key as string],
      `${name}.${String(key)}`,
    );
    if (!fieldResult.ok) {
      return fieldResult as ValidationResult<T>;
    }
    result[key] = fieldResult.value;
  }

  return ok(result as T);
}

// ============================================================================
// ERROR AGGREGATION
// ============================================================================

/**
 * Collect all validation errors instead of failing on first
 */
export function validateAll<T>(
  validations: Array<() => ValidationResult<unknown>>,
  onSuccess: () => T,
): ValidationResult<T> {
  const errors: string[] = [];

  for (const validate of validations) {
    const result = validate();
    if (!result.ok) {
      errors.push(result.error);
    }
  }

  if (errors.length > 0) {
    return fail(errors.join("; "));
  }

  return ok(onSuccess());
}
