// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                          // input // validation // utilities
// ════════════════════════════════════════════════════════════════════════════
// Runtime validation for input boundaries (AI commands, file imports, user input)
// These functions ACTUALLY CHECK values at runtime, not just assert types.
// ════════════════════════════════════════════════════════════════════════════

import type { JSONValue } from "@/types/dataAsset";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

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

// ════════════════════════════════════════════════════════════════════════════
//                                                   // primitive // validators
// ════════════════════════════════════════════════════════════════════════════

/**
 * Validate that value is a string
 */
export function validateString(
  value: RuntimeValue,
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
  value: RuntimeValue,
  name: string,
  options: { min?: number; max?: number; allowNaN?: boolean } = {},
): ValidationResult<number> {
  const num = typeof value === "number" ? value : Number(value);

  if (Number.isNaN(num)) {
    if (options.allowNaN) return ok(num);
    return fail(`${name} must be a valid number, got NaN`);
  }

  if (!Number.isFinite(num)) {
    return fail(`${name} must be a finite number, got ${String(value)}`);
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
  value: RuntimeValue,
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
  value: RuntimeValue,
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
  value: RuntimeValue,
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

// ════════════════════════════════════════════════════════════════════════════
//                                                       // array // validators
// ════════════════════════════════════════════════════════════════════════════

/**
 * Validate that value is an array
 */
export function validateArray<T extends JSONValue>(
  value: RuntimeValue,
  name: string,
  itemValidator: (item: JSONValue, index: number) => ValidationResult<T>,
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
    const itemValue = value[i] as JSONValue;
    const itemResult = itemValidator(itemValue, i);
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
  value: RuntimeValue,
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
    (item, i) => {
      const itemValue = item as RuntimeValue;
      return validateFiniteNumber(itemValue, `item ${i}`, {
        min: options.min,
        max: options.max,
      });
    },
    { minLength: options.minLength, maxLength: options.maxLength },
  );
}

// ════════════════════════════════════════════════════════════════════════════
//                                                      // object // validators
// ════════════════════════════════════════════════════════════════════════════

/**
 * Generic object type for validation
 */
export interface ValidatedObject {
  [key: string]: JSONValue;
}

/**
 * Validate that value is a non-null object
 */
export function validateObject(
  value: RuntimeValue,
  name: string,
): ValidationResult<ValidatedObject> {
  if (typeof value !== "object" || value === null) {
    return fail(
      `${name} must be an object, got ${value === null ? "null" : typeof value}`,
    );
  }
  return ok(value as ValidatedObject);
}

/**
 * Validate a Vec2 (x, y coordinates)
 */
export function validateVec2(
  value: RuntimeValue,
  name: string,
): ValidationResult<{ x: number; y: number }> {
  const objResult = validateObject(value, name);
  if (!objResult.ok) return objResult;

  const obj = objResult.value;
  const xValue = obj.x as RuntimeValue;
  const x = validateFiniteNumber(xValue, `${name}.x`);
  if (!x.ok) return x;

  const yValue = obj.y as RuntimeValue;
  const y = validateFiniteNumber(yValue, `${name}.y`);
  if (!y.ok) return y;

  return ok({ x: x.value, y: y.value });
}

/**
 * Validate a Vec3 (x, y, z coordinates)
 */
export function validateVec3(
  value: RuntimeValue,
  name: string,
  options: { allowMissingZ?: boolean } = {},
): ValidationResult<{ x: number; y: number; z: number }> {
  const objResult = validateObject(value, name);
  if (!objResult.ok) return objResult;

  const obj = objResult.value;
  const xValue = obj.x as RuntimeValue;
  const x = validateFiniteNumber(xValue, `${name}.x`);
  if (!x.ok) return x;

  const yValue = obj.y as RuntimeValue;
  const y = validateFiniteNumber(yValue, `${name}.y`);
  if (!y.ok) return y;

  let z: number;
  if (obj.z === undefined && options.allowMissingZ) {
    z = 0;
  } else {
    const zValue = obj.z as RuntimeValue;
    const zResult = validateFiniteNumber(zValue, `${name}.z`);
    if (!zResult.ok) return zResult;
    z = zResult.value;
  }

  return ok({ x: x.value, y: y.value, z });
}

/**
 * Validate a color object (r, g, b, optional a)
 */
export function validateColor(
  value: RuntimeValue,
  name: string,
): ValidationResult<{ r: number; g: number; b: number; a?: number }> {
  const objResult = validateObject(value, name);
  if (!objResult.ok) return objResult;

  const obj = objResult.value;
  const rValue = obj.r as RuntimeValue;
  const r = validateFiniteNumber(rValue, `${name}.r`, { min: 0, max: 255 });
  if (!r.ok) return r;

  const gValue = obj.g as RuntimeValue;
  const g = validateFiniteNumber(gValue, `${name}.g`, { min: 0, max: 255 });
  if (!g.ok) return g;

  const bValue = obj.b as RuntimeValue;
  const b = validateFiniteNumber(bValue, `${name}.b`, { min: 0, max: 255 });
  if (!b.ok) return b;

  if (obj.a !== undefined) {
    const aValue = obj.a as RuntimeValue;
    const a = validateFiniteNumber(aValue, `${name}.a`, { min: 0, max: 1 });
    if (!a.ok) return a;
    return ok({ r: r.value, g: g.value, b: b.value, a: a.value });
  }

  return ok({ r: r.value, g: g.value, b: b.value });
}

// ════════════════════════════════════════════════════════════════════════════
//                                                    // optional // validators
// ════════════════════════════════════════════════════════════════════════════

/**
 * Make a validator optional - returns undefined if value is undefined/null
 */
export function optional<T extends JSONValue>(
  validator: (value: RuntimeValue, name: string) => ValidationResult<T>,
): (value: RuntimeValue, name: string) => ValidationResult<T | undefined> {
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
export function withDefault<T extends JSONValue>(
  validator: (value: RuntimeValue, name: string) => ValidationResult<T>,
  defaultValue: T,
): (value: RuntimeValue, name: string) => ValidationResult<T> {
  return (value, name) => {
    if (value === undefined || value === null) {
      return ok(defaultValue);
    }
    return validator(value, name);
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                    // composition // helpers
// ════════════════════════════════════════════════════════════════════════════

/**
 * Validate all fields of an object schema
 * Returns typed object if all validations pass
 */
export function validateSchema<T extends ValidatedObject>(
  value: RuntimeValue,
  name: string,
  schema: {
    [K in keyof T]: (value: JSONValue, name: string) => ValidationResult<T[K]>;
  },
): ValidationResult<T> {
  const objResult = validateObject(value, name);
  if (!objResult.ok) return objResult;

  const obj = objResult.value;
  const result: Partial<T> = {};

  for (const key of Object.keys(schema) as (keyof T)[]) {
    const fieldValidator = schema[key];
    const fieldValue = obj[key as string] as JSONValue;
    const fieldResult = fieldValidator(
      fieldValue,
      `${name}.${String(key)}`,
    );
    if (!fieldResult.ok) {
      return fieldResult as ValidationResult<T>;
    }
    result[key] = fieldResult.value;
  }

  return ok(result as T);
}

// ════════════════════════════════════════════════════════════════════════════
//                                                      // error // aggregation
// ════════════════════════════════════════════════════════════════════════════

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
