// ============================================================================
// RUNTIME TYPE GUARDS
// ============================================================================
// These are ACTUAL runtime checks, not type assertions.
// They narrow TypeScript types by checking values at runtime.
// ============================================================================

// ============================================================================
// PRIMITIVE TYPE GUARDS
// ============================================================================

/**
 * Generic object type for type guards
 */
export interface GenericObject {
  [key: string]: unknown;
}

/**
 * Check if value is a non-null object
 */
export function isObject(value: unknown): value is GenericObject {
  return typeof value === "object" && value !== null;
}

/**
 * Check if value is a finite number (not NaN, not Infinity)
 */
export function isFiniteNumber(value: unknown): value is number {
  return typeof value === "number" && Number.isFinite(value);
}

/**
 * Check if value is a non-empty string
 */
export function isNonEmptyString(value: unknown): value is string {
  return typeof value === "string" && value.length > 0;
}

/**
 * Check if value is an array
 */
export function isArray(value: unknown): value is unknown[] {
  return Array.isArray(value);
}

/**
 * Check if value is a function
 */
export function isFunction(
  value: unknown,
): value is (...args: unknown[]) => unknown {
  return typeof value === "function";
}

// ============================================================================
// GEOMETRY TYPE GUARDS
// ============================================================================

/**
 * Check if value has numeric x and y properties
 */
export function hasXY(value: unknown): value is { x: number; y: number } {
  if (!isObject(value)) return false;
  return isFiniteNumber(value.x) && isFiniteNumber(value.y);
}

/**
 * Check if value has numeric x, y, and z properties
 */
export function hasXYZ(
  value: unknown,
): value is { x: number; y: number; z: number } {
  if (!isObject(value)) return false;
  return (
    isFiniteNumber(value.x) && isFiniteNumber(value.y) && isFiniteNumber(value.z)
  );
}

/**
 * Check if value is a valid bounding box
 */
export function isBoundingBox(
  value: unknown,
): value is { x: number; y: number; width: number; height: number } {
  if (!isObject(value)) return false;
  return (
    isFiniteNumber(value.x) &&
    isFiniteNumber(value.y) &&
    isFiniteNumber(value.width) &&
    isFiniteNumber(value.height)
  );
}

// ============================================================================
// COLOR TYPE GUARDS
// ============================================================================

/**
 * Check if value is a valid RGB color
 */
export function isRGBColor(
  value: unknown,
): value is { r: number; g: number; b: number } {
  if (!isObject(value)) return false;
  return (
    isFiniteNumber(value.r) &&
    isFiniteNumber(value.g) &&
    isFiniteNumber(value.b) &&
    (value.r as number) >= 0 &&
    (value.r as number) <= 255 &&
    (value.g as number) >= 0 &&
    (value.g as number) <= 255 &&
    (value.b as number) >= 0 &&
    (value.b as number) <= 255
  );
}

/**
 * Check if value is a valid RGBA color
 */
export function isRGBAColor(
  value: unknown,
): value is { r: number; g: number; b: number; a: number } {
  if (!isRGBColor(value)) return false;
  // value is already narrowed to { r: number; g: number; b: number } by isRGBColor
  return (
    "a" in value &&
    isFiniteNumber(value.a) &&
    value.a >= 0 &&
    value.a <= 1
  );
}

// ============================================================================
// ANIMATION TYPE GUARDS
// ============================================================================

/**
 * Check if value looks like an animatable property
 */
export function isAnimatableProperty(
  value: unknown,
): value is { value: unknown; animated: boolean; keyframes: unknown[] } {
  if (!isObject(value)) return false;
  return (
    "value" in value &&
    typeof value.animated === "boolean" &&
    Array.isArray(value.keyframes)
  );
}

/**
 * Check if value looks like a keyframe
 */
export function isKeyframe(
  value: unknown,
): value is { id: string; frame: number; value: unknown } {
  if (!isObject(value)) return false;
  return (
    isNonEmptyString(value.id) && isFiniteNumber(value.frame) && "value" in value
  );
}

// ============================================================================
// LAYER TYPE GUARDS
// ============================================================================

/**
 * Check if layer data has asset ID
 */
export function hasAssetId(value: unknown): value is { assetId: string | null } {
  if (!isObject(value)) return false;
  return value.assetId === null || isNonEmptyString(value.assetId);
}

/**
 * Check if layer data has composition ID (for nested comps)
 */
export function hasCompositionId(
  value: unknown,
): value is { compositionId: string } {
  if (!isObject(value)) return false;
  return isNonEmptyString(value.compositionId);
}

/**
 * Check if layer data has source URL/path
 */
export function hasSource(value: unknown): value is { source: string } {
  if (!isObject(value)) return false;
  return isNonEmptyString(value.source);
}

/**
 * Type guard: Check if layer data has width and height properties directly
 * (e.g., SolidLayerData)
 * 
 * Production-grade type guard with runtime validation:
 * - Checks that value is an object
 * - Validates width and height are finite numbers
 * - Ensures dimensions are positive (prevents division by zero)
 */
export function hasDimensions(
  value: unknown,
): value is { width: number; height: number } {
  if (!isObject(value)) return false;
  return (
    isFiniteNumber(value.width) &&
    isFiniteNumber(value.height) &&
    value.width > 0 &&
    value.height > 0
  );
}

/**
 * Type guard: Check if layer data has assetId property
 * (e.g., ImageLayerData, VideoData)
 * 
 * Production-grade type guard with runtime validation:
 * - Checks that value is an object
 * - Validates assetId exists and is either null or a string
 */
export function hasAssetIdProperty(
  value: unknown,
): value is { assetId: string | null } {
  if (!isObject(value)) return false;
  return "assetId" in value && (value.assetId === null || typeof value.assetId === "string");
}

/**
 * Check if object has a specific property with specific type
 */
export function hasProperty<K extends string, V>(
  obj: unknown,
  key: K,
  typeCheck: (value: unknown) => value is V,
): obj is Record<K, V> {
  if (!isObject(obj)) return false;
  return key in obj && typeCheck(obj[key]);
}

// ============================================================================
// ARRAY TYPE GUARDS
// ============================================================================

/**
 * Check if all elements of array satisfy a type guard
 */
export function isArrayOf<T>(
  value: unknown,
  itemGuard: (item: unknown) => item is T,
): value is T[] {
  if (!Array.isArray(value)) return false;
  return value.every(itemGuard);
}

/**
 * Check if value is an array of finite numbers
 */
export function isNumberArray(value: unknown): value is number[] {
  return isArrayOf(value, isFiniteNumber);
}

/**
 * Check if value is an array of Vec2
 */
export function isVec2Array(
  value: unknown,
): value is Array<{ x: number; y: number }> {
  return isArrayOf(value, hasXY);
}

// ============================================================================
// TRANSFORM TYPE GUARDS
// ============================================================================

/**
 * Check if value has position property with x, y coordinates
 */
export function hasPosition(
  value: unknown,
): value is { position: { value: { x: number; y: number } } } {
  if (!isObject(value)) return false;
  const pos = value.position;
  if (!isObject(pos)) return false;
  return hasXY(pos.value);
}

/**
 * Check if value has scale property with x, y values
 */
export function hasScale(
  value: unknown,
): value is { scale: { value: { x: number; y: number } } } {
  if (!isObject(value)) return false;
  const scale = value.scale;
  if (!isObject(scale)) return false;
  return hasXY(scale.value);
}

/**
 * Check if value has rotation property with numeric value
 */
export function hasRotation(
  value: unknown,
): value is { rotation: { value: number } } {
  if (!isObject(value)) return false;
  const rotation = value.rotation;
  if (!isObject(rotation)) return false;
  return isFiniteNumber(rotation.value);
}

// ============================================================================
// LAYER DATA TYPE GUARDS
// ============================================================================

/**
 * Type guard: Check if layer data is TextData
 * 
 * Production-grade type guard with runtime validation:
 * - Checks that value is an object
 * - Validates required TextData properties exist with correct types
 */
export function isTextData(value: unknown): value is import("@/types/text").TextData {
  if (!isObject(value)) return false;
  return (
    typeof value.text === "string" &&
    typeof value.fontFamily === "string" &&
    isFiniteNumber(value.fontSize) &&
    typeof value.fontWeight === "string" &&
    (value.fontStyle === "normal" || value.fontStyle === "italic") &&
    typeof value.fill === "string" &&
    typeof value.stroke === "string" &&
    isFiniteNumber(value.strokeWidth) &&
    isFiniteNumber(value.tracking) &&
    isFiniteNumber(value.lineSpacing) &&
    isFiniteNumber(value.lineAnchor) &&
    typeof value.lineHeight === "number" &&
    (value.textAlign === "left" || value.textAlign === "center" || value.textAlign === "right")
  );
}

// ============================================================================
// UTILITY: ASSERT WITH MESSAGE
// ============================================================================

/**
 * Assert condition and narrow type, throw if false
 * Use at boundaries where invalid data should crash
 */
export function assertType<T>(
  value: unknown,
  guard: (v: unknown) => v is T,
  message: string,
): asserts value is T {
  if (!guard(value)) {
    throw new TypeError(message);
  }
}

/**
 * Assert value is defined (not null or undefined)
 */
export function assertDefined<T>(
  value: T | null | undefined,
  message: string,
): asserts value is T {
  if (value === null || value === undefined) {
    throw new TypeError(message);
  }
}
