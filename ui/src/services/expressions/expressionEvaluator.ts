/**
 * Expression Evaluator
 *
 * Core expression evaluation functions including evaluateExpression,
 * evaluateCustomExpression, and preset/function evaluation.
 */

import {
  fromComp,
  fromWorld,
  type LayerTransform,
  toComp,
  toWorld,
} from "./coordinateConversion";
import { jitter } from "./jitterExpressions";
import { repeatAfter, repeatBefore } from "./loopExpressions";
import { bounce, elastic, inertia } from "./motionExpressions";
import { evaluateInSES } from "./sesEvaluator";
import type { Expression, ExpressionContext } from "./types";

/**
 * SECURITY NOTE (upgraded 2025-12-28):
 *
 * This expression evaluator now uses SES (Secure ECMAScript) for sandboxing
 * when available. SES provides stronger security guarantees than the previous
 * Proxy+with approach:
 *
 * - All JavaScript intrinsics are frozen (Object, Array, Function prototypes)
 * - Constructor chain escapes are blocked
 * - Prototype pollution is prevented
 * - No access to global objects (window, document, process, etc.)
 *
 * The old Proxy+with sandbox is kept as a fallback if SES initialization fails.
 *
 * To enable SES protection, call initializeSES() at application startup:
 *
 *   import { initializeSES } from '@/services/expressions/sesEvaluator';
 *   await initializeSES();
 *
 * @see AUDIT/SECURITY_ARCHITECTURE.md for full security analysis
 */

// ============================================================
// TIME EXPRESSIONS
// ============================================================

export const timeExpressions = {
  timeRamp(
    startTime: number,
    endTime: number,
    startValue: number,
    endValue: number,
    time: number,
  ): number {
    if (time <= startTime) return startValue;
    if (time >= endTime) return endValue;
    const duration = endTime - startTime;
    if (!Number.isFinite(duration) || duration === 0) return startValue;
    const t = (time - startTime) / duration;
    return startValue + (endValue - startValue) * t;
  },

  periodic(time: number, period: number): number {
    if (!Number.isFinite(period) || period === 0) return 0;
    return (time % period) / period;
  },

  sawtooth(time: number, frequency: number, amplitude: number = 1): number {
    if (
      !Number.isFinite(time) ||
      !Number.isFinite(frequency) ||
      !Number.isFinite(amplitude)
    )
      return 0;
    const t = time * frequency;
    return amplitude * 2 * (t - Math.floor(t + 0.5));
  },

  triangle(time: number, frequency: number, amplitude: number = 1): number {
    if (
      !Number.isFinite(time) ||
      !Number.isFinite(frequency) ||
      !Number.isFinite(amplitude)
    )
      return 0;
    const t = time * frequency;
    return amplitude * (2 * Math.abs(2 * (t - Math.floor(t + 0.5))) - 1);
  },

  square(time: number, frequency: number, amplitude: number = 1): number {
    if (
      !Number.isFinite(time) ||
      !Number.isFinite(frequency) ||
      !Number.isFinite(amplitude)
    )
      return 0;
    const t = time * frequency;
    return amplitude * (t - Math.floor(t) < 0.5 ? 1 : -1);
  },

  sine(
    time: number,
    frequency: number,
    amplitude: number = 1,
    phase: number = 0,
  ): number {
    return amplitude * Math.sin(2 * Math.PI * frequency * time + phase);
  },

  pulse(
    time: number,
    frequency: number,
    dutyCycle: number = 0.5,
    amplitude: number = 1,
  ): number {
    const t = (time * frequency) % 1;
    return amplitude * (t < dutyCycle ? 1 : 0);
  },
};

// ============================================================
// MATH EXPRESSIONS
// ============================================================

export const mathExpressions = {
  lerp(a: number, b: number, t: number): number {
    return a + (b - a) * t;
  },

  clamp(value: number, min: number, max: number): number {
    return Math.min(max, Math.max(min, value));
  },

  map(
    value: number,
    inMin: number,
    inMax: number,
    outMin: number,
    outMax: number,
  ): number {
    const range = inMax - inMin;
    if (!Number.isFinite(range) || range === 0) return outMin;
    return outMin + (outMax - outMin) * ((value - inMin) / range);
  },

  normalize(value: number, min: number, max: number): number {
    const range = max - min;
    if (!Number.isFinite(range) || range === 0) return 0;
    return (value - min) / range;
  },

  smoothstep(edge0: number, edge1: number, x: number): number {
    const range = edge1 - edge0;
    if (!Number.isFinite(range) || range === 0) {
      return x < edge0 ? 0 : 1;
    }
    const t = mathExpressions.clamp((x - edge0) / range, 0, 1);
    return t * t * (3 - 2 * t);
  },

  smootherstep(edge0: number, edge1: number, x: number): number {
    const range = edge1 - edge0;
    if (!Number.isFinite(range) || range === 0) {
      return x < edge0 ? 0 : 1;
    }
    const t = mathExpressions.clamp((x - edge0) / range, 0, 1);
    return t * t * t * (t * (t * 6 - 15) + 10);
  },

  mod(a: number, b: number): number {
    if (!Number.isFinite(b) || b === 0) return 0;
    if (!Number.isFinite(a)) return 0;
    return ((a % b) + b) % b;
  },

  distance(x1: number, y1: number, x2: number, y2: number): number {
    const dx = x2 - x1;
    const dy = y2 - y1;
    return Math.sqrt(dx * dx + dy * dy);
  },

  angleBetween(x1: number, y1: number, x2: number, y2: number): number {
    return Math.atan2(y2 - y1, x2 - x1);
  },

  degreesToRadians(degrees: number): number {
    return (degrees * Math.PI) / 180;
  },

  radiansToDegrees(radians: number): number {
    return (radians * 180) / Math.PI;
  },

  seedRandom(seed: number, min: number = 0, max: number = 1): number {
    const x = Math.sin(seed * 12.9898) * 43758.5453;
    const rand = x - Math.floor(x);
    return min + rand * (max - min);
  },

  gaussRandom(
    mean: number = 0,
    stdDev: number = 1,
    seed: number = 12345,
  ): number {
    if (
      !Number.isFinite(mean) ||
      !Number.isFinite(stdDev) ||
      !Number.isFinite(seed)
    ) {
      return 0;
    }
    const seededRand = (s: number) => {
      const x = Math.sin(s * 12.9898) * 43758.5453;
      return x - Math.floor(x);
    };
    const u1Raw = seededRand(seed);
    const u1 = Number.isFinite(u1Raw) ? Math.max(0.0001, u1Raw) : 0.0001;
    const u2Raw = seededRand(seed + 1);
    const u2 = Number.isFinite(u2Raw) ? u2Raw : 0;
    const z0 = Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
    return mean + z0 * stdDev;
  },
};

// ============================================================
// EXPRESSION EASE FUNCTIONS
// ============================================================

/**
 * Ease function for expressions (count-up animations)
 * Compatible with industry-standard ease() function
 */
export function expressionEase(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number | number[],
  vMax: number | number[],
): number | number[] {
  const range = tMax - tMin;
  let normalized: number;
  if (!Number.isFinite(range) || range === 0) {
    normalized = t < tMin ? 0 : 1;
  } else {
    normalized = (t - tMin) / range;
    normalized = Math.max(0, Math.min(1, normalized));
  }

  const eased =
    normalized < 0.5
      ? 4 * normalized * normalized * normalized
      : 1 - (-2 * normalized + 2) ** 3 / 2;

  if (Array.isArray(vMin) && Array.isArray(vMax)) {
    return vMin.map((v, i) => v + (vMax[i] - v) * eased);
  }

  return (vMin as number) + ((vMax as number) - (vMin as number)) * eased;
}

/**
 * easeIn function for expressions
 */
export function expressionEaseIn(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number | number[],
  vMax: number | number[],
): number | number[] {
  const range = tMax - tMin;
  let normalized: number;
  if (!Number.isFinite(range) || range === 0) {
    normalized = t < tMin ? 0 : 1;
  } else {
    normalized = (t - tMin) / range;
    normalized = Math.max(0, Math.min(1, normalized));
  }

  const eased = normalized * normalized * normalized;

  if (Array.isArray(vMin) && Array.isArray(vMax)) {
    return vMin.map((v, i) => v + (vMax[i] - v) * eased);
  }

  return (vMin as number) + ((vMax as number) - (vMin as number)) * eased;
}

/**
 * easeOut function for expressions
 */
export function expressionEaseOut(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number | number[],
  vMax: number | number[],
): number | number[] {
  const range = tMax - tMin;
  let normalized: number;
  if (!Number.isFinite(range) || range === 0) {
    normalized = t < tMin ? 0 : 1;
  } else {
    normalized = (t - tMin) / range;
    normalized = Math.max(0, Math.min(1, normalized));
  }

  const eased = 1 - (1 - normalized) ** 3;

  if (Array.isArray(vMin) && Array.isArray(vMax)) {
    return vMin.map((v, i) => v + (vMax[i] - v) * eased);
  }

  return (vMin as number) + ((vMax as number) - (vMin as number)) * eased;
}

// ============================================================
// EXPRESSION EVALUATOR
// ============================================================

/**
 * Evaluate an expression on a property
 */
export function evaluateExpression(
  expression: Expression,
  ctx: ExpressionContext,
): number | number[] | string {
  if (!expression.enabled) return ctx.value;

  switch (expression.type) {
    case "preset":
      return evaluatePreset(expression.name, ctx, expression.params);
    case "function":
      return evaluateFunction(expression.name, ctx, expression.params);
    case "custom":
      return evaluateCustomExpression(expression.code || "", ctx);
    default:
      return ctx.value;
  }
}

function evaluatePreset(
  name: string,
  ctx: ExpressionContext,
  params: Record<string, any>,
): number | number[] {
  switch (name) {
    case "inertia":
      return inertia(ctx, params.amplitude, params.frequency, params.decay);
    case "bounce":
      return bounce(ctx, params.elasticity, params.gravity);
    case "elastic":
      return elastic(ctx, params.amplitude, params.period);
    case "jitter":
      return jitter(ctx, params.frequency, params.amplitude, params.octaves);
    case "repeatAfter":
      return repeatAfter(ctx, params.type, params.numKeyframes);
    case "repeatBefore":
      return repeatBefore(ctx, params.type, params.numKeyframes);
    default:
      return ctx.value;
  }
}

function evaluateFunction(
  name: string,
  ctx: ExpressionContext,
  params: Record<string, any>,
): number | number[] {
  // Time functions
  if (name in timeExpressions) {
    const fn = (timeExpressions as any)[name];
    return fn(ctx.time, ...Object.values(params));
  }

  // Math functions
  if (name in mathExpressions) {
    const fn = (mathExpressions as any)[name];
    const val = typeof ctx.value === "number" ? ctx.value : ctx.value[0];
    return fn(val, ...Object.values(params));
  }

  return ctx.value;
}

/**
 * Evaluate a custom JavaScript expression string
 *
 * SECURITY: This function uses SES (Secure ECMAScript) sandbox ONLY.
 * If SES is not available, expressions are DISABLED and return ctx.value unchanged.
 * There is NO fallback to a weaker sandbox - we fail CLOSED, not open.
 *
 * To enable expressions, call initializeSES() at app startup.
 */
export function evaluateCustomExpression(
  code: string,
  ctx: ExpressionContext,
): number | number[] | string {
  // SECURITY: Type check - code must be a string
  // Prevents objects with malicious .trim() or valueOf() from being passed
  if (typeof code !== "string") {
    console.warn("[SECURITY] Expression code is not a string:", typeof code);
    return ctx.value;
  }

  // Empty code returns value unchanged
  if (!code || code.trim() === "") {
    return ctx.value;
  }

  // SECURITY: All expression evaluation goes through SES
  // evaluateInSES() handles: length limit, SES check, sandbox evaluation
  return evaluateInSES(code, ctx);
}

// =============================================================================
// LEGACY PROXY+WITH SANDBOX - REMOVED FOR SECURITY
// =============================================================================
//
// The previous Proxy+with sandbox was REMOVED because it was bypassable.
//
// Known bypasses of Proxy+with sandbox:
//   [].constructor.constructor('return this')()
//   ({}).constructor.constructor('alert(1)')()
//   try { null.f() } catch(e) { e.constructor.constructor('return window')() }
//
// The ONLY secure way to evaluate untrusted expressions is SES.
// If SES fails to load, expressions are DISABLED, not degraded.
// =============================================================================

// Helper to create thisComp object
function _createThisCompObject(ctx: ExpressionContext) {
  const fps = Number.isFinite(ctx.fps) && ctx.fps > 0 ? ctx.fps : 30;
  const duration = Number.isFinite(ctx.duration) ? ctx.duration : 0;

  return {
    duration: duration,
    frameDuration: 1 / fps,
    width: ctx.compWidth ?? 1920,
    height: ctx.compHeight ?? 1080,
    numLayers: ctx.allLayers?.length ?? 0,
    layer: (nameOrIndex: string | number) => {
      const getLayerProperty = ctx.getLayerProperty;
      const getLayerEffectParam = ctx.getLayerEffectParam;
      let layerId: string;

      if (typeof nameOrIndex === "number") {
        const layerInfo = ctx.allLayers?.find((l) => l.index === nameOrIndex);
        layerId = layerInfo?.id ?? `layer_${nameOrIndex}`;
      } else {
        const layerInfo = ctx.allLayers?.find((l) => l.name === nameOrIndex);
        layerId = layerInfo?.id ?? nameOrIndex;
      }

      const getTransform = (): LayerTransform => ({
        position: (getLayerProperty?.(
          layerId,
          "transform.position",
        ) as number[]) ?? [0, 0, 0],
        scale: (getLayerProperty?.(layerId, "transform.scale") as number[]) ?? [
          100, 100, 100,
        ],
        rotation: (getLayerProperty?.(
          layerId,
          "transform.rotation",
        ) as number[]) ?? [0, 0, 0],
        anchor: (getLayerProperty?.(
          layerId,
          "transform.anchorPoint",
        ) as number[]) ?? [0, 0, 0],
      });

      const createEffectAccessor = (effectName: string) => {
        const accessor = (paramName: string) => {
          return getLayerEffectParam?.(layerId, effectName, paramName) ?? 0;
        };
        accessor.param = accessor;
        // Slider Control
        accessor.value =
          getLayerEffectParam?.(layerId, effectName, "value") ?? 0;
        accessor.slider =
          getLayerEffectParam?.(layerId, effectName, "slider") ??
          getLayerEffectParam?.(layerId, effectName, "Slider") ??
          0;
        // Angle Control
        accessor.angle =
          getLayerEffectParam?.(layerId, effectName, "angle") ??
          getLayerEffectParam?.(layerId, effectName, "Angle") ??
          0;
        // Checkbox Control
        accessor.checkbox =
          getLayerEffectParam?.(layerId, effectName, "checkbox") ??
          getLayerEffectParam?.(layerId, effectName, "Checkbox") ??
          false;
        // Color Control
        accessor.color = getLayerEffectParam?.(layerId, effectName, "color") ??
          getLayerEffectParam?.(layerId, effectName, "Color") ?? [1, 1, 1, 1];
        // Point Control (2D and 3D)
        accessor.point = getLayerEffectParam?.(layerId, effectName, "point") ??
          getLayerEffectParam?.(layerId, effectName, "Point") ?? [0, 0];
        accessor.point3D = getLayerEffectParam?.(
          layerId,
          effectName,
          "point3D",
        ) ??
          getLayerEffectParam?.(layerId, effectName, "3D Point") ?? [0, 0, 0];
        // Dropdown Menu Control
        accessor.menu =
          getLayerEffectParam?.(layerId, effectName, "menu") ??
          getLayerEffectParam?.(layerId, effectName, "Menu") ??
          1;
        // Layer Control
        accessor.layer =
          getLayerEffectParam?.(layerId, effectName, "layer") ??
          getLayerEffectParam?.(layerId, effectName, "Layer") ??
          null;
        return accessor;
      };

      return {
        name: ctx.allLayers?.find((l) => l.id === layerId)?.name ?? "",
        index: ctx.allLayers?.find((l) => l.id === layerId)?.index ?? 0,
        position: getLayerProperty?.(layerId, "transform.position") ?? [0, 0],
        scale: getLayerProperty?.(layerId, "transform.scale") ?? [100, 100],
        rotation: getLayerProperty?.(layerId, "transform.rotation") ?? 0,
        opacity: getLayerProperty?.(layerId, "transform.opacity") ?? 100,
        anchorPoint: getLayerProperty?.(layerId, "transform.anchorPoint") ?? [
          0, 0,
        ],
        origin: getLayerProperty?.(layerId, "transform.origin") ?? [0, 0],
        transform: {
          position: getLayerProperty?.(layerId, "transform.position") ?? [
            0, 0, 0,
          ],
          rotation: getLayerProperty?.(layerId, "transform.rotation") ?? [
            0, 0, 0,
          ],
          scale: getLayerProperty?.(layerId, "transform.scale") ?? [
            100, 100, 100,
          ],
          opacity: getLayerProperty?.(layerId, "transform.opacity") ?? 100,
          anchorPoint: getLayerProperty?.(layerId, "transform.anchorPoint") ?? [
            0, 0, 0,
          ],
          origin: getLayerProperty?.(layerId, "transform.origin") ?? [0, 0, 0],
        },
        toComp: (point: number[]) => toComp(point, getTransform()),
        fromComp: (point: number[]) => fromComp(point, getTransform()),
        toWorld: (point: number[]) => toWorld(point, getTransform()),
        fromWorld: (point: number[]) => fromWorld(point, getTransform()),
        effect: createEffectAccessor,
      };
    },
  };
}

// Helper to create thisLayer object
function _createThisLayerObject(ctx: ExpressionContext) {
  return {
    name: ctx.layerName,
    index: ctx.layerIndex,
    inPoint: ctx.inPoint,
    outPoint: ctx.outPoint,
    position: ctx.layerTransform?.position ?? [0, 0, 0],
    rotation: ctx.layerTransform?.rotation ?? [0, 0, 0],
    scale: ctx.layerTransform?.scale ?? [100, 100, 100],
    opacity: ctx.layerTransform?.opacity ?? 100,
    anchorPoint: ctx.layerTransform?.origin ?? [0, 0, 0],
    origin: ctx.layerTransform?.origin ?? [0, 0, 0],
    transform: {
      position: ctx.layerTransform?.position ?? [0, 0, 0],
      rotation: ctx.layerTransform?.rotation ?? [0, 0, 0],
      scale: ctx.layerTransform?.scale ?? [100, 100, 100],
      opacity: ctx.layerTransform?.opacity ?? 100,
      anchorPoint: ctx.layerTransform?.origin ?? [0, 0, 0],
      origin: ctx.layerTransform?.origin ?? [0, 0, 0],
    },
    effect: (effectName: string) => {
      const eff = ctx.layerEffects?.find(
        (e) => e.name === effectName || e.effectKey === effectName,
      );
      const accessor = (paramName: string) => {
        if (!eff) return 0;
        return eff.parameters[paramName] ?? 0;
      };
      accessor.param = accessor;
      // Slider Control
      accessor.value = eff?.parameters.value ?? 0;
      accessor.slider = eff?.parameters.slider ?? eff?.parameters.Slider ?? 0;
      // Angle Control
      accessor.angle = eff?.parameters.angle ?? eff?.parameters.Angle ?? 0;
      // Checkbox Control
      accessor.checkbox =
        eff?.parameters.checkbox ?? eff?.parameters.Checkbox ?? false;
      // Color Control
      accessor.color = eff?.parameters.color ??
        eff?.parameters.Color ?? [1, 1, 1, 1];
      // Point Control (2D and 3D)
      accessor.point = eff?.parameters.point ?? eff?.parameters.Point ?? [0, 0];
      accessor.point3D = eff?.parameters.point3D ??
        eff?.parameters["3D Point"] ?? [0, 0, 0];
      // Dropdown Menu Control
      accessor.menu = eff?.parameters.menu ?? eff?.parameters.Menu ?? 1;
      // Layer Control
      accessor.layer = eff?.parameters.layer ?? eff?.parameters.Layer ?? null;
      return accessor;
    },
    sourceRectAtTime: (
      _t: number = ctx.time,
      _includeExtents: boolean = false,
    ) => {
      return { top: 0, left: 0, width: 100, height: 100 };
    },
    toComp: (point: number[]) => {
      const transform: LayerTransform = {
        position: ctx.layerTransform?.position ?? [0, 0, 0],
        scale: ctx.layerTransform?.scale ?? [100, 100, 100],
        rotation: ctx.layerTransform?.rotation ?? [0, 0, 0],
        anchor: ctx.layerTransform?.origin ?? [0, 0, 0],
      };
      return toComp(point, transform);
    },
    fromComp: (point: number[]) => {
      const transform: LayerTransform = {
        position: ctx.layerTransform?.position ?? [0, 0, 0],
        scale: ctx.layerTransform?.scale ?? [100, 100, 100],
        rotation: ctx.layerTransform?.rotation ?? [0, 0, 0],
        anchor: ctx.layerTransform?.origin ?? [0, 0, 0],
      };
      return fromComp(point, transform);
    },
    toWorld: (point: number[]) => {
      const transform: LayerTransform = {
        position: ctx.layerTransform?.position ?? [0, 0, 0],
        scale: ctx.layerTransform?.scale ?? [100, 100, 100],
        rotation: ctx.layerTransform?.rotation ?? [0, 0, 0],
        anchor: ctx.layerTransform?.origin ?? [0, 0, 0],
      };
      return toWorld(point, transform);
    },
    fromWorld: (point: number[]) => {
      const transform: LayerTransform = {
        position: ctx.layerTransform?.position ?? [0, 0, 0],
        scale: ctx.layerTransform?.scale ?? [100, 100, 100],
        rotation: ctx.layerTransform?.rotation ?? [0, 0, 0],
        anchor: ctx.layerTransform?.origin ?? [0, 0, 0],
      };
      return fromWorld(point, transform);
    },
  };
}
