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
import { repeatAfter, repeatBefore, type LoopType } from "./loopExpressions";
import { bounce, elastic, inertia } from "./motionExpressions";
import { evaluateInSES } from "./sesEvaluator";
import type { Expression, ExpressionContext } from "./types";
import { isFiniteNumber, isNumberArray } from "@/utils/typeGuards";

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

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // time // expressions
// ════════════════════════════════════════════════════════════════════════════

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

// ════════════════════════════════════════════════════════════════════════════
//                                                       // math // expressions
// ════════════════════════════════════════════════════════════════════════════

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

// ════════════════════════════════════════════════════════════════════════════
//                                           // expression // ease // functions
// ════════════════════════════════════════════════════════════════════════════

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

// ════════════════════════════════════════════════════════════════════════════
//                                                   // expression // evaluator
// ════════════════════════════════════════════════════════════════════════════

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
  params: Record<string, number | string | boolean>,
): number | number[] {
  switch (name) {
    case "inertia": {
      const amplitude = typeof params.amplitude === "number" ? params.amplitude : 0.1;
      const frequency = typeof params.frequency === "number" ? params.frequency : 2.0;
      const decay = typeof params.decay === "number" ? params.decay : 2.0;
      return inertia(ctx, amplitude, frequency, decay);
    }
    case "bounce": {
      const elasticity = typeof params.elasticity === "number" ? params.elasticity : 0.7;
      const gravity = typeof params.gravity === "number" ? params.gravity : 4000;
      return bounce(ctx, elasticity, gravity);
    }
    case "elastic": {
      const amplitude = typeof params.amplitude === "number" ? params.amplitude : 1;
      const period = typeof params.period === "number" ? params.period : 0.3;
      return elastic(ctx, amplitude, period);
    }
    case "jitter": {
      const frequency = typeof params.frequency === "number" ? params.frequency : 10;
      const amplitude = typeof params.amplitude === "number" ? params.amplitude : 5;
      const octaves = typeof params.octaves === "number" ? params.octaves : 1;
      return jitter(ctx, frequency, amplitude, octaves);
    }
    case "repeatAfter": {
      const type = (typeof params.type === "string" && 
        (params.type === "cycle" || params.type === "pingpong" || params.type === "offset" || params.type === "continue"))
        ? params.type
        : "cycle";
      const numKeyframes = typeof params.numKeyframes === "number" ? params.numKeyframes : 0;
      return repeatAfter(ctx, type, numKeyframes);
    }
    case "repeatBefore": {
      const type = (typeof params.type === "string" && 
        (params.type === "cycle" || params.type === "pingpong" || params.type === "offset" || params.type === "continue"))
        ? params.type
        : "cycle";
      const numKeyframes = typeof params.numKeyframes === "number" ? params.numKeyframes : 0;
      return repeatBefore(ctx, type, numKeyframes);
    }
    default:
      return ctx.value;
  }
}

function evaluateFunction(
  name: string,
  ctx: ExpressionContext,
  params: Record<string, number | string | boolean>,
): number | number[] {
  // Time functions
  if (name in timeExpressions) {
    const timeExprs = timeExpressions as Record<
      string,
      (time: number, ...args: (number | string | boolean)[]) => number | number[]
    >;
    const fn = timeExprs[name];
    if (fn) {
      return fn(ctx.time, ...Object.values(params));
    }
  }

  // Math functions
  if (name in mathExpressions) {
    const mathExprs = mathExpressions as Record<
      string,
      (val: number, ...args: (number | string | boolean)[]) => number | number[]
    >;
    const fn = mathExprs[name];
    if (fn) {
      const val = typeof ctx.value === "number" ? ctx.value : ctx.value[0];
      return fn(val, ...Object.values(params));
    }
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
  //                                                                  // security
  // Prevents objects with malicious .trim() or valueOf() from being passed
  if (typeof code !== "string") {
    console.warn("[SECURITY] Expression code is not a string:", typeof code);
    return ctx.value;
  }

  // Empty code returns value unchanged
  if (!code || code.trim() === "") {
    return ctx.value;
  }

  //                                                                  // security
  // evaluateInSES() handles: length limit, SES check, sandbox evaluation
  return evaluateInSES(code, ctx);
}

// ════════════════════════════════════════════════════════════════════════════
//                                                           // legacy // proxy
// ════════════════════════════════════════════════════════════════════════════
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
// ════════════════════════════════════════════════════════════════════════════

// Helper to create thisComp object
function _createThisCompObject(ctx: ExpressionContext) {
  const fps = Number.isFinite(ctx.fps) && ctx.fps > 0 ? ctx.fps : 30;
  const duration = Number.isFinite(ctx.duration) ? ctx.duration : 0;

  return {
    duration: duration,
    frameDuration: 1 / fps,
    width: ctx.compWidth,
    height: ctx.compHeight,
    numLayers: ctx.allLayers.length,
    layer: (nameOrIndex: string | number) => {
      const getLayerProperty = ctx.getLayerProperty;
      const getLayerEffectParam = ctx.getLayerEffectParam;
      let layerId: string;

      // Lean4/PureScript/Haskell: Explicit pattern matching on union type
      // Type proof: nameOrIndex ∈ string | number → layerId: string
      if (typeof nameOrIndex === "number") {
        const layerInfo = ctx.allLayers.find((l) => l.index === nameOrIndex);
        // Type proof: layerInfo ∈ { id: string } | undefined → string
        layerId = layerInfo !== undefined && typeof layerInfo.id === "string"
          ? layerInfo.id
          : `layer_${nameOrIndex}`;
      } else {
        const layerInfo = ctx.allLayers.find((l) => l.name === nameOrIndex);
        // Type proof: layerInfo ∈ { id: string } | undefined → string
        layerId = layerInfo !== undefined && typeof layerInfo.id === "string"
          ? layerInfo.id
          : nameOrIndex;
      }

      // Lean4/PureScript/Haskell: Explicit pattern matching on union type
      // Type proof: getLayerProperty returns number | number[] | null
      // PureScript: case getLayerProperty of Just x -> x; Nothing -> default
      const getTransform = (): LayerTransform => {
        // Type proof: position ∈ number | number[] | null → number[]
        const positionRaw = getLayerProperty(layerId, "transform.position");
        const position: number[] = isNumberArray(positionRaw) && positionRaw.length >= 3
          ? [positionRaw[0], positionRaw[1], positionRaw[2]]
          : isNumberArray(positionRaw) && positionRaw.length === 2
            ? [positionRaw[0], positionRaw[1], 0]
            : [0, 0, 0];

        // Type proof: scale ∈ number | number[] | null → number[]
        const scaleRaw = getLayerProperty(layerId, "transform.scale");
        const scale: number[] = isNumberArray(scaleRaw) && scaleRaw.length >= 3
          ? [scaleRaw[0], scaleRaw[1], scaleRaw[2]]
          : isNumberArray(scaleRaw) && scaleRaw.length === 2
            ? [scaleRaw[0], scaleRaw[1], 100]
            : [100, 100, 100];

        // Type proof: rotation ∈ number | number[] | null → number[]
        const rotationRaw = getLayerProperty(layerId, "transform.rotation");
        const rotation: number[] = isNumberArray(rotationRaw) && rotationRaw.length >= 3
          ? [rotationRaw[0], rotationRaw[1], rotationRaw[2]]
          : isNumberArray(rotationRaw) && rotationRaw.length === 2
            ? [rotationRaw[0], rotationRaw[1], 0]
            : isFiniteNumber(rotationRaw)
              ? [0, 0, rotationRaw]
              : [0, 0, 0];

        // Type proof: anchor ∈ number | number[] | null → number[]
        const anchorRaw = getLayerProperty(layerId, "transform.anchorPoint");
        const anchor: number[] = isNumberArray(anchorRaw) && anchorRaw.length >= 3
          ? [anchorRaw[0], anchorRaw[1], anchorRaw[2]]
          : isNumberArray(anchorRaw) && anchorRaw.length === 2
            ? [anchorRaw[0], anchorRaw[1], 0]
            : [0, 0, 0];

        return { position, scale, rotation, anchor };
      };

      // Lean4/PureScript/Haskell: Explicit pattern matching on union type
      // Type proof: getLayerEffectParam returns number | number[] | string | boolean | null
      const createEffectAccessor = (effectName: string) => {
        // Helper: Pattern match on union type with explicit type narrowing
        // PureScript: case getLayerEffectParam of Just (Number n) -> n; _ -> 0
        const getNumericParam = (paramName: string, altParamName: string | null, defaultValue: number): number => {
          const primary = getLayerEffectParam(layerId, effectName, paramName);
          if (isFiniteNumber(primary)) return primary;
          if (altParamName !== null) {
            const alt = getLayerEffectParam(layerId, effectName, altParamName);
            if (isFiniteNumber(alt)) return alt;
          }
          return defaultValue;
        };

        const getBooleanParam = (paramName: string, altParamName: string | null, defaultValue: boolean): boolean => {
          const primary = getLayerEffectParam(layerId, effectName, paramName);
          if (typeof primary === "boolean") return primary;
          if (altParamName !== null) {
            const alt = getLayerEffectParam(layerId, effectName, altParamName);
            if (typeof alt === "boolean") return alt;
          }
          return defaultValue;
        };

        const getArrayParam = (paramName: string, altParamName: string | null, defaultValue: number[]): number[] => {
          const primary = getLayerEffectParam(layerId, effectName, paramName);
          if (isNumberArray(primary)) return primary;
          if (altParamName !== null) {
            const alt = getLayerEffectParam(layerId, effectName, altParamName);
            if (isNumberArray(alt)) return alt;
          }
          return defaultValue;
        };

        const getStringParam = (paramName: string, altParamName: string | null, defaultValue: string | null): string | null => {
          const primary = getLayerEffectParam(layerId, effectName, paramName);
          if (typeof primary === "string") return primary;
          if (altParamName !== null) {
            const alt = getLayerEffectParam(layerId, effectName, altParamName);
            if (typeof alt === "string") return alt;
          }
          return defaultValue;
        };

        const accessor = (paramName: string) => {
          // Type proof: param ∈ number | number[] | string | boolean | null → number
          const value = getLayerEffectParam(layerId, effectName, paramName);
          return isFiniteNumber(value) ? value : 0;
        };
        accessor.param = accessor;
        
        // Slider Control - Type proof: value ∈ number | number[] | string | boolean | null → number
        accessor.value = getNumericParam("value", null, 0);
        
        // Slider Control (case-insensitive) - Type proof: slider ∈ number | number[] | string | boolean | null → number
        accessor.slider = getNumericParam("slider", "Slider", 0);
        
        // Angle Control (case-insensitive) - Type proof: angle ∈ number | number[] | string | boolean | null → number
        accessor.angle = getNumericParam("angle", "Angle", 0);
        
        // Checkbox Control (case-insensitive) - Type proof: checkbox ∈ number | number[] | string | boolean | null → boolean
        accessor.checkbox = getBooleanParam("checkbox", "Checkbox", false);
        
        // Color Control (case-insensitive) - Type proof: color ∈ number | number[] | string | boolean | null → number[]
        accessor.color = getArrayParam("color", "Color", [1, 1, 1, 1]);
        
        // Point Control 2D (case-insensitive) - Type proof: point ∈ number | number[] | string | boolean | null → number[]
        accessor.point = getArrayParam("point", "Point", [0, 0]);
        
        // Point Control 3D (case-insensitive) - Type proof: point3D ∈ number | number[] | string | boolean | null → number[]
        accessor.point3D = getArrayParam("point3D", "3D Point", [0, 0, 0]);
        
        // Dropdown Menu Control (case-insensitive) - Type proof: menu ∈ number | number[] | string | boolean | null → number
        accessor.menu = getNumericParam("menu", "Menu", 1);
        
        // Layer Control (case-insensitive) - Type proof: layer ∈ number | number[] | string | boolean | null → string | null
        accessor.layer = getStringParam("layer", "Layer", null);
        
        return accessor;
      };

      // Lean4/PureScript/Haskell: Explicit pattern matching on union types
      // Type proof: allLayers.find returns { id, name, index } | undefined
      const foundLayer = ctx.allLayers.find((l) => l.id === layerId);
      const layerName: string = foundLayer !== undefined && typeof foundLayer.name === "string"
        ? foundLayer.name
        : "";
      const layerIndex: number = foundLayer !== undefined && typeof foundLayer.index === "number" && Number.isFinite(foundLayer.index)
        ? foundLayer.index
        : 0;

      // Type proof: getLayerProperty returns number | number[] | null
      // PureScript: case getLayerProperty of Just (Array [x, y]) -> [x, y]; _ -> [0, 0]
      const getPosition2D = (): number[] => {
        const raw = getLayerProperty(layerId, "transform.position");
        return isNumberArray(raw) && raw.length >= 2 ? [raw[0], raw[1]] : [0, 0];
      };

      const getScale2D = (): number[] => {
        const raw = getLayerProperty(layerId, "transform.scale");
        return isNumberArray(raw) && raw.length >= 2 ? [raw[0], raw[1]] : [100, 100];
      };

      const getRotationScalar = (): number => {
        const raw = getLayerProperty(layerId, "transform.rotation");
        return isFiniteNumber(raw) ? raw : 0;
      };

      const getOpacityScalar = (): number => {
        const raw = getLayerProperty(layerId, "transform.opacity");
        return isFiniteNumber(raw) ? raw : 100;
      };

      const getAnchor2D = (): number[] => {
        const raw = getLayerProperty(layerId, "transform.anchorPoint");
        return isNumberArray(raw) && raw.length >= 2 ? [raw[0], raw[1]] : [0, 0];
      };

      const getOrigin2D = (): number[] => {
        const raw = getLayerProperty(layerId, "transform.origin");
        return isNumberArray(raw) && raw.length >= 2 ? [raw[0], raw[1]] : [0, 0];
      };

      const getPosition3D = (): number[] => {
        const raw = getLayerProperty(layerId, "transform.position");
        if (isNumberArray(raw) && raw.length >= 3) return [raw[0], raw[1], raw[2]];
        if (isNumberArray(raw) && raw.length === 2) return [raw[0], raw[1], 0];
        return [0, 0, 0];
      };

      const getRotation3D = (): number[] => {
        const raw = getLayerProperty(layerId, "transform.rotation");
        if (isNumberArray(raw) && raw.length >= 3) return [raw[0], raw[1], raw[2]];
        if (isNumberArray(raw) && raw.length === 2) return [raw[0], raw[1], 0];
        if (isFiniteNumber(raw)) return [0, 0, raw];
        return [0, 0, 0];
      };

      const getScale3D = (): number[] => {
        const raw = getLayerProperty(layerId, "transform.scale");
        if (isNumberArray(raw) && raw.length >= 3) return [raw[0], raw[1], raw[2]];
        if (isNumberArray(raw) && raw.length === 2) return [raw[0], raw[1], 100];
        return [100, 100, 100];
      };

      const getAnchor3D = (): number[] => {
        const raw = getLayerProperty(layerId, "transform.anchorPoint");
        if (isNumberArray(raw) && raw.length >= 3) return [raw[0], raw[1], raw[2]];
        if (isNumberArray(raw) && raw.length === 2) return [raw[0], raw[1], 0];
        return [0, 0, 0];
      };

      const getOrigin3D = (): number[] => {
        const raw = getLayerProperty(layerId, "transform.origin");
        if (isNumberArray(raw) && raw.length >= 3) return [raw[0], raw[1], raw[2]];
        if (isNumberArray(raw) && raw.length === 2) return [raw[0], raw[1], 0];
        return [0, 0, 0];
      };

      return {
        name: layerName,
        index: layerIndex,
        position: getPosition2D(),
        scale: getScale2D(),
        rotation: getRotationScalar(),
        opacity: getOpacityScalar(),
        anchorPoint: getAnchor2D(),
        origin: getOrigin2D(),
        transform: {
          position: getPosition3D(),
          rotation: getRotation3D(),
          scale: getScale3D(),
          opacity: getOpacityScalar(),
          anchorPoint: getAnchor3D(),
          origin: getOrigin3D(),
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
    position: ctx.layerTransform.position,
    rotation: ctx.layerTransform.rotation,
    scale: ctx.layerTransform.scale,
    opacity: ctx.layerTransform.opacity,
    anchorPoint: ctx.layerTransform.origin,
    origin: ctx.layerTransform.origin,
    transform: {
      position: ctx.layerTransform.position,
      rotation: ctx.layerTransform.rotation,
      scale: ctx.layerTransform.scale,
      opacity: ctx.layerTransform.opacity,
      anchorPoint: ctx.layerTransform.origin,
      origin: ctx.layerTransform.origin,
    },
    effect: (effectName: string) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching
      // Type proof: find returns { parameters: Record<...> } | undefined
      const eff = ctx.layerEffects.find(
        (e) => e.name === effectName || e.effectKey === effectName,
      );
      
      // PureScript: case eff of Just e -> e.parameters; Nothing -> {}
      const params = eff !== undefined ? eff.parameters : {};
      
      const accessor = (paramName: string) => {
        // Type proof: params[paramName] ∈ number | number[] | string | boolean | undefined → number
        const value = params[paramName];
        return isFiniteNumber(value) ? value : 0;
      };
      accessor.param = accessor;
      
      // Helper functions for explicit pattern matching
      const getNumericParam = (key: string, altKey: string | null, defaultValue: number): number => {
        const primary = params[key];
        if (isFiniteNumber(primary)) return primary;
        if (altKey !== null) {
          const alt = params[altKey];
          if (isFiniteNumber(alt)) return alt;
        }
        return defaultValue;
      };

      const getBooleanParam = (key: string, altKey: string | null, defaultValue: boolean): boolean => {
        const primary = params[key];
        if (typeof primary === "boolean") return primary;
        if (altKey !== null) {
          const alt = params[altKey];
          if (typeof alt === "boolean") return alt;
        }
        return defaultValue;
      };

      const getArrayParam = (key: string, altKey: string | null, defaultValue: number[]): number[] => {
        const primary = params[key];
        if (isNumberArray(primary)) return primary;
        if (altKey !== null) {
          const alt = params[altKey];
          if (isNumberArray(alt)) return alt;
        }
        return defaultValue;
      };

      const getStringParam = (key: string, altKey: string | null, defaultValue: string | null): string | null => {
        const primary = params[key];
        if (typeof primary === "string") return primary;
        if (altKey !== null) {
          const alt = params[altKey];
          if (typeof alt === "string") return alt;
        }
        return defaultValue;
      };
      
      // Slider Control - Type proof: value ∈ number | number[] | string | boolean | undefined → number
      accessor.value = getNumericParam("value", null, 0);
      
      // Slider Control (case-insensitive)
      accessor.slider = getNumericParam("slider", "Slider", 0);
      
      // Angle Control (case-insensitive)
      accessor.angle = getNumericParam("angle", "Angle", 0);
      
      // Checkbox Control (case-insensitive)
      accessor.checkbox = getBooleanParam("checkbox", "Checkbox", false);
      
      // Color Control (case-insensitive)
      accessor.color = getArrayParam("color", "Color", [1, 1, 1, 1]);
      
      // Point Control 2D (case-insensitive)
      accessor.point = getArrayParam("point", "Point", [0, 0]);
      
      // Point Control 3D (case-insensitive)
      accessor.point3D = getArrayParam("point3D", "3D Point", [0, 0, 0]);
      
      // Dropdown Menu Control (case-insensitive)
      accessor.menu = getNumericParam("menu", "Menu", 1);
      
      // Layer Control (case-insensitive)
      accessor.layer = getStringParam("layer", "Layer", null);
      
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
        position: ctx.layerTransform.position,
        scale: ctx.layerTransform.scale,
        rotation: ctx.layerTransform.rotation,
        anchor: ctx.layerTransform.origin,
      };
      return toComp(point, transform);
    },
    fromComp: (point: number[]) => {
      const transform: LayerTransform = {
        position: ctx.layerTransform.position,
        scale: ctx.layerTransform.scale,
        rotation: ctx.layerTransform.rotation,
        anchor: ctx.layerTransform.origin,
      };
      return fromComp(point, transform);
    },
    toWorld: (point: number[]) => {
      const transform: LayerTransform = {
        position: ctx.layerTransform.position,
        scale: ctx.layerTransform.scale,
        rotation: ctx.layerTransform.rotation,
        anchor: ctx.layerTransform.origin,
      };
      return toWorld(point, transform);
    },
    fromWorld: (point: number[]) => {
      const transform: LayerTransform = {
        position: ctx.layerTransform.position,
        scale: ctx.layerTransform.scale,
        rotation: ctx.layerTransform.rotation,
        anchor: ctx.layerTransform.origin,
      };
      return fromWorld(point, transform);
    },
  };
}
