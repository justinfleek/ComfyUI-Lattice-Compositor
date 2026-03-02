/**
 * Expression Validator
 *
 * Pre-validates all expressions in a project using Worker-based timeout.
 * Catches infinite loops BEFORE they can hang the render loop.
 *
 * Call validateProjectExpressions() when loading a project to detect
 * dangerous expressions before they execute.
 */

import type { PropertyExpression } from "@/types/animation";
import type { AnimatableProperty, LatticeProject } from "@/types/project";
import type { TextAnimator, TextExpressionSelector } from "@/types/text";
import type { EvalResult } from "./workerEvaluator";
import { evaluateWithTimeout, isWorkerAvailable } from "./workerEvaluator";
import type { ExpressionContext } from "./types";

/**
 * Create a test ExpressionContext with all required values for validation.
 * Values are typical defaults - the actual values don't matter for validation,
 * we just need a complete context to avoid TypeScript errors.
 */
function createTestContext(): ExpressionContext {
  return {
    // Time
    time: 0,
    frame: 0,
    fps: 30,
    duration: 10,
    // Composition
    compWidth: 1920,
    compHeight: 1080,
    // Layer info
    layerId: "test-layer",
    layerIndex: 0,
    layerName: "Test Layer",
    inPoint: 0,
    outPoint: 300,
    // Property
    propertyName: "value",
    value: 0,
    velocity: 0,
    numKeys: 0,
    keyframes: [],
    // Expression controls
    params: {},
    // Layer access (no-op for validation)
    getLayerProperty: () => null,
    // Data-driven animation (no-op for validation)
    footage: () => null,
    // Layer transform
    layerTransform: {
      position: [0, 0, 0],
      rotation: [0, 0, 0],
      scale: [100, 100, 100],
      opacity: 100,
      origin: [0, 0, 0],
    },
    // Effects
    layerEffects: [],
    // All layers
    allLayers: [],
    // Effect parameter access (no-op for validation)
    getLayerEffectParam: () => null,
  };
}

export interface ValidationResult {
  valid: boolean;
  dangerous: DangerousExpression[];
  total: number;
  validated: number;
}

export interface DangerousExpression {
  location: string;
  expression: string;
  reason: "timeout" | "error";
  error?: string;
}

/**
 * Extract all expression code strings from a project
 */
function extractExpressions(
  project: LatticeProject,
): Array<{ location: string; code: string }> {
  const expressions: Array<{ location: string; code: string }> = [];

  // Helper to check property expressions
  // Custom expressions store code in params.code
  function checkPropertyExpression(
    expr: PropertyExpression | undefined,
    location: string,
  ) {
    // Type guard: expr must be defined and enabled
    if (expr === null || expr === undefined) return;
    if (typeof expr !== "object") return;
    if (!("enabled" in expr) || typeof expr.enabled !== "boolean" || !expr.enabled) return;

    // Only custom type has user code - presets/functions are safe (hardcoded)
    // Type guard: check for custom type and valid code
    if (expr.type !== "custom") return;
    const params = ("params" in expr && expr.params !== null && typeof expr.params === "object") ? expr.params : undefined;
    if (params === undefined) return;
    const code = ("code" in params && typeof params.code === "string") ? params.code : undefined;
    if (code === undefined) return;

    expressions.push({ location, code });
  }

  // Helper to check animatable property
  function checkAnimatableProperty(
    prop: AnimatableProperty<unknown> | undefined,
    location: string,
  ) {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const propExpression = (prop != null && typeof prop === "object" && "expression" in prop && prop.expression != null) ? prop.expression : undefined;
    if (!propExpression) return;
    checkPropertyExpression(propExpression as PropertyExpression, location);
  }

  // Check all layers
  for (const layer of project.layers) {
    const layerLoc = `layer[${layer.name}]`;

    // Transform properties
    if (layer.transform) {
      const t = layer.transform;
      checkAnimatableProperty(
        t.position as AnimatableProperty<unknown>,
        `${layerLoc}.transform.position`,
      );
      checkAnimatableProperty(
        t.scale as AnimatableProperty<unknown>,
        `${layerLoc}.transform.scale`,
      );
      checkAnimatableProperty(
        t.rotation as AnimatableProperty<unknown>,
        `${layerLoc}.transform.rotation`,
      );
      checkAnimatableProperty(
        t.anchorPoint as AnimatableProperty<unknown>,
        `${layerLoc}.transform.anchorPoint`,
      );
    }
    // Opacity is on the layer, not transform
    if (layer.opacity) {
      checkAnimatableProperty(
        layer.opacity as AnimatableProperty<unknown>,
        `${layerLoc}.opacity`,
      );
    }

    // Text layer - check text animators' expression selectors
    if (layer.type === "text") {
      const data = layer.data as { animators?: TextAnimator[] };
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const animators = (data != null && typeof data === "object" && "animators" in data && Array.isArray(data.animators)) ? data.animators : undefined;
      if (animators != null) {
        animators.forEach((anim, i) => {
          // Check expression selector
          const exprSel = anim.expressionSelector as
            | TextExpressionSelector
            | undefined;
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          const exprSelEnabled = (exprSel != null && typeof exprSel === "object" && "enabled" in exprSel && typeof exprSel.enabled === "boolean" && exprSel.enabled) ? true : false;
          const amountExpression = (exprSel != null && typeof exprSel === "object" && "amountExpression" in exprSel && typeof exprSel.amountExpression === "string") ? exprSel.amountExpression : undefined;
          if (exprSelEnabled && amountExpression != null) {
            expressions.push({
              location: `${layerLoc}.textAnimator[${anim.name || i}].expressionSelector`,
              code: amountExpression,
            });
          }

          // Check animator properties for expressions
          if (anim.properties) {
            for (const [key, prop] of Object.entries(anim.properties)) {
              if (prop) {
                checkAnimatableProperty(
                  prop as AnimatableProperty<unknown>,
                  `${layerLoc}.textAnimator[${anim.name || i}].${key}`,
                );
              }
            }
          }
        });
      }
    }

    // Effect parameters
    if (layer.effects) {
      layer.effects.forEach((effect, ei) => {
        if (effect.parameters) {
          for (const [key, param] of Object.entries(effect.parameters)) {
            const p = param as AnimatableProperty<unknown>;
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
            const pExpression = (p != null && typeof p === "object" && "expression" in p && p.expression != null) ? p.expression : undefined;
            if (pExpression != null) {
              checkPropertyExpression(
                pExpression as PropertyExpression,
                `${layerLoc}.effect[${effect.name || ei}].${key}`,
              );
            }
          }
        }
      });
    }
  }

  return expressions;
}

/**
 * Validate all expressions in a project using Worker timeout
 *
 * @param project - The project to validate
 * @returns Validation result with list of dangerous expressions
 */
export async function validateProjectExpressions(
  project: LatticeProject,
): Promise<ValidationResult> {
  if (!isWorkerAvailable()) {
    console.warn(
      "[ExpressionValidator] Workers not available, skipping validation",
    );
    return { valid: true, dangerous: [], total: 0, validated: 0 };
  }

  const expressions = extractExpressions(project);
  const dangerous: DangerousExpression[] = [];

  // Test context with all required values
  const testContext = createTestContext();

  for (const { location, code } of expressions) {
    const result: EvalResult = await evaluateWithTimeout(code, testContext);

    if (result.timedOut) {
      dangerous.push({
        location,
        expression: code.slice(0, 100) + (code.length > 100 ? "..." : ""),
        reason: "timeout",
      });
    } else if (result.error) {
      // Syntax errors are also dangerous - could be malformed infinite loops
      dangerous.push({
        location,
        expression: code.slice(0, 100) + (code.length > 100 ? "..." : ""),
        reason: "error",
        error: result.error,
      });
    }
  }

  return {
    valid: dangerous.length === 0,
    dangerous,
    total: expressions.length,
    validated: expressions.length,
  };
}

/**
 * Quick check if an expression is safe (doesn't timeout or error)
 *
 * SECURITY: Also rejects expressions that throw errors because:
 * - Stack overflow (recursive bombs) throws before timeout
 * - Syntax errors could be malformed attack attempts
 * - Runtime errors indicate problematic code
 */
export async function isExpressionSafe(code: string): Promise<boolean> {
  if (!isWorkerAvailable()) return true; // Can't validate without worker

  const result = await evaluateWithTimeout(code, createTestContext());
  return !result.timedOut && !result.error;
}
