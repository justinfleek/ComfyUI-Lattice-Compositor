/**
 * Expression Validator
 *
 * Pre-validates all expressions in a project using Worker-based timeout.
 * Catches infinite loops BEFORE they can hang the render loop.
 *
 * Call validateProjectExpressions() when loading a project to detect
 * dangerous expressions before they execute.
 */

import { evaluateWithTimeout, isWorkerAvailable } from './workerEvaluator';
import type { EvalResult } from './workerEvaluator';
import type { LatticeProject, Layer, AnimatableProperty } from '@/types/project';
import type { PropertyExpression } from '@/types/animation';
import type { TextAnimator, TextExpressionSelector } from '@/types/text';

export interface ValidationResult {
  valid: boolean;
  dangerous: DangerousExpression[];
  total: number;
  validated: number;
}

export interface DangerousExpression {
  location: string;
  expression: string;
  reason: 'timeout' | 'error';
  error?: string;
}

/**
 * Extract all expression code strings from a project
 */
function extractExpressions(project: LatticeProject): Array<{ location: string; code: string }> {
  const expressions: Array<{ location: string; code: string }> = [];

  // Helper to check property expressions
  // Custom expressions store code in params.code
  function checkPropertyExpression(expr: PropertyExpression | undefined, location: string) {
    if (!expr?.enabled) return;

    // Only custom type has user code - presets/functions are safe (hardcoded)
    if (expr.type === 'custom' && expr.params?.code && typeof expr.params.code === 'string') {
      expressions.push({ location, code: expr.params.code });
    }
  }

  // Helper to check animatable property
  function checkAnimatableProperty(prop: AnimatableProperty<unknown> | undefined, location: string) {
    if (!prop?.expression) return;
    checkPropertyExpression(prop.expression as PropertyExpression, location);
  }

  // Check all layers
  for (const layer of project.layers) {
    const layerLoc = `layer[${layer.name}]`;

    // Transform properties
    if (layer.transform) {
      const t = layer.transform;
      checkAnimatableProperty(t.position as AnimatableProperty<unknown>, `${layerLoc}.transform.position`);
      checkAnimatableProperty(t.scale as AnimatableProperty<unknown>, `${layerLoc}.transform.scale`);
      checkAnimatableProperty(t.rotation as AnimatableProperty<unknown>, `${layerLoc}.transform.rotation`);
      checkAnimatableProperty(t.anchorPoint as AnimatableProperty<unknown>, `${layerLoc}.transform.anchorPoint`);
    }
    // Opacity is on the layer, not transform
    if (layer.opacity) {
      checkAnimatableProperty(layer.opacity as AnimatableProperty<unknown>, `${layerLoc}.opacity`);
    }

    // Text layer - check text animators' expression selectors
    if (layer.type === 'text') {
      const data = layer.data as { animators?: TextAnimator[] };
      if (data?.animators) {
        data.animators.forEach((anim, i) => {
          // Check expression selector
          const exprSel = anim.expressionSelector as TextExpressionSelector | undefined;
          if (exprSel?.enabled && exprSel.amountExpression) {
            expressions.push({
              location: `${layerLoc}.textAnimator[${anim.name || i}].expressionSelector`,
              code: exprSel.amountExpression
            });
          }

          // Check animator properties for expressions
          if (anim.properties) {
            for (const [key, prop] of Object.entries(anim.properties)) {
              if (prop) {
                checkAnimatableProperty(prop as AnimatableProperty<unknown>, `${layerLoc}.textAnimator[${anim.name || i}].${key}`);
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
            if (p?.expression) {
              checkPropertyExpression(p.expression as PropertyExpression, `${layerLoc}.effect[${effect.name || ei}].${key}`);
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
  project: LatticeProject
): Promise<ValidationResult> {
  if (!isWorkerAvailable()) {
    console.warn('[ExpressionValidator] Workers not available, skipping validation');
    return { valid: true, dangerous: [], total: 0, validated: 0 };
  }

  const expressions = extractExpressions(project);
  const dangerous: DangerousExpression[] = [];

  // Test context with typical values
  const testContext = {
    value: 0,
    frame: 0,
    time: 0,
    index: 0,
    numLayers: 1,
    fps: 30,
    duration: 10,
    width: 1920,
    height: 1080,
    // Text animator context
    textIndex: 0,
    textTotal: 10,
    selectorValue: 1,
  };

  for (const { location, code } of expressions) {
    const result: EvalResult = await evaluateWithTimeout(code, testContext);

    if (result.timedOut) {
      dangerous.push({
        location,
        expression: code.slice(0, 100) + (code.length > 100 ? '...' : ''),
        reason: 'timeout'
      });
    } else if (result.error) {
      // Syntax errors are also dangerous - could be malformed infinite loops
      dangerous.push({
        location,
        expression: code.slice(0, 100) + (code.length > 100 ? '...' : ''),
        reason: 'error',
        error: result.error
      });
    }
  }

  return {
    valid: dangerous.length === 0,
    dangerous,
    total: expressions.length,
    validated: expressions.length
  };
}

/**
 * Quick check if an expression is safe (doesn't timeout)
 */
export async function isExpressionSafe(code: string): Promise<boolean> {
  if (!isWorkerAvailable()) return true; // Can't validate without worker

  const result = await evaluateWithTimeout(code, { value: 0, frame: 0 });
  return !result.timedOut;
}
