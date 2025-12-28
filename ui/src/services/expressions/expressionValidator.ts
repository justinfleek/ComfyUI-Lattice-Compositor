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
import type { LatticeProject, Layer, AnimatableProperty } from '@/types/project';

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
 * Extract all expression strings from a project
 */
function extractExpressions(project: LatticeProject): Array<{ location: string; code: string }> {
  const expressions: Array<{ location: string; code: string }> = [];

  // Helper to check animatable properties
  function checkProperty(prop: AnimatableProperty<unknown> | undefined, location: string) {
    if (!prop?.expression?.enabled || !prop.expression.code) return;
    expressions.push({ location, code: prop.expression.code });
  }

  // Check all layers
  for (const layer of project.layers) {
    const layerLoc = `layer[${layer.name}]`;

    // Transform properties
    if (layer.transform) {
      checkProperty(layer.transform.position as any, `${layerLoc}.transform.position`);
      checkProperty(layer.transform.scale as any, `${layerLoc}.transform.scale`);
      checkProperty(layer.transform.rotation as any, `${layerLoc}.transform.rotation`);
      checkProperty(layer.transform.anchorPoint as any, `${layerLoc}.transform.anchorPoint`);
      checkProperty(layer.transform.opacity as any, `${layerLoc}.transform.opacity`);
    }

    // Layer-specific data with expressions
    const data = layer.data as Record<string, unknown>;
    if (data) {
      // Text layer expressions
      if (layer.type === 'text' && data.textAnimators) {
        const animators = data.textAnimators as Array<{ expression?: string; name?: string }>;
        animators.forEach((anim, i) => {
          if (anim.expression) {
            expressions.push({
              location: `${layerLoc}.textAnimator[${anim.name || i}]`,
              code: anim.expression
            });
          }
        });
      }
    }

    // Effect expressions
    if (layer.effects) {
      layer.effects.forEach((effect, ei) => {
        if (effect.params) {
          Object.entries(effect.params).forEach(([key, param]) => {
            const p = param as AnimatableProperty<unknown>;
            if (p?.expression?.enabled && p.expression.code) {
              expressions.push({
                location: `${layerLoc}.effect[${effect.name || ei}].${key}`,
                code: p.expression.code
              });
            }
          });
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
  };

  for (const { location, code } of expressions) {
    try {
      // evaluateWithTimeout returns fallback on timeout (doesn't throw)
      // We need to detect if it actually timed out
      const startTime = performance.now();
      await evaluateWithTimeout(code, testContext, NaN);
      const elapsed = performance.now() - startTime;

      // If it took close to 100ms, it probably timed out
      if (elapsed >= 95) {
        dangerous.push({
          location,
          expression: code.slice(0, 100) + (code.length > 100 ? '...' : ''),
          reason: 'timeout'
        });
      }
    } catch (err) {
      dangerous.push({
        location,
        expression: code.slice(0, 100) + (code.length > 100 ? '...' : ''),
        reason: 'error',
        error: err instanceof Error ? err.message : String(err)
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

  const startTime = performance.now();
  await evaluateWithTimeout(code, { value: 0, frame: 0 }, NaN);
  const elapsed = performance.now() - startTime;

  return elapsed < 95; // Didn't timeout
}
