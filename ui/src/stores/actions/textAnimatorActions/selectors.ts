/**
 * Text Animator Actions - Selectors
 *
 * Range selector, expression selector, and wiggly selector operations.
 */

import { isExpressionSafe } from "@/services/expressions/expressionValidator";
import {
  createExpressionSelector,
  createWigglySelector,
} from "@/services/textAnimator";
import { getTextLayer, getTextData, updateModified } from "./helpers";
import type {
  TextAnimatorStore,
  RangeSelectorConfig,
  ExpressionSelectorConfig,
  WigglySelectorConfig,
} from "./types";

// ============================================================================
// RANGE SELECTOR OPERATIONS
// ============================================================================

/**
 * Configure the range selector for a text animator
 */
export function configureRangeSelector(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  config: RangeSelectorConfig,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find((a) => a.id === animatorId);
  if (!animator) return false;

  store.pushHistory();

  const selector = animator.rangeSelector;

  if (config.start !== undefined) selector.start.value = config.start;
  if (config.end !== undefined) selector.end.value = config.end;
  if (config.offset !== undefined) selector.offset.value = config.offset;
  if (config.shape !== undefined) selector.shape = config.shape;
  if (config.amount !== undefined) selector.amount = config.amount;
  if (config.smoothness !== undefined) selector.smoothness = config.smoothness;
  if (config.basedOn !== undefined) selector.basedOn = config.basedOn;
  if (config.randomizeOrder !== undefined)
    selector.randomizeOrder = config.randomizeOrder;

  updateModified(store);
  return true;
}

// ============================================================================
// EXPRESSION SELECTOR OPERATIONS
// ============================================================================

/**
 * Add or configure an expression selector for a text animator
 * SECURITY: Validates expressions before applying (DoS protection)
 */
export async function configureExpressionSelector(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  config: ExpressionSelectorConfig,
): Promise<boolean> {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find((a) => a.id === animatorId);
  if (!animator) return false;

  // SECURITY: Validate expression before applying
  if (
    config.expression !== undefined &&
    typeof config.expression === "string" &&
    config.expression.trim()
  ) {
    const safe = await isExpressionSafe(config.expression);
    if (!safe) {
      console.error(
        "[SECURITY] Expression blocked - timeout detected (possible infinite loop)",
      );
      return false;
    }
  }

  store.pushHistory();

  // Create expression selector if doesn't exist
  if (!animator.expressionSelector) {
    animator.expressionSelector = createExpressionSelector(
      config.expression || "selectorValue",
    );
  }

  const selector = animator.expressionSelector;
  selector.enabled = true;

  if (config.expression !== undefined)
    selector.amountExpression = config.expression;
  if (config.mode !== undefined) selector.mode = config.mode;
  if (config.basedOn !== undefined) selector.basedOn = config.basedOn;

  updateModified(store);
  return true;
}

/**
 * Remove expression selector from animator
 */
export function removeExpressionSelector(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find((a) => a.id === animatorId);
  if (!animator || !animator.expressionSelector) return false;

  store.pushHistory();
  animator.expressionSelector.enabled = false;
  updateModified(store);
  return true;
}

// ============================================================================
// WIGGLY SELECTOR OPERATIONS
// ============================================================================

/**
 * Add or configure a wiggly selector for a text animator
 */
export function configureWigglySelector(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  config: WigglySelectorConfig,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find((a) => a.id === animatorId);
  if (!animator) return false;

  store.pushHistory();

  // Create wiggly selector if doesn't exist
  if (!animator.wigglySelector) {
    animator.wigglySelector = createWigglySelector({ enabled: true });
  }

  const selector = animator.wigglySelector;
  selector.enabled = true;

  if (config.mode !== undefined) selector.mode = config.mode;
  if (config.maxAmount !== undefined) selector.maxAmount = config.maxAmount;
  if (config.minAmount !== undefined) selector.minAmount = config.minAmount;
  if (config.wigglesPerSecond !== undefined)
    selector.wigglesPerSecond = config.wigglesPerSecond;
  if (config.correlation !== undefined)
    selector.correlation = config.correlation;
  if (config.lockDimensions !== undefined)
    selector.lockDimensions = config.lockDimensions;
  if (config.randomSeed !== undefined) selector.randomSeed = config.randomSeed;

  updateModified(store);
  return true;
}

/**
 * Remove wiggly selector from animator
 */
export function removeWigglySelector(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find((a) => a.id === animatorId);
  if (!animator || !animator.wigglySelector) return false;

  store.pushHistory();
  animator.wigglySelector.enabled = false;
  updateModified(store);
  return true;
}
