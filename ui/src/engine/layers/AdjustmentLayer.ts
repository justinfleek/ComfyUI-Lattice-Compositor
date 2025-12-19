/**
 * AdjustmentLayer - DEPRECATED
 *
 * This file re-exports from EffectLayer for backwards compatibility.
 * Use EffectLayer directly in new code.
 *
 * @deprecated Import from './EffectLayer' instead
 */

export {
  EffectLayer as AdjustmentLayer,
  EffectLayer,
  type EffectLayerRenderContext as AdjustmentRenderContext,
  type EffectLayerRenderContext,
  isEffectLayer as isAdjustmentLayer,
  isEffectLayer,
} from './EffectLayer';
