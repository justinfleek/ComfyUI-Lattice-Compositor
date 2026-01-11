/**
 * Effect Store
 *
 * Domain store for layer effects and Photoshop-style layer styles.
 *
 * MODULE STRUCTURE:
 * - Layer effects: add, remove, update, toggle, reorder, duplicate
 * - Layer styles: drop shadow, glow, stroke, bevel/emboss, overlays
 * - Style clipboard: copy/paste styles between layers
 * - Style presets: built-in style templates
 */

import { defineStore } from "pinia";
import type { LayerStyles } from "@/types/layerStyles";

// Import action implementations
import {
  addEffectToLayer as addEffectToLayerImpl,
  removeEffectFromLayer as removeEffectFromLayerImpl,
  updateEffectParameter as updateEffectParameterImpl,
  setEffectParamAnimated as setEffectParamAnimatedImpl,
  toggleEffect as toggleEffectImpl,
  reorderEffects as reorderEffectsImpl,
  duplicateEffect as duplicateEffectImpl,
  getEffectParameterValue as getEffectParameterValueImpl,
  type EffectStore as EffectStoreAccess,
} from "../actions/effectActions";

import {
  setLayerStylesEnabled as setLayerStylesEnabledImpl,
  setStyleEnabled as setStyleEnabledImpl,
  updateStyleProperty as updateStylePropertyImpl,
  setStyle as setStyleImpl,
  setLayerStyles as setLayerStylesImpl,
  copyLayerStyles as copyLayerStylesImpl,
  pasteLayerStyles as pasteLayerStylesImpl,
  pasteLayerStylesToMultiple as pasteLayerStylesToMultipleImpl,
  clearLayerStyles as clearLayerStylesImpl,
  addDropShadow as addDropShadowImpl,
  addStroke as addStrokeImpl,
  addOuterGlow as addOuterGlowImpl,
  addColorOverlay as addColorOverlayImpl,
  addBevelEmboss as addBevelEmbossImpl,
  applyStylePreset as applyStylePresetImpl,
  getStylePresetNames as getStylePresetNamesImpl,
  STYLE_PRESETS,
  type LayerStyleStore,
} from "../actions/layerStyleActions";

import type { RGBA } from "@/types/layerStyles";

// Re-export for consumers
export { STYLE_PRESETS };
export type { EffectStoreAccess, LayerStyleStore };

// ============================================================================
// STATE INTERFACE
// ============================================================================

interface EffectState {
  /** Clipboard for copy/paste layer styles */
  styleClipboard: LayerStyles | null;
}

// ============================================================================
// STORE DEFINITION
// ============================================================================

export const useEffectStore = defineStore("effect", {
  state: (): EffectState => ({
    styleClipboard: null,
  }),

  getters: {
    /** Check if clipboard has layer styles */
    hasStylesInClipboard: (state) => state.styleClipboard !== null,
  },

  actions: {
    // ========================================================================
    // LAYER EFFECTS
    // ========================================================================

    addEffectToLayer(
      compositorStore: EffectStoreAccess,
      layerId: string,
      effectKey: string,
    ): void {
      addEffectToLayerImpl(compositorStore, layerId, effectKey);
    },

    removeEffectFromLayer(
      compositorStore: EffectStoreAccess,
      layerId: string,
      effectId: string,
    ): void {
      removeEffectFromLayerImpl(compositorStore, layerId, effectId);
    },

    updateEffectParameter(
      compositorStore: EffectStoreAccess,
      layerId: string,
      effectId: string,
      paramKey: string,
      value: unknown,
    ): void {
      updateEffectParameterImpl(compositorStore, layerId, effectId, paramKey, value);
    },

    setEffectParamAnimated(
      compositorStore: EffectStoreAccess,
      layerId: string,
      effectId: string,
      paramKey: string,
      animated: boolean,
    ): void {
      setEffectParamAnimatedImpl(compositorStore, layerId, effectId, paramKey, animated);
    },

    toggleEffect(
      compositorStore: EffectStoreAccess,
      layerId: string,
      effectId: string,
    ): void {
      toggleEffectImpl(compositorStore, layerId, effectId);
    },

    reorderEffects(
      compositorStore: EffectStoreAccess,
      layerId: string,
      fromIndex: number,
      toIndex: number,
    ): void {
      reorderEffectsImpl(compositorStore, layerId, fromIndex, toIndex);
    },

    duplicateEffect(
      compositorStore: EffectStoreAccess,
      layerId: string,
      effectId: string,
    ): void {
      duplicateEffectImpl(compositorStore, layerId, effectId);
    },

    getEffectParameterValue(
      compositorStore: EffectStoreAccess,
      layerId: string,
      effectId: string,
      paramKey: string,
      frame?: number,
    ): unknown {
      return getEffectParameterValueImpl(compositorStore, layerId, effectId, paramKey, frame);
    },

    // ========================================================================
    // LAYER STYLES - ENABLE/DISABLE
    // ========================================================================

    setLayerStylesEnabled(
      compositorStore: LayerStyleStore,
      layerId: string,
      enabled: boolean,
    ): void {
      setLayerStylesEnabledImpl(compositorStore, layerId, enabled);
    },

    setStyleEnabled(
      compositorStore: LayerStyleStore,
      layerId: string,
      styleType: keyof LayerStyles,
      enabled: boolean,
    ): void {
      setStyleEnabledImpl(compositorStore, layerId, styleType, enabled);
    },

    // ========================================================================
    // LAYER STYLES - UPDATE PROPERTIES
    // ========================================================================

    updateStyleProperty<
      T extends keyof LayerStyles,
      K extends keyof NonNullable<LayerStyles[T]>,
    >(
      compositorStore: LayerStyleStore,
      layerId: string,
      styleType: T,
      property: K,
      value: unknown,
    ): void {
      updateStylePropertyImpl(compositorStore, layerId, styleType, property, value as any);
    },

    setStyle<T extends keyof LayerStyles>(
      compositorStore: LayerStyleStore,
      layerId: string,
      styleType: T,
      styleConfig: LayerStyles[T],
    ): void {
      setStyleImpl(compositorStore, layerId, styleType, styleConfig);
    },

    setLayerStyles(
      compositorStore: LayerStyleStore,
      layerId: string,
      layerStyles: LayerStyles,
    ): void {
      setLayerStylesImpl(compositorStore, layerId, layerStyles);
    },

    // ========================================================================
    // LAYER STYLES - COPY/PASTE
    // ========================================================================

    copyLayerStyles(
      compositorStore: LayerStyleStore,
      layerId: string,
    ): LayerStyles | null {
      const copied = copyLayerStylesImpl(compositorStore, layerId);
      if (copied) {
        this.styleClipboard = copied;
      }
      return copied;
    },

    pasteLayerStyles(
      compositorStore: LayerStyleStore,
      layerId: string,
      styles?: LayerStyles,
    ): void {
      const stylesToPaste = styles ?? this.styleClipboard ?? undefined;
      pasteLayerStylesImpl(compositorStore, layerId, stylesToPaste);
    },

    pasteLayerStylesToMultiple(
      compositorStore: LayerStyleStore,
      layerIds: string[],
      styles?: LayerStyles,
    ): void {
      const stylesToPaste = styles ?? this.styleClipboard ?? undefined;
      pasteLayerStylesToMultipleImpl(compositorStore, layerIds, stylesToPaste);
    },

    clearLayerStyles(
      compositorStore: LayerStyleStore,
      layerId: string,
    ): void {
      clearLayerStylesImpl(compositorStore, layerId);
    },

    clearStyleClipboard(): void {
      this.styleClipboard = null;
    },

    getStylesFromClipboard(): LayerStyles | null {
      return this.styleClipboard;
    },

    // ========================================================================
    // LAYER STYLES - QUICK HELPERS
    // ========================================================================

    addDropShadow(
      compositorStore: LayerStyleStore,
      layerId: string,
      options?: {
        color?: RGBA;
        angle?: number;
        distance?: number;
        spread?: number;
        size?: number;
        opacity?: number;
      },
    ): void {
      addDropShadowImpl(compositorStore, layerId, options);
    },

    addStroke(
      compositorStore: LayerStyleStore,
      layerId: string,
      options?: {
        color?: RGBA;
        size?: number;
        position?: "outside" | "inside" | "center";
        opacity?: number;
      },
    ): void {
      addStrokeImpl(compositorStore, layerId, options);
    },

    addOuterGlow(
      compositorStore: LayerStyleStore,
      layerId: string,
      options?: {
        color?: RGBA;
        spread?: number;
        size?: number;
        opacity?: number;
      },
    ): void {
      addOuterGlowImpl(compositorStore, layerId, options);
    },

    addColorOverlay(
      compositorStore: LayerStyleStore,
      layerId: string,
      options?: {
        color?: RGBA;
        opacity?: number;
        blendMode?: string;
      },
    ): void {
      addColorOverlayImpl(compositorStore, layerId, options);
    },

    addBevelEmboss(
      compositorStore: LayerStyleStore,
      layerId: string,
      options?: {
        style?:
          | "outer-bevel"
          | "inner-bevel"
          | "emboss"
          | "pillow-emboss"
          | "stroke-emboss";
        technique?: "smooth" | "chisel-hard" | "chisel-soft";
        depth?: number;
        direction?: "up" | "down";
        size?: number;
        soften?: number;
        angle?: number;
        altitude?: number;
      },
    ): void {
      addBevelEmbossImpl(compositorStore, layerId, options);
    },

    // ========================================================================
    // LAYER STYLES - PRESETS
    // ========================================================================

    applyStylePreset(
      compositorStore: LayerStyleStore,
      layerId: string,
      presetName: string,
    ): void {
      applyStylePresetImpl(compositorStore, layerId, presetName);
    },

    getStylePresetNames(): string[] {
      return getStylePresetNamesImpl();
    },
  },
});

// ============================================================================
// TYPE EXPORTS
// ============================================================================

export type EffectStoreType = ReturnType<typeof useEffectStore>;
