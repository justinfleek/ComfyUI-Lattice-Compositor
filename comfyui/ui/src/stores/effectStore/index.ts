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
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import { defineStore } from "pinia";
import { markLayerDirty } from "@/services/layerEvaluationCache";
import { interpolateProperty } from "@/services/interpolation";
import { createEffectInstance } from "@/types/effects";
import type { JSONValue } from "@/types/dataAsset";
import type { PropertyValue } from "@/types/animation";
import type {
  LayerStyles,
  RGBA,
} from "@/types/layerStyles";
import {
  createDefaultBevelEmboss,
  createDefaultBlendingOptions,
  createDefaultColorOverlay,
  createDefaultDropShadow,
  createDefaultGradientOverlay,
  createDefaultInnerGlow,
  createDefaultInnerShadow,
  createDefaultLayerStyles,
  createDefaultOuterGlow,
  createDefaultSatin,
  createDefaultStroke,
} from "@/types/layerStyles";
import type {
  Composition,
  EffectInstance,
  InterpolationType,
  Layer,
} from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { generateKeyframeId } from "@/utils/uuid5";
import { safeFrame } from "@/stores/keyframeStore/helpers";
import type { Keyframe } from "@/types/animation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                            // store // access // interfaces
// ═══════════════════════════════════════════════════════════════════════════

export interface EffectStoreAccess {
  project: {
    meta: { modified: string };
  };
  currentFrame: number;
  getActiveCompLayers(): Layer[];
  getActiveComp(): Composition | null;
  pushHistory(): void;
}

export interface LayerStyleStore {
  project: {
    meta: { modified: string };
  };
  getActiveCompLayers(): Layer[];
  pushHistory(): void;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                         // style // presets
// ═══════════════════════════════════════════════════════════════════════════

export const STYLE_PRESETS: Record<string, Partial<LayerStyles>> = {
  "soft-shadow": {
    enabled: true,
    dropShadow: {
      ...createDefaultDropShadow(),
      opacity: { id: "", name: "", type: "number", value: 40, animated: false, keyframes: [] },
      size: { id: "", name: "", type: "number", value: 15, animated: false, keyframes: [] },
      distance: { id: "", name: "", type: "number", value: 8, animated: false, keyframes: [] },
    },
  },
  "hard-shadow": {
    enabled: true,
    dropShadow: {
      ...createDefaultDropShadow(),
      opacity: { id: "", name: "", type: "number", value: 80, animated: false, keyframes: [] },
      size: { id: "", name: "", type: "number", value: 0, animated: false, keyframes: [] },
      spread: { id: "", name: "", type: "number", value: 100, animated: false, keyframes: [] },
      distance: { id: "", name: "", type: "number", value: 4, animated: false, keyframes: [] },
    },
  },
  "neon-glow": {
    enabled: true,
    outerGlow: {
      ...createDefaultOuterGlow(),
      color: { id: "", name: "", type: "color", value: { r: 0, g: 255, b: 255, a: 1 }, animated: false, keyframes: [] },
      opacity: { id: "", name: "", type: "number", value: 100, animated: false, keyframes: [] },
      size: { id: "", name: "", type: "number", value: 20, animated: false, keyframes: [] },
    },
    innerGlow: {
      ...createDefaultInnerGlow(),
      color: { id: "", name: "", type: "color", value: { r: 255, g: 255, b: 255, a: 1 }, animated: false, keyframes: [] },
      opacity: { id: "", name: "", type: "number", value: 75, animated: false, keyframes: [] },
      size: { id: "", name: "", type: "number", value: 5, animated: false, keyframes: [] },
    },
  },
  "simple-stroke": {
    enabled: true,
    stroke: {
      ...createDefaultStroke(),
      color: { id: "", name: "", type: "color", value: { r: 0, g: 0, b: 0, a: 1 }, animated: false, keyframes: [] },
      size: { id: "", name: "", type: "number", value: 2, animated: false, keyframes: [] },
      position: "outside",
    },
  },
  embossed: {
    enabled: true,
    bevelEmboss: {
      ...createDefaultBevelEmboss(),
      style: "emboss",
      depth: { id: "", name: "", type: "number", value: 200, animated: false, keyframes: [] },
      size: { id: "", name: "", type: "number", value: 3, animated: false, keyframes: [] },
    },
  },
  "inner-bevel": {
    enabled: true,
    bevelEmboss: {
      ...createDefaultBevelEmboss(),
      style: "inner-bevel",
      technique: "smooth",
      depth: { id: "", name: "", type: "number", value: 100, animated: false, keyframes: [] },
      size: { id: "", name: "", type: "number", value: 5, animated: false, keyframes: [] },
    },
  },
  "pillow-emboss": {
    enabled: true,
    bevelEmboss: {
      ...createDefaultBevelEmboss(),
      style: "pillow-emboss",
      depth: { id: "", name: "", type: "number", value: 150, animated: false, keyframes: [] },
      size: { id: "", name: "", type: "number", value: 10, animated: false, keyframes: [] },
    },
  },
};

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // helper // functions
// ═══════════════════════════════════════════════════════════════════════════

function getLayerById(store: LayerStyleStore, layerId: string): Layer | undefined {
  return store.getActiveCompLayers().find((l) => l.id === layerId);
}

function ensureLayerStyles(layer: Layer): LayerStyles {
  if (!layer.layerStyles) {
    layer.layerStyles = createDefaultLayerStyles();
  }
  return layer.layerStyles;
}

function updateModified(store: LayerStyleStore): void {
  store.project.meta.modified = new Date().toISOString();
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                       // state // interface
// ═══════════════════════════════════════════════════════════════════════════

interface EffectState {
  styleClipboard: LayerStyles | null;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // store // definition
// ═══════════════════════════════════════════════════════════════════════════

export const useEffectStore = defineStore("effect", {
  state: (): EffectState => ({
    styleClipboard: null,
  }),

  getters: {
    hasStylesInClipboard: (state) => state.styleClipboard !== null,
  },

  actions: {
    // ═══════════════════════════════════════════════════════════════════════════
    //                                                         // layer // effects
    // ═══════════════════════════════════════════════════════════════════════════

    /**
     * Add effect to layer.
     */
    addEffectToLayer(store: EffectStoreAccess, layerId: string, effectKey: string): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer) return;

      const effect = createEffectInstance(effectKey);
      if (!effect) return;

      if (!layer.effects) layer.effects = [];
      layer.effects.push(effect);
      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();
    },

    /**
     * Remove effect from layer.
     */
    removeEffectFromLayer(store: EffectStoreAccess, layerId: string, effectId: string): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || !layer.effects) return;

      const index = layer.effects.findIndex((e) => e.id === effectId);
      if (index >= 0) {
        layer.effects.splice(index, 1);
        store.project.meta.modified = new Date().toISOString();
        store.pushHistory();
      }
    },

    /**
     * Update effect parameter value.
     */
    updateEffectParameter(store: EffectStoreAccess, layerId: string, effectId: string, paramKey: string, value: PropertyValue | JSONValue): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || !layer.effects) return;

      const effect = layer.effects.find((e) => e.id === effectId);
      if (!effect || !effect.parameters[paramKey]) return;

      effect.parameters[paramKey].value = value;
      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();
    },

    /**
     * Toggle effect parameter animation state.
     */
    setEffectParamAnimated(store: EffectStoreAccess, layerId: string, effectId: string, paramKey: string, animated: boolean): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || !layer.effects) return;

      const effect = layer.effects.find((e) => e.id === effectId);
      if (!effect || !effect.parameters[paramKey]) return;

      const param = effect.parameters[paramKey];
      param.animated = animated;

      if (animated && (!param.keyframes || param.keyframes.length === 0)) {
        // Deterministic ID generation: same layer/effect/param/frame/value always produces same ID
        const propertyPath = `effects.${effectId}.${paramKey}`;
        const valueStr = String(param.value);
        param.keyframes = [{
          id: generateKeyframeId(layerId, propertyPath, store.currentFrame, valueStr),
          frame: store.currentFrame,
          value: param.value,
          interpolation: "linear" as InterpolationType,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        }];
      }

      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();
    },

    /**
     * Toggle effect enabled state.
     */
    toggleEffect(store: EffectStoreAccess, layerId: string, effectId: string): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || !layer.effects) return;

      const effect = layer.effects.find((e) => e.id === effectId);
      if (!effect) return;

      effect.enabled = !effect.enabled;
      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();
    },

    /**
     * Reorder effects in stack.
     */
    reorderEffects(store: EffectStoreAccess, layerId: string, fromIndex: number, toIndex: number): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || !layer.effects) return;

      if (!Number.isInteger(fromIndex) || fromIndex < 0 || fromIndex >= layer.effects.length) return;
      if (!Number.isInteger(toIndex) || toIndex < 0 || toIndex >= layer.effects.length) return;

      const [effect] = layer.effects.splice(fromIndex, 1);
      layer.effects.splice(toIndex, 0, effect);
      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();
    },

    /**
     * Duplicate effect on layer.
     */
    duplicateEffect(store: EffectStoreAccess, layerId: string, effectId: string): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || !layer.effects) return;

      const effect = layer.effects.find((e) => e.id === effectId);
      if (!effect) return;

      const duplicate: EffectInstance = structuredClone(effect);
      duplicate.id = `effect_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
      duplicate.name = `${effect.name} Copy`;

      // Regenerate keyframe IDs for all effect parameters to avoid conflicts
      regenerateEffectKeyframeIds(layerId, duplicate);

      const index = layer.effects.findIndex((e) => e.id === effectId);
      layer.effects.splice(index + 1, 0, duplicate);

      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();
    },

    /**
     * Get evaluated effect parameter value at a given frame.
     */
    getEffectParameterValue(store: EffectStoreAccess, layerId: string, effectId: string, paramKey: string, frame?: number): PropertyValue | JSONValue {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || !layer.effects) {
        throw new Error(`[EffectStore] Cannot get parameter value: Layer "${layerId}" not found or has no effects`);
      }

      const effect = layer.effects.find((e) => e.id === effectId);
      if (!effect || !effect.parameters[paramKey]) {
        throw new Error(`[EffectStore] Cannot get parameter value: Effect "${effectId}" or parameter "${paramKey}" not found on layer "${layerId}"`);
      }

      const param = effect.parameters[paramKey];
      // Type proof: frame ∈ ℕ ∪ {undefined} → ℕ
      const frameValue = frame;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const activeComp = store.getActiveComp();
      const compCurrentFrameValue = (activeComp != null && typeof activeComp === "object" && "currentFrame" in activeComp && typeof activeComp.currentFrame === "number") ? activeComp.currentFrame : undefined;
      const rawFrame = isFiniteNumber(frameValue) && Number.isInteger(frameValue) && frameValue >= 0
        ? frameValue
        : (isFiniteNumber(compCurrentFrameValue) && Number.isInteger(compCurrentFrameValue) && compCurrentFrameValue >= 0 ? compCurrentFrameValue : 0);
      const targetFrame = Number.isFinite(rawFrame) ? rawFrame : 0;

      if (param.animated && param.keyframes.length > 0) {
        return interpolateProperty(param, targetFrame);
      }

      return param.value;
    },

    // ═══════════════════════════════════════════════════════════════════════════
    // LAYER STYLES - ENABLE/DISABLE
    // ═══════════════════════════════════════════════════════════════════════════

    /**
     * Enable or disable all layer styles for a layer.
     */
    setLayerStylesEnabled(store: LayerStyleStore, layerId: string, enabled: boolean): void {
      const layer = getLayerById(store, layerId);
      if (!layer) {
        storeLogger.warn("setLayerStylesEnabled: Layer not found", { layerId });
        return;
      }

      store.pushHistory();
      const styles = ensureLayerStyles(layer);
      styles.enabled = enabled;

      markLayerDirty(layerId);
      updateModified(store);
    },

    /**
     * Enable or disable a specific style type.
     */
    setStyleEnabled(store: LayerStyleStore, layerId: string, styleType: keyof LayerStyles, enabled: boolean): void {
      const layer = getLayerById(store, layerId);
      if (!layer) {
        storeLogger.warn("setStyleEnabled: Layer not found", { layerId });
        return;
      }

      store.pushHistory();
      const styles = ensureLayerStyles(layer);

      if (enabled && !styles[styleType]) {
        switch (styleType) {
          case "dropShadow": styles.dropShadow = createDefaultDropShadow(); break;
          case "innerShadow": styles.innerShadow = createDefaultInnerShadow(); break;
          case "outerGlow": styles.outerGlow = createDefaultOuterGlow(); break;
          case "innerGlow": styles.innerGlow = createDefaultInnerGlow(); break;
          case "bevelEmboss": styles.bevelEmboss = createDefaultBevelEmboss(); break;
          case "satin": styles.satin = createDefaultSatin(); break;
          case "colorOverlay": styles.colorOverlay = createDefaultColorOverlay(); break;
          case "gradientOverlay": styles.gradientOverlay = createDefaultGradientOverlay(); break;
          case "stroke": styles.stroke = createDefaultStroke(); break;
          case "blendingOptions": styles.blendingOptions = createDefaultBlendingOptions(); break;
        }
      }

      const style = styles[styleType];
      if (style && typeof style === "object" && "enabled" in style) {
        (style as { enabled: boolean }).enabled = enabled;
      }

      if (enabled && !styles.enabled) styles.enabled = true;

      markLayerDirty(layerId);
      updateModified(store);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                  // layer // styles // update // properties
    // ═══════════════════════════════════════════════════════════════════════════

    /**
     * Update a property on a specific style.
     */
    updateStyleProperty<T extends keyof LayerStyles, K extends keyof NonNullable<LayerStyles[T]>>(
      store: LayerStyleStore,
      layerId: string,
      styleType: T,
      property: K,
      value: PropertyValue | JSONValue,
    ): void {
      const layer = getLayerById(store, layerId);
      if (!layer) {
        storeLogger.warn("updateStyleProperty: Layer not found", { layerId });
        return;
      }

      store.pushHistory();
      const styles = ensureLayerStyles(layer);
      const style = styles[styleType];

      if (!style) {
        storeLogger.warn("updateStyleProperty: Style not found", { layerId, styleType });
        return;
      }

      // Guard: "enabled" is a boolean, not a style object - cannot update properties on it
      if (typeof style === "boolean") {
        storeLogger.warn("updateStyleProperty: Cannot update properties on boolean style", { layerId, styleType });
        return;
      }

      // Type-safe dynamic property access on style objects
      // Style is now narrowed to be an object (not boolean) - use Object.prototype for safe access
      const propertyKey = property as string;
      if (propertyKey in style) {
        // Access property via Object.getOwnPropertyDescriptor for type-safe dynamic access
        const styleObj = style as object;
        const prop = (styleObj as Record<string, PropertyValue | JSONValue | { value: PropertyValue | JSONValue }>)[propertyKey];
        if (prop && typeof prop === "object" && prop !== null && "value" in prop) {
          (prop as { value: PropertyValue | JSONValue }).value = value;
        } else {
          (styleObj as Record<string, PropertyValue | JSONValue>)[propertyKey] = value;
        }
      } else {
        storeLogger.warn("updateStyleProperty: Property not found on style", { layerId, styleType, property });
      }

      markLayerDirty(layerId);
      updateModified(store);
    },

    /**
     * Set entire style configuration.
     */
    setStyle<T extends keyof LayerStyles>(store: LayerStyleStore, layerId: string, styleType: T, styleConfig: LayerStyles[T]): void {
      const layer = getLayerById(store, layerId);
      if (!layer) {
        storeLogger.warn("setStyle: Layer not found", { layerId });
        return;
      }

      store.pushHistory();
      const styles = ensureLayerStyles(layer);
      Object.assign(styles, { [styleType]: styleConfig });

      markLayerDirty(layerId);
      updateModified(store);
    },

    /**
     * Set all layer styles at once.
     */
    setLayerStyles(store: LayerStyleStore, layerId: string, layerStyles: LayerStyles): void {
      const layer = getLayerById(store, layerId);
      if (!layer) {
        storeLogger.warn("setLayerStyles: Layer not found", { layerId });
        return;
      }

      store.pushHistory();
      layer.layerStyles = layerStyles;

      markLayerDirty(layerId);
      updateModified(store);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    // LAYER STYLES - COPY/PASTE
    // ═══════════════════════════════════════════════════════════════════════════

    /**
     * Copy layer styles from a layer.
     */
    copyLayerStyles(store: LayerStyleStore, layerId: string): LayerStyles | null {
      const layer = getLayerById(store, layerId);
      if (!layer || !layer.layerStyles) {
        throw new Error(`[EffectStore] Cannot copy layer styles: Layer "${layerId}" not found or has no layerStyles`);
      }

      const copied = JSON.parse(JSON.stringify(layer.layerStyles));
      this.styleClipboard = copied;
      storeLogger.debug("copyLayerStyles", { layerId });
      return copied;
    },

    /**
     * Paste layer styles to a layer.
     */
    pasteLayerStyles(store: LayerStyleStore, layerId: string, styles?: LayerStyles): void {
      // Type proof: stylesToPaste ∈ LayerStyles | undefined → LayerStyles | undefined
      const stylesToPaste = styles !== undefined ? styles : this.styleClipboard;
      if (!stylesToPaste) {
        storeLogger.warn("pasteLayerStyles: No styles provided");
        return;
      }

      const layer = getLayerById(store, layerId);
      if (!layer) {
        storeLogger.warn("pasteLayerStyles: Layer not found", { layerId });
        return;
      }

      store.pushHistory();
      layer.layerStyles = JSON.parse(JSON.stringify(stylesToPaste));

      markLayerDirty(layerId);
      updateModified(store);
    },

    /**
     * Paste layer styles to multiple layers.
     */
    pasteLayerStylesToMultiple(store: LayerStyleStore, layerIds: string[], styles?: LayerStyles): void {
      // Type proof: stylesToPaste ∈ LayerStyles | undefined → LayerStyles | undefined
      const stylesToPaste = styles !== undefined ? styles : this.styleClipboard;
      if (!stylesToPaste) {
        storeLogger.warn("pasteLayerStylesToMultiple: No styles provided");
        return;
      }

      store.pushHistory();

      for (const layerId of layerIds) {
        const layer = getLayerById(store, layerId);
        if (layer) {
          layer.layerStyles = JSON.parse(JSON.stringify(stylesToPaste));
          markLayerDirty(layerId);
        }
      }

      updateModified(store);
    },

    /**
     * Clear layer styles from a layer.
     */
    clearLayerStyles(store: LayerStyleStore, layerId: string): void {
      const layer = getLayerById(store, layerId);
      if (!layer) {
        storeLogger.warn("clearLayerStyles: Layer not found", { layerId });
        return;
      }

      store.pushHistory();
      layer.layerStyles = undefined;

      markLayerDirty(layerId);
      updateModified(store);
    },

    /**
     * Clear the style clipboard.
     */
    clearStyleClipboard(): void {
      this.styleClipboard = null;
    },

    /**
     * Get styles from clipboard.
     */
    getStylesFromClipboard(): LayerStyles | null {
      return this.styleClipboard;
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                      // layer // styles // quick // helpers
    // ═══════════════════════════════════════════════════════════════════════════

    /**
     * Add a drop shadow with specified parameters.
     */
    addDropShadow(store: LayerStyleStore, layerId: string, options?: {
      color?: RGBA;
      angle?: number;
      distance?: number;
      spread?: number;
      size?: number;
      opacity?: number;
    }): void {
      const layer = getLayerById(store, layerId);
      if (!layer) return;

      store.pushHistory();
      const styles = ensureLayerStyles(layer);
      styles.enabled = true;

      const shadow = createDefaultDropShadow();
      if (options) {
        if (options.color) shadow.color.value = options.color;
        if (options.angle !== undefined) shadow.angle.value = options.angle;
        if (options.distance !== undefined) shadow.distance.value = options.distance;
        if (options.spread !== undefined) shadow.spread.value = options.spread;
        if (options.size !== undefined) shadow.size.value = options.size;
        if (options.opacity !== undefined) shadow.opacity.value = options.opacity;
      }
      styles.dropShadow = shadow;

      markLayerDirty(layerId);
      updateModified(store);
    },

    /**
     * Add a stroke with specified parameters.
     */
    addStroke(store: LayerStyleStore, layerId: string, options?: {
      color?: RGBA;
      size?: number;
      position?: "outside" | "inside" | "center";
      opacity?: number;
    }): void {
      const layer = getLayerById(store, layerId);
      if (!layer) return;

      store.pushHistory();
      const styles = ensureLayerStyles(layer);
      styles.enabled = true;

      const stroke = createDefaultStroke();
      if (options) {
        if (options.color) stroke.color.value = options.color;
        if (options.size !== undefined) stroke.size.value = options.size;
        if (options.position) stroke.position = options.position;
        if (options.opacity !== undefined) stroke.opacity.value = options.opacity;
      }
      styles.stroke = stroke;

      markLayerDirty(layerId);
      updateModified(store);
    },

    /**
     * Add an outer glow with specified parameters.
     */
    addOuterGlow(store: LayerStyleStore, layerId: string, options?: {
      color?: RGBA;
      spread?: number;
      size?: number;
      opacity?: number;
    }): void {
      const layer = getLayerById(store, layerId);
      if (!layer) return;

      store.pushHistory();
      const styles = ensureLayerStyles(layer);
      styles.enabled = true;

      const glow = createDefaultOuterGlow();
      if (options) {
        if (options.color) glow.color.value = options.color;
        if (options.spread !== undefined) glow.spread.value = options.spread;
        if (options.size !== undefined) glow.size.value = options.size;
        if (options.opacity !== undefined) glow.opacity.value = options.opacity;
      }
      styles.outerGlow = glow;

      markLayerDirty(layerId);
      updateModified(store);
    },

    /**
     * Add a color overlay with specified parameters.
     */
    addColorOverlay(store: LayerStyleStore, layerId: string, options?: {
      color?: RGBA;
      opacity?: number;
      blendMode?: string;
    }): void {
      const layer = getLayerById(store, layerId);
      if (!layer) return;

      store.pushHistory();
      const styles = ensureLayerStyles(layer);
      styles.enabled = true;

      const overlay = createDefaultColorOverlay();
      if (options) {
        if (options.color) overlay.color.value = options.color;
        if (options.opacity !== undefined) overlay.opacity.value = options.opacity;
        if (options.blendMode) overlay.blendMode = options.blendMode as typeof overlay.blendMode;
      }
      styles.colorOverlay = overlay;

      markLayerDirty(layerId);
      updateModified(store);
    },

    /**
     * Add bevel and emboss with specified parameters.
     */
    addBevelEmboss(store: LayerStyleStore, layerId: string, options?: {
      style?: "outer-bevel" | "inner-bevel" | "emboss" | "pillow-emboss" | "stroke-emboss";
      technique?: "smooth" | "chisel-hard" | "chisel-soft";
      depth?: number;
      direction?: "up" | "down";
      size?: number;
      soften?: number;
      angle?: number;
      altitude?: number;
    }): void {
      const layer = getLayerById(store, layerId);
      if (!layer) return;

      store.pushHistory();
      const styles = ensureLayerStyles(layer);
      styles.enabled = true;

      const bevel = createDefaultBevelEmboss();
      if (options) {
        if (options.style) bevel.style = options.style;
        if (options.technique) bevel.technique = options.technique;
        if (options.depth !== undefined) bevel.depth.value = options.depth;
        if (options.direction) bevel.direction = options.direction;
        if (options.size !== undefined) bevel.size.value = options.size;
        if (options.soften !== undefined) bevel.soften.value = options.soften;
        if (options.angle !== undefined) bevel.angle.value = options.angle;
        if (options.altitude !== undefined) bevel.altitude.value = options.altitude;
      }
      styles.bevelEmboss = bevel;

      markLayerDirty(layerId);
      updateModified(store);
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                               // layer // styles // presets
    // ═══════════════════════════════════════════════════════════════════════════

    /**
     * Apply a style preset to a layer.
     */
    applyStylePreset(store: LayerStyleStore, layerId: string, presetName: string): void {
      const preset = STYLE_PRESETS[presetName];
      if (!preset) {
        storeLogger.warn("applyStylePreset: Preset not found", { presetName });
        return;
      }

      const layer = getLayerById(store, layerId);
      if (!layer) return;

      store.pushHistory();
      const styles = ensureLayerStyles(layer);
      Object.assign(styles, JSON.parse(JSON.stringify(preset)));

      markLayerDirty(layerId);
      updateModified(store);
    },

    /**
     * Get list of available style preset names.
     */
    getStylePresetNames(): string[] {
      return Object.keys(STYLE_PRESETS);
    },
  },
});

// ═══════════════════════════════════════════════════════════════════════════
// HELPER: Regenerate keyframe IDs for effect parameters
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Regenerate all keyframe IDs in an effect's parameters to avoid conflicts when duplicating
 * Uses correct property paths for deterministic ID generation: effects.${effectId}.${paramKey}
 */
function regenerateEffectKeyframeIds(layerId: string, effect: EffectInstance): void {
  if (!effect.parameters) return;

  for (const [paramKey, param] of Object.entries(effect.parameters)) {
    if (param && param.keyframes && Array.isArray(param.keyframes) && param.keyframes.length > 0) {
      const propertyPath = `effects.${effect.id}.${paramKey}`;
      param.keyframes = param.keyframes.map((kf: Keyframe<PropertyValue>) => {
        const valueStr = typeof kf.value === "object" && kf.value !== null && "x" in kf.value && "y" in kf.value
          ? `${(kf.value as { x: number; y: number }).x},${(kf.value as { x: number; y: number }).y}${"z" in kf.value ? `,${(kf.value as { x: number; y: number; z?: number }).z}` : ""}`
          : String(kf.value);
        return {
          ...kf,
          id: generateKeyframeId(layerId, propertyPath, safeFrame(kf.frame, 0), valueStr),
        };
      });
    }
  }
}

export type EffectStoreType = ReturnType<typeof useEffectStore>;
