/**
 * Layer Style Actions - Style Presets
 *
 * Built-in style presets and preset application functions.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import type { LayerStyles } from "@/types/layerStyles";
import {
  createDefaultBevelEmboss,
  createDefaultDropShadow,
  createDefaultInnerGlow,
  createDefaultOuterGlow,
  createDefaultStroke,
} from "@/types/layerStyles";
import { storeLogger } from "@/utils/logger";
import {
  type LayerStyleStore,
  getLayerById,
  ensureLayerStyles,
  updateModified,
} from "./types";

// ============================================================================
// STYLE PRESETS
// ============================================================================

/** Built-in style presets */
export const STYLE_PRESETS: Record<string, Partial<LayerStyles>> = {
  "soft-shadow": {
    enabled: true,
    dropShadow: {
      ...createDefaultDropShadow(),
      opacity: {
        id: "",
        name: "",
        type: "number",
        value: 40,
        animated: false,
        keyframes: [],
      },
      size: {
        id: "",
        name: "",
        type: "number",
        value: 15,
        animated: false,
        keyframes: [],
      },
      distance: {
        id: "",
        name: "",
        type: "number",
        value: 8,
        animated: false,
        keyframes: [],
      },
    },
  },
  "hard-shadow": {
    enabled: true,
    dropShadow: {
      ...createDefaultDropShadow(),
      opacity: {
        id: "",
        name: "",
        type: "number",
        value: 80,
        animated: false,
        keyframes: [],
      },
      size: {
        id: "",
        name: "",
        type: "number",
        value: 0,
        animated: false,
        keyframes: [],
      },
      spread: {
        id: "",
        name: "",
        type: "number",
        value: 100,
        animated: false,
        keyframes: [],
      },
      distance: {
        id: "",
        name: "",
        type: "number",
        value: 4,
        animated: false,
        keyframes: [],
      },
    },
  },
  "neon-glow": {
    enabled: true,
    outerGlow: {
      ...createDefaultOuterGlow(),
      color: {
        id: "",
        name: "",
        type: "color",
        value: { r: 0, g: 255, b: 255, a: 1 },
        animated: false,
        keyframes: [],
      },
      opacity: {
        id: "",
        name: "",
        type: "number",
        value: 100,
        animated: false,
        keyframes: [],
      },
      size: {
        id: "",
        name: "",
        type: "number",
        value: 20,
        animated: false,
        keyframes: [],
      },
    },
    innerGlow: {
      ...createDefaultInnerGlow(),
      color: {
        id: "",
        name: "",
        type: "color",
        value: { r: 255, g: 255, b: 255, a: 1 },
        animated: false,
        keyframes: [],
      },
      opacity: {
        id: "",
        name: "",
        type: "number",
        value: 75,
        animated: false,
        keyframes: [],
      },
      size: {
        id: "",
        name: "",
        type: "number",
        value: 5,
        animated: false,
        keyframes: [],
      },
    },
  },
  "simple-stroke": {
    enabled: true,
    stroke: {
      ...createDefaultStroke(),
      color: {
        id: "",
        name: "",
        type: "color",
        value: { r: 0, g: 0, b: 0, a: 1 },
        animated: false,
        keyframes: [],
      },
      size: {
        id: "",
        name: "",
        type: "number",
        value: 2,
        animated: false,
        keyframes: [],
      },
      position: "outside",
    },
  },
  embossed: {
    enabled: true,
    bevelEmboss: {
      ...createDefaultBevelEmboss(),
      style: "emboss",
      depth: {
        id: "",
        name: "",
        type: "number",
        value: 200,
        animated: false,
        keyframes: [],
      },
      size: {
        id: "",
        name: "",
        type: "number",
        value: 3,
        animated: false,
        keyframes: [],
      },
    },
  },
  "inner-bevel": {
    enabled: true,
    bevelEmboss: {
      ...createDefaultBevelEmboss(),
      style: "inner-bevel",
      technique: "smooth",
      depth: {
        id: "",
        name: "",
        type: "number",
        value: 100,
        animated: false,
        keyframes: [],
      },
      size: {
        id: "",
        name: "",
        type: "number",
        value: 5,
        animated: false,
        keyframes: [],
      },
    },
  },
  "pillow-emboss": {
    enabled: true,
    bevelEmboss: {
      ...createDefaultBevelEmboss(),
      style: "pillow-emboss",
      depth: {
        id: "",
        name: "",
        type: "number",
        value: 150,
        animated: false,
        keyframes: [],
      },
      size: {
        id: "",
        name: "",
        type: "number",
        value: 10,
        animated: false,
        keyframes: [],
      },
    },
  },
};

// ============================================================================
// PRESET FUNCTIONS
// ============================================================================

/**
 * Apply a style preset to a layer
 */
export function applyStylePreset(
  store: LayerStyleStore,
  layerId: string,
  presetName: string,
): void {
  const preset = STYLE_PRESETS[presetName];
  if (!preset) {
    storeLogger.warn("applyStylePreset: Preset not found", { presetName });
    return;
  }

  const layer = getLayerById(store, layerId);
  if (!layer) return;

  store.pushHistory();
  const styles = ensureLayerStyles(layer);

  // Merge preset into existing styles
  Object.assign(styles, JSON.parse(JSON.stringify(preset)));

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("applyStylePreset", { layerId, presetName });
}

/**
 * Get list of available style preset names
 */
export function getStylePresetNames(): string[] {
  return Object.keys(STYLE_PRESETS);
}
