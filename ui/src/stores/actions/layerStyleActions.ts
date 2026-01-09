/**
 * Layer Style Actions
 *
 * Store actions for managing Photoshop-style Layer Styles:
 * - Enable/disable styles
 * - Update style properties
 * - Copy/paste styles between layers
 * - Create style presets
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import type { LayerStyles, RGBA } from "@/types/layerStyles";
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
import type { Layer } from "@/types/project";
import { storeLogger } from "@/utils/logger";

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface LayerStyleStore {
  project: {
    meta: { modified: string };
  };
  getActiveCompLayers(): Layer[];
  pushHistory(): void;
}

// ============================================================================
// HELPERS
// ============================================================================

/**
 * Get a layer by ID from the active composition
 */
function getLayerById(
  store: LayerStyleStore,
  layerId: string,
): Layer | undefined {
  const layers = store.getActiveCompLayers();
  return layers.find((l) => l.id === layerId);
}

/**
 * Ensure layer has layerStyles initialized
 */
function ensureLayerStyles(layer: Layer): LayerStyles {
  if (!layer.layerStyles) {
    layer.layerStyles = createDefaultLayerStyles();
  }
  return layer.layerStyles;
}

/**
 * Update modified timestamp
 */
function updateModified(store: LayerStyleStore): void {
  store.project.meta.modified = new Date().toISOString();
}

// ============================================================================
// LAYER STYLES - ENABLE/DISABLE
// ============================================================================

/**
 * Enable or disable all layer styles for a layer
 */
export function setLayerStylesEnabled(
  store: LayerStyleStore,
  layerId: string,
  enabled: boolean,
): void {
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

  storeLogger.debug("setLayerStylesEnabled", { layerId, enabled });
}

/**
 * Enable or disable a specific style type
 */
export function setStyleEnabled(
  store: LayerStyleStore,
  layerId: string,
  styleType: keyof LayerStyles,
  enabled: boolean,
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("setStyleEnabled: Layer not found", { layerId });
    return;
  }

  store.pushHistory();
  const styles = ensureLayerStyles(layer);

  // Create default style if enabling and doesn't exist
  if (enabled && !styles[styleType]) {
    switch (styleType) {
      case "dropShadow":
        styles.dropShadow = createDefaultDropShadow();
        break;
      case "innerShadow":
        styles.innerShadow = createDefaultInnerShadow();
        break;
      case "outerGlow":
        styles.outerGlow = createDefaultOuterGlow();
        break;
      case "innerGlow":
        styles.innerGlow = createDefaultInnerGlow();
        break;
      case "bevelEmboss":
        styles.bevelEmboss = createDefaultBevelEmboss();
        break;
      case "satin":
        styles.satin = createDefaultSatin();
        break;
      case "colorOverlay":
        styles.colorOverlay = createDefaultColorOverlay();
        break;
      case "gradientOverlay":
        styles.gradientOverlay = createDefaultGradientOverlay();
        break;
      case "stroke":
        styles.stroke = createDefaultStroke();
        break;
      case "blendingOptions":
        styles.blendingOptions = createDefaultBlendingOptions();
        break;
    }
  }

  // Set enabled state
  const style = styles[styleType];
  if (style && typeof style === "object" && "enabled" in style) {
    (style as any).enabled = enabled;
  }

  // Also enable master styles if enabling a child
  if (enabled && !styles.enabled) {
    styles.enabled = true;
  }

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("setStyleEnabled", { layerId, styleType, enabled });
}

// ============================================================================
// LAYER STYLES - UPDATE PROPERTIES
// ============================================================================

/**
 * Update a property on a specific style
 */
export function updateStyleProperty<
  T extends keyof LayerStyles,
  K extends keyof NonNullable<LayerStyles[T]>,
>(
  store: LayerStyleStore,
  layerId: string,
  styleType: T,
  property: K,
  value: any,
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("updateStyleProperty: Layer not found", { layerId });
    return;
  }

  store.pushHistory();
  const styles = ensureLayerStyles(layer);
  const style = styles[styleType] as any;

  if (!style) {
    storeLogger.warn("updateStyleProperty: Style not found", {
      layerId,
      styleType,
    });
    return;
  }

  // Handle animatable properties
  if (
    style[property] &&
    typeof style[property] === "object" &&
    "value" in style[property]
  ) {
    style[property].value = value;
  } else {
    style[property] = value;
  }

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("updateStyleProperty", {
    layerId,
    styleType,
    property,
    value,
  });
}

/**
 * Set entire style configuration
 */
export function setStyle<T extends keyof LayerStyles>(
  store: LayerStyleStore,
  layerId: string,
  styleType: T,
  styleConfig: LayerStyles[T],
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("setStyle: Layer not found", { layerId });
    return;
  }

  store.pushHistory();
  const styles = ensureLayerStyles(layer);
  (styles as any)[styleType] = styleConfig;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("setStyle", { layerId, styleType });
}

/**
 * Set all layer styles at once
 */
export function setLayerStyles(
  store: LayerStyleStore,
  layerId: string,
  layerStyles: LayerStyles,
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("setLayerStyles: Layer not found", { layerId });
    return;
  }

  store.pushHistory();
  layer.layerStyles = layerStyles;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("setLayerStyles", { layerId });
}

// ============================================================================
// COPY/PASTE LAYER STYLES
// ============================================================================

/** Clipboard for layer styles */
let styleClipboard: LayerStyles | null = null;

/**
 * Copy layer styles from a layer
 */
export function copyLayerStyles(
  store: LayerStyleStore,
  layerId: string,
): LayerStyles | null {
  const layer = getLayerById(store, layerId);
  if (!layer || !layer.layerStyles) {
    storeLogger.warn("copyLayerStyles: Layer or styles not found", { layerId });
    return null;
  }

  // Deep clone the styles
  styleClipboard = JSON.parse(JSON.stringify(layer.layerStyles));

  storeLogger.debug("copyLayerStyles", { layerId });
  return styleClipboard;
}

/**
 * Paste layer styles to a layer
 */
export function pasteLayerStyles(
  store: LayerStyleStore,
  layerId: string,
  styles?: LayerStyles,
): void {
  const stylesToPaste = styles ?? styleClipboard;
  if (!stylesToPaste) {
    storeLogger.warn("pasteLayerStyles: No styles in clipboard");
    return;
  }

  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("pasteLayerStyles: Layer not found", { layerId });
    return;
  }

  store.pushHistory();

  // Deep clone to avoid reference issues
  layer.layerStyles = JSON.parse(JSON.stringify(stylesToPaste));

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("pasteLayerStyles", { layerId });
}

/**
 * Paste layer styles to multiple layers
 */
export function pasteLayerStylesToMultiple(
  store: LayerStyleStore,
  layerIds: string[],
  styles?: LayerStyles,
): void {
  const stylesToPaste = styles ?? styleClipboard;
  if (!stylesToPaste) {
    storeLogger.warn("pasteLayerStylesToMultiple: No styles in clipboard");
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
  storeLogger.debug("pasteLayerStylesToMultiple", { layerIds });
}

/**
 * Clear layer styles from a layer
 */
export function clearLayerStyles(
  store: LayerStyleStore,
  layerId: string,
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("clearLayerStyles: Layer not found", { layerId });
    return;
  }

  store.pushHistory();
  layer.layerStyles = undefined;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("clearLayerStyles", { layerId });
}

/**
 * Check if clipboard has layer styles
 */
export function hasStylesInClipboard(): boolean {
  return styleClipboard !== null;
}

/**
 * Get styles from clipboard
 */
export function getStylesFromClipboard(): LayerStyles | null {
  return styleClipboard;
}

// ============================================================================
// QUICK STYLE HELPERS
// ============================================================================

/**
 * Add a drop shadow with specified parameters
 */
export function addDropShadow(
  store: LayerStyleStore,
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
  const layer = getLayerById(store, layerId);
  if (!layer) return;

  store.pushHistory();
  const styles = ensureLayerStyles(layer);
  styles.enabled = true;

  const shadow = createDefaultDropShadow();

  if (options) {
    if (options.color) shadow.color.value = options.color;
    if (options.angle !== undefined) shadow.angle.value = options.angle;
    if (options.distance !== undefined)
      shadow.distance.value = options.distance;
    if (options.spread !== undefined) shadow.spread.value = options.spread;
    if (options.size !== undefined) shadow.size.value = options.size;
    if (options.opacity !== undefined) shadow.opacity.value = options.opacity;
  }

  styles.dropShadow = shadow;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("addDropShadow", { layerId, options });
}

/**
 * Add a stroke with specified parameters
 */
export function addStroke(
  store: LayerStyleStore,
  layerId: string,
  options?: {
    color?: RGBA;
    size?: number;
    position?: "outside" | "inside" | "center";
    opacity?: number;
  },
): void {
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

  storeLogger.debug("addStroke", { layerId, options });
}

/**
 * Add an outer glow with specified parameters
 */
export function addOuterGlow(
  store: LayerStyleStore,
  layerId: string,
  options?: {
    color?: RGBA;
    spread?: number;
    size?: number;
    opacity?: number;
  },
): void {
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

  storeLogger.debug("addOuterGlow", { layerId, options });
}

/**
 * Add a color overlay with specified parameters
 */
export function addColorOverlay(
  store: LayerStyleStore,
  layerId: string,
  options?: {
    color?: RGBA;
    opacity?: number;
    blendMode?: string;
  },
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) return;

  store.pushHistory();
  const styles = ensureLayerStyles(layer);
  styles.enabled = true;

  const overlay = createDefaultColorOverlay();

  if (options) {
    if (options.color) overlay.color.value = options.color;
    if (options.opacity !== undefined) overlay.opacity.value = options.opacity;
    if (options.blendMode) overlay.blendMode = options.blendMode as any;
  }

  styles.colorOverlay = overlay;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("addColorOverlay", { layerId, options });
}

/**
 * Add bevel and emboss with specified parameters
 */
export function addBevelEmboss(
  store: LayerStyleStore,
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

  storeLogger.debug("addBevelEmboss", { layerId, options });
}

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
