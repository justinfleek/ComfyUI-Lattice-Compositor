/**
 * Layer Style Actions
 *
 * Store actions for managing Photoshop-style Layer Styles.
 *
 * MODULE STRUCTURE:
 * - types.ts: Store interface and helper functions
 * - core.ts: Enable/disable styles, update properties
 * - clipboard.ts: Copy/paste styles between layers
 * - quickStyles.ts: Convenience functions for common styles
 * - presets.ts: Built-in style presets
 */

// Types
export type { LayerStyleStore } from "./types";

// Core operations
export {
  setLayerStylesEnabled,
  setStyleEnabled,
  updateStyleProperty,
  setStyle,
  setLayerStyles,
} from "./core";

// Clipboard operations
export {
  copyLayerStyles,
  pasteLayerStyles,
  pasteLayerStylesToMultiple,
  clearLayerStyles,
} from "./clipboard";

// Quick style helpers
export {
  addDropShadow,
  addStroke,
  addOuterGlow,
  addColorOverlay,
  addBevelEmboss,
} from "./quickStyles";

// Presets
export {
  STYLE_PRESETS,
  applyStylePreset,
  getStylePresetNames,
} from "./presets";
