/**
 * Text Animator Actions
 *
 * Store actions for managing text animators, selectors, and computing
 * per-character transforms. Provides the public API for Tutorial 06
 * text animation features.
 *
 * MODULE STRUCTURE:
 * - types.ts: Store interface and configuration types
 * - helpers.ts: Color conversion and data access helpers
 * - crud.ts: Add, remove, update, get text animators
 * - selectors.ts: Range, expression, and wiggly selector operations
 * - computed.ts: Character transform calculations
 * - utility.ts: Property setters and queries
 * - textOnPath.ts: Text on path operations
 */

// Types
export type {
  TextAnimatorStore,
  CharacterTransform,
  AddTextAnimatorConfig,
  RangeSelectorConfig,
  ExpressionSelectorConfig,
  WigglySelectorConfig,
  TextPathConfig,
} from "./types";

// CRUD operations
export {
  addTextAnimator,
  removeTextAnimator,
  updateTextAnimator,
  getTextAnimator,
  getTextAnimators,
} from "./crud";

// Selector operations
export {
  configureRangeSelector,
  configureExpressionSelector,
  removeExpressionSelector,
  configureWigglySelector,
  removeWigglySelector,
} from "./selectors";

// Computed values
export {
  getCharacterTransforms,
  getSelectionValues,
  getRangeSelectionValue,
} from "./computed";

// Utility functions
export {
  setAnimatorPropertyValue,
  hasTextAnimators,
  getTextContent,
  setTextContent,
} from "./utility";

// Text on path operations
export {
  setTextPath,
  getTextPathConfig,
  updateTextPath,
  getCharacterPathPlacements,
  getPathLength,
  hasTextPath,
  clearTextPath,
} from "./textOnPath";
