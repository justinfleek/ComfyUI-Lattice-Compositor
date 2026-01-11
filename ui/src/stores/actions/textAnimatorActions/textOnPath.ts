/**
 * Text Animator Actions - Text On Path
 *
 * Operations for positioning text along Bezier paths.
 */

import {
  type CharacterPlacement,
  type TextOnPathConfig,
  TextOnPathService,
} from "@/services/textOnPath";
import {
  getTextLayer,
  getTextData,
  updateModified,
  type TextDataWithPath,
} from "./helpers";
import type { TextAnimatorStore, TextPathConfig } from "./types";

// ============================================================================
// PATH SERVICE MANAGEMENT
// ============================================================================

// Singleton path service instances per layer
const pathServices = new Map<string, TextOnPathService>();

/**
 * Get or create a TextOnPath service instance for a layer
 */
function getPathService(layerId: string): TextOnPathService {
  let service = pathServices.get(layerId);
  if (!service) {
    service = new TextOnPathService();
    pathServices.set(layerId, service);
  }
  return service;
}

// ============================================================================
// PATH CONFIGURATION
// ============================================================================

/**
 * Configure text on path for a text layer
 */
export function setTextPath(
  store: TextAnimatorStore,
  layerId: string,
  config: TextPathConfig,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer) as TextDataWithPath | undefined;
  if (!textData) return false;

  store.pushHistory();

  // Store path config on layer data
  textData.pathConfig = {
    pathPoints: config.pathPoints,
    closed: config.closed ?? false,
    reversed: config.reversed ?? false,
    perpendicularToPath: config.perpendicularToPath ?? true,
    forceAlignment: config.forceAlignment ?? false,
    firstMargin: config.firstMargin ?? 0,
    lastMargin: config.lastMargin ?? 0,
    offset: config.offset ?? 0,
    align: config.align ?? "left",
  };

  // Set path on service
  const service = getPathService(layerId);
  service.setPath(config.pathPoints, config.closed ?? false);

  updateModified(store);
  return true;
}

/**
 * Get text path config from a text layer
 */
export function getTextPathConfig(
  store: TextAnimatorStore,
  layerId: string,
): TextPathConfig | undefined {
  const layer = getTextLayer(store, layerId);
  if (!layer) return undefined;

  const textData = getTextData(layer) as TextDataWithPath | undefined;
  if (!textData) return undefined;

  return textData.pathConfig;
}

/**
 * Update specific path properties
 */
export function updateTextPath(
  store: TextAnimatorStore,
  layerId: string,
  updates: Partial<TextPathConfig>,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer) as TextDataWithPath | undefined;
  if (!textData) return false;

  const currentConfig = textData.pathConfig;
  if (!currentConfig) return false;

  store.pushHistory();

  // Apply updates
  Object.assign(currentConfig, updates);

  // Rebuild path if points changed
  if (updates.pathPoints || updates.closed !== undefined) {
    const service = getPathService(layerId);
    service.setPath(currentConfig.pathPoints, currentConfig.closed ?? false);
  }

  updateModified(store);
  return true;
}

// ============================================================================
// CHARACTER PLACEMENT
// ============================================================================

/**
 * Get character placements along the path
 *
 * Returns detailed placement info including:
 * - position (x, y, z)
 * - rotation (for perpendicular to path)
 * - distance along path
 * - visibility
 */
export function getCharacterPathPlacements(
  store: TextAnimatorStore,
  layerId: string,
  _frame: number,
): CharacterPlacement[] {
  const layer = getTextLayer(store, layerId);
  if (!layer) return [];

  const textData = getTextData(layer) as TextDataWithPath | undefined;
  if (!textData) return [];

  const pathConfig = textData.pathConfig;
  if (
    !pathConfig ||
    !pathConfig.pathPoints ||
    pathConfig.pathPoints.length < 2
  ) {
    return [];
  }

  const text = textData.text || "";
  if (text.length === 0) return [];

  const service = getPathService(layerId);

  // Ensure path is set
  if (!service.hasPath()) {
    service.setPath(pathConfig.pathPoints, pathConfig.closed ?? false);
  }

  // Estimate character widths (assume monospace for simplicity - could be enhanced)
  const fontSize = textData.fontSize || 72;
  const charWidth = fontSize * 0.6; // Approximate character width
  const characterWidths = Array(text.length).fill(charWidth);

  // Build config
  const config: TextOnPathConfig = {
    pathLayerId: layerId,
    reversed: pathConfig.reversed ?? false,
    perpendicularToPath: pathConfig.perpendicularToPath ?? true,
    forceAlignment: pathConfig.forceAlignment ?? false,
    firstMargin: pathConfig.firstMargin ?? 0,
    lastMargin: pathConfig.lastMargin ?? 0,
    offset: pathConfig.offset ?? 0,
    align: pathConfig.align ?? "left",
  };

  const tracking = textData.tracking || 0;
  return service.calculatePlacements(
    characterWidths,
    config,
    tracking,
    fontSize,
  );
}

// ============================================================================
// PATH QUERIES
// ============================================================================

/**
 * Get total path length in pixels
 */
export function getPathLength(
  store: TextAnimatorStore,
  layerId: string,
): number {
  const layer = getTextLayer(store, layerId);
  if (!layer) return 0;

  const textData = getTextData(layer) as TextDataWithPath | undefined;
  if (!textData) return 0;

  const pathConfig = textData.pathConfig;
  if (
    !pathConfig ||
    !pathConfig.pathPoints ||
    pathConfig.pathPoints.length < 2
  ) {
    return 0;
  }

  const service = getPathService(layerId);
  if (!service.hasPath()) {
    service.setPath(pathConfig.pathPoints, pathConfig.closed ?? false);
  }

  return service.getTotalLength();
}

/**
 * Check if text layer has path configured
 */
export function hasTextPath(
  store: TextAnimatorStore,
  layerId: string,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer) as TextDataWithPath | undefined;
  if (!textData) return false;

  const pathConfig = textData.pathConfig;
  return !!(pathConfig?.pathPoints && pathConfig.pathPoints.length >= 2);
}

// ============================================================================
// CLEANUP
// ============================================================================

/**
 * Clear text path (return to normal text layout)
 */
export function clearTextPath(
  store: TextAnimatorStore,
  layerId: string,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer) as TextDataWithPath | undefined;
  if (!textData) return false;

  store.pushHistory();

  delete textData.pathConfig;

  // Clean up service
  const service = pathServices.get(layerId);
  if (service) {
    service.dispose();
    pathServices.delete(layerId);
  }

  updateModified(store);
  return true;
}
