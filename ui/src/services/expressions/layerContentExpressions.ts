/**
 * Layer Content Expressions
 *
 * Functions for accessing layer content dimensions and properties.
 * Includes sourceRectAtTime, textSource, and effectValue.
 */

import { measureTextLayerRect } from "../textMeasurement";
import type { SourceRect, TextSourceInfo } from "./types";

// ============================================================
// SOURCE RECT AT TIME
// ============================================================

/**
 * Get the bounding rectangle of a layer's content at a specific time
 *
 * This is crucial for responsive templates where background elements
 * need to resize based on text content.
 *
 * In After Effects: sourceRectAtTime(t, includeExtents)
 *
 * @param layerData - The layer's type-specific data (e.g., TextLayerData)
 * @param layerType - Type of the layer
 * @param time - Time in seconds (default: 0)
 * @param includeExtents - Include stroke width and effects (default: false)
 * @returns SourceRect with top, left, width, height
 */
export function sourceRectAtTime(
  layerData: any,
  layerType: string,
  _time: number = 0,
  includeExtents: boolean = false,
): SourceRect {
  const defaultRect: SourceRect = {
    top: 0,
    left: 0,
    width: 100,
    height: 100,
  };

  if (!layerData) return defaultRect;

  switch (layerType) {
    case "text":
      return getTextSourceRect(layerData, includeExtents);

    case "shape":
      return getShapeSourceRect(layerData, includeExtents);

    case "solid":
      return getSolidSourceRect(layerData);

    case "image":
    case "video":
      return getMediaSourceRect(layerData);

    default:
      return defaultRect;
  }
}

/**
 * Calculate source rect for text layers
 * Uses accurate Canvas API text measurement
 */
function getTextSourceRect(data: any, includeExtents: boolean): SourceRect {
  const rect = measureTextLayerRect(data, includeExtents);

  return {
    top: rect.top,
    left: rect.left,
    width: rect.width,
    height: rect.height,
  };
}

/**
 * Calculate source rect for shape layers
 */
function getShapeSourceRect(data: any, includeExtents: boolean): SourceRect {
  let minX = Infinity,
    minY = Infinity;
  let maxX = -Infinity,
    maxY = -Infinity;

  const paths = data.paths || [];

  if (paths.length === 0) {
    return { top: 0, left: 0, width: 100, height: 100 };
  }

  paths.forEach((path: any) => {
    const points = path.points || [];
    points.forEach((point: any) => {
      const x = point.x ?? point[0] ?? 0;
      const y = point.y ?? point[1] ?? 0;
      minX = Math.min(minX, x);
      minY = Math.min(minY, y);
      maxX = Math.max(maxX, x);
      maxY = Math.max(maxY, y);
    });
  });

  if (!Number.isFinite(minX)) {
    return { top: 0, left: 0, width: 100, height: 100 };
  }

  let width = maxX - minX;
  let height = maxY - minY;

  if (includeExtents && data.stroke?.width) {
    const strokeExtent = data.stroke.width / 2;
    minX -= strokeExtent;
    minY -= strokeExtent;
    width += strokeExtent * 2;
    height += strokeExtent * 2;
  }

  return {
    top: minY,
    left: minX,
    width,
    height,
  };
}

/**
 * Calculate source rect for solid layers
 */
function getSolidSourceRect(data: any): SourceRect {
  const width = data.width || 100;
  const height = data.height || 100;

  return {
    top: -height / 2,
    left: -width / 2,
    width,
    height,
  };
}

/**
 * Calculate source rect for image/video layers
 */
function getMediaSourceRect(data: any): SourceRect {
  const width = data.width || data.naturalWidth || 1920;
  const height = data.height || data.naturalHeight || 1080;

  return {
    top: -height / 2,
    left: -width / 2,
    width,
    height,
  };
}

// ============================================================
// TEXT SOURCE
// ============================================================

/**
 * Get text layer content as an expression-accessible object
 * Mimics After Effects' text.sourceText
 */
export function textSource(layerData: any): TextSourceInfo {
  return {
    text: layerData?.text || "",
    fontSize: layerData?.fontSize || 72,
    fontFamily: layerData?.fontFamily || "Arial",
    fontStyle: layerData?.fontStyle || "normal",
    fillColor: layerData?.fill || { r: 1, g: 1, b: 1, a: 1 },
    strokeColor: layerData?.stroke || { r: 0, g: 0, b: 0, a: 1 },
    strokeWidth: layerData?.strokeWidth || 0,
    tracking: layerData?.letterSpacing || 0,
    leading: layerData?.lineHeight || 1.2,
  };
}

// ============================================================
// EFFECT VALUE
// ============================================================

/**
 * Get the value of an expression control effect
 *
 * Usage in expressions:
 *   effect("Slider Control")("Slider")
 *   effect("Checkbox Control")("Checkbox") * 100  // for opacity
 *   effect("Color Control")("Color")
 *
 * @param effects - Array of effects on the layer
 * @param effectName - Name of the effect to find
 * @param parameterName - Name of the parameter to get
 * @param frame - Current frame for animated parameters
 * @returns The parameter value, or null if not found
 */
export function effectValue(
  effects: any[] | undefined,
  effectName: string,
  parameterName: string,
  _frame: number = 0,
): any {
  if (!effects || effects.length === 0) return null;

  const effect = effects.find((e: any) => e.name === effectName);
  if (!effect) return null;

  const paramKey = parameterName.toLowerCase().replace(/\s+/g, "_");
  const param = effect.parameters?.[paramKey];

  if (!param) return null;

  return param.value;
}

// ============================================================
// NAMESPACE EXPORTS
// ============================================================

/**
 * Layer dimension expressions namespace
 */
export const layer = {
  sourceRectAtTime,
  textSource,
};

/**
 * Effect access namespace for expressions
 */
export const effect = {
  value: effectValue,
};
