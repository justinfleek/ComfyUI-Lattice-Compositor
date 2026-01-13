/**
 * Layer Content Expressions
 *
 * Functions for accessing layer content dimensions and properties.
 * Includes sourceRectAtTime, textSource, and effectValue.
 */

import { measureTextLayerRect } from "../textMeasurement";
import type { SourceRect, TextSourceInfo } from "./types";
import type {
  TextData,
  ShapeLayerData,
  SolidLayerData,
  ImageLayerData,
  VideoData,
  EffectInstance,
} from "@/types/project";
import type { BezierPath, BezierVertex } from "@/types/shapes";

// ============================================================
// SOURCE RECT AT TIME
// ============================================================

/**
 * Get the bounding rectangle of a layer's content at a specific time
 *
 * This is crucial for responsive templates where background elements
 * need to resize based on text content.
 *
 * Industry-standard: sourceRectAtTime(t, includeExtents)
 *
 * @param layerData - The layer's type-specific data (e.g., TextLayerData)
 * @param layerType - Type of the layer
 * @param time - Time in seconds (default: 0)
 * @param includeExtents - Include stroke width and effects (default: false)
 * @returns SourceRect with top, left, width, height
 */
export function sourceRectAtTime(
  layerData:
    | TextData
    | ShapeLayerData
    | SolidLayerData
    | ImageLayerData
    | VideoData
    | null
    | undefined,
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
      return getTextSourceRect(layerData as TextData, includeExtents);

    case "shape":
      return getShapeSourceRect(layerData as ShapeLayerData, includeExtents);

    case "solid":
      return getSolidSourceRect(layerData as SolidLayerData);

    case "image":
    case "video":
      return getMediaSourceRect(layerData as ImageLayerData | VideoData);

    default:
      return defaultRect;
  }
}

/**
 * Calculate source rect for text layers
 * Uses accurate Canvas API text measurement
 */
function getTextSourceRect(
  data: TextData,
  includeExtents: boolean,
): SourceRect {
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
function getShapeSourceRect(
  data: ShapeLayerData,
  includeExtents: boolean,
): SourceRect {
  let minX = Infinity,
    minY = Infinity;
  let maxX = -Infinity,
    maxY = -Infinity;

  // Extract paths from shape layer contents
  const paths: BezierPath[] = [];
  function extractPaths(contents: ShapeLayerData["contents"]): void {
    for (const item of contents) {
      if (item.type === "path") {
        // Path shape has a path property with vertices
        const pathShape = item as { path: { value: BezierPath } };
        if (pathShape.path?.value?.vertices) {
          paths.push(pathShape.path.value);
        }
      } else if (item.type === "group") {
        // Recursively extract from groups
        extractPaths(item.contents);
      }
    }
  }

  extractPaths(data.contents ?? []);

  if (paths.length === 0) {
    return { top: 0, left: 0, width: 100, height: 100 };
  }

  paths.forEach((path: BezierPath) => {
    const vertices = path.vertices ?? [];
    vertices.forEach((vertex: BezierVertex) => {
      const x = vertex.point?.x ?? 0;
      const y = vertex.point?.y ?? 0;
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

  if (includeExtents) {
    // Find stroke width from stroke shapes in contents
    let maxStrokeWidth = 0;
    function findStrokeWidth(contents: ShapeLayerData["contents"]): void {
      for (const item of contents) {
        if (item.type === "stroke") {
          const strokeWidth = typeof item.width?.value === "number" ? item.width.value : 0;
          maxStrokeWidth = Math.max(maxStrokeWidth, strokeWidth);
        } else if (item.type === "group") {
          findStrokeWidth(item.contents);
        }
      }
    }
    findStrokeWidth(data.contents ?? []);
    
    if (maxStrokeWidth > 0) {
      const strokeExtent = maxStrokeWidth / 2;
      minX -= strokeExtent;
      minY -= strokeExtent;
      width += strokeExtent * 2;
      height += strokeExtent * 2;
    }
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
function getSolidSourceRect(data: SolidLayerData): SourceRect {
  const width = data.width ?? 100;
  const height = data.height ?? 100;

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
function getMediaSourceRect(data: ImageLayerData | VideoData): SourceRect {
  // For image/video layers, we need to get dimensions from the asset
  // Since we don't have direct access to asset dimensions here, use defaults
  // In practice, this would be resolved by the expression evaluator with asset context
  const width = 1920; // Default fallback
  const height = 1080; // Default fallback

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
 * Mimics industry-standard text.sourceText
 */
export function textSource(layerData: TextData): TextSourceInfo {
  return {
    text: layerData?.text ?? "",
    fontSize: layerData?.fontSize ?? 72,
    fontFamily: layerData?.fontFamily ?? "Arial",
    fontStyle: layerData?.fontStyle ?? "normal",
    fillColor: layerData?.fill ?? "#FFFFFF",
    strokeColor: layerData?.stroke ?? "#000000",
    strokeWidth: layerData?.strokeWidth ?? 0,
    tracking: layerData?.letterSpacing ?? 0,
    leading: layerData?.lineHeight ?? 1.2,
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
  effects: EffectInstance[] | undefined,
  effectName: string,
  parameterName: string,
  _frame: number = 0,
): number | string | boolean | null {
  if (!effects || effects.length === 0) return null;

  const effect = effects.find((e: EffectInstance) => e.name === effectName);
  if (!effect) return null;

  const paramKey = parameterName.toLowerCase().replace(/\s+/g, "_");
  const param = effect.parameters?.[paramKey];

  if (!param) return null;

  return param.value as number | string | boolean;
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
