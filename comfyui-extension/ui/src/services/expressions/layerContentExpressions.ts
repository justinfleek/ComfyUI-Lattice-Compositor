/**
 * Layer Content Expressions
 *
 * Functions for accessing layer content dimensions and properties.
 * Includes sourceRectAtTime, textSource, and effectValue.
 */

import { isFiniteNumber } from "@/utils/typeGuards";
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
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        const pathShapePath = (typeof pathShape.path === "object" && pathShape.path !== null && "value" in pathShape.path && typeof pathShape.path.value === "object" && pathShape.path.value !== null && "vertices" in pathShape.path.value && Array.isArray(pathShape.path.value.vertices));
        if (pathShapePath) {
          paths.push(pathShape.path.value);
        }
      } else if (item.type === "group") {
        // Recursively extract from groups
        extractPaths(item.contents);
      }
    }
  }

  // Type proof: contents ∈ array | undefined → array
  const contents = data.contents;
  extractPaths(Array.isArray(contents) ? contents : []);

  if (paths.length === 0) {
    return { top: 0, left: 0, width: 100, height: 100 };
  }

  paths.forEach((path: BezierPath) => {
    // Type proof: vertices ∈ array | undefined → array
    const vertices = path.vertices;
    const verticesArray = Array.isArray(vertices) ? vertices : [];
    verticesArray.forEach((vertex: BezierVertex) => {
      // Type proof: point.x/y ∈ ℝ ∪ {undefined} → ℝ
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      const pointX = (typeof vertex.point === "object" && vertex.point !== null && "x" in vertex.point && typeof vertex.point.x === "number")
        ? vertex.point.x
        : 0;
      const x = isFiniteNumber(pointX) ? pointX : 0;
      const pointY = (typeof vertex.point === "object" && vertex.point !== null && "y" in vertex.point && typeof vertex.point.y === "number")
        ? vertex.point.y
        : 0;
      const y = isFiniteNumber(pointY) ? pointY : 0;
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
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
          const strokeWidth = (typeof item.width === "object" && item.width !== null && "value" in item.width && typeof item.width.value === "number")
            ? item.width.value
            : 0;
          maxStrokeWidth = Math.max(maxStrokeWidth, strokeWidth);
        } else if (item.type === "group") {
          findStrokeWidth(item.contents);
        }
      }
    }
    // Type proof: contents ∈ array | undefined → array
    const contents = data.contents;
    findStrokeWidth(Array.isArray(contents) ? contents : []);
    
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
  // Type proof: width/height ∈ ℝ ∪ {undefined} → ℝ
  const widthValue = data.width;
  const width = isFiniteNumber(widthValue) && widthValue > 0 ? widthValue : 100;
  const heightValue = data.height;
  const height = isFiniteNumber(heightValue) && heightValue > 0 ? heightValue : 100;

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
  // Type proof: text properties with explicit type proofs
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  const textValue = (typeof layerData === "object" && layerData !== null && "text" in layerData && typeof layerData.text === "string")
    ? layerData.text
    : "";
  const text = typeof textValue === "string" ? textValue : "";
  const fontSizeValue = (typeof layerData === "object" && layerData !== null && "fontSize" in layerData && typeof layerData.fontSize === "number")
    ? layerData.fontSize
    : 72;
  const fontSize = isFiniteNumber(fontSizeValue) && fontSizeValue > 0 ? fontSizeValue : 72;
  const fontFamilyValue = (typeof layerData === "object" && layerData !== null && "fontFamily" in layerData && typeof layerData.fontFamily === "string")
    ? layerData.fontFamily
    : "Arial";
  const fontFamily = typeof fontFamilyValue === "string" && fontFamilyValue.length > 0 ? fontFamilyValue : "Arial";
  const fontStyleValue = (typeof layerData === "object" && layerData !== null && "fontStyle" in layerData && typeof layerData.fontStyle === "string")
    ? layerData.fontStyle
    : "normal";
  const fontStyle = typeof fontStyleValue === "string" ? fontStyleValue : "normal";
  const fillValue = (typeof layerData === "object" && layerData !== null && "fill" in layerData && typeof layerData.fill === "string")
    ? layerData.fill
    : "#FFFFFF";
  const fillColor = typeof fillValue === "string" && fillValue.length > 0 ? fillValue : "#FFFFFF";
  const strokeValue = (typeof layerData === "object" && layerData !== null && "stroke" in layerData && typeof layerData.stroke === "string")
    ? layerData.stroke
    : "#000000";
  const strokeColor = typeof strokeValue === "string" && strokeValue.length > 0 ? strokeValue : "#000000";
  const strokeWidthValue = (typeof layerData === "object" && layerData !== null && "strokeWidth" in layerData && typeof layerData.strokeWidth === "number")
    ? layerData.strokeWidth
    : 0;
  const strokeWidth = isFiniteNumber(strokeWidthValue) && strokeWidthValue >= 0 ? strokeWidthValue : 0;
  const letterSpacingValue = (typeof layerData === "object" && layerData !== null && "letterSpacing" in layerData && typeof layerData.letterSpacing === "number")
    ? layerData.letterSpacing
    : 0;
  const tracking = isFiniteNumber(letterSpacingValue) ? letterSpacingValue : 0;
  const lineHeightValue = (typeof layerData === "object" && layerData !== null && "lineHeight" in layerData && typeof layerData.lineHeight === "number")
    ? layerData.lineHeight
    : 1.2;
  const leading = isFiniteNumber(lineHeightValue) && lineHeightValue > 0 ? lineHeightValue : 1.2;

  return {
    text: text,
    fontSize: fontSize,
    fontFamily: fontFamily,
    fontStyle: fontStyle,
    fillColor: fillColor,
    strokeColor: strokeColor,
    strokeWidth: strokeWidth,
    tracking: tracking,
    leading: leading,
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
 * System F/Omega proof: Explicit validation of effect and parameter existence
 * Type proof: effects ∈ Array<EffectInstance> | undefined, effectName ∈ string, parameterName ∈ string → number | string | boolean (non-nullable)
 * Mathematical proof: Effect and parameter must exist to retrieve value
 * Pattern proof: Missing effect/parameter is an explicit failure condition, not a lazy null return
 *
 * @param effects - Array of effects on the layer
 * @param effectName - Name of the effect to find
 * @param parameterName - Name of the parameter to get
 * @param frame - Current frame for animated parameters
 * @returns The parameter value (throws error if not found - wrap in try/catch for expected "not found" case)
 */
export function effectValue(
  effects: EffectInstance[] | undefined,
  effectName: string,
  parameterName: string,
  _frame: number = 0,
): number | string | boolean {
  // System F/Omega proof: Explicit validation of effects array existence
  // Type proof: effects ∈ Array<EffectInstance> | undefined → Array<EffectInstance>
  // Mathematical proof: Effects array must exist and be non-empty to search for effect
  if (!effects || !Array.isArray(effects) || effects.length === 0) {
    throw new Error(
      `[LayerContentExpressions] Cannot get effect value: Effects array is empty or undefined. ` +
      `Effect name: "${effectName}", parameter name: "${parameterName}", frame: ${_frame}. ` +
      `Layer must have effects to retrieve effect parameter values. ` +
      `Wrap in try/catch if "no effects" is an expected state.`
    );
  }

  // System F/Omega proof: Explicit validation of effect existence
  // Type proof: effects.find() ∈ EffectInstance | undefined
  // Mathematical proof: Effect with matching name must exist in effects array
  const effect = effects.find((e: EffectInstance) => e.name === effectName);
  if (!effect) {
    const availableEffects = effects.map((e) => e.name).join(", ") || "none";
    throw new Error(
      `[LayerContentExpressions] Cannot get effect value: Effect not found. ` +
      `Effect name: "${effectName}", parameter name: "${parameterName}", frame: ${_frame}. ` +
      `Available effects: [${availableEffects}]. ` +
      `Effect name must match exactly (case-sensitive). ` +
      `Wrap in try/catch if "effect not found" is an expected state.`
    );
  }

  const paramKey = parameterName.toLowerCase().replace(/\s+/g, "_");
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  const parameters = (typeof effect.parameters === "object" && effect.parameters !== null)
    ? effect.parameters
    : {};
  const param = (paramKey in parameters && typeof parameters[paramKey] === "object")
    ? parameters[paramKey]
    : undefined;

  // System F/Omega proof: Explicit validation of parameter existence
  // Type proof: param ∈ AnimatableProperty | undefined
  // Mathematical proof: Parameter with matching key must exist in effect parameters
  if (!param) {
    const availableParams = Object.keys(parameters).join(", ") || "none";
    throw new Error(
      `[LayerContentExpressions] Cannot get effect value: Parameter not found. ` +
      `Effect name: "${effectName}", parameter name: "${parameterName}" (key: "${paramKey}"), frame: ${_frame}. ` +
      `Available parameters: [${availableParams}]. ` +
      `Parameter name is case-insensitive and spaces are converted to underscores. ` +
      `Wrap in try/catch if "parameter not found" is an expected state.`
    );
  }

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
