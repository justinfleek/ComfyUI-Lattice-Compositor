/**
 * Expression Control Renderer
 *
 * Expression Controls are special "effects" that don't process pixels.
 * They provide animatable values that can be:
 * 1. Keyframed like any other property
 * 2. Exposed in the Essential Graphics panel
 * 3. Referenced in expressions via effect("Control Name")("Parameter")
 *
 * These renderers simply pass through the input unchanged.
 */

import type {
  EffectStackResult,
  EvaluatedEffectParams,
} from "../effectProcessor";
import { registerEffectRenderer } from "../effectProcessor";

/**
 * Passthrough renderer for Slider Control
 * The slider value is available to expressions, but doesn't modify the image
 */
function sliderControlRenderer(
  input: EffectStackResult,
  _params: EvaluatedEffectParams,
): EffectStackResult {
  // No pixel processing - just pass through
  // The slider value is available via params.slider for expression access
  return input;
}

/**
 * Passthrough renderer for Checkbox Control
 */
function checkboxControlRenderer(
  input: EffectStackResult,
  _params: EvaluatedEffectParams,
): EffectStackResult {
  // Value: 1 when checked, 0 when unchecked
  return input;
}

/**
 * Passthrough renderer for Dropdown Menu Control
 */
function dropdownMenuControlRenderer(
  input: EffectStackResult,
  _params: EvaluatedEffectParams,
): EffectStackResult {
  // Value: 1-based index of selected option
  return input;
}

/**
 * Passthrough renderer for Color Control
 */
function colorControlRenderer(
  input: EffectStackResult,
  _params: EvaluatedEffectParams,
): EffectStackResult {
  // Value: { r, g, b, a } color object
  return input;
}

/**
 * Passthrough renderer for Point Control
 */
function pointControlRenderer(
  input: EffectStackResult,
  _params: EvaluatedEffectParams,
): EffectStackResult {
  // Value: { x, y } point object
  return input;
}

/**
 * Passthrough renderer for 3D Point Control
 */
function point3DControlRenderer(
  input: EffectStackResult,
  _params: EvaluatedEffectParams,
): EffectStackResult {
  // Value: { x, y, z } 3D point object
  return input;
}

/**
 * Passthrough renderer for Angle Control
 */
function angleControlRenderer(
  input: EffectStackResult,
  _params: EvaluatedEffectParams,
): EffectStackResult {
  // Value: angle in degrees
  return input;
}

/**
 * Passthrough renderer for Layer Control
 */
function layerControlRenderer(
  input: EffectStackResult,
  _params: EvaluatedEffectParams,
): EffectStackResult {
  // Value: layer ID reference
  return input;
}

/**
 * Register all Expression Control renderers
 */
export function registerExpressionControlRenderers(): void {
  registerEffectRenderer("slider-control", sliderControlRenderer);
  registerEffectRenderer("checkbox-control", checkboxControlRenderer);
  registerEffectRenderer("dropdown-menu-control", dropdownMenuControlRenderer);
  registerEffectRenderer("color-control", colorControlRenderer);
  registerEffectRenderer("point-control", pointControlRenderer);
  registerEffectRenderer("3d-point-control", point3DControlRenderer);
  registerEffectRenderer("angle-control", angleControlRenderer);
  registerEffectRenderer("layer-control", layerControlRenderer);
}

/**
 * Check if an effect key is an expression control
 */
export function isExpressionControl(effectKey: string): boolean {
  return [
    "slider-control",
    "checkbox-control",
    "dropdown-menu-control",
    "color-control",
    "point-control",
    "3d-point-control",
    "angle-control",
    "layer-control",
  ].includes(effectKey);
}

/**
 * Get the primary parameter name for an expression control
 * Used for expression access: effect("Slider Control")("Slider")
 */
export function getControlParameterName(effectKey: string): string {
  switch (effectKey) {
    case "slider-control":
      return "slider";
    case "checkbox-control":
      return "checkbox";
    case "dropdown-menu-control":
      return "menu";
    case "color-control":
      return "color";
    case "point-control":
      return "point";
    case "3d-point-control":
      return "point3D";
    case "angle-control":
      return "angle";
    case "layer-control":
      return "layer";
    default:
      return "value";
  }
}
