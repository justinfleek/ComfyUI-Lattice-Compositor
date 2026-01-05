/**
 * Blend Mode Utilities for Three.js Materials
 *
 * Extracted from BaseLayer.ts - provides blend mode configuration
 * for layer materials in the Lattice compositor.
 *
 * Supports: normal, add, multiply, screen, overlay, soft-light, hard-light,
 * color-dodge, color-burn, difference, exclusion, darken, lighten
 */

import * as THREE from "three";

/**
 * Configure a material's blend mode
 * @param material - Three.js material to configure
 * @param mode - Blend mode name
 */
export function setMaterialBlendMode(
  material: THREE.Material,
  mode: string,
): void {
  // Reset to defaults first
  material.blending = THREE.NormalBlending;
  material.blendEquation = THREE.AddEquation;
  material.blendSrc = THREE.SrcAlphaFactor;
  material.blendDst = THREE.OneMinusSrcAlphaFactor;
  material.blendEquationAlpha = THREE.AddEquation;
  material.blendSrcAlpha = THREE.OneFactor;
  material.blendDstAlpha = THREE.OneMinusSrcAlphaFactor;

  switch (mode) {
    case "normal":
      material.blending = THREE.NormalBlending;
      break;

    case "add":
      material.blending = THREE.AdditiveBlending;
      break;

    case "multiply":
      material.blending = THREE.MultiplyBlending;
      break;

    case "screen":
      // Screen: 1 - (1-a)(1-b) = a + b - ab
      // In GL terms: src * 1 + dst * (1 - src)
      material.blending = THREE.CustomBlending;
      material.blendEquation = THREE.AddEquation;
      material.blendSrc = THREE.OneFactor;
      material.blendDst = THREE.OneMinusSrcColorFactor;
      break;

    case "overlay":
      // Overlay is a combination of multiply and screen
      // Can't be done with simple blend factors - needs shader
      // Fallback to multiply for dark, screen for light
      material.blending = THREE.MultiplyBlending;
      break;

    case "soft-light":
      // Soft light is complex - needs shader
      // Approximate with normal blending at reduced opacity
      material.blending = THREE.NormalBlending;
      break;

    case "hard-light":
      // Hard light is overlay with layers swapped
      material.blending = THREE.MultiplyBlending;
      break;

    case "color-dodge":
      // Color dodge: a / (1 - b)
      // Approximation using additive with boost
      material.blending = THREE.AdditiveBlending;
      break;

    case "color-burn":
      // Color burn: 1 - (1-a) / b
      // Approximation using subtractive
      material.blending = THREE.SubtractiveBlending;
      break;

    case "difference":
      // Difference: |a - b|
      // Use subtractive blending as approximation
      material.blending = THREE.CustomBlending;
      material.blendEquation = THREE.SubtractEquation;
      material.blendSrc = THREE.OneFactor;
      material.blendDst = THREE.OneFactor;
      break;

    case "exclusion":
      // Exclusion: a + b - 2ab
      // Similar to difference but softer
      material.blending = THREE.CustomBlending;
      material.blendEquation = THREE.AddEquation;
      material.blendSrc = THREE.OneMinusDstColorFactor;
      material.blendDst = THREE.OneMinusSrcColorFactor;
      break;

    case "darken":
      // Darken: min(a, b)
      material.blending = THREE.CustomBlending;
      material.blendEquation = THREE.MinEquation;
      material.blendSrc = THREE.OneFactor;
      material.blendDst = THREE.OneFactor;
      break;

    case "lighten":
      // Lighten: max(a, b)
      material.blending = THREE.CustomBlending;
      material.blendEquation = THREE.MaxEquation;
      material.blendSrc = THREE.OneFactor;
      material.blendDst = THREE.OneFactor;
      break;

    default:
      material.blending = THREE.NormalBlending;
      break;
  }
}

/**
 * Apply blend mode to all materials in a Three.js group
 * @param group - Three.js group containing meshes
 * @param mode - Blend mode name
 */
export function applyBlendModeToGroup(group: THREE.Group, mode: string): void {
  group.traverse((child) => {
    if (child instanceof THREE.Mesh && child.material) {
      const material = child.material as THREE.Material;
      setMaterialBlendMode(material, mode);
      material.needsUpdate = true;
    }
  });
}

/**
 * Supported blend modes
 */
export const SUPPORTED_BLEND_MODES = [
  "normal",
  "add",
  "multiply",
  "screen",
  "overlay",
  "soft-light",
  "hard-light",
  "color-dodge",
  "color-burn",
  "difference",
  "exclusion",
  "darken",
  "lighten",
] as const;

export type BlendModeName = (typeof SUPPORTED_BLEND_MODES)[number];

/**
 * Check if a blend mode is supported
 */
export function isValidBlendMode(mode: string): mode is BlendModeName {
  return SUPPORTED_BLEND_MODES.includes(mode as BlendModeName);
}
