/**
 * Expression Validation
 *
 * Functions for validating expressions without executing them.
 */

import type { ExpressionValidationResult } from "./types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                 // expression // validation
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Validate an expression without executing it
 * Returns validation result with error details if invalid
 */
export function validateExpression(code: string): ExpressionValidationResult {
  if (!code || code.trim() === "") {
    return { valid: true };
  }

  try {
    // Create mock context variables for validation
    const mockContextVars = {
      time: 0,
      frame: 0,
      fps: 30,
      duration: 5,
      value: 0,
      velocity: 0,
      index: 0,
      numKeys: 0,
      // Common functions
      wiggle: () => 0,
      loopOut: () => 0,
      loopIn: () => 0,
      repeatAfter: () => 0,
      repeatBefore: () => 0,
      ease: () => 0,
      easeIn: () => 0,
      easeOut: () => 0,
      linear: () => 0,
      random: () => 0,
      clamp: () => 0,
      Math: Math,
      // Objects
      thisComp: {
        duration: 5,
        frameDuration: 1 / 30,
        width: 1920,
        height: 1080,
        numLayers: 0,
        layer: () => ({
          position: [0, 0],
          scale: [100, 100],
          rotation: 0,
          opacity: 100,
          transform: {},
          effect: () => () => 0,
        }),
      },
      thisLayer: {
        name: "",
        index: 0,
        inPoint: 0,
        outPoint: 5,
        position: [0, 0, 0],
        rotation: [0, 0, 0],
        scale: [100, 100, 100],
        opacity: 100,
        transform: {},
        effect: () => () => 0,
        toComp: () => [0, 0, 0],
        fromComp: () => [0, 0, 0],
      },
      thisProperty: {
        value: 0,
        velocity: 0,
        numKeys: 0,
        key: () => ({ time: 0, value: 0 }),
        nearestKey: () => ({ time: 0, value: 0 }),
        valueAtTime: () => 0,
        velocityAtTime: () => 0,
      },
      footage: () => ({ sourceData: {}, dataValue: () => 0 }),
    };

    const paramNames = Object.keys(mockContextVars);
    const wrappedCode = `
      "use strict";
      return (function() {
        ${code}
      })();
    `;

    // Try to create the function - this validates syntax
    new Function(...paramNames, wrappedCode);

    return { valid: true };
  } catch (error) {
    const err = error as Error;
    let errorMessage = err.message;

    // Try to extract line/column info from error
    let errorLine: number | undefined;
    let errorColumn: number | undefined;

    const lineMatch = errorMessage.match(/line (\d+)/i);
    const colMatch = errorMessage.match(/column (\d+)/i);

    if (lineMatch) {
      errorLine = parseInt(lineMatch[1], 10) - 4; // Adjust for wrapper lines
    }
    if (colMatch) {
      errorColumn = parseInt(colMatch[1], 10);
    }

    // Clean up error message
    errorMessage = errorMessage
      .replace(/^SyntaxError:\s*/i, "")
      .replace(/\(anonymous\)/g, "expression");

    return {
      valid: false,
      error: errorMessage,
      errorLine: errorLine && errorLine > 0 ? errorLine : undefined,
      errorColumn,
    };
  }
}

/**
 * Get list of available expression functions for autocomplete/documentation
 */
export function getExpressionFunctions(): Array<{
  name: string;
  description: string;
  syntax: string;
}> {
  return [
    {
      name: "wiggle",
      description: "Random oscillation",
      syntax: "wiggle(frequency, amplitude)",
    },
    {
      name: "loopOut",
      description: "Loop after last keyframe",
      syntax: 'loopOut("cycle" | "pingpong" | "offset" | "continue")',
    },
    {
      name: "loopIn",
      description: "Loop before first keyframe",
      syntax: 'loopIn("cycle" | "pingpong" | "offset" | "continue")',
    },
    {
      name: "repeatAfter",
      description: "Repeat keyframes after last",
      syntax: 'repeatAfter("cycle" | "pingpong" | "offset")',
    },
    {
      name: "repeatBefore",
      description: "Repeat keyframes before first",
      syntax: 'repeatBefore("cycle" | "pingpong" | "offset")',
    },
    {
      name: "ease",
      description: "Smooth interpolation",
      syntax: "ease(t, tMin, tMax, vMin, vMax)",
    },
    {
      name: "easeIn",
      description: "Ease in interpolation",
      syntax: "easeIn(t, tMin, tMax, vMin, vMax)",
    },
    {
      name: "easeOut",
      description: "Ease out interpolation",
      syntax: "easeOut(t, tMin, tMax, vMin, vMax)",
    },
    {
      name: "linear",
      description: "Linear interpolation",
      syntax: "linear(t, tMin, tMax, vMin, vMax)",
    },
    {
      name: "random",
      description: "Seeded random number",
      syntax: "random() or random(min, max)",
    },
    {
      name: "noise",
      description: "Perlin-like noise",
      syntax: "noise(value) or noise([x, y, z])",
    },
    {
      name: "clamp",
      description: "Clamp value to range",
      syntax: "clamp(value, min, max)",
    },
    {
      name: "inertia",
      description: "Inertia/overshoot",
      syntax: "inertia(amplitude, frequency, decay)",
    },
    {
      name: "bounce",
      description: "Bounce at end",
      syntax: "bounce(elasticity, gravity)",
    },
    {
      name: "elastic",
      description: "Elastic spring",
      syntax: "elastic(amplitude, frequency, decay)",
    },
    {
      name: "valueAtTime",
      description: "Property value at time",
      syntax: "valueAtTime(time)",
    },
    {
      name: "velocityAtTime",
      description: "Velocity at time",
      syntax: "velocityAtTime(time)",
    },
    {
      name: "speedAtTime",
      description: "Speed (velocity magnitude) at time",
      syntax: "speedAtTime(time)",
    },
    { name: "key", description: "Get keyframe by index", syntax: "key(index)" },
    {
      name: "nearestKey",
      description: "Get nearest keyframe",
      syntax: "nearestKey(time)",
    },
    {
      name: "footage",
      description: "Access data file",
      syntax: 'footage("filename.csv").dataValue([row, col])',
    },
  ];
}
