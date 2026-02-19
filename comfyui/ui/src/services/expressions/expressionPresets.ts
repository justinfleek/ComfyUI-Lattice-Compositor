/**
 * Expression Presets
 *
 * Pre-configured expression presets for common animation patterns.
 */

import { EASING_PRESETS } from "./easing";
import type { Expression } from "./types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                    // expression // presets
// ═══════════════════════════════════════════════════════════════════════════

export const EXPRESSION_PRESETS: Record<string, Expression> = {
  // Motion presets
  inertiaLight: {
    type: "preset",
    name: "inertia",
    params: { amplitude: 0.05, frequency: 3, decay: 3 },
    enabled: true,
  },
  inertiaHeavy: {
    type: "preset",
    name: "inertia",
    params: { amplitude: 0.15, frequency: 1.5, decay: 1.5 },
    enabled: true,
  },
  bounceGentle: {
    type: "preset",
    name: "bounce",
    params: { elasticity: 0.6, gravity: 3000 },
    enabled: true,
  },
  bounceFirm: {
    type: "preset",
    name: "bounce",
    params: { elasticity: 0.8, gravity: 5000 },
    enabled: true,
  },
  elasticSnappy: {
    type: "preset",
    name: "elastic",
    params: { amplitude: 1, period: 0.2 },
    enabled: true,
  },
  elasticLoose: {
    type: "preset",
    name: "elastic",
    params: { amplitude: 1.5, period: 0.5 },
    enabled: true,
  },

  // Jitter presets
  jitterSubtle: {
    type: "preset",
    name: "jitter",
    params: { frequency: 2, amplitude: 10, octaves: 1 },
    enabled: true,
  },
  jitterModerate: {
    type: "preset",
    name: "jitter",
    params: { frequency: 4, amplitude: 30, octaves: 2 },
    enabled: true,
  },
  jitterIntense: {
    type: "preset",
    name: "jitter",
    params: { frequency: 8, amplitude: 50, octaves: 3 },
    enabled: true,
  },

  // Repeat presets
  repeatCycle: {
    type: "preset",
    name: "repeatAfter",
    params: { type: "cycle", numKeyframes: 0 },
    enabled: true,
  },
  repeatPingpong: {
    type: "preset",
    name: "repeatAfter",
    params: { type: "pingpong", numKeyframes: 0 },
    enabled: true,
  },
  repeatOffset: {
    type: "preset",
    name: "repeatAfter",
    params: { type: "offset", numKeyframes: 0 },
    enabled: true,
  },
};

/**
 * Get an expression preset by name
 */
export function getExpressionPreset(name: string): Expression | null {
  return EXPRESSION_PRESETS[name] || null;
}

/**
 * List all expression presets
 */
export function listExpressionPresets(): string[] {
  return Object.keys(EXPRESSION_PRESETS);
}

/**
 * List all easing presets
 */
export function listEasingPresets(): string[] {
  return Object.keys(EASING_PRESETS);
}
