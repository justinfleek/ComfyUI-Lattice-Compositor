/**
 * Preset System Types
 *
 * Defines types for saving and loading presets for particles, effects,
 * animations, and other configurable elements.
 */

import type { CameraShakeConfig } from "../services/cameraEnhancements";
import type { TrajectoryConfig } from "../services/cameraTrajectory";
import type { SplinePathEffect } from "./project";

// ============================================================================
// PRESET CATEGORIES
// ============================================================================

export type PresetCategory =
  | "particle"
  | "effect"
  | "animation"
  | "camera-shake"
  | "camera-trajectory"
  | "path-effect"
  | "text-style"
  | "color-palette";

// ============================================================================
// BASE PRESET
// ============================================================================

export interface PresetMetadata {
  id: string;
  name: string;
  category: PresetCategory;
  description?: string;
  tags?: string[];
  author?: string;
  createdAt: number;
  updatedAt: number;
  thumbnail?: string; // Base64 data URL
  isBuiltIn?: boolean;
  version?: number;
}

// ============================================================================
// SPECIFIC PRESET TYPES
// ============================================================================

/** Combined particle preset config (system + emitter settings) */
export interface ParticlePresetConfig {
  // System-level settings
  maxParticles?: number;
  gravity?: number;
  turbulenceStrength?: number;
  // Emitter-level settings
  emissionRate?: number;
  lifespan?: number;
  startSize?: number;
  endSize?: number;
  startColor?: string;
  endColor?: string;
  velocitySpread?: number;
}

export interface ParticlePreset extends PresetMetadata {
  category: "particle";
  config: ParticlePresetConfig;
}

export interface EffectPreset extends PresetMetadata {
  category: "effect";
  effects: Array<{
    type: string;
    params: Record<string, unknown>;
  }>;
}

export interface PathEffectPreset extends PresetMetadata {
  category: "path-effect";
  effects: SplinePathEffect[];
}

export interface CameraShakePreset extends PresetMetadata {
  category: "camera-shake";
  config: Partial<CameraShakeConfig>;
}

export interface CameraTrajectoryPreset extends PresetMetadata {
  category: "camera-trajectory";
  config: Partial<TrajectoryConfig>;
}

export interface TextStylePreset extends PresetMetadata {
  category: "text-style";
  style: {
    fontFamily?: string;
    fontSize?: number;
    fontWeight?: number;
    fill?: string;
    stroke?: string;
    strokeWidth?: number;
    letterSpacing?: number;
    lineHeight?: number;
    textAlign?: "left" | "center" | "right";
  };
}

export interface ColorPalettePreset extends PresetMetadata {
  category: "color-palette";
  colors: string[];
}

export interface AnimationPreset extends PresetMetadata {
  category: "animation";
  keyframes: Array<{
    property: string;
    keyframes: Array<{
      frame: number;
      value: unknown;
      easing?: string;
    }>;
  }>;
  duration: number;
}

// ============================================================================
// UNION TYPE
// ============================================================================

export type Preset =
  | ParticlePreset
  | EffectPreset
  | PathEffectPreset
  | CameraShakePreset
  | CameraTrajectoryPreset
  | TextStylePreset
  | ColorPalettePreset
  | AnimationPreset;

// ============================================================================
// PRESET COLLECTION
// ============================================================================

export interface PresetCollection {
  version: number;
  presets: Preset[];
  exportedAt: number;
}

// ============================================================================
// BUILT-IN PRESETS
// ============================================================================

export const BUILT_IN_PARTICLE_PRESETS: ParticlePreset[] = [
  {
    id: "builtin-particle-fire",
    name: "Fire",
    category: "particle",
    description: "Flickering flame effect",
    tags: ["fire", "flame", "hot"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 500,
      emissionRate: 50,
      lifespan: 1.5,
      startSize: 20,
      endSize: 5,
      startColor: "#ff6600",
      endColor: "#ffff00",
      gravity: -50,
      turbulenceStrength: 30,
      velocitySpread: 30,
    },
  },
  {
    id: "builtin-particle-snow",
    name: "Snow",
    category: "particle",
    description: "Gentle falling snowflakes",
    tags: ["snow", "winter", "cold"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 300,
      emissionRate: 20,
      lifespan: 5,
      startSize: 8,
      endSize: 6,
      startColor: "#ffffff",
      endColor: "#ccccff",
      gravity: 20,
      turbulenceStrength: 10,
      velocitySpread: 20,
    },
  },
  {
    id: "builtin-particle-sparks",
    name: "Sparks",
    category: "particle",
    description: "Electric spark burst",
    tags: ["sparks", "electric", "energy"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 200,
      emissionRate: 100,
      lifespan: 0.5,
      startSize: 4,
      endSize: 1,
      startColor: "#ffff00",
      endColor: "#ff8800",
      gravity: 100,
      velocitySpread: 180,
    },
  },
  {
    id: "builtin-particle-smoke",
    name: "Smoke",
    category: "particle",
    description: "Rising smoke plume",
    tags: ["smoke", "fog", "mist"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 100,
      emissionRate: 10,
      lifespan: 4,
      startSize: 30,
      endSize: 80,
      startColor: "#444444",
      endColor: "#888888",
      gravity: -30,
      turbulenceStrength: 20,
    },
  },
  {
    id: "builtin-particle-confetti",
    name: "Confetti",
    category: "particle",
    description: "Colorful celebration confetti",
    tags: ["confetti", "celebration", "party"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 500,
      emissionRate: 100,
      lifespan: 3,
      startSize: 10,
      endSize: 8,
      gravity: 50,
      velocitySpread: 60,
      turbulenceStrength: 15,
    },
  },
  {
    id: "builtin-particle-rain",
    name: "Rain",
    category: "particle",
    description: "Falling rain drops",
    tags: ["rain", "weather", "water"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 1000,
      emissionRate: 200,
      lifespan: 1.5,
      startSize: 3,
      endSize: 2,
      startColor: "#88bbff",
      endColor: "#6699cc",
      gravity: 400,
      velocitySpread: 5,
    },
  },
  {
    id: "builtin-particle-dust",
    name: "Dust",
    category: "particle",
    description: "Floating dust motes",
    tags: ["dust", "ambient", "atmosphere"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 200,
      emissionRate: 5,
      lifespan: 8,
      startSize: 2,
      endSize: 1,
      startColor: "#ccccbb",
      endColor: "#888877",
      gravity: -2,
      turbulenceStrength: 5,
      velocitySpread: 360,
    },
  },
  {
    id: "builtin-particle-magic",
    name: "Magic Sparkle",
    category: "particle",
    description: "Magical glowing particles",
    tags: ["magic", "sparkle", "glow", "fantasy"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 300,
      emissionRate: 30,
      lifespan: 2,
      startSize: 8,
      endSize: 2,
      startColor: "#ff88ff",
      endColor: "#8844ff",
      gravity: -20,
      turbulenceStrength: 25,
      velocitySpread: 180,
    },
  },
  {
    id: "builtin-particle-bubbles",
    name: "Bubbles",
    category: "particle",
    description: "Rising soap bubbles",
    tags: ["bubbles", "water", "soap"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 100,
      emissionRate: 8,
      lifespan: 4,
      startSize: 15,
      endSize: 25,
      startColor: "#aaddff",
      endColor: "#ffffff",
      gravity: -30,
      turbulenceStrength: 15,
      velocitySpread: 30,
    },
  },
  {
    id: "builtin-particle-leaves",
    name: "Falling Leaves",
    category: "particle",
    description: "Autumn leaves floating down",
    tags: ["leaves", "autumn", "nature", "fall"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 150,
      emissionRate: 10,
      lifespan: 5,
      startSize: 12,
      endSize: 10,
      startColor: "#dd8833",
      endColor: "#884422",
      gravity: 25,
      turbulenceStrength: 40,
      velocitySpread: 45,
    },
  },
  {
    id: "builtin-particle-stars",
    name: "Twinkling Stars",
    category: "particle",
    description: "Starfield with twinkling effect",
    tags: ["stars", "night", "space", "twinkle"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 300,
      emissionRate: 15,
      lifespan: 3,
      startSize: 4,
      endSize: 1,
      startColor: "#ffffff",
      endColor: "#ffffcc",
      gravity: 0,
      turbulenceStrength: 2,
      velocitySpread: 360,
    },
  },
  {
    id: "builtin-particle-fireworks",
    name: "Fireworks",
    category: "particle",
    description: "Explosive firework burst",
    tags: ["fireworks", "explosion", "celebration"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 500,
      emissionRate: 200,
      lifespan: 1.5,
      startSize: 6,
      endSize: 2,
      startColor: "#ffff00",
      endColor: "#ff4400",
      gravity: 100,
      velocitySpread: 180,
    },
  },
  {
    id: "builtin-particle-aurora",
    name: "Aurora",
    category: "particle",
    description: "Northern lights effect",
    tags: ["aurora", "northern lights", "glow"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 200,
      emissionRate: 20,
      lifespan: 4,
      startSize: 30,
      endSize: 50,
      startColor: "#00ff88",
      endColor: "#8844ff",
      gravity: -5,
      turbulenceStrength: 30,
      velocitySpread: 20,
    },
  },
  {
    id: "builtin-particle-embers",
    name: "Embers",
    category: "particle",
    description: "Glowing fire embers",
    tags: ["embers", "fire", "glow", "heat"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 150,
      emissionRate: 25,
      lifespan: 3,
      startSize: 4,
      endSize: 1,
      startColor: "#ff6622",
      endColor: "#441100",
      gravity: -40,
      turbulenceStrength: 20,
      velocitySpread: 30,
    },
  },
  {
    id: "builtin-particle-fog",
    name: "Dense Fog",
    category: "particle",
    description: "Thick rolling fog",
    tags: ["fog", "mist", "atmosphere", "weather"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 50,
      emissionRate: 3,
      lifespan: 10,
      startSize: 100,
      endSize: 200,
      startColor: "#888888",
      endColor: "#666666",
      gravity: 0,
      turbulenceStrength: 10,
      velocitySpread: 20,
    },
  },
  {
    id: "builtin-particle-explosion",
    name: "Explosion",
    category: "particle",
    description: "Violent debris explosion",
    tags: ["explosion", "debris", "blast"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 300,
      emissionRate: 500,
      lifespan: 0.8,
      startSize: 10,
      endSize: 3,
      startColor: "#ffaa00",
      endColor: "#331100",
      gravity: 150,
      velocitySpread: 180,
    },
  },
  {
    id: "builtin-particle-portal",
    name: "Portal Swirl",
    category: "particle",
    description: "Magical portal vortex",
    tags: ["portal", "vortex", "magic", "swirl"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 400,
      emissionRate: 60,
      lifespan: 2,
      startSize: 6,
      endSize: 2,
      startColor: "#00ddff",
      endColor: "#4400ff",
      gravity: 0,
      turbulenceStrength: 15,
      velocitySpread: 30,
    },
  },
  {
    id: "builtin-particle-electricity",
    name: "Electricity",
    category: "particle",
    description: "Electric arcs and sparks",
    tags: ["electricity", "lightning", "energy"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 200,
      emissionRate: 150,
      lifespan: 0.3,
      startSize: 3,
      endSize: 1,
      startColor: "#aaeeff",
      endColor: "#ffffff",
      gravity: 0,
      turbulenceStrength: 50,
      velocitySpread: 180,
    },
  },
  {
    id: "builtin-particle-hearts",
    name: "Hearts",
    category: "particle",
    description: "Floating heart particles",
    tags: ["hearts", "love", "romance", "valentine"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 100,
      emissionRate: 15,
      lifespan: 3,
      startSize: 15,
      endSize: 8,
      startColor: "#ff4466",
      endColor: "#ff88aa",
      gravity: -25,
      turbulenceStrength: 10,
      velocitySpread: 60,
    },
  },
  {
    id: "builtin-particle-waterfall",
    name: "Waterfall",
    category: "particle",
    description: "Cascading water effect",
    tags: ["water", "waterfall", "cascade", "splash"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 600,
      emissionRate: 150,
      lifespan: 1.2,
      startSize: 5,
      endSize: 8,
      startColor: "#aaddff",
      endColor: "#ffffff",
      gravity: 300,
      turbulenceStrength: 10,
      velocitySpread: 15,
    },
  },
  {
    id: "builtin-particle-fireflies",
    name: "Fireflies",
    category: "particle",
    description: "Gently glowing fireflies",
    tags: ["fireflies", "glow", "nature", "night"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 50,
      emissionRate: 3,
      lifespan: 6,
      startSize: 5,
      endSize: 3,
      startColor: "#ccff66",
      endColor: "#669933",
      gravity: -5,
      turbulenceStrength: 20,
      velocitySpread: 360,
    },
  },
  {
    id: "builtin-particle-sandstorm",
    name: "Sandstorm",
    category: "particle",
    description: "Blowing desert sand",
    tags: ["sand", "desert", "storm", "wind"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 800,
      emissionRate: 200,
      lifespan: 2,
      startSize: 3,
      endSize: 2,
      startColor: "#cc9966",
      endColor: "#886644",
      gravity: 20,
      turbulenceStrength: 60,
      velocitySpread: 30,
    },
  },
  {
    id: "builtin-particle-glitter",
    name: "Glitter",
    category: "particle",
    description: "Shimmering glitter particles",
    tags: ["glitter", "sparkle", "shine"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 400,
      emissionRate: 80,
      lifespan: 1.5,
      startSize: 3,
      endSize: 1,
      startColor: "#ffffff",
      endColor: "#ffdd88",
      gravity: 30,
      turbulenceStrength: 8,
      velocitySpread: 120,
    },
  },
  {
    id: "builtin-particle-path-light",
    name: "Path Light",
    category: "particle",
    description:
      "Glowing lights that follow spline edges - perfect for logo edge tracing",
    tags: ["path", "light", "glow", "edge", "trace", "logo", "outline", "neon"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 200,
      emissionRate: 40, // Moderate emission for smooth coverage
      lifespan: 2.5, // Long enough to traverse logo edges
      startSize: 6, // Visible glow point
      endSize: 2, // Fade out smaller
      startColor: "#ffffff", // Bright white core
      endColor: "#00ffff", // Cyan glow tail
      gravity: 0, // No gravity - follow path only
      turbulenceStrength: 3, // Minimal turbulence for clean edge following
      velocitySpread: 15, // Tight spread along path tangent
    },
  },
  {
    id: "builtin-particle-path-light-warm",
    name: "Path Light (Warm)",
    category: "particle",
    description: "Warm glowing lights for edge tracing - gold/amber variant",
    tags: ["path", "light", "glow", "edge", "warm", "gold", "amber"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 200,
      emissionRate: 40,
      lifespan: 2.5,
      startSize: 6,
      endSize: 2,
      startColor: "#ffffff",
      endColor: "#ffaa00", // Amber/gold glow
      gravity: 0,
      turbulenceStrength: 3,
      velocitySpread: 15,
    },
  },
  {
    id: "builtin-particle-path-light-neon",
    name: "Path Light (Neon)",
    category: "particle",
    description: "Intense neon lights for edge tracing - magenta/pink variant",
    tags: ["path", "light", "glow", "edge", "neon", "pink", "magenta"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 300,
      emissionRate: 60, // Higher emission for intense neon look
      lifespan: 1.8,
      startSize: 8, // Larger for neon glow
      endSize: 3,
      startColor: "#ff88ff", // Pink core
      endColor: "#ff00ff", // Magenta trail
      gravity: 0,
      turbulenceStrength: 5,
      velocitySpread: 20,
    },
  },
  {
    id: "builtin-particle-path-comet",
    name: "Path Comet",
    category: "particle",
    description:
      "Comet-like particles with long trails - great for motion paths",
    tags: ["path", "comet", "trail", "motion", "streak"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 50,
      emissionRate: 10, // Sparse for distinct comets
      lifespan: 3, // Long life for visible trails
      startSize: 10,
      endSize: 1, // Sharp tail falloff
      startColor: "#ffffff",
      endColor: "#0066ff", // Blue trail
      gravity: 0,
      turbulenceStrength: 0, // No turbulence - pure path following
      velocitySpread: 5, // Very tight to path
    },
  },
];

export const BUILT_IN_PATH_EFFECT_PRESETS: PathEffectPreset[] = [
  {
    id: "builtin-path-sketch",
    name: "Sketchy",
    category: "path-effect",
    description: "Hand-drawn sketch effect",
    tags: ["sketch", "hand-drawn", "rough"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    effects: [
      {
        id: "roughen-1",
        type: "roughen",
        enabled: true,
        order: 0,
        size: {
          id: "r-size",
          name: "Size",
          type: "number",
          value: 3,
          animated: false,
          keyframes: [],
        },
        detail: {
          id: "r-detail",
          name: "Detail",
          type: "number",
          value: 4,
          animated: false,
          keyframes: [],
        },
        seed: 12345,
      } as any,
    ],
  },
  {
    id: "builtin-path-wavy",
    name: "Wavy",
    category: "path-effect",
    description: "Smooth wave deformation",
    tags: ["wave", "smooth", "organic"],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    effects: [
      {
        id: "wave-1",
        type: "wave",
        enabled: true,
        order: 0,
        amplitude: {
          id: "w-amp",
          name: "Amplitude",
          type: "number",
          value: 10,
          animated: false,
          keyframes: [],
        },
        frequency: {
          id: "w-freq",
          name: "Frequency",
          type: "number",
          value: 3,
          animated: false,
          keyframes: [],
        },
        phase: {
          id: "w-phase",
          name: "Phase",
          type: "number",
          value: 0,
          animated: false,
          keyframes: [],
        },
        waveType: "sine",
      } as any,
    ],
  },
];
