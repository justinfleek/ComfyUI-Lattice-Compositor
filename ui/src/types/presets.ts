/**
 * Preset System Types
 *
 * Defines types for saving and loading presets for particles, effects,
 * animations, and other configurable elements.
 */

import type { ParticleSystemConfig } from './particles';
import type { SplinePathEffect } from './project';
import type { CameraShakeConfig } from '../services/cameraEnhancements';
import type { TrajectoryConfig } from '../services/cameraTrajectory';

// ============================================================================
// PRESET CATEGORIES
// ============================================================================

export type PresetCategory =
  | 'particle'
  | 'effect'
  | 'animation'
  | 'camera-shake'
  | 'camera-trajectory'
  | 'path-effect'
  | 'text-style'
  | 'color-palette';

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

export interface ParticlePreset extends PresetMetadata {
  category: 'particle';
  config: Partial<ParticleSystemConfig>;
}

export interface EffectPreset extends PresetMetadata {
  category: 'effect';
  effects: Array<{
    type: string;
    params: Record<string, unknown>;
  }>;
}

export interface PathEffectPreset extends PresetMetadata {
  category: 'path-effect';
  effects: SplinePathEffect[];
}

export interface CameraShakePreset extends PresetMetadata {
  category: 'camera-shake';
  config: Partial<CameraShakeConfig>;
}

export interface CameraTrajectoryPreset extends PresetMetadata {
  category: 'camera-trajectory';
  config: Partial<TrajectoryConfig>;
}

export interface TextStylePreset extends PresetMetadata {
  category: 'text-style';
  style: {
    fontFamily?: string;
    fontSize?: number;
    fontWeight?: number;
    fill?: string;
    stroke?: string;
    strokeWidth?: number;
    letterSpacing?: number;
    lineHeight?: number;
    textAlign?: 'left' | 'center' | 'right';
  };
}

export interface ColorPalettePreset extends PresetMetadata {
  category: 'color-palette';
  colors: string[];
}

export interface AnimationPreset extends PresetMetadata {
  category: 'animation';
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
    id: 'builtin-particle-fire',
    name: 'Fire',
    category: 'particle',
    description: 'Flickering flame effect',
    tags: ['fire', 'flame', 'hot'],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 500,
      emissionRate: 50,
      lifespan: 1.5,
      startSize: 20,
      endSize: 5,
      startColor: '#ff6600',
      endColor: '#ffff00',
      gravity: { x: 0, y: -50, z: 0 },
      turbulenceStrength: 30,
      velocitySpread: 30,
    }
  },
  {
    id: 'builtin-particle-snow',
    name: 'Snow',
    category: 'particle',
    description: 'Gentle falling snowflakes',
    tags: ['snow', 'winter', 'cold'],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 300,
      emissionRate: 20,
      lifespan: 5,
      startSize: 8,
      endSize: 6,
      startColor: '#ffffff',
      endColor: '#ccccff',
      gravity: { x: 0, y: 20, z: 0 },
      turbulenceStrength: 10,
      velocitySpread: 20,
    }
  },
  {
    id: 'builtin-particle-sparks',
    name: 'Sparks',
    category: 'particle',
    description: 'Electric spark burst',
    tags: ['sparks', 'electric', 'energy'],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 200,
      emissionRate: 100,
      lifespan: 0.5,
      startSize: 4,
      endSize: 1,
      startColor: '#ffff00',
      endColor: '#ff8800',
      gravity: { x: 0, y: 100, z: 0 },
      velocitySpread: 180,
    }
  },
  {
    id: 'builtin-particle-smoke',
    name: 'Smoke',
    category: 'particle',
    description: 'Rising smoke plume',
    tags: ['smoke', 'fog', 'mist'],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 100,
      emissionRate: 10,
      lifespan: 4,
      startSize: 30,
      endSize: 80,
      startColor: '#444444',
      endColor: '#888888',
      gravity: { x: 0, y: -30, z: 0 },
      turbulenceStrength: 20,
    }
  },
  {
    id: 'builtin-particle-confetti',
    name: 'Confetti',
    category: 'particle',
    description: 'Colorful celebration confetti',
    tags: ['confetti', 'celebration', 'party'],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    config: {
      maxParticles: 500,
      emissionRate: 100,
      lifespan: 3,
      startSize: 10,
      endSize: 8,
      gravity: { x: 0, y: 50, z: 0 },
      velocitySpread: 60,
      turbulenceStrength: 15,
    }
  },
];

export const BUILT_IN_PATH_EFFECT_PRESETS: PathEffectPreset[] = [
  {
    id: 'builtin-path-sketch',
    name: 'Sketchy',
    category: 'path-effect',
    description: 'Hand-drawn sketch effect',
    tags: ['sketch', 'hand-drawn', 'rough'],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    effects: [
      {
        id: 'roughen-1',
        type: 'roughen',
        enabled: true,
        order: 0,
        size: { id: 'r-size', name: 'Size', type: 'number', value: 3, animated: false, keyframes: [] },
        detail: { id: 'r-detail', name: 'Detail', type: 'number', value: 4, animated: false, keyframes: [] },
        seed: 12345,
      } as any,
    ],
  },
  {
    id: 'builtin-path-wavy',
    name: 'Wavy',
    category: 'path-effect',
    description: 'Smooth wave deformation',
    tags: ['wave', 'smooth', 'organic'],
    isBuiltIn: true,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    effects: [
      {
        id: 'wave-1',
        type: 'wave',
        enabled: true,
        order: 0,
        amplitude: { id: 'w-amp', name: 'Amplitude', type: 'number', value: 10, animated: false, keyframes: [] },
        frequency: { id: 'w-freq', name: 'Frequency', type: 'number', value: 3, animated: false, keyframes: [] },
        phase: { id: 'w-phase', name: 'Phase', type: 'number', value: 0, animated: false, keyframes: [] },
        waveType: 'sine',
      } as any,
    ],
  },
];
