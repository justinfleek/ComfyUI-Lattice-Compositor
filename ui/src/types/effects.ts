/**
 * Effect System Types
 * Defines effects, presets, and animation templates
 */

import type { AnimatableProperty, Keyframe, BezierHandle } from './project';
import type { WarpPin, WarpMesh } from './meshWarp';

export type EffectCategory =
  | 'blur-sharpen'
  | 'color-correction'
  | 'distort'
  | 'generate'
  | 'keying'
  | 'matte'
  | 'noise-grain'
  | 'perspective'
  | 'stylize'
  | 'time'
  | 'transition'
  | 'utility';

export interface EffectParameter {
  id: string;
  name: string;
  type: 'number' | 'color' | 'point' | 'point3D' | 'angle' | 'checkbox' | 'dropdown' | 'layer' | 'string' | 'curve' | 'data';
  value: any;
  defaultValue: any;
  min?: number;
  max?: number;
  step?: number;
  options?: Array<{ label: string; value: any }>;
  animatable: boolean;
  group?: string;
}

export interface Effect {
  id: string;
  name: string;
  category: EffectCategory;
  enabled: boolean;
  expanded: boolean;
  parameters: EffectParameter[];
  // Optional GPU shader code
  fragmentShader?: string;
}

/**
 * Effect instance stored on a layer - parameters are animatable
 */
export interface EffectInstance {
  id: string;
  effectKey: string;  // Key into EFFECT_DEFINITIONS (e.g., 'gaussian-blur')
  name: string;
  category: EffectCategory;
  enabled: boolean;
  expanded: boolean;
  // Parameters as AnimatableProperty for keyframe support
  parameters: Record<string, AnimatableProperty<any>>;
}

/**
 * Mesh Deform effect instance with puppet pins
 * Extends base EffectInstance with pin storage and cached mesh
 */
export interface MeshDeformEffectInstance extends EffectInstance {
  effectKey: 'mesh-deform';
  /** Control pins for deformation (position, bend, starch, overlap, advanced) */
  pins: WarpPin[];
  /** Cached mesh (rebuilt when pins or source changes) */
  cachedMesh?: WarpMesh;
  /** Whether mesh needs rebuild (set to true when pins or source changes) */
  meshDirty: boolean;
}

/**
 * Parameter type mapping for effect definitions
 */
export type EffectParameterType = 'number' | 'color' | 'point' | 'point3d' | 'angle' | 'checkbox' | 'dropdown' | 'layer' | 'string' | 'curve' | 'data';

/**
 * Get the AnimatableProperty type string for a parameter type
 * Returns the type that matches AnimatableProperty.type in project.ts
 */
export function getAnimatableType(paramType: EffectParameterType): 'number' | 'position' | 'color' | 'enum' | 'vector3' {
  switch (paramType) {
    case 'number':
    case 'angle':
      return 'number';
    case 'point':
      return 'position';
    case 'point3d':
      return 'vector3';
    case 'color':
      return 'color';
    case 'checkbox':
    case 'dropdown':
    case 'layer':
    case 'string':
    case 'curve':
    case 'data':
      return 'enum';
    default:
      return 'number';
  }
}

export interface EffectDefinition {
  name: string;
  category: EffectCategory;
  description: string;
  parameters: Omit<EffectParameter, 'id' | 'value'>[];
  fragmentShader?: string;
}

// Built-in effect definitions
export const EFFECT_DEFINITIONS: Record<string, EffectDefinition> = {
  // Blur & Sharpen
  'gaussian-blur': {
    name: 'Gaussian Blur',
    category: 'blur-sharpen',
    description: 'Smooth, bell-curve blur',
    parameters: [
      { name: 'Blurriness', type: 'number', defaultValue: 10, min: 0, max: 250, animatable: true },
      { name: 'Blur Dimensions', type: 'dropdown', defaultValue: 'both', options: [
        { label: 'Horizontal and Vertical', value: 'both' },
        { label: 'Horizontal', value: 'horizontal' },
        { label: 'Vertical', value: 'vertical' }
      ], animatable: false },
      { name: 'Repeat Edge Pixels', type: 'checkbox', defaultValue: true, animatable: false }
    ]
  },

  'directional-blur': {
    name: 'Directional Blur',
    category: 'blur-sharpen',
    description: 'Blur in a specific direction',
    parameters: [
      { name: 'Direction', type: 'angle', defaultValue: 0, animatable: true },
      { name: 'Blur Length', type: 'number', defaultValue: 10, min: 0, max: 500, animatable: true }
    ]
  },

  'radial-blur': {
    name: 'Radial Blur',
    category: 'blur-sharpen',
    description: 'Spin or zoom blur effect',
    parameters: [
      { name: 'Amount', type: 'number', defaultValue: 10, min: 0, max: 100, animatable: true },
      { name: 'Center', type: 'point', defaultValue: { x: 0.5, y: 0.5 }, animatable: true },
      { name: 'Type', type: 'dropdown', defaultValue: 'spin', options: [
        { label: 'Spin', value: 'spin' },
        { label: 'Zoom', value: 'zoom' }
      ], animatable: false },
      { name: 'Antialiasing', type: 'dropdown', defaultValue: 'high', options: [
        { label: 'Low', value: 'low' },
        { label: 'Medium', value: 'medium' },
        { label: 'High', value: 'high' }
      ], animatable: false }
    ]
  },

  'box-blur': {
    name: 'Box Blur',
    category: 'blur-sharpen',
    description: 'Fast uniform blur using box averaging',
    parameters: [
      { name: 'Blur Radius', type: 'number', defaultValue: 5, min: 0, max: 100, animatable: true },
      { name: 'Iterations', type: 'number', defaultValue: 1, min: 1, max: 5, animatable: false }
    ]
  },

  'sharpen': {
    name: 'Sharpen',
    category: 'blur-sharpen',
    description: 'Increase image contrast at edges',
    parameters: [
      { name: 'Sharpen Amount', type: 'number', defaultValue: 50, min: 0, max: 500, animatable: true }
    ]
  },

  'unsharp-mask': {
    name: 'Unsharp Mask',
    category: 'blur-sharpen',
    description: 'Professional sharpening with radius control',
    parameters: [
      { name: 'Amount', type: 'number', defaultValue: 100, min: 1, max: 500, animatable: true },
      { name: 'Radius', type: 'number', defaultValue: 1, min: 0.1, max: 250, step: 0.1, animatable: true },
      { name: 'Threshold', type: 'number', defaultValue: 0, min: 0, max: 255, animatable: true }
    ]
  },

  // Color Correction
  'brightness-contrast': {
    name: 'Brightness & Contrast',
    category: 'color-correction',
    description: 'Adjust brightness and contrast',
    parameters: [
      { name: 'Brightness', type: 'number', defaultValue: 0, min: -150, max: 150, animatable: true },
      { name: 'Contrast', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Use Legacy', type: 'checkbox', defaultValue: false, animatable: false }
    ]
  },

  'hue-saturation': {
    name: 'Hue/Saturation',
    category: 'color-correction',
    description: 'Adjust hue, saturation, and lightness',
    parameters: [
      { name: 'Channel Control', type: 'dropdown', defaultValue: 'master', options: [
        { label: 'Master', value: 'master' },
        { label: 'Reds', value: 'reds' },
        { label: 'Yellows', value: 'yellows' },
        { label: 'Greens', value: 'greens' },
        { label: 'Cyans', value: 'cyans' },
        { label: 'Blues', value: 'blues' },
        { label: 'Magentas', value: 'magentas' }
      ], animatable: false },
      { name: 'Master Hue', type: 'angle', defaultValue: 0, animatable: true, group: 'Master' },
      { name: 'Master Saturation', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true, group: 'Master' },
      { name: 'Master Lightness', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true, group: 'Master' },
      { name: 'Colorize', type: 'checkbox', defaultValue: false, animatable: false }
    ]
  },

  'curves': {
    name: 'Curves',
    category: 'color-correction',
    description: 'Precise tonal adjustment with curves',
    parameters: [
      { name: 'Channel', type: 'dropdown', defaultValue: 'rgb', options: [
        { label: 'RGB', value: 'rgb' },
        { label: 'Red', value: 'red' },
        { label: 'Green', value: 'green' },
        { label: 'Blue', value: 'blue' }
      ], animatable: false }
      // Note: Actual curve control would be a custom component
    ]
  },

  'levels': {
    name: 'Levels',
    category: 'color-correction',
    description: 'Adjust input/output levels',
    parameters: [
      { name: 'Channel', type: 'dropdown', defaultValue: 'rgb', options: [
        { label: 'RGB', value: 'rgb' },
        { label: 'Red', value: 'red' },
        { label: 'Green', value: 'green' },
        { label: 'Blue', value: 'blue' },
        { label: 'Alpha', value: 'alpha' }
      ], animatable: false },
      { name: 'Input Black', type: 'number', defaultValue: 0, min: 0, max: 255, animatable: true },
      { name: 'Input White', type: 'number', defaultValue: 255, min: 0, max: 255, animatable: true },
      { name: 'Gamma', type: 'number', defaultValue: 1, min: 0.1, max: 10, step: 0.01, animatable: true },
      { name: 'Output Black', type: 'number', defaultValue: 0, min: 0, max: 255, animatable: true },
      { name: 'Output White', type: 'number', defaultValue: 255, min: 0, max: 255, animatable: true }
    ]
  },

  'color-balance': {
    name: 'Color Balance',
    category: 'color-correction',
    description: 'Adjust color balance by tonal range',
    parameters: [
      { name: 'Shadow Red', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true, group: 'Shadows' },
      { name: 'Shadow Green', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true, group: 'Shadows' },
      { name: 'Shadow Blue', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true, group: 'Shadows' },
      { name: 'Midtone Red', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true, group: 'Midtones' },
      { name: 'Midtone Green', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true, group: 'Midtones' },
      { name: 'Midtone Blue', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true, group: 'Midtones' },
      { name: 'Highlight Red', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true, group: 'Highlights' },
      { name: 'Highlight Green', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true, group: 'Highlights' },
      { name: 'Highlight Blue', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true, group: 'Highlights' },
      { name: 'Preserve Luminosity', type: 'checkbox', defaultValue: true, animatable: false }
    ]
  },

  'tint': {
    name: 'Tint',
    category: 'color-correction',
    description: 'Map black and white to colors',
    parameters: [
      { name: 'Map Black To', type: 'color', defaultValue: { r: 0, g: 0, b: 0, a: 1 }, animatable: true },
      { name: 'Map White To', type: 'color', defaultValue: { r: 255, g: 255, b: 255, a: 1 }, animatable: true },
      { name: 'Amount to Tint', type: 'number', defaultValue: 100, min: 0, max: 100, animatable: true }
    ]
  },

  // Distort
  'transform': {
    name: 'Transform',
    category: 'distort',
    description: 'Transform layer with anchor point control',
    parameters: [
      { name: 'Anchor Point', type: 'point', defaultValue: { x: 0.5, y: 0.5 }, animatable: true },
      { name: 'Position', type: 'point', defaultValue: { x: 0.5, y: 0.5 }, animatable: true },
      { name: 'Scale Height', type: 'number', defaultValue: 100, min: -10000, max: 10000, animatable: true },
      { name: 'Scale Width', type: 'number', defaultValue: 100, min: -10000, max: 10000, animatable: true },
      { name: 'Skew', type: 'number', defaultValue: 0, min: -85, max: 85, animatable: true },
      { name: 'Skew Axis', type: 'angle', defaultValue: 0, animatable: true },
      { name: 'Rotation', type: 'angle', defaultValue: 0, animatable: true },
      { name: 'Opacity', type: 'number', defaultValue: 100, min: 0, max: 100, animatable: true }
    ]
  },

  'warp': {
    name: 'Warp',
    category: 'distort',
    description: 'Apply warp distortion',
    parameters: [
      { name: 'Warp Style', type: 'dropdown', defaultValue: 'arc', options: [
        { label: 'Arc', value: 'arc' },
        { label: 'Arc Lower', value: 'arc-lower' },
        { label: 'Arc Upper', value: 'arc-upper' },
        { label: 'Arch', value: 'arch' },
        { label: 'Bulge', value: 'bulge' },
        { label: 'Shell Lower', value: 'shell-lower' },
        { label: 'Shell Upper', value: 'shell-upper' },
        { label: 'Flag', value: 'flag' },
        { label: 'Wave', value: 'wave' },
        { label: 'Fish', value: 'fish' },
        { label: 'Rise', value: 'rise' },
        { label: 'Fisheye', value: 'fisheye' },
        { label: 'Inflate', value: 'inflate' },
        { label: 'Squeeze', value: 'squeeze' },
        { label: 'Twist', value: 'twist' }
      ], animatable: false },
      { name: 'Bend', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Horizontal Distortion', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Vertical Distortion', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true }
    ]
  },

  'displacement-map': {
    name: 'Displacement Map',
    category: 'distort',
    description: 'Displace pixels using a map layer or procedural pattern',
    parameters: [
      { name: 'Displacement Map Layer', type: 'layer', defaultValue: null, animatable: false },
      { name: 'Map Type', type: 'dropdown', defaultValue: 'layer', options: [
        { label: 'Use Layer', value: 'layer' },
        { label: 'Noise', value: 'noise' },
        { label: 'Gradient H', value: 'gradient-h' },
        { label: 'Gradient V', value: 'gradient-v' },
        { label: 'Radial', value: 'radial' },
        { label: 'Sine H', value: 'sine-h' },
        { label: 'Sine V', value: 'sine-v' },
        { label: 'Checker', value: 'checker' }
      ], animatable: false },
      { name: 'Displacement Map Behavior', type: 'dropdown', defaultValue: 'stretch', options: [
        { label: 'Center Map', value: 'center' },
        { label: 'Stretch Map to Fit', value: 'stretch' },
        { label: 'Tile Map', value: 'tile' }
      ], animatable: false },
      { name: 'Use For Horizontal', type: 'dropdown', defaultValue: 'red', options: [
        { label: 'Red', value: 'red' },
        { label: 'Green', value: 'green' },
        { label: 'Blue', value: 'blue' },
        { label: 'Alpha', value: 'alpha' },
        { label: 'Luminance', value: 'luminance' },
        { label: 'Off', value: 'off' }
      ], animatable: false },
      { name: 'Max Horizontal', type: 'number', defaultValue: 0, min: -4000, max: 4000, animatable: true },
      { name: 'Use For Vertical', type: 'dropdown', defaultValue: 'green', options: [
        { label: 'Red', value: 'red' },
        { label: 'Green', value: 'green' },
        { label: 'Blue', value: 'blue' },
        { label: 'Alpha', value: 'alpha' },
        { label: 'Luminance', value: 'luminance' },
        { label: 'Off', value: 'off' }
      ], animatable: false },
      { name: 'Max Vertical', type: 'number', defaultValue: 0, min: -4000, max: 4000, animatable: true },
      { name: 'Edge Behavior', type: 'dropdown', defaultValue: 'off', options: [
        { label: 'Clip', value: 'off' },
        { label: 'Wrap Pixels', value: 'tiles' },
        { label: 'Mirror Pixels', value: 'mirror' }
      ], animatable: false },
      { name: 'Map Scale', type: 'number', defaultValue: 1, min: 0.1, max: 10, step: 0.1, animatable: true, group: 'Procedural' }
    ]
  },

  // Generate
  'fill': {
    name: 'Fill',
    category: 'generate',
    description: 'Fill layer with a solid color',
    parameters: [
      { name: 'Fill Mask', type: 'dropdown', defaultValue: 'all', options: [
        { label: 'All Masks', value: 'all' },
        { label: 'None', value: 'none' }
      ], animatable: false },
      { name: 'Color', type: 'color', defaultValue: { r: 255, g: 0, b: 0, a: 1 }, animatable: true },
      { name: 'Invert', type: 'checkbox', defaultValue: false, animatable: false },
      { name: 'Horizontal Feather', type: 'number', defaultValue: 0, min: 0, max: 500, animatable: true },
      { name: 'Vertical Feather', type: 'number', defaultValue: 0, min: 0, max: 500, animatable: true },
      { name: 'Opacity', type: 'number', defaultValue: 100, min: 0, max: 100, animatable: true }
    ]
  },

  'gradient-ramp': {
    name: 'Gradient Ramp',
    category: 'generate',
    description: 'Generate a color gradient',
    parameters: [
      { name: 'Start of Ramp', type: 'point', defaultValue: { x: 0, y: 0.5 }, animatable: true },
      { name: 'Start Color', type: 'color', defaultValue: { r: 0, g: 0, b: 0, a: 1 }, animatable: true },
      { name: 'End of Ramp', type: 'point', defaultValue: { x: 1, y: 0.5 }, animatable: true },
      { name: 'End Color', type: 'color', defaultValue: { r: 255, g: 255, b: 255, a: 1 }, animatable: true },
      { name: 'Ramp Shape', type: 'dropdown', defaultValue: 'linear', options: [
        { label: 'Linear Ramp', value: 'linear' },
        { label: 'Radial Ramp', value: 'radial' }
      ], animatable: false },
      { name: 'Ramp Scatter', type: 'number', defaultValue: 0, min: 0, max: 100, animatable: true },
      { name: 'Blend With Original', type: 'number', defaultValue: 0, min: 0, max: 100, animatable: true }
    ]
  },

  'radio-waves': {
    name: 'Radio Waves',
    category: 'generate',
    description: 'Generate expanding concentric rings for shockwave effects',
    parameters: [
      { name: 'Center', type: 'point', defaultValue: { x: 0.5, y: 0.5 }, animatable: true },
      { name: 'Frequency', type: 'number', defaultValue: 4, min: 1, max: 50, animatable: true },
      { name: 'Expansion', type: 'number', defaultValue: 50, min: 0, max: 100, animatable: true },
      { name: 'Wave Width', type: 'number', defaultValue: 20, min: 1, max: 100, animatable: true },
      { name: 'Stroke Color', type: 'color', defaultValue: { r: 255, g: 255, b: 255, a: 1 }, animatable: true },
      { name: 'Background Color', type: 'color', defaultValue: { r: 128, g: 128, b: 128, a: 1 }, animatable: true },
      { name: 'Fade Start', type: 'number', defaultValue: 0, min: 0, max: 100, animatable: true },
      { name: 'Fade End', type: 'number', defaultValue: 100, min: 0, max: 100, animatable: true },
      { name: 'Invert', type: 'checkbox', defaultValue: false, animatable: false }
    ]
  },

  'ellipse': {
    name: 'Ellipse',
    category: 'generate',
    description: 'Generate ellipse/circle shapes for displacement maps',
    parameters: [
      { name: 'Center', type: 'point', defaultValue: { x: 0.5, y: 0.5 }, animatable: true },
      { name: 'Ellipse Width', type: 'number', defaultValue: 200, min: 1, max: 4000, animatable: true },
      { name: 'Ellipse Height', type: 'number', defaultValue: 200, min: 1, max: 4000, animatable: true },
      { name: 'Softness', type: 'number', defaultValue: 0, min: 0, max: 100, animatable: true },
      { name: 'Stroke Width', type: 'number', defaultValue: 0, min: 0, max: 500, animatable: true },
      { name: 'Stroke Color', type: 'color', defaultValue: { r: 255, g: 255, b: 255, a: 1 }, animatable: true },
      { name: 'Background Color', type: 'color', defaultValue: { r: 0, g: 0, b: 0, a: 1 }, animatable: true },
      { name: 'Invert', type: 'checkbox', defaultValue: false, animatable: false }
    ]
  },

  // Stylize
  'glow': {
    name: 'Glow',
    category: 'stylize',
    description: 'Add a glow effect',
    parameters: [
      { name: 'Glow Threshold', type: 'number', defaultValue: 60, min: 0, max: 100, animatable: true },
      { name: 'Glow Radius', type: 'number', defaultValue: 25, min: 0, max: 500, animatable: true },
      { name: 'Glow Intensity', type: 'number', defaultValue: 1, min: 0, max: 10, step: 0.1, animatable: true },
      { name: 'Composite Original', type: 'dropdown', defaultValue: 'on-top', options: [
        { label: 'On Top', value: 'on-top' },
        { label: 'Behind', value: 'behind' },
        { label: 'None', value: 'none' }
      ], animatable: false },
      { name: 'Glow Colors', type: 'dropdown', defaultValue: 'original', options: [
        { label: 'Original Colors', value: 'original' },
        { label: 'A & B Colors', value: 'ab' }
      ], animatable: false },
      { name: 'Color A', type: 'color', defaultValue: { r: 255, g: 255, b: 255, a: 1 }, animatable: true },
      { name: 'Color B', type: 'color', defaultValue: { r: 255, g: 128, b: 0, a: 1 }, animatable: true },
      { name: 'Color Looping', type: 'dropdown', defaultValue: 'none', options: [
        { label: 'None', value: 'none' },
        { label: 'Sawtooth A>B', value: 'sawtooth_ab' },
        { label: 'Sawtooth B>A', value: 'sawtooth_ba' },
        { label: 'Triangle A>B>A', value: 'triangle' }
      ], animatable: false },
      { name: 'Color Looping Speed', type: 'number', defaultValue: 1, min: 0.1, max: 10, step: 0.1, animatable: true },
      { name: 'Glow Dimensions', type: 'dropdown', defaultValue: 'both', options: [
        { label: 'Horizontal and Vertical', value: 'both' },
        { label: 'Horizontal', value: 'horizontal' },
        { label: 'Vertical', value: 'vertical' }
      ], animatable: false }
    ]
  },

  'cinematic-bloom': {
    name: 'Cinematic Bloom',
    category: 'stylize',
    description: 'Professional bloom with inverse-square falloff, tonemapping, chromatic aberration, and lens dirt',
    parameters: [
      // Core glow settings
      { name: 'Intensity', type: 'number', defaultValue: 1, min: 0, max: 10, step: 0.1, animatable: true, group: 'Core' },
      { name: 'Threshold', type: 'number', defaultValue: 0.8, min: 0, max: 1, step: 0.01, animatable: true, group: 'Core' },
      { name: 'Radius', type: 'number', defaultValue: 50, min: 0, max: 200, animatable: true, group: 'Core' },
      // Falloff mode
      { name: 'Falloff Mode', type: 'dropdown', defaultValue: 'inverse_square', options: [
        { label: 'Inverse Square (Cinematic)', value: 'inverse_square' },
        { label: 'Gaussian (Standard)', value: 'gaussian' },
        { label: 'Exponential', value: 'exponential' }
      ], animatable: false, group: 'Falloff' },
      { name: 'Falloff Exponent', type: 'number', defaultValue: 2, min: 1, max: 4, step: 0.1, animatable: true, group: 'Falloff' },
      // Per-channel radius (color fringing)
      { name: 'Radius R', type: 'number', defaultValue: 1, min: 0, max: 2, step: 0.01, animatable: true, group: 'Color Fringing' },
      { name: 'Radius G', type: 'number', defaultValue: 1, min: 0, max: 2, step: 0.01, animatable: true, group: 'Color Fringing' },
      { name: 'Radius B', type: 'number', defaultValue: 1, min: 0, max: 2, step: 0.01, animatable: true, group: 'Color Fringing' },
      // Tonemapping
      { name: 'Tonemap', type: 'dropdown', defaultValue: 'aces', options: [
        { label: 'None', value: 'none' },
        { label: 'ACES Filmic', value: 'aces' },
        { label: 'Reinhard', value: 'reinhard' },
        { label: 'Hable (Uncharted 2)', value: 'hable' }
      ], animatable: false, group: 'Tonemapping' },
      { name: 'Exposure', type: 'number', defaultValue: 0, min: -5, max: 5, step: 0.1, animatable: true, group: 'Tonemapping' },
      // Chromatic aberration
      { name: 'Chromatic Aberration', type: 'number', defaultValue: 0, min: 0, max: 20, step: 0.5, animatable: true, group: 'Aberration' },
      // Lens dirt
      { name: 'Lens Dirt Enabled', type: 'checkbox', defaultValue: false, animatable: false, group: 'Lens Dirt' },
      { name: 'Lens Dirt Intensity', type: 'number', defaultValue: 0.5, min: 0, max: 1, step: 0.01, animatable: true, group: 'Lens Dirt' },
      { name: 'Lens Dirt Scale', type: 'number', defaultValue: 1, min: 0.5, max: 2, step: 0.1, animatable: true, group: 'Lens Dirt' },
      // Blend mode
      { name: 'Blend Mode', type: 'dropdown', defaultValue: 'add', options: [
        { label: 'Add', value: 'add' },
        { label: 'Screen', value: 'screen' },
        { label: 'Overlay', value: 'overlay' },
        { label: 'Soft Light', value: 'soft_light' }
      ], animatable: false, group: 'Blending' }
    ]
  },

  'drop-shadow': {
    name: 'Drop Shadow',
    category: 'stylize',
    description: 'Add a drop shadow',
    parameters: [
      { name: 'Shadow Color', type: 'color', defaultValue: { r: 0, g: 0, b: 0, a: 0.5 }, animatable: true },
      { name: 'Opacity', type: 'number', defaultValue: 50, min: 0, max: 100, animatable: true },
      { name: 'Direction', type: 'angle', defaultValue: 135, animatable: true },
      { name: 'Distance', type: 'number', defaultValue: 5, min: 0, max: 1000, animatable: true },
      { name: 'Softness', type: 'number', defaultValue: 5, min: 0, max: 250, animatable: true },
      { name: 'Shadow Only', type: 'checkbox', defaultValue: false, animatable: false }
    ]
  },

  // Noise & Grain
  'fractal-noise': {
    name: 'Fractal Noise',
    category: 'noise-grain',
    description: 'Generate fractal noise pattern',
    parameters: [
      { name: 'Fractal Type', type: 'dropdown', defaultValue: 'basic', options: [
        { label: 'Basic', value: 'basic' },
        { label: 'Turbulent Basic', value: 'turbulent-basic' },
        { label: 'Soft Linear', value: 'soft-linear' },
        { label: 'Turbulent Soft', value: 'turbulent-soft' }
      ], animatable: false },
      { name: 'Noise Type', type: 'dropdown', defaultValue: 'block', options: [
        { label: 'Block', value: 'block' },
        { label: 'Linear', value: 'linear' },
        { label: 'Soft Linear', value: 'soft-linear' },
        { label: 'Spline', value: 'spline' }
      ], animatable: false },
      { name: 'Invert', type: 'checkbox', defaultValue: false, animatable: false },
      { name: 'Contrast', type: 'number', defaultValue: 100, min: 0, max: 400, animatable: true },
      { name: 'Brightness', type: 'number', defaultValue: 0, min: -200, max: 200, animatable: true },
      { name: 'Scale', type: 'number', defaultValue: 100, min: 10, max: 10000, animatable: true },
      { name: 'Complexity', type: 'number', defaultValue: 6, min: 1, max: 20, animatable: true },
      { name: 'Evolution', type: 'angle', defaultValue: 0, animatable: true }
    ]
  },

  // Time Effects
  'echo': {
    name: 'Echo',
    category: 'time',
    description: 'Create motion trails by compositing previous frames',
    parameters: [
      { name: 'Echo Time', type: 'number', defaultValue: -0.033, min: -2, max: 2, step: 0.001, animatable: true },
      { name: 'Number of Echoes', type: 'number', defaultValue: 8, min: 1, max: 50, animatable: true },
      { name: 'Starting Intensity', type: 'number', defaultValue: 1, min: 0, max: 2, step: 0.01, animatable: true },
      { name: 'Decay', type: 'number', defaultValue: 0.5, min: 0, max: 1, step: 0.01, animatable: true },
      { name: 'Echo Operator', type: 'dropdown', defaultValue: 'add', options: [
        { label: 'Add', value: 'add' },
        { label: 'Screen', value: 'screen' },
        { label: 'Maximum', value: 'maximum' },
        { label: 'Minimum', value: 'minimum' },
        { label: 'Composite in Back', value: 'composite_back' },
        { label: 'Composite in Front', value: 'composite_front' },
        { label: 'Blend', value: 'blend' }
      ], animatable: false }
    ]
  },

  'posterize-time': {
    name: 'Posterize Time',
    category: 'time',
    description: 'Reduce temporal resolution for stylized frame rate',
    parameters: [
      { name: 'Frame Rate', type: 'number', defaultValue: 12, min: 1, max: 60, animatable: true }
    ]
  },

  'freeze-frame': {
    name: 'Freeze Frame',
    category: 'time',
    description: 'Freezes the layer at a specific source frame',
    parameters: [
      { name: 'Freeze At Frame', type: 'number', defaultValue: 0, min: 0, animatable: true }
    ]
  },

  'time-displacement': {
    name: 'Time Displacement',
    category: 'time',
    description: 'Displace pixels in time based on luminance values',
    parameters: [
      { name: 'Max Displacement', type: 'number', defaultValue: 10, min: 0, max: 60, animatable: true },
      { name: 'Time Resolution', type: 'dropdown', defaultValue: 'frame', options: [
        { label: 'Frame', value: 'frame' },
        { label: 'Half Frame', value: 'half' },
        { label: 'Quarter Frame', value: 'quarter' }
      ], animatable: false }
    ]
  },

  // Note: Timewarp is NOT an effect - it's a layer property on Video/NestedComp layers
  // that modifies timing with animatable speed curves. See VideoData.timewarpEnabled.

  // Stylize - Additional
  'add-grain': {
    name: 'Add Grain',
    category: 'noise-grain',
    description: 'Add film grain texture',
    parameters: [
      { name: 'Intensity', type: 'number', defaultValue: 0.5, min: 0, max: 1, step: 0.01, animatable: true },
      { name: 'Size', type: 'number', defaultValue: 1, min: 0.5, max: 4, step: 0.1, animatable: true },
      { name: 'Softness', type: 'number', defaultValue: 0, min: 0, max: 1, step: 0.01, animatable: true },
      { name: 'Animate', type: 'checkbox', defaultValue: true, animatable: false },
      { name: 'Color', type: 'checkbox', defaultValue: false, animatable: false }
    ]
  },

  // Stylize - Glitch Effects
  'rgb-split': {
    name: 'RGB Split',
    category: 'stylize',
    description: 'Chromatic aberration / RGB channel separation',
    parameters: [
      { name: 'Red Offset X', type: 'number', defaultValue: 5, min: -100, max: 100, animatable: true },
      { name: 'Red Offset Y', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Green Offset X', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Green Offset Y', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Blue Offset X', type: 'number', defaultValue: -5, min: -100, max: 100, animatable: true },
      { name: 'Blue Offset Y', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Blend Mode', type: 'dropdown', defaultValue: 'screen', options: [
        { label: 'Screen', value: 'screen' },
        { label: 'Add', value: 'add' },
        { label: 'Normal', value: 'normal' }
      ], animatable: false }
    ]
  },

  'scanlines': {
    name: 'Scan Lines',
    category: 'stylize',
    description: 'CRT monitor scan line effect',
    parameters: [
      { name: 'Line Width', type: 'number', defaultValue: 2, min: 1, max: 20, animatable: true },
      { name: 'Line Spacing', type: 'number', defaultValue: 2, min: 1, max: 20, animatable: true },
      { name: 'Opacity', type: 'number', defaultValue: 0.3, min: 0, max: 1, step: 0.01, animatable: true },
      { name: 'Direction', type: 'dropdown', defaultValue: 'horizontal', options: [
        { label: 'Horizontal', value: 'horizontal' },
        { label: 'Vertical', value: 'vertical' }
      ], animatable: false },
      { name: 'Animate', type: 'checkbox', defaultValue: false, animatable: false }
    ]
  },

  'vhs': {
    name: 'VHS',
    category: 'stylize',
    description: 'VHS tape distortion effect',
    parameters: [
      { name: 'Tracking', type: 'number', defaultValue: 0.5, min: 0, max: 1, step: 0.01, animatable: true },
      { name: 'Noise', type: 'number', defaultValue: 0.3, min: 0, max: 1, step: 0.01, animatable: true },
      { name: 'Color Bleed', type: 'number', defaultValue: 3, min: 0, max: 20, animatable: true },
      { name: 'Jitter', type: 'number', defaultValue: 0.5, min: 0, max: 5, animatable: true },
      { name: 'Rolling Bands', type: 'checkbox', defaultValue: true, animatable: false }
    ]
  },

  // Color Correction - Additional
  'selective-color': {
    name: 'Selective Color',
    category: 'color-correction',
    description: 'Adjust colors in specific color ranges',
    parameters: [
      { name: 'Colors', type: 'dropdown', defaultValue: 'reds', options: [
        { label: 'Reds', value: 'reds' },
        { label: 'Yellows', value: 'yellows' },
        { label: 'Greens', value: 'greens' },
        { label: 'Cyans', value: 'cyans' },
        { label: 'Blues', value: 'blues' },
        { label: 'Magentas', value: 'magentas' },
        { label: 'Whites', value: 'whites' },
        { label: 'Neutrals', value: 'neutrals' },
        { label: 'Blacks', value: 'blacks' }
      ], animatable: false },
      { name: 'Cyan', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Magenta', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Yellow', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Black', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true }
    ]
  },

  'photo-filter': {
    name: 'Photo Filter',
    category: 'color-correction',
    description: 'Apply warming/cooling filter',
    parameters: [
      { name: 'Filter', type: 'dropdown', defaultValue: 'warming_85', options: [
        { label: 'Warming Filter (85)', value: 'warming_85' },
        { label: 'Warming Filter (81)', value: 'warming_81' },
        { label: 'Cooling Filter (80)', value: 'cooling_80' },
        { label: 'Cooling Filter (82)', value: 'cooling_82' },
        { label: 'Sepia', value: 'sepia' },
        { label: 'Deep Blue', value: 'deep_blue' },
        { label: 'Underwater', value: 'underwater' }
      ], animatable: false },
      { name: 'Color', type: 'color', defaultValue: { r: 236, g: 138, b: 0, a: 1 }, animatable: true },
      { name: 'Density', type: 'number', defaultValue: 25, min: 0, max: 100, animatable: true },
      { name: 'Preserve Luminosity', type: 'checkbox', defaultValue: true, animatable: false }
    ]
  },

  'channel-mixer': {
    name: 'Channel Mixer',
    category: 'color-correction',
    description: 'Mix RGB channels',
    parameters: [
      { name: 'Output Channel', type: 'dropdown', defaultValue: 'red', options: [
        { label: 'Red', value: 'red' },
        { label: 'Green', value: 'green' },
        { label: 'Blue', value: 'blue' }
      ], animatable: false },
      { name: 'Red', type: 'number', defaultValue: 100, min: -200, max: 200, animatable: true },
      { name: 'Green', type: 'number', defaultValue: 0, min: -200, max: 200, animatable: true },
      { name: 'Blue', type: 'number', defaultValue: 0, min: -200, max: 200, animatable: true },
      { name: 'Constant', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Monochrome', type: 'checkbox', defaultValue: false, animatable: false }
    ]
  },

  'gradient-map': {
    name: 'Gradient Map',
    category: 'color-correction',
    description: 'Map luminance to gradient colors',
    parameters: [
      { name: 'Color 1', type: 'color', defaultValue: { r: 0, g: 0, b: 0, a: 1 }, animatable: true },
      { name: 'Color 2', type: 'color', defaultValue: { r: 255, g: 255, b: 255, a: 1 }, animatable: true },
      { name: 'Dither', type: 'number', defaultValue: 0, min: 0, max: 100, animatable: false },
      { name: 'Reverse', type: 'checkbox', defaultValue: false, animatable: false }
    ]
  },

  'black-white': {
    name: 'Black & White',
    category: 'color-correction',
    description: 'Convert to monochrome with color channel control',
    parameters: [
      { name: 'Reds', type: 'number', defaultValue: 40, min: -200, max: 300, animatable: true },
      { name: 'Yellows', type: 'number', defaultValue: 60, min: -200, max: 300, animatable: true },
      { name: 'Greens', type: 'number', defaultValue: 40, min: -200, max: 300, animatable: true },
      { name: 'Cyans', type: 'number', defaultValue: 60, min: -200, max: 300, animatable: true },
      { name: 'Blues', type: 'number', defaultValue: 20, min: -200, max: 300, animatable: true },
      { name: 'Magentas', type: 'number', defaultValue: 80, min: -200, max: 300, animatable: true },
      { name: 'Tint', type: 'checkbox', defaultValue: false, animatable: false },
      { name: 'Tint Color', type: 'color', defaultValue: { r: 225, g: 210, b: 180, a: 1 }, animatable: true }
    ]
  },

  'vignette': {
    name: 'Vignette',
    category: 'color-correction',
    description: 'Darken or lighten edges to focus attention',
    parameters: [
      { name: 'Amount', type: 'number', defaultValue: 50, min: -100, max: 100, animatable: true },
      { name: 'Midpoint', type: 'number', defaultValue: 50, min: 0, max: 100, animatable: true },
      { name: 'Roundness', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Feather', type: 'number', defaultValue: 50, min: 0, max: 100, animatable: true }
    ]
  },

  'lut': {
    name: 'LUT (Look-Up Table)',
    category: 'color-correction',
    description: 'Apply .cube color grading look-up table',
    parameters: [
      { name: 'LUT Data', type: 'string', defaultValue: '', animatable: false },
      { name: 'Intensity', type: 'number', defaultValue: 100, min: 0, max: 100, animatable: true }
    ]
  },

  'lift-gamma-gain': {
    name: 'Lift/Gamma/Gain',
    category: 'color-correction',
    description: 'ASC CDL-style three-way color correction',
    parameters: [
      // Lift (Shadows)
      { name: 'Lift Red', type: 'number', defaultValue: 0, min: -1, max: 1, step: 0.01, animatable: true },
      { name: 'Lift Green', type: 'number', defaultValue: 0, min: -1, max: 1, step: 0.01, animatable: true },
      { name: 'Lift Blue', type: 'number', defaultValue: 0, min: -1, max: 1, step: 0.01, animatable: true },
      // Gamma (Midtones)
      { name: 'Gamma Red', type: 'number', defaultValue: 1, min: 0.1, max: 4, step: 0.01, animatable: true },
      { name: 'Gamma Green', type: 'number', defaultValue: 1, min: 0.1, max: 4, step: 0.01, animatable: true },
      { name: 'Gamma Blue', type: 'number', defaultValue: 1, min: 0.1, max: 4, step: 0.01, animatable: true },
      // Gain (Highlights)
      { name: 'Gain Red', type: 'number', defaultValue: 1, min: 0, max: 4, step: 0.01, animatable: true },
      { name: 'Gain Green', type: 'number', defaultValue: 1, min: 0, max: 4, step: 0.01, animatable: true },
      { name: 'Gain Blue', type: 'number', defaultValue: 1, min: 0, max: 4, step: 0.01, animatable: true }
    ]
  },

  'hsl-secondary': {
    name: 'HSL Secondary',
    category: 'color-correction',
    description: 'Targeted color correction by hue/saturation/luminance range',
    parameters: [
      // Qualification
      { name: 'Hue Center', type: 'number', defaultValue: 0, min: 0, max: 360, step: 1, animatable: true },
      { name: 'Hue Width', type: 'number', defaultValue: 30, min: 0, max: 180, step: 1, animatable: true },
      { name: 'Hue Falloff', type: 'number', defaultValue: 10, min: 0, max: 90, step: 1, animatable: true },
      { name: 'Sat Min', type: 'number', defaultValue: 0, min: 0, max: 100, step: 1, animatable: true },
      { name: 'Sat Max', type: 'number', defaultValue: 100, min: 0, max: 100, step: 1, animatable: true },
      { name: 'Sat Falloff', type: 'number', defaultValue: 10, min: 0, max: 50, step: 1, animatable: true },
      { name: 'Lum Min', type: 'number', defaultValue: 0, min: 0, max: 100, step: 1, animatable: true },
      { name: 'Lum Max', type: 'number', defaultValue: 100, min: 0, max: 100, step: 1, animatable: true },
      { name: 'Lum Falloff', type: 'number', defaultValue: 10, min: 0, max: 50, step: 1, animatable: true },
      // Correction
      { name: 'Hue Shift', type: 'number', defaultValue: 0, min: -180, max: 180, step: 1, animatable: true },
      { name: 'Saturation', type: 'number', defaultValue: 0, min: -100, max: 100, step: 1, animatable: true },
      { name: 'Luminance', type: 'number', defaultValue: 0, min: -100, max: 100, step: 1, animatable: true },
      // Preview
      { name: 'Show Mask', type: 'checkbox', defaultValue: false, animatable: false }
    ]
  },

  'hue-vs-curves': {
    name: 'Hue vs Curves',
    category: 'color-correction',
    description: 'HSL-space curve adjustments for precise color control',
    parameters: [
      { name: 'Hue vs Hue', type: 'curve', defaultValue: [], animatable: false },
      { name: 'Hue vs Sat', type: 'curve', defaultValue: [], animatable: false },
      { name: 'Hue vs Lum', type: 'curve', defaultValue: [], animatable: false },
      { name: 'Lum vs Sat', type: 'curve', defaultValue: [], animatable: false },
      { name: 'Sat vs Sat', type: 'curve', defaultValue: [], animatable: false }
    ]
  },

  'color-match': {
    name: 'Color Match',
    category: 'color-correction',
    description: 'Match color distribution to a reference image',
    parameters: [
      { name: 'Reference Histogram R', type: 'data', defaultValue: null, animatable: false },
      { name: 'Reference Histogram G', type: 'data', defaultValue: null, animatable: false },
      { name: 'Reference Histogram B', type: 'data', defaultValue: null, animatable: false },
      { name: 'Reference Pixels', type: 'number', defaultValue: 0, animatable: false },
      { name: 'Strength', type: 'number', defaultValue: 100, min: 0, max: 100, step: 1, animatable: true },
      { name: 'Match Luminance', type: 'checkbox', defaultValue: true, animatable: false },
      { name: 'Match Color', type: 'checkbox', defaultValue: true, animatable: false }
    ]
  },

  // Stylize - VFX Effects (inspired by filliptm's ComfyUI_Fill-Nodes)
  // Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
  'pixel-sort': {
    name: 'Pixel Sort',
    category: 'stylize',
    description: 'Sort pixels by color properties within intervals',
    parameters: [
      { name: 'Direction', type: 'dropdown', defaultValue: 'horizontal', options: [
        { label: 'Horizontal', value: 'horizontal' },
        { label: 'Vertical', value: 'vertical' }
      ], animatable: false },
      { name: 'Threshold', type: 'number', defaultValue: 0.25, min: 0, max: 1, step: 0.01, animatable: true },
      { name: 'Smoothing', type: 'number', defaultValue: 0.1, min: 0, max: 1, step: 0.01, animatable: true },
      { name: 'Sort By', type: 'dropdown', defaultValue: 'saturation', options: [
        { label: 'Saturation', value: 'saturation' },
        { label: 'Brightness', value: 'brightness' },
        { label: 'Hue', value: 'hue' }
      ], animatable: false },
      { name: 'Reverse', type: 'checkbox', defaultValue: false, animatable: false }
    ]
  },

  'glitch': {
    name: 'Glitch',
    category: 'stylize',
    description: 'Digital corruption/distortion effect',
    parameters: [
      { name: 'Glitch Amount', type: 'number', defaultValue: 5, min: 0, max: 10, step: 0.1, animatable: true },
      { name: 'Color Offset', type: 'checkbox', defaultValue: true, animatable: false },
      { name: 'Block Size', type: 'number', defaultValue: 8, min: 1, max: 50, animatable: true },
      { name: 'Seed', type: 'number', defaultValue: 12345, min: 0, max: 99999, animatable: false },
      { name: 'Scanlines', type: 'checkbox', defaultValue: true, animatable: false }
    ]
  },

  'halftone': {
    name: 'Halftone',
    category: 'stylize',
    description: 'Print-style dot pattern effect',
    parameters: [
      { name: 'Dot Size', type: 'number', defaultValue: 6, min: 2, max: 20, animatable: true },
      { name: 'Angle', type: 'angle', defaultValue: 45, animatable: true },
      { name: 'Color Mode', type: 'dropdown', defaultValue: 'grayscale', options: [
        { label: 'Grayscale', value: 'grayscale' },
        { label: 'RGB', value: 'rgb' },
        { label: 'CMYK', value: 'cmyk' }
      ], animatable: false }
    ]
  },

  'dither': {
    name: 'Dither',
    category: 'stylize',
    description: 'Reduce color depth with dithering patterns',
    parameters: [
      { name: 'Method', type: 'dropdown', defaultValue: 'ordered', options: [
        { label: 'Ordered (Bayer)', value: 'ordered' },
        { label: 'Floyd-Steinberg', value: 'floyd_steinberg' },
        { label: 'Atkinson', value: 'atkinson' }
      ], animatable: false },
      { name: 'Levels', type: 'number', defaultValue: 4, min: 2, max: 256, animatable: true },
      { name: 'Matrix Size', type: 'dropdown', defaultValue: '4', options: [
        { label: '2x2', value: '2' },
        { label: '4x4', value: '4' },
        { label: '8x8', value: '8' }
      ], animatable: false }
    ]
  },

  // Stylize - Additional
  'emboss': {
    name: 'Emboss',
    category: 'stylize',
    description: 'Create embossed relief effect',
    parameters: [
      { name: 'Direction', type: 'angle', defaultValue: 135, animatable: true },
      { name: 'Height', type: 'number', defaultValue: 3, min: 1, max: 10, animatable: true },
      { name: 'Amount', type: 'number', defaultValue: 100, min: 1, max: 500, animatable: true }
    ]
  },

  'find-edges': {
    name: 'Find Edges',
    category: 'stylize',
    description: 'Detect and highlight edges',
    parameters: [
      { name: 'Invert', type: 'checkbox', defaultValue: false, animatable: false },
      { name: 'Blend with Original', type: 'number', defaultValue: 0, min: 0, max: 100, animatable: true }
    ]
  },

  'mosaic': {
    name: 'Mosaic',
    category: 'stylize',
    description: 'Pixelate effect',
    parameters: [
      { name: 'Horizontal Blocks', type: 'number', defaultValue: 10, min: 2, max: 200, animatable: true },
      { name: 'Vertical Blocks', type: 'number', defaultValue: 10, min: 2, max: 200, animatable: true },
      { name: 'Sharp Corners', type: 'checkbox', defaultValue: true, animatable: false }
    ]
  },

  // Blur - Additional
  'lens-blur': {
    name: 'Lens Blur',
    category: 'blur-sharpen',
    description: 'Simulate camera lens blur with bokeh',
    parameters: [
      { name: 'Radius', type: 'number', defaultValue: 15, min: 0, max: 100, animatable: true },
      { name: 'Blade Curvature', type: 'number', defaultValue: 0, min: 0, max: 100, animatable: true },
      { name: 'Rotation', type: 'angle', defaultValue: 0, animatable: true },
      { name: 'Brightness', type: 'number', defaultValue: 0, min: -100, max: 100, animatable: true },
      { name: 'Threshold', type: 'number', defaultValue: 255, min: 0, max: 255, animatable: true }
    ]
  },

  // Distort - Additional
  'bulge': {
    name: 'Bulge',
    category: 'distort',
    description: 'Spherical bulge distortion',
    parameters: [
      { name: 'Horizontal Radius', type: 'number', defaultValue: 100, min: 0, max: 1000, animatable: true },
      { name: 'Vertical Radius', type: 'number', defaultValue: 100, min: 0, max: 1000, animatable: true },
      { name: 'Bulge Center', type: 'point', defaultValue: { x: 0.5, y: 0.5 }, animatable: true },
      { name: 'Bulge Height', type: 'number', defaultValue: 1, min: -4, max: 4, step: 0.1, animatable: true },
      { name: 'Taper Radius', type: 'number', defaultValue: 0, min: 0, max: 100, animatable: true }
    ]
  },

  'twirl': {
    name: 'Twirl',
    category: 'distort',
    description: 'Spiral twist distortion',
    parameters: [
      { name: 'Angle', type: 'angle', defaultValue: 50, animatable: true },
      { name: 'Twirl Radius', type: 'number', defaultValue: 200, min: 0, max: 2000, animatable: true },
      { name: 'Twirl Center', type: 'point', defaultValue: { x: 0.5, y: 0.5 }, animatable: true }
    ]
  },

  'ripple': {
    name: 'Ripple',
    category: 'distort',
    description: 'Water ripple distortion',
    parameters: [
      { name: 'Radius', type: 'number', defaultValue: 100, min: 1, max: 500, animatable: true },
      { name: 'Wave Length', type: 'number', defaultValue: 30, min: 1, max: 999, animatable: true },
      { name: 'Amplitude', type: 'number', defaultValue: 10, min: -100, max: 100, animatable: true },
      { name: 'Center', type: 'point', defaultValue: { x: 0.5, y: 0.5 }, animatable: true },
      { name: 'Phase', type: 'angle', defaultValue: 0, animatable: true }
    ]
  },

  'wave': {
    name: 'Wave',
    category: 'distort',
    description: 'Wave distortion',
    parameters: [
      { name: 'Wave Type', type: 'dropdown', defaultValue: 'sine', options: [
        { label: 'Sine', value: 'sine' },
        { label: 'Triangle', value: 'triangle' },
        { label: 'Square', value: 'square' }
      ], animatable: false },
      { name: 'Wave Height', type: 'number', defaultValue: 10, min: 0, max: 100, animatable: true },
      { name: 'Wave Width', type: 'number', defaultValue: 100, min: 1, max: 500, animatable: true },
      { name: 'Direction', type: 'angle', defaultValue: 0, animatable: true },
      { name: 'Phase', type: 'angle', defaultValue: 0, animatable: true }
    ]
  },

  'turbulent-displace': {
    name: 'Turbulent Displace',
    category: 'distort',
    description: 'Procedural organic distortion using turbulent noise',
    parameters: [
      { name: 'Displacement', type: 'dropdown', defaultValue: 'turbulent', options: [
        { label: 'Turbulent', value: 'turbulent' },
        { label: 'Bulge', value: 'bulge' },
        { label: 'Twist', value: 'twist' },
        { label: 'Turbulent Smoother', value: 'turbulent-smoother' },
        { label: 'Horizontal Displacement', value: 'horizontal' },
        { label: 'Vertical Displacement', value: 'vertical' },
        { label: 'Cross Displacement', value: 'cross' }
      ], animatable: false },
      { name: 'Amount', type: 'number', defaultValue: 50, min: 0, max: 1000, animatable: true },
      { name: 'Size', type: 'number', defaultValue: 100, min: 1, max: 1000, animatable: true },
      { name: 'Complexity', type: 'number', defaultValue: 3, min: 1, max: 10, animatable: true },
      { name: 'Evolution', type: 'angle', defaultValue: 0, animatable: true },
      { name: 'Cycle Evolution', type: 'checkbox', defaultValue: false, animatable: false, group: 'Evolution Options' },
      { name: 'Cycle Revolutions', type: 'number', defaultValue: 1, min: 1, max: 100, animatable: false, group: 'Evolution Options' },
      { name: 'Random Seed', type: 'number', defaultValue: 0, min: 0, max: 99999, animatable: false },
      { name: 'Offset', type: 'point', defaultValue: { x: 0, y: 0 }, animatable: true },
      { name: 'Pinning', type: 'dropdown', defaultValue: 'none', options: [
        { label: 'None', value: 'none' },
        { label: 'Pin All', value: 'all' },
        { label: 'Pin Horizontally', value: 'horizontal' },
        { label: 'Pin Vertically', value: 'vertical' }
      ], animatable: false }
    ]
  },

  'ripple-distort': {
    name: 'Ripple',
    category: 'distort',
    description: 'Concentric wave distortion from center point',
    parameters: [
      { name: 'Center', type: 'point', defaultValue: { x: 0.5, y: 0.5 }, animatable: true },
      { name: 'Radius', type: 'number', defaultValue: 200, min: 1, max: 2000, animatable: true },
      { name: 'Wave Length', type: 'number', defaultValue: 50, min: 1, max: 500, animatable: true },
      { name: 'Amplitude', type: 'number', defaultValue: 20, min: -100, max: 100, animatable: true },
      { name: 'Phase', type: 'angle', defaultValue: 0, animatable: true },
      { name: 'Decay', type: 'number', defaultValue: 50, min: 0, max: 100, animatable: true }
    ]
  },

  'mesh-deform': {
    name: 'Mesh Deform',
    category: 'distort',
    description: 'Puppet pin-style deformation using control pins. Add pins to deform the image organically.',
    parameters: [
      // Mesh generation
      { name: 'Triangle Count', type: 'number', defaultValue: 200, min: 50, max: 1000, step: 10, animatable: false, group: 'Mesh' },
      { name: 'Expansion', type: 'number', defaultValue: 3, min: 0, max: 50, animatable: false, group: 'Mesh' },
      { name: 'Alpha Threshold', type: 'number', defaultValue: 128, min: 0, max: 255, animatable: false, group: 'Mesh' },
      // Debug/display
      { name: 'Show Mesh', type: 'checkbox', defaultValue: false, animatable: false, group: 'Display' },
      { name: 'Show Pins', type: 'checkbox', defaultValue: true, animatable: false, group: 'Display' },
      // Pin behavior
      { name: 'Pin Falloff', type: 'dropdown', defaultValue: 'inverse-distance', options: [
        { label: 'Inverse Distance', value: 'inverse-distance' },
        { label: 'Radial Basis', value: 'radial-basis' }
      ], animatable: false, group: 'Pins' },
      { name: 'Falloff Power', type: 'number', defaultValue: 2, min: 1, max: 5, step: 0.1, animatable: false, group: 'Pins' },
      // Overlap rendering
      { name: 'Enable Overlap', type: 'checkbox', defaultValue: false, animatable: false, group: 'Overlap' }
    ]
  },

  // ============================================================================
  // PERSPECTIVE / 3D EFFECTS
  // ============================================================================

  'fog-3d': {
    name: 'Fog 3D',
    category: 'perspective',
    description: 'Depth-based atmospheric fog effect for 3D compositions',
    parameters: [
      { name: 'Fog Start Depth', type: 'number', defaultValue: 0, min: -10000, max: 10000, step: 10, animatable: true },
      { name: 'Fog End Depth', type: 'number', defaultValue: 2000, min: -10000, max: 10000, step: 10, animatable: true },
      { name: 'Fog Color', type: 'color', defaultValue: { r: 200, g: 200, b: 220 }, animatable: true },
      { name: 'Fog Opacity', type: 'number', defaultValue: 100, min: 0, max: 100, step: 1, animatable: true },
      { name: 'Scattering', type: 'number', defaultValue: 0, min: 0, max: 100, step: 1, animatable: true },
      { name: 'Gradient Mode', type: 'dropdown', defaultValue: 'linear', options: [
        { label: 'Linear', value: 'linear' },
        { label: 'Exponential', value: 'exponential' },
        { label: 'Exponential Squared', value: 'exponential2' }
      ], animatable: false },
      { name: 'Use Comp Camera', type: 'checkbox', defaultValue: true, animatable: false },
      { name: 'Layer Depth', type: 'number', defaultValue: 0, min: -10000, max: 10000, step: 10, animatable: true }
    ]
  },

  'depth-matte': {
    name: 'Depth Matte',
    category: 'perspective',
    description: 'Create matte based on layer Z-depth',
    parameters: [
      { name: 'Near Depth', type: 'number', defaultValue: 0, min: -10000, max: 10000, step: 10, animatable: true },
      { name: 'Far Depth', type: 'number', defaultValue: 1000, min: -10000, max: 10000, step: 10, animatable: true },
      { name: 'Invert', type: 'checkbox', defaultValue: false, animatable: false },
      { name: 'Softness', type: 'number', defaultValue: 0, min: 0, max: 100, step: 1, animatable: true }
    ]
  },

  '3d-glasses': {
    name: '3D Glasses',
    category: 'perspective',
    description: 'Anaglyph 3D effect for stereoscopic viewing',
    parameters: [
      { name: '3D View', type: 'dropdown', defaultValue: 'red-cyan', options: [
        { label: 'Red-Cyan', value: 'red-cyan' },
        { label: 'Green-Magenta', value: 'green-magenta' },
        { label: 'Amber-Blue', value: 'amber-blue' }
      ], animatable: false },
      { name: 'Left View', type: 'dropdown', defaultValue: 'red', options: [
        { label: 'Red', value: 'red' },
        { label: 'Green', value: 'green' },
        { label: 'Blue', value: 'blue' }
      ], animatable: false },
      { name: 'Right View', type: 'dropdown', defaultValue: 'cyan', options: [
        { label: 'Cyan', value: 'cyan' },
        { label: 'Magenta', value: 'magenta' },
        { label: 'Yellow', value: 'yellow' }
      ], animatable: false },
      { name: 'Convergence', type: 'number', defaultValue: 0, min: -100, max: 100, step: 1, animatable: true },
      { name: 'Balance', type: 'number', defaultValue: 0, min: -100, max: 100, step: 1, animatable: true }
    ]
  },

  // ============================================================================
  // EXPRESSION CONTROLS
  // These are special "effects" that provide controllable values for expressions
  // They don't process pixels - they expose animatable parameters
  // ============================================================================

  'slider-control': {
    name: 'Slider Control',
    category: 'utility',
    description: 'Provides an animatable numeric value for expressions. Use effect("Slider Control")("Slider") in expressions.',
    parameters: [
      { name: 'Slider', type: 'number', defaultValue: 0, min: -1000000, max: 1000000, step: 0.01, animatable: true }
    ]
  },

  'checkbox-control': {
    name: 'Checkbox Control',
    category: 'utility',
    description: 'Provides a boolean toggle for expressions. Returns 1 when checked, 0 when unchecked.',
    parameters: [
      { name: 'Checkbox', type: 'checkbox', defaultValue: false, animatable: true }
    ]
  },

  'dropdown-menu-control': {
    name: 'Dropdown Menu Control',
    category: 'utility',
    description: 'Provides a menu selection for expressions. Returns the index (1-based) of the selected option.',
    parameters: [
      { name: 'Menu', type: 'dropdown', defaultValue: 1, options: [
        { label: 'Option 1', value: 1 },
        { label: 'Option 2', value: 2 },
        { label: 'Option 3', value: 3 }
      ], animatable: false }
    ]
  },

  'color-control': {
    name: 'Color Control',
    category: 'utility',
    description: 'Provides an animatable color value for expressions.',
    parameters: [
      { name: 'Color', type: 'color', defaultValue: { r: 255, g: 0, b: 0 }, animatable: true }
    ]
  },

  'point-control': {
    name: 'Point Control',
    category: 'utility',
    description: 'Provides an animatable 2D point for expressions.',
    parameters: [
      { name: 'Point', type: 'point', defaultValue: { x: 0, y: 0 }, animatable: true }
    ]
  },

  '3d-point-control': {
    name: '3D Point Control',
    category: 'utility',
    description: 'Provides an animatable 3D point for expressions.',
    parameters: [
      { name: '3D Point', type: 'point3D', defaultValue: { x: 0, y: 0, z: 0 }, animatable: true }
    ]
  },

  'angle-control': {
    name: 'Angle Control',
    category: 'utility',
    description: 'Provides an animatable angle value for expressions.',
    parameters: [
      { name: 'Angle', type: 'angle', defaultValue: 0, animatable: true }
    ]
  },

  'layer-control': {
    name: 'Layer Control',
    category: 'utility',
    description: 'Provides a layer reference for expressions.',
    parameters: [
      { name: 'Layer', type: 'layer', defaultValue: null, animatable: false }
    ]
  }
};

// Effect categories with icons and descriptions
export const EFFECT_CATEGORIES: Record<EffectCategory, { label: string; icon: string; description: string }> = {
  'blur-sharpen': { label: 'Blur & Sharpen', icon: 'B', description: 'Blur and sharpen effects' },
  'color-correction': { label: 'Color Correction', icon: 'C', description: 'Color adjustment effects' },
  'distort': { label: 'Distort', icon: 'D', description: 'Distortion effects' },
  'generate': { label: 'Generate', icon: 'G', description: 'Generate patterns and fills' },
  'keying': { label: 'Keying', icon: 'K', description: 'Chromakey and luma key' },
  'matte': { label: 'Matte', icon: 'M', description: 'Matte manipulation' },
  'noise-grain': { label: 'Noise & Grain', icon: 'N', description: 'Add or remove noise' },
  'perspective': { label: 'Perspective', icon: 'P', description: '3D perspective effects' },
  'stylize': { label: 'Stylize', icon: 'S', description: 'Stylization effects' },
  'time': { label: 'Time', icon: 'T', description: 'Time-based effects' },
  'transition': { label: 'Transition', icon: 'Tr', description: 'Transition effects' },
  'utility': { label: 'Utility', icon: 'U', description: 'Utility effects' }
};

/**
 * Create effect instance from definition (legacy - returns Effect)
 * @deprecated Use createEffectInstance instead
 */
export function createEffect(definitionKey: string): Effect | null {
  const def = EFFECT_DEFINITIONS[definitionKey];
  if (!def) return null;

  return {
    id: `effect-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`,
    name: def.name,
    category: def.category,
    enabled: true,
    expanded: true,
    parameters: def.parameters.map((p, index) => ({
      ...p,
      id: `param-${index}`,
      value: p.defaultValue
    })),
    fragmentShader: def.fragmentShader
  };
}

/**
 * Create effect instance with animatable parameters
 * This is the proper way to create effects for layers
 */
export function createEffectInstance(definitionKey: string): EffectInstance | null {
  const def = EFFECT_DEFINITIONS[definitionKey];
  if (!def) return null;

  const parameters: Record<string, AnimatableProperty<any>> = {};

  def.parameters.forEach((param, index) => {
    // Generate a safe key from the parameter name (e.g., "Blur Dimensions" -> "blurDimensions")
    const paramKey = param.name
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, '_')
      .replace(/^_|_$/g, '');

    parameters[paramKey] = {
      id: `${definitionKey}-${paramKey}-${index}`,
      name: param.name,
      type: getAnimatableType(param.type as EffectParameterType),
      value: param.defaultValue,
      animated: false,
      keyframes: []
    };
  });

  return {
    id: `effect-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`,
    effectKey: definitionKey,
    name: def.name,
    category: def.category,
    enabled: true,
    expanded: true,
    parameters
  };
}

/**
 * Create a mesh-deform effect instance with empty pins array
 * Use this instead of createEffectInstance for mesh-deform effects
 */
export function createMeshDeformEffectInstance(): MeshDeformEffectInstance | null {
  const baseInstance = createEffectInstance('mesh-deform');
  if (!baseInstance) return null;

  return {
    ...baseInstance,
    effectKey: 'mesh-deform',
    pins: [],
    meshDirty: true
  };
}

/**
 * Type guard to check if an effect instance is a MeshDeformEffectInstance
 */
export function isMeshDeformEffect(effect: EffectInstance): effect is MeshDeformEffectInstance {
  return effect.effectKey === 'mesh-deform' && 'pins' in effect;
}

// Animation presets
export interface AnimationPreset {
  id: string;
  name: string;
  category: string;
  description: string;
  keyframes: Array<{
    property: string;
    keyframes: Array<{
      time: number;  // 0-1 normalized
      value: any;
      inHandle?: { x: number; y: number };
      outHandle?: { x: number; y: number };
    }>;
  }>;
}

export const ANIMATION_PRESETS: AnimationPreset[] = [
  {
    id: 'fade-in',
    name: 'Fade In',
    category: 'Fade',
    description: 'Fade from transparent to opaque',
    keyframes: [{
      property: 'opacity',
      keyframes: [
        { time: 0, value: 0, outHandle: { x: 0.4, y: 0 } },
        { time: 1, value: 100, inHandle: { x: 0.6, y: 1 } }
      ]
    }]
  },
  {
    id: 'fade-out',
    name: 'Fade Out',
    category: 'Fade',
    description: 'Fade from opaque to transparent',
    keyframes: [{
      property: 'opacity',
      keyframes: [
        { time: 0, value: 100, outHandle: { x: 0.4, y: 1 } },
        { time: 1, value: 0, inHandle: { x: 0.6, y: 0 } }
      ]
    }]
  },
  {
    id: 'scale-up',
    name: 'Scale Up',
    category: 'Scale',
    description: 'Scale from small to full size',
    keyframes: [{
      property: 'scale',
      keyframes: [
        { time: 0, value: { x: 0, y: 0 }, outHandle: { x: 0.25, y: 0.1 } },
        { time: 1, value: { x: 100, y: 100 }, inHandle: { x: 0.25, y: 1 } }
      ]
    }]
  },
  {
    id: 'bounce-in',
    name: 'Bounce In',
    category: 'Scale',
    description: 'Scale up with bounce effect',
    keyframes: [{
      property: 'scale',
      keyframes: [
        { time: 0, value: { x: 0, y: 0 } },
        { time: 0.6, value: { x: 110, y: 110 } },
        { time: 0.8, value: { x: 95, y: 95 } },
        { time: 1, value: { x: 100, y: 100 } }
      ]
    }]
  },
  {
    id: 'slide-left',
    name: 'Slide Left',
    category: 'Position',
    description: 'Slide in from right',
    keyframes: [{
      property: 'position',
      keyframes: [
        { time: 0, value: { x: 1.5, y: 0.5 }, outHandle: { x: 0.25, y: 0.1 } },
        { time: 1, value: { x: 0.5, y: 0.5 }, inHandle: { x: 0.25, y: 1 } }
      ]
    }]
  },
  {
    id: 'rotate-in',
    name: 'Rotate In',
    category: 'Rotation',
    description: 'Rotate from 0 to 360 degrees',
    keyframes: [{
      property: 'rotation',
      keyframes: [
        { time: 0, value: 0 },
        { time: 1, value: 360 }
      ]
    }]
  },
  {
    id: 'typewriter',
    name: 'Typewriter',
    category: 'Text',
    description: 'Reveal text character by character',
    keyframes: [{
      property: 'textReveal',
      keyframes: [
        { time: 0, value: 0 },
        { time: 1, value: 100 }
      ]
    }]
  }
];
