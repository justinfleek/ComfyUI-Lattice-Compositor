/**
 * Effect System Types
 * Defines effects, presets, and animation templates
 */

import type { AnimatableProperty, Keyframe, BezierHandle } from './project';

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
  type: 'number' | 'color' | 'point' | 'angle' | 'checkbox' | 'dropdown' | 'layer';
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
 * Parameter type mapping for effect definitions
 */
export type EffectParameterType = 'number' | 'color' | 'point' | 'point3d' | 'angle' | 'checkbox' | 'dropdown' | 'layer';

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
    description: 'Displace pixels using a map layer',
    parameters: [
      { name: 'Displacement Map Layer', type: 'layer', defaultValue: null, animatable: false },
      { name: 'Use For Horizontal', type: 'dropdown', defaultValue: 'red', options: [
        { label: 'Red', value: 'red' },
        { label: 'Green', value: 'green' },
        { label: 'Blue', value: 'blue' },
        { label: 'Alpha', value: 'alpha' },
        { label: 'Luminance', value: 'luminance' }
      ], animatable: false },
      { name: 'Max Horizontal', type: 'number', defaultValue: 0, min: -4000, max: 4000, animatable: true },
      { name: 'Use For Vertical', type: 'dropdown', defaultValue: 'green', options: [
        { label: 'Red', value: 'red' },
        { label: 'Green', value: 'green' },
        { label: 'Blue', value: 'blue' },
        { label: 'Alpha', value: 'alpha' },
        { label: 'Luminance', value: 'luminance' }
      ], animatable: false },
      { name: 'Max Vertical', type: 'number', defaultValue: 0, min: -4000, max: 4000, animatable: true }
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
      { name: 'Color B', type: 'color', defaultValue: { r: 255, g: 128, b: 0, a: 1 }, animatable: true }
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
    id: `effect-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
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
    id: `effect-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
    effectKey: definitionKey,
    name: def.name,
    category: def.category,
    enabled: true,
    expanded: true,
    parameters
  };
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
