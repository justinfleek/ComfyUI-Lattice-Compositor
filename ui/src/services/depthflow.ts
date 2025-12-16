/**
 * Depthflow Parallax System
 *
 * Creates 2.5D parallax animation from image + depth map.
 * Matches akatz-ai/ComfyUI-Depthflow-Nodes functionality.
 *
 * Enhanced with stackable motion components (Depthflow-style).
 */

import { renderLogger } from '@/utils/logger';

// ============================================================================
// Motion Component Types (Depthflow-style stackable effects)
// ============================================================================

export type MotionType = 'linear' | 'exponential' | 'sine' | 'cosine' | 'arc' | 'setTarget' | 'bounce' | 'elastic';

export type MotionParameter = 'zoom' | 'offsetX' | 'offsetY' | 'rotation' | 'depthScale' | 'focusDepth';

export type EasingType = 'linear' | 'ease-in' | 'ease-out' | 'ease-in-out' | 'bounce' | 'elastic' | 'back';

export interface MotionComponent {
  id: string;
  type: MotionType;
  parameter: MotionParameter;
  startValue: number;
  endValue: number;
  startFrame: number;      // Relative to layer start
  endFrame: number;        // Relative to layer start
  easing: EasingType;
  amplitude?: number;      // For sine/cosine/arc
  frequency?: number;      // For sine/cosine
  loops?: number;          // Number of cycles
  phase?: number;          // Starting phase (0-1)
  enabled: boolean;
}

export interface DOFConfig {
  enabled: boolean;
  focusDepth: number;      // 0-1, depth value to focus on
  aperture: number;        // Blur strength
  bokehShape: 'circle' | 'hexagon' | 'heart';
  bokehSize: number;
}

export interface DepthflowEnhanced {
  motions: MotionComponent[];
  dof: DOFConfig;
  vignette: number;        // 0-1, edge darkening
  quality: number;         // 1-100
  ssaa: number;            // 0-2 supersampling
  tilingMode: 'none' | 'repeat' | 'mirror';
}

// ============================================================================
// Types
// ============================================================================

export type DepthflowPreset =
  | 'static'
  | 'zoom_in'
  | 'zoom_out'
  | 'dolly_zoom_in'
  | 'dolly_zoom_out'
  | 'pan_left'
  | 'pan_right'
  | 'pan_up'
  | 'pan_down'
  | 'circle_cw'
  | 'circle_ccw'
  | 'horizontal_swing'
  | 'vertical_swing'
  | 'custom';

export interface DepthflowConfig {
  preset: DepthflowPreset;
  zoom: number;
  offsetX: number;
  offsetY: number;
  rotation: number;
  depthScale: number;
  focusDepth: number;
  dollyZoom: number;
  orbitRadius: number;
  orbitSpeed: number;
  swingAmplitude: number;
  swingFrequency: number;
  edgeDilation: number;
  inpaintEdges: boolean;
}

export interface DepthflowState {
  config: DepthflowConfig;
  currentFrame: number;
  totalFrames: number;
}

// ============================================================================
// Default Configuration
// ============================================================================

export function createDefaultDepthflowConfig(): DepthflowConfig {
  return {
    preset: 'static',
    zoom: 1.0,
    offsetX: 0,
    offsetY: 0,
    rotation: 0,
    depthScale: 1.0,
    focusDepth: 0.5,
    dollyZoom: 0,
    orbitRadius: 0.1,
    orbitSpeed: 2,
    swingAmplitude: 0.1,
    swingFrequency: 0.5,
    edgeDilation: 5,
    inpaintEdges: true
  };
}

export function createDefaultDOFConfig(): DOFConfig {
  return {
    enabled: false,
    focusDepth: 0.5,
    aperture: 2.8,
    bokehShape: 'circle',
    bokehSize: 1.0
  };
}

export function createDefaultEnhancedConfig(): DepthflowEnhanced {
  return {
    motions: [],
    dof: createDefaultDOFConfig(),
    vignette: 0,
    quality: 80,
    ssaa: 1,
    tilingMode: 'none'
  };
}

// ============================================================================
// Motion Component Functions
// ============================================================================

let motionIdCounter = 0;

export function createMotionComponent(overrides?: Partial<MotionComponent>): MotionComponent {
  return {
    id: `motion_${++motionIdCounter}`,
    type: 'linear',
    parameter: 'zoom',
    startValue: 1.0,
    endValue: 1.2,
    startFrame: 0,
    endFrame: 30,
    easing: 'ease-in-out',
    enabled: true,
    ...overrides
  };
}

/**
 * Apply easing function to normalized time
 */
export function applyEasing(t: number, easing: EasingType): number {
  switch (easing) {
    case 'linear':
      return t;

    case 'ease-in':
      return t * t;

    case 'ease-out':
      return 1 - (1 - t) * (1 - t);

    case 'ease-in-out':
      return t < 0.5
        ? 2 * t * t
        : 1 - Math.pow(-2 * t + 2, 2) / 2;

    case 'bounce': {
      const n1 = 7.5625;
      const d1 = 2.75;
      if (t < 1 / d1) {
        return n1 * t * t;
      } else if (t < 2 / d1) {
        return n1 * (t -= 1.5 / d1) * t + 0.75;
      } else if (t < 2.5 / d1) {
        return n1 * (t -= 2.25 / d1) * t + 0.9375;
      } else {
        return n1 * (t -= 2.625 / d1) * t + 0.984375;
      }
    }

    case 'elastic': {
      const c4 = (2 * Math.PI) / 3;
      return t === 0
        ? 0
        : t === 1
        ? 1
        : Math.pow(2, -10 * t) * Math.sin((t * 10 - 0.75) * c4) + 1;
    }

    case 'back': {
      const c1 = 1.70158;
      const c3 = c1 + 1;
      return 1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2);
    }

    default:
      return t;
  }
}

/**
 * Evaluate a single motion component at a specific frame
 */
export function evaluateMotionComponent(
  motion: MotionComponent,
  frame: number
): number | null {
  if (!motion.enabled) return null;

  // Check if frame is within motion range
  if (frame < motion.startFrame || frame > motion.endFrame) {
    // Return start or end value depending on whether we're before or after
    if (frame < motion.startFrame) return motion.startValue;
    return motion.endValue;
  }

  // Calculate normalized time within motion range
  const duration = motion.endFrame - motion.startFrame;
  const localFrame = frame - motion.startFrame;
  const t = duration > 0 ? localFrame / duration : 1;

  // Apply easing
  const easedT = applyEasing(t, motion.easing);

  // Calculate value based on motion type
  switch (motion.type) {
    case 'linear':
      return motion.startValue + (motion.endValue - motion.startValue) * easedT;

    case 'exponential': {
      const ratio = motion.endValue / motion.startValue;
      return motion.startValue * Math.pow(ratio, easedT);
    }

    case 'sine': {
      const amplitude = motion.amplitude ?? (motion.endValue - motion.startValue) / 2;
      const frequency = motion.frequency ?? 1;
      const phase = motion.phase ?? 0;
      const loops = motion.loops ?? 1;
      const baseValue = (motion.startValue + motion.endValue) / 2;
      return baseValue + amplitude * Math.sin((easedT * loops + phase) * Math.PI * 2 * frequency);
    }

    case 'cosine': {
      const amplitude = motion.amplitude ?? (motion.endValue - motion.startValue) / 2;
      const frequency = motion.frequency ?? 1;
      const phase = motion.phase ?? 0;
      const loops = motion.loops ?? 1;
      const baseValue = (motion.startValue + motion.endValue) / 2;
      return baseValue + amplitude * Math.cos((easedT * loops + phase) * Math.PI * 2 * frequency);
    }

    case 'arc': {
      // Arc motion: follows a curved path
      const amplitude = motion.amplitude ?? 1;
      const midValue = (motion.startValue + motion.endValue) / 2;
      const range = motion.endValue - motion.startValue;
      // Parabolic arc
      const arcOffset = amplitude * 4 * easedT * (1 - easedT);
      return motion.startValue + range * easedT + arcOffset;
    }

    case 'setTarget':
      // Instant jump to end value at start frame
      return frame >= motion.startFrame ? motion.endValue : motion.startValue;

    case 'bounce': {
      // Bouncy transition
      const baseValue = motion.startValue + (motion.endValue - motion.startValue) * easedT;
      const bounceDecay = Math.exp(-easedT * 5);
      const bounce = Math.sin(easedT * Math.PI * 4) * bounceDecay * 0.2;
      return baseValue * (1 + bounce);
    }

    case 'elastic': {
      // Elastic overshoot
      const baseValue = motion.startValue + (motion.endValue - motion.startValue) * easedT;
      if (easedT === 0 || easedT === 1) return baseValue;
      const elasticDecay = Math.exp(-easedT * 3);
      const elastic = Math.sin(easedT * Math.PI * 6) * elasticDecay * 0.3;
      return baseValue * (1 + elastic);
    }

    default:
      return motion.startValue + (motion.endValue - motion.startValue) * easedT;
  }
}

/**
 * Evaluate all motion components for a parameter and combine them
 */
export function evaluateMotionsForParameter(
  motions: MotionComponent[],
  parameter: MotionParameter,
  frame: number,
  baseValue: number
): number {
  const parameterMotions = motions.filter(m => m.parameter === parameter && m.enabled);

  if (parameterMotions.length === 0) {
    return baseValue;
  }

  // Combine all motion values additively (relative to base)
  let result = baseValue;

  for (const motion of parameterMotions) {
    const value = evaluateMotionComponent(motion, frame);
    if (value !== null) {
      // Calculate delta from start value and add to result
      const delta = value - motion.startValue;
      result += delta;
    }
  }

  return result;
}

/**
 * Get all animated values for a frame from motion components
 */
export function evaluateAllMotions(
  motions: MotionComponent[],
  frame: number,
  baseConfig: DepthflowConfig
): {
  zoom: number;
  offsetX: number;
  offsetY: number;
  rotation: number;
  depthScale: number;
  focusDepth: number;
} {
  return {
    zoom: evaluateMotionsForParameter(motions, 'zoom', frame, baseConfig.zoom),
    offsetX: evaluateMotionsForParameter(motions, 'offsetX', frame, baseConfig.offsetX),
    offsetY: evaluateMotionsForParameter(motions, 'offsetY', frame, baseConfig.offsetY),
    rotation: evaluateMotionsForParameter(motions, 'rotation', frame, baseConfig.rotation),
    depthScale: evaluateMotionsForParameter(motions, 'depthScale', frame, baseConfig.depthScale),
    focusDepth: evaluateMotionsForParameter(motions, 'focusDepth', frame, baseConfig.focusDepth),
  };
}

// ============================================================================
// Motion Presets
// ============================================================================

export const MOTION_PRESETS: Record<string, MotionComponent[]> = {
  // Gentle zoom in
  'zoom_in_gentle': [
    createMotionComponent({
      type: 'linear',
      parameter: 'zoom',
      startValue: 1.0,
      endValue: 1.15,
      easing: 'ease-in-out'
    })
  ],

  // Ken Burns effect
  'ken_burns': [
    createMotionComponent({
      type: 'linear',
      parameter: 'zoom',
      startValue: 1.0,
      endValue: 1.2,
      easing: 'ease-out'
    }),
    createMotionComponent({
      type: 'linear',
      parameter: 'offsetX',
      startValue: -0.1,
      endValue: 0.1,
      easing: 'ease-in-out'
    })
  ],

  // Vertigo (dolly zoom)
  'vertigo': [
    createMotionComponent({
      type: 'linear',
      parameter: 'zoom',
      startValue: 1.0,
      endValue: 1.5,
      easing: 'ease-in'
    }),
    createMotionComponent({
      type: 'linear',
      parameter: 'depthScale',
      startValue: 1.0,
      endValue: 0.3,
      easing: 'ease-in'
    })
  ],

  // Breathing effect
  'breathing': [
    createMotionComponent({
      type: 'sine',
      parameter: 'zoom',
      startValue: 1.0,
      endValue: 1.0,
      amplitude: 0.03,
      frequency: 0.5,
      loops: 2,
      easing: 'linear'
    }),
    createMotionComponent({
      type: 'cosine',
      parameter: 'depthScale',
      startValue: 1.0,
      endValue: 1.0,
      amplitude: 0.1,
      frequency: 0.5,
      loops: 2,
      easing: 'linear'
    })
  ],

  // Swing left to right
  'swing_horizontal': [
    createMotionComponent({
      type: 'sine',
      parameter: 'offsetX',
      startValue: 0,
      endValue: 0,
      amplitude: 0.15,
      frequency: 1,
      loops: 1,
      easing: 'linear'
    })
  ],

  // Circular orbit
  'orbit': [
    createMotionComponent({
      type: 'sine',
      parameter: 'offsetX',
      startValue: 0,
      endValue: 0,
      amplitude: 0.1,
      frequency: 1,
      loops: 1,
      phase: 0,
      easing: 'linear'
    }),
    createMotionComponent({
      type: 'cosine',
      parameter: 'offsetY',
      startValue: 0,
      endValue: 0,
      amplitude: 0.1,
      frequency: 1,
      loops: 1,
      phase: 0,
      easing: 'linear'
    })
  ],

  // Focus pull (rack focus)
  'rack_focus': [
    createMotionComponent({
      type: 'linear',
      parameter: 'focusDepth',
      startValue: 0.2,
      endValue: 0.8,
      easing: 'ease-in-out'
    })
  ],

  // Dramatic reveal
  'reveal': [
    createMotionComponent({
      type: 'exponential',
      parameter: 'zoom',
      startValue: 1.5,
      endValue: 1.0,
      easing: 'ease-out'
    }),
    createMotionComponent({
      type: 'linear',
      parameter: 'depthScale',
      startValue: 0.5,
      endValue: 1.0,
      easing: 'ease-out'
    })
  ],

  // Tilt shift simulation
  'tilt_shift': [
    createMotionComponent({
      type: 'sine',
      parameter: 'focusDepth',
      startValue: 0.5,
      endValue: 0.5,
      amplitude: 0.3,
      frequency: 0.25,
      loops: 1,
      easing: 'linear'
    })
  ]
};

/**
 * Apply a motion preset with custom duration
 */
export function applyMotionPreset(
  presetName: string,
  startFrame: number,
  duration: number
): MotionComponent[] {
  const preset = MOTION_PRESETS[presetName];
  if (!preset) return [];

  return preset.map(motion => ({
    ...motion,
    id: `motion_${++motionIdCounter}`,
    startFrame,
    endFrame: startFrame + duration
  }));
}

/**
 * Get available motion preset names
 */
export function getMotionPresetNames(): string[] {
  return Object.keys(MOTION_PRESETS);
}

/**
 * Get description for a motion preset
 */
export function getMotionPresetDescription(presetName: string): string {
  const descriptions: Record<string, string> = {
    'zoom_in_gentle': 'Smooth zoom in effect',
    'ken_burns': 'Classic documentary-style pan and zoom',
    'vertigo': 'Hitchcock-style dolly zoom (background changes size)',
    'breathing': 'Subtle pulsing effect that simulates breathing',
    'swing_horizontal': 'Gentle left-right swinging motion',
    'orbit': 'Circular orbiting motion around center',
    'rack_focus': 'Shift focus from foreground to background',
    'reveal': 'Dramatic zoom-out reveal',
    'tilt_shift': 'Animated miniature/tilt-shift focus effect'
  };

  return descriptions[presetName] || 'Custom motion effect';
}

// ============================================================================
// WebGL Shaders
// ============================================================================

const VERTEX_SHADER = `#version 300 es
in vec2 a_position;
in vec2 a_texCoord;
out vec2 v_texCoord;

void main() {
  gl_Position = vec4(a_position, 0.0, 1.0);
  v_texCoord = a_texCoord;
}
`;

const FRAGMENT_SHADER = `#version 300 es
precision highp float;

in vec2 v_texCoord;
out vec4 outColor;

uniform sampler2D u_source;
uniform sampler2D u_depth;
uniform float u_zoom;
uniform vec2 u_offset;
uniform float u_rotation;
uniform float u_depthScale;
uniform float u_focusDepth;
uniform float u_edgeDilation;
uniform vec2 u_resolution;

vec2 rotate2D(vec2 p, float angle) {
  float c = cos(angle);
  float s = sin(angle);
  return vec2(p.x * c - p.y * s, p.x * s + p.y * c);
}

void main() {
  // Get depth at current pixel
  float depth = texture(u_depth, v_texCoord).r;

  // Calculate parallax offset based on depth
  // Objects closer than focus depth move more, objects further move less
  float depthDiff = (depth - u_focusDepth) * u_depthScale;

  // Transform texture coordinates
  vec2 center = vec2(0.5, 0.5);
  vec2 coord = v_texCoord - center;

  // Apply rotation
  float rotRad = u_rotation * 3.14159265 / 180.0;
  coord = rotate2D(coord, rotRad);

  // Apply zoom
  coord /= u_zoom;

  // Apply parallax offset based on depth
  vec2 parallaxOffset = u_offset * depthDiff;
  coord += parallaxOffset;

  // Apply camera offset
  coord -= u_offset * 0.5;

  coord += center;

  // Edge handling with dilation
  float dilatePixels = u_edgeDilation / u_resolution.x;

  // Clamp coordinates
  vec2 clampedCoord = clamp(coord, vec2(dilatePixels), vec2(1.0 - dilatePixels));

  // Check if we're sampling outside bounds
  float outOfBounds = step(0.0, coord.x) * step(coord.x, 1.0) *
                      step(0.0, coord.y) * step(coord.y, 1.0);

  // Sample source texture
  vec4 color = texture(u_source, clampedCoord);

  // Fade edges if out of bounds
  if (outOfBounds < 0.5) {
    // Sample from clamped position with reduced alpha
    color = texture(u_source, clampedCoord);
    color.a *= 0.3;
  }

  outColor = color;
}
`;

// ============================================================================
// Depthflow Renderer Class
// ============================================================================

export class DepthflowRenderer {
  private sourceCanvas: HTMLCanvasElement;
  private depthCanvas: HTMLCanvasElement;
  private outputCanvas: HTMLCanvasElement;
  private gl: WebGL2RenderingContext | null = null;
  private program: WebGLProgram | null = null;
  private useWebGL: boolean = false;

  // WebGL resources
  private sourceTexture: WebGLTexture | null = null;
  private depthTexture: WebGLTexture | null = null;
  private positionBuffer: WebGLBuffer | null = null;
  private texCoordBuffer: WebGLBuffer | null = null;

  // Uniform locations
  private uniforms: Record<string, WebGLUniformLocation | null> = {};

  // Current config
  private config: DepthflowConfig = createDefaultDepthflowConfig();

  // Source dimensions
  private width: number = 0;
  private height: number = 0;

  constructor() {
    this.sourceCanvas = document.createElement('canvas');
    this.depthCanvas = document.createElement('canvas');
    this.outputCanvas = document.createElement('canvas');

    this.initWebGL();
  }

  private initWebGL(): void {
    const gl = this.outputCanvas.getContext('webgl2', {
      premultipliedAlpha: false,
      preserveDrawingBuffer: true
    });

    if (!gl) {
      renderLogger.warn('Depthflow: WebGL2 not available, using Canvas2D fallback');
      this.useWebGL = false;
      return;
    }

    this.gl = gl;
    this.useWebGL = true;

    // Create shader program
    const vertexShader = this.compileShader(gl, gl.VERTEX_SHADER, VERTEX_SHADER);
    const fragmentShader = this.compileShader(gl, gl.FRAGMENT_SHADER, FRAGMENT_SHADER);

    if (!vertexShader || !fragmentShader) {
      this.useWebGL = false;
      return;
    }

    const program = gl.createProgram()!;
    gl.attachShader(program, vertexShader);
    gl.attachShader(program, fragmentShader);
    gl.linkProgram(program);

    if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
      renderLogger.error('Depthflow: Program link error:', gl.getProgramInfoLog(program));
      this.useWebGL = false;
      return;
    }

    this.program = program;

    // Get uniform locations
    this.uniforms = {
      u_source: gl.getUniformLocation(program, 'u_source'),
      u_depth: gl.getUniformLocation(program, 'u_depth'),
      u_zoom: gl.getUniformLocation(program, 'u_zoom'),
      u_offset: gl.getUniformLocation(program, 'u_offset'),
      u_rotation: gl.getUniformLocation(program, 'u_rotation'),
      u_depthScale: gl.getUniformLocation(program, 'u_depthScale'),
      u_focusDepth: gl.getUniformLocation(program, 'u_focusDepth'),
      u_edgeDilation: gl.getUniformLocation(program, 'u_edgeDilation'),
      u_resolution: gl.getUniformLocation(program, 'u_resolution')
    };

    // Create buffers
    this.positionBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, this.positionBuffer);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([
      -1, -1,  1, -1,  -1, 1,
      -1, 1,   1, -1,   1, 1
    ]), gl.STATIC_DRAW);

    this.texCoordBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, this.texCoordBuffer);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([
      0, 1,  1, 1,  0, 0,
      0, 0,  1, 1,  1, 0
    ]), gl.STATIC_DRAW);
  }

  private compileShader(gl: WebGL2RenderingContext, type: number, source: string): WebGLShader | null {
    const shader = gl.createShader(type)!;
    gl.shaderSource(shader, source);
    gl.compileShader(shader);

    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
      renderLogger.error('Depthflow: Shader compile error:', gl.getShaderInfoLog(shader));
      gl.deleteShader(shader);
      return null;
    }

    return shader;
  }

  setSource(image: ImageData | HTMLImageElement | HTMLCanvasElement): void {
    if (image instanceof ImageData) {
      this.sourceCanvas.width = image.width;
      this.sourceCanvas.height = image.height;
      const ctx = this.sourceCanvas.getContext('2d')!;
      ctx.putImageData(image, 0, 0);
    } else {
      this.sourceCanvas.width = image.width;
      this.sourceCanvas.height = image.height;
      const ctx = this.sourceCanvas.getContext('2d')!;
      ctx.drawImage(image, 0, 0);
    }

    this.width = this.sourceCanvas.width;
    this.height = this.sourceCanvas.height;
    this.outputCanvas.width = this.width;
    this.outputCanvas.height = this.height;

    if (this.useWebGL && this.gl) {
      this.updateTexture('source');
    }
  }

  setDepthMap(depth: ImageData | HTMLImageElement | HTMLCanvasElement): void {
    if (depth instanceof ImageData) {
      this.depthCanvas.width = depth.width;
      this.depthCanvas.height = depth.height;
      const ctx = this.depthCanvas.getContext('2d')!;
      ctx.putImageData(depth, 0, 0);
    } else {
      this.depthCanvas.width = depth.width;
      this.depthCanvas.height = depth.height;
      const ctx = this.depthCanvas.getContext('2d')!;
      ctx.drawImage(depth, 0, 0);
    }

    if (this.useWebGL && this.gl) {
      this.updateTexture('depth');
    }
  }

  private updateTexture(which: 'source' | 'depth'): void {
    const gl = this.gl!;
    const canvas = which === 'source' ? this.sourceCanvas : this.depthCanvas;

    if (which === 'source') {
      if (this.sourceTexture) gl.deleteTexture(this.sourceTexture);
      this.sourceTexture = gl.createTexture();
      gl.activeTexture(gl.TEXTURE0);
      gl.bindTexture(gl.TEXTURE_2D, this.sourceTexture);
    } else {
      if (this.depthTexture) gl.deleteTexture(this.depthTexture);
      this.depthTexture = gl.createTexture();
      gl.activeTexture(gl.TEXTURE1);
      gl.bindTexture(gl.TEXTURE_2D, this.depthTexture);
    }

    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, canvas);
  }

  setConfig(config: Partial<DepthflowConfig>): void {
    this.config = { ...this.config, ...config };
  }

  getConfig(): DepthflowConfig {
    return { ...this.config };
  }

  /**
   * Get animated camera parameters for a specific frame based on preset
   */
  private getAnimatedParams(frame: number, totalFrames: number): {
    zoom: number;
    offsetX: number;
    offsetY: number;
    rotation: number;
    depthScale: number;
  } {
    const progress = totalFrames > 1 ? frame / (totalFrames - 1) : 0;
    const { preset, orbitRadius, orbitSpeed, swingAmplitude, swingFrequency } = this.config;

    let zoom = this.config.zoom;
    let offsetX = this.config.offsetX;
    let offsetY = this.config.offsetY;
    let rotation = this.config.rotation;
    let depthScale = this.config.depthScale;

    switch (preset) {
      case 'static':
        // No animation
        break;

      case 'zoom_in':
        zoom = 1.0 + progress * 0.3;
        break;

      case 'zoom_out':
        zoom = 1.0 - progress * 0.3;
        break;

      case 'dolly_zoom_in':
        // Vertigo effect: zoom in while decreasing depth scale
        zoom = 1.0 + progress * 0.4;
        depthScale = this.config.depthScale * (1.0 - progress * 0.5);
        break;

      case 'dolly_zoom_out':
        // Reverse vertigo
        zoom = 1.0 - progress * 0.3;
        depthScale = this.config.depthScale * (1.0 + progress * 0.5);
        break;

      case 'pan_left':
        offsetX = -progress * 0.3;
        break;

      case 'pan_right':
        offsetX = progress * 0.3;
        break;

      case 'pan_up':
        offsetY = -progress * 0.3;
        break;

      case 'pan_down':
        offsetY = progress * 0.3;
        break;

      case 'circle_cw': {
        const angle = progress * Math.PI * 2 * (orbitSpeed / 360);
        offsetX = Math.cos(angle) * orbitRadius;
        offsetY = Math.sin(angle) * orbitRadius;
        break;
      }

      case 'circle_ccw': {
        const angle = -progress * Math.PI * 2 * (orbitSpeed / 360);
        offsetX = Math.cos(angle) * orbitRadius;
        offsetY = Math.sin(angle) * orbitRadius;
        break;
      }

      case 'horizontal_swing':
        offsetX = Math.sin(progress * Math.PI * 2 * swingFrequency) * swingAmplitude;
        break;

      case 'vertical_swing':
        offsetY = Math.sin(progress * Math.PI * 2 * swingFrequency) * swingAmplitude;
        break;

      case 'custom':
        // Use config values directly (allow keyframe animation)
        break;
    }

    return { zoom, offsetX, offsetY, rotation, depthScale };
  }

  renderFrame(frame: number, totalFrames: number): ImageData {
    const params = this.getAnimatedParams(frame, totalFrames);

    if (this.useWebGL && this.gl && this.program) {
      return this.renderWebGL(params);
    } else {
      return this.renderCanvas2D(params);
    }
  }

  private renderWebGL(params: {
    zoom: number;
    offsetX: number;
    offsetY: number;
    rotation: number;
    depthScale: number;
  }): ImageData {
    const gl = this.gl!;

    gl.viewport(0, 0, this.width, this.height);
    gl.useProgram(this.program);

    // Bind textures
    gl.activeTexture(gl.TEXTURE0);
    gl.bindTexture(gl.TEXTURE_2D, this.sourceTexture);
    gl.uniform1i(this.uniforms.u_source, 0);

    gl.activeTexture(gl.TEXTURE1);
    gl.bindTexture(gl.TEXTURE_2D, this.depthTexture);
    gl.uniform1i(this.uniforms.u_depth, 1);

    // Set uniforms
    gl.uniform1f(this.uniforms.u_zoom, params.zoom);
    gl.uniform2f(this.uniforms.u_offset, params.offsetX, params.offsetY);
    gl.uniform1f(this.uniforms.u_rotation, params.rotation);
    gl.uniform1f(this.uniforms.u_depthScale, params.depthScale);
    gl.uniform1f(this.uniforms.u_focusDepth, this.config.focusDepth);
    gl.uniform1f(this.uniforms.u_edgeDilation, this.config.edgeDilation);
    gl.uniform2f(this.uniforms.u_resolution, this.width, this.height);

    // Bind position attribute
    const positionLoc = gl.getAttribLocation(this.program!, 'a_position');
    gl.bindBuffer(gl.ARRAY_BUFFER, this.positionBuffer);
    gl.enableVertexAttribArray(positionLoc);
    gl.vertexAttribPointer(positionLoc, 2, gl.FLOAT, false, 0, 0);

    // Bind texcoord attribute
    const texCoordLoc = gl.getAttribLocation(this.program!, 'a_texCoord');
    gl.bindBuffer(gl.ARRAY_BUFFER, this.texCoordBuffer);
    gl.enableVertexAttribArray(texCoordLoc);
    gl.vertexAttribPointer(texCoordLoc, 2, gl.FLOAT, false, 0, 0);

    // Draw
    gl.drawArrays(gl.TRIANGLES, 0, 6);

    // Read pixels
    const pixels = new Uint8ClampedArray(this.width * this.height * 4);
    gl.readPixels(0, 0, this.width, this.height, gl.RGBA, gl.UNSIGNED_BYTE, pixels);

    // Flip Y (WebGL has inverted Y)
    const flipped = new Uint8ClampedArray(pixels.length);
    for (let y = 0; y < this.height; y++) {
      const srcRow = (this.height - 1 - y) * this.width * 4;
      const dstRow = y * this.width * 4;
      flipped.set(pixels.subarray(srcRow, srcRow + this.width * 4), dstRow);
    }

    return new ImageData(flipped, this.width, this.height);
  }

  private renderCanvas2D(params: {
    zoom: number;
    offsetX: number;
    offsetY: number;
    rotation: number;
    depthScale: number;
  }): ImageData {
    const ctx = this.outputCanvas.getContext('2d')!;
    const sourceCtx = this.sourceCanvas.getContext('2d')!;
    const depthCtx = this.depthCanvas.getContext('2d')!;

    const sourceData = sourceCtx.getImageData(0, 0, this.width, this.height);
    const depthData = depthCtx.getImageData(0, 0, this.width, this.height);
    const outputData = ctx.createImageData(this.width, this.height);

    const { zoom, offsetX, offsetY, rotation, depthScale } = params;
    const { focusDepth } = this.config;
    const rotRad = (rotation * Math.PI) / 180;
    const cosR = Math.cos(rotRad);
    const sinR = Math.sin(rotRad);

    for (let y = 0; y < this.height; y++) {
      for (let x = 0; x < this.width; x++) {
        const idx = (y * this.width + x) * 4;

        // Get depth value (0-1)
        const depth = depthData.data[idx] / 255;
        const depthDiff = (depth - focusDepth) * depthScale;

        // Calculate source coordinates
        let sx = (x / this.width - 0.5);
        let sy = (y / this.height - 0.5);

        // Apply rotation
        const rx = sx * cosR - sy * sinR;
        const ry = sx * sinR + sy * cosR;
        sx = rx;
        sy = ry;

        // Apply zoom
        sx /= zoom;
        sy /= zoom;

        // Apply parallax offset
        sx += offsetX * depthDiff;
        sy += offsetY * depthDiff;

        // Apply camera offset
        sx -= offsetX * 0.5;
        sy -= offsetY * 0.5;

        // Convert back to pixel coordinates
        sx = (sx + 0.5) * this.width;
        sy = (sy + 0.5) * this.height;

        // Bilinear sampling
        const x0 = Math.floor(sx);
        const y0 = Math.floor(sy);
        const x1 = x0 + 1;
        const y1 = y0 + 1;
        const fx = sx - x0;
        const fy = sy - y0;

        // Clamp coordinates
        const cx0 = Math.max(0, Math.min(this.width - 1, x0));
        const cy0 = Math.max(0, Math.min(this.height - 1, y0));
        const cx1 = Math.max(0, Math.min(this.width - 1, x1));
        const cy1 = Math.max(0, Math.min(this.height - 1, y1));

        // Sample 4 pixels
        const i00 = (cy0 * this.width + cx0) * 4;
        const i10 = (cy0 * this.width + cx1) * 4;
        const i01 = (cy1 * this.width + cx0) * 4;
        const i11 = (cy1 * this.width + cx1) * 4;

        // Bilinear interpolation
        for (let c = 0; c < 4; c++) {
          const v00 = sourceData.data[i00 + c];
          const v10 = sourceData.data[i10 + c];
          const v01 = sourceData.data[i01 + c];
          const v11 = sourceData.data[i11 + c];

          const v0 = v00 * (1 - fx) + v10 * fx;
          const v1 = v01 * (1 - fx) + v11 * fx;
          outputData.data[idx + c] = Math.round(v0 * (1 - fy) + v1 * fy);
        }

        // Handle out of bounds
        if (sx < 0 || sx >= this.width || sy < 0 || sy >= this.height) {
          outputData.data[idx + 3] = Math.round(outputData.data[idx + 3] * 0.3);
        }
      }
    }

    ctx.putImageData(outputData, 0, 0);
    return outputData;
  }

  renderSequence(totalFrames: number, onProgress?: (frame: number) => void): ImageData[] {
    const frames: ImageData[] = [];

    for (let i = 0; i < totalFrames; i++) {
      frames.push(this.renderFrame(i, totalFrames));
      if (onProgress) {
        onProgress(i);
      }
    }

    return frames;
  }

  /**
   * Get preset configuration with optional intensity modifier
   */
  getPresetConfig(preset: DepthflowPreset, intensity: number = 1.0): Partial<DepthflowConfig> {
    const base: Partial<DepthflowConfig> = { preset };

    switch (preset) {
      case 'zoom_in':
      case 'zoom_out':
        return { ...base, depthScale: 1.0 * intensity };

      case 'dolly_zoom_in':
      case 'dolly_zoom_out':
        return { ...base, depthScale: 1.5 * intensity, dollyZoom: 0.5 * intensity };

      case 'pan_left':
      case 'pan_right':
      case 'pan_up':
      case 'pan_down':
        return { ...base, depthScale: 0.8 * intensity };

      case 'circle_cw':
      case 'circle_ccw':
        return { ...base, orbitRadius: 0.1 * intensity, orbitSpeed: 360 };

      case 'horizontal_swing':
      case 'vertical_swing':
        return { ...base, swingAmplitude: 0.1 * intensity, swingFrequency: 1 };

      default:
        return base;
    }
  }

  getOutputCanvas(): HTMLCanvasElement {
    return this.outputCanvas;
  }

  dispose(): void {
    if (this.gl) {
      if (this.sourceTexture) this.gl.deleteTexture(this.sourceTexture);
      if (this.depthTexture) this.gl.deleteTexture(this.depthTexture);
      if (this.positionBuffer) this.gl.deleteBuffer(this.positionBuffer);
      if (this.texCoordBuffer) this.gl.deleteBuffer(this.texCoordBuffer);
      if (this.program) this.gl.deleteProgram(this.program);
    }

    this.sourceTexture = null;
    this.depthTexture = null;
    this.positionBuffer = null;
    this.texCoordBuffer = null;
    this.program = null;
    this.gl = null;
  }
}

// ============================================================================
// Depth Slicer (from Eden pipelines)
// ============================================================================

export interface DepthSliceConfig {
  numSlices: number;          // K-means clusters (2-10)
  sliceIndex: number;         // Which slice to isolate (0 to numSlices-1)
  featherAmount: number;      // Edge softness in pixels
}

/**
 * K-means clustering on depth map to create region masks
 * Like Eden's DepthSlicer node
 */
export function createDepthSliceMask(
  depthMap: ImageData,
  config: DepthSliceConfig
): ImageData {
  const { numSlices, sliceIndex, featherAmount } = config;
  const { width, height, data } = depthMap;

  // Extract depth values (grayscale from R channel or luminance)
  const depthValues: number[] = [];
  for (let i = 0; i < data.length; i += 4) {
    // Use luminance formula for depth
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    const depth = (r * 0.299 + g * 0.587 + b * 0.114) / 255;
    depthValues.push(depth);
  }

  // Perform K-means clustering
  const clusterCenters = kMeansClustering(depthValues, numSlices);

  // Sort cluster centers by depth value (ascending)
  clusterCenters.sort((a, b) => a - b);

  // Get the range for the selected slice
  const sliceMin = sliceIndex === 0 ? 0 : clusterCenters[sliceIndex - 1];
  const sliceMax = sliceIndex < clusterCenters.length ? clusterCenters[sliceIndex] : 1;

  // Create mask with feathering
  const canvas = new OffscreenCanvas(width, height);
  const ctx = canvas.getContext('2d')!;
  const outputImageData = ctx.createImageData(width, height);
  const outputData = outputImageData.data;

  for (let i = 0; i < depthValues.length; i++) {
    const depth = depthValues[i];

    // Calculate distance to slice range
    let maskValue: number;

    if (depth >= sliceMin && depth <= sliceMax) {
      // Inside slice - full white
      maskValue = 255;
    } else {
      // Outside slice - calculate feather falloff
      const distanceToSlice = depth < sliceMin
        ? sliceMin - depth
        : depth - sliceMax;

      // Convert featherAmount from pixels to depth units (approximate)
      const featherDepth = featherAmount / Math.max(width, height);

      if (distanceToSlice < featherDepth) {
        // Within feather zone
        maskValue = 255 * (1 - distanceToSlice / featherDepth);
      } else {
        maskValue = 0;
      }
    }

    const pixelIndex = i * 4;
    outputData[pixelIndex] = maskValue;
    outputData[pixelIndex + 1] = maskValue;
    outputData[pixelIndex + 2] = maskValue;
    outputData[pixelIndex + 3] = 255;
  }

  // Apply Gaussian blur for smoother feathering if featherAmount > 0
  if (featherAmount > 0) {
    return applyGaussianBlur(outputImageData, Math.ceil(featherAmount / 2));
  }

  return outputImageData;
}

/**
 * K-means clustering algorithm
 */
function kMeansClustering(values: number[], k: number, maxIterations: number = 50): number[] {
  // Initialize cluster centers evenly spaced
  let centers: number[] = [];
  for (let i = 0; i < k; i++) {
    centers.push((i + 0.5) / k);
  }

  // Iteratively update centers
  for (let iter = 0; iter < maxIterations; iter++) {
    // Assign each value to nearest center
    const assignments: number[][] = Array.from({ length: k }, () => []);

    for (const value of values) {
      let nearestCenter = 0;
      let nearestDist = Math.abs(value - centers[0]);

      for (let c = 1; c < k; c++) {
        const dist = Math.abs(value - centers[c]);
        if (dist < nearestDist) {
          nearestDist = dist;
          nearestCenter = c;
        }
      }

      assignments[nearestCenter].push(value);
    }

    // Update centers
    const newCenters: number[] = [];
    let converged = true;

    for (let c = 0; c < k; c++) {
      if (assignments[c].length > 0) {
        const mean = assignments[c].reduce((a, b) => a + b, 0) / assignments[c].length;
        newCenters.push(mean);

        if (Math.abs(mean - centers[c]) > 0.001) {
          converged = false;
        }
      } else {
        // Empty cluster - keep old center
        newCenters.push(centers[c]);
      }
    }

    centers = newCenters;

    if (converged) break;
  }

  return centers;
}

/**
 * Simple Gaussian blur implementation
 */
function applyGaussianBlur(imageData: ImageData, radius: number): ImageData {
  const { width, height, data } = imageData;
  const output = new ImageData(width, height);
  const outputData = output.data;

  // Create Gaussian kernel
  const kernelSize = radius * 2 + 1;
  const kernel: number[] = [];
  const sigma = radius / 2;
  let kernelSum = 0;

  for (let i = 0; i < kernelSize; i++) {
    const x = i - radius;
    const g = Math.exp(-(x * x) / (2 * sigma * sigma));
    kernel.push(g);
    kernelSum += g;
  }

  // Normalize kernel
  for (let i = 0; i < kernelSize; i++) {
    kernel[i] /= kernelSum;
  }

  // Temporary buffer for horizontal pass
  const temp = new Float32Array(width * height);

  // Horizontal pass
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let sum = 0;
      for (let k = 0; k < kernelSize; k++) {
        const px = Math.max(0, Math.min(width - 1, x + k - radius));
        sum += data[(y * width + px) * 4] * kernel[k];
      }
      temp[y * width + x] = sum;
    }
  }

  // Vertical pass
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let sum = 0;
      for (let k = 0; k < kernelSize; k++) {
        const py = Math.max(0, Math.min(height - 1, y + k - radius));
        sum += temp[py * width + x] * kernel[k];
      }

      const pixelIndex = (y * width + x) * 4;
      const value = Math.round(sum);
      outputData[pixelIndex] = value;
      outputData[pixelIndex + 1] = value;
      outputData[pixelIndex + 2] = value;
      outputData[pixelIndex + 3] = 255;
    }
  }

  return output;
}

/**
 * Animated depth slice - different slice per frame
 */
export function createAnimatedDepthSlice(
  depthMap: ImageData,
  numSlices: number,
  frameCount: number,
  featherAmount: number
): ImageData[] {
  const masks: ImageData[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    // Calculate which slice to show at this frame
    // Cycles through all slices over the duration
    const sliceIndex = Math.floor((frame / frameCount) * numSlices) % numSlices;

    const mask = createDepthSliceMask(depthMap, {
      numSlices,
      sliceIndex,
      featherAmount
    });

    masks.push(mask);
  }

  return masks;
}

/**
 * Get all slices as separate masks
 */
export function createAllDepthSlices(
  depthMap: ImageData,
  numSlices: number,
  featherAmount: number
): ImageData[] {
  const masks: ImageData[] = [];

  for (let sliceIndex = 0; sliceIndex < numSlices; sliceIndex++) {
    const mask = createDepthSliceMask(depthMap, {
      numSlices,
      sliceIndex,
      featherAmount
    });
    masks.push(mask);
  }

  return masks;
}

export default DepthflowRenderer;
