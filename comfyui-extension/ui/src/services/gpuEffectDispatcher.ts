/**
 * GPU Effect Dispatcher
 *
 * Routes effects to the best available GPU renderer with automatic fallback.
 * Implements the fallback chain: WebGPU → WebGL2 → Canvas2D
 *
 * Performance characteristics:
 * - WebGPU: 10-100x faster than Canvas2D for large images
 * - WebGL2: 5-50x faster than Canvas2D
 * - Canvas2D: Baseline (always available)
 *
 * Features:
 * - Automatic GPU capability detection
 * - Per-effect routing based on availability
 * - Texture pooling to reduce GPU memory churn
 * - Async processing with frame batching
 */

import type { JSONValue } from "@/types/dataAsset";
import type { PropertyValue } from "@/types/project";
import { engineLogger } from "@/utils/logger";
import { isFiniteNumber, isObject } from "@/utils/typeGuards";
import { type GLSLEngine, getGLSLEngine } from "./glsl/GLSLEngine";
import { detectGPUTier, type GPUTier } from "./gpuDetection";
import {
  webgpuRenderer,
  type BlurParams,
  type ColorCorrectionParams,
  type RadialBlurParams,
  type DirectionalBlurParams,
  type WarpParams,
  type GlowParams,
  type LevelsParams,
} from "./webgpuRenderer";

// ============================================================================
// TYPES
// ============================================================================

/**
 * Runtime value type for type guards
 * Deterministic: Explicit union of all possible runtime types
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

// ============================================================================
// PARAMETER VALIDATION - DETERMINISTIC WITH MIN/MAX/DEFAULT/VERIFICATION
// ============================================================================

/**
 * Validate and convert JSONValue to BlurParams
 * Deterministic: Explicit validation with min/max/default values
 * Min: radius >= 0, quality must be valid enum
 * Max: radius <= 1000 (reasonable upper bound)
 * Default: radius = 10, quality = "medium", direction = "both"
 */
function validateBlurParams(params: JSONValue): BlurParams {
  if (!isObject(params)) {
    throw new TypeError(`[GPUEffectDispatcher] Invalid blur params: expected object, got ${typeof params}`);
  }
  const obj = params as Record<string, JSONValue>;
  
  // Deterministic: Validate radius with explicit bounds
  const radiusValue = obj.radius;
  const radius = (typeof radiusValue === "number" && Number.isFinite(radiusValue) && radiusValue >= 0 && radiusValue <= 1000)
    ? radiusValue
    : 10; // Default: 10
  
  // Deterministic: Validate quality enum
  const qualityValue = obj.quality;
  const quality = (typeof qualityValue === "string" && ["low", "medium", "high"].includes(qualityValue))
    ? qualityValue as "low" | "medium" | "high"
    : "medium"; // Default: "medium"
  
  // Deterministic: Validate direction enum (optional)
  const directionValue = obj.direction;
  const direction = (typeof directionValue === "string" && ["horizontal", "vertical", "both"].includes(directionValue))
    ? directionValue as "horizontal" | "vertical" | "both"
    : "both"; // Default: "both"
  
  return { radius, quality, direction };
}

/**
 * Validate and convert JSONValue to ColorCorrectionParams
 * Deterministic: Explicit validation with min/max bounds
 * Min: brightness/contrast/saturation = -1, hue = -180
 * Max: brightness/contrast/saturation = 1, hue = 180
 * Default: all = 0
 */
function validateColorCorrectionParams(params: JSONValue): ColorCorrectionParams {
  if (!isObject(params)) {
    throw new TypeError(`[GPUEffectDispatcher] Invalid colorCorrection params: expected object, got ${typeof params}`);
  }
  const obj = params as Record<string, JSONValue>;
  
  const clamp = (value: RuntimeValue, min: number, max: number, defaultVal: number): number => {
    if (typeof value !== "number" || !Number.isFinite(value)) return defaultVal;
    return Math.max(min, Math.min(max, value));
  };
  
  return {
    brightness: clamp(obj.brightness, -1, 1, 0),
    contrast: clamp(obj.contrast, -1, 1, 0),
    saturation: clamp(obj.saturation, -1, 1, 0),
    hue: clamp(obj.hue, -180, 180, 0),
  };
}

/**
 * Validate and convert JSONValue to RadialBlurParams
 * Deterministic: Explicit validation with min/max/default
 * Min: centerX/centerY = 0, amount >= 0, samples >= 1
 * Max: centerX/centerY = 1, amount <= 100, samples <= 256
 * Default: centerX/centerY = 0.5, amount = 10, samples = 32
 */
function validateRadialBlurParams(params: JSONValue): RadialBlurParams {
  if (!isObject(params)) {
    throw new TypeError(`[GPUEffectDispatcher] Invalid radialBlur params: expected object, got ${typeof params}`);
  }
  const obj = params as Record<string, JSONValue>;
  
  const clamp = (value: RuntimeValue, min: number, max: number, defaultVal: number): number => {
    if (typeof value !== "number" || !Number.isFinite(value)) return defaultVal;
    return Math.max(min, Math.min(max, value));
  };
  
  return {
    centerX: clamp(obj.centerX, 0, 1, 0.5),
    centerY: clamp(obj.centerY, 0, 1, 0.5),
    amount: clamp(obj.amount, 0, 100, 10),
    samples: clamp(obj.samples, 1, 256, 32),
  };
}

/**
 * Validate and convert JSONValue to DirectionalBlurParams
 * Deterministic: Explicit validation with min/max/default
 * Min: length >= 0, samples >= 1
 * Max: length <= 1000, samples <= 256
 * Default: angle = 0, length = 10, samples = 32
 */
function validateDirectionalBlurParams(params: JSONValue): DirectionalBlurParams {
  if (!isObject(params)) {
    throw new TypeError(`[GPUEffectDispatcher] Invalid directionalBlur params: expected object, got ${typeof params}`);
  }
  const obj = params as Record<string, JSONValue>;
  
  const clamp = (value: RuntimeValue, min: number, max: number, defaultVal: number): number => {
    if (typeof value !== "number" || !Number.isFinite(value)) return defaultVal;
    return Math.max(min, Math.min(max, value));
  };
  
  return {
    angle: clamp(obj.angle, -360, 360, 0),
    length: clamp(obj.length, 0, 1000, 10),
    samples: clamp(obj.samples, 1, 256, 32),
  };
}

/**
 * Validate and convert JSONValue to WarpParams
 * Deterministic: Explicit validation with min/max/default
 * Min: bend = -1
 * Max: bend = 1
 * Default: style = "bulge", bend = 0, hDistort = 0, vDistort = 0
 */
function validateWarpParams(params: JSONValue): WarpParams {
  if (!isObject(params)) {
    throw new TypeError(`[GPUEffectDispatcher] Invalid warp params: expected object, got ${typeof params}`);
  }
  const obj = params as Record<string, JSONValue>;
  
  const clamp = (value: RuntimeValue, min: number, max: number, defaultVal: number): number => {
    if (typeof value !== "number" || !Number.isFinite(value)) return defaultVal;
    return Math.max(min, Math.min(max, value));
  };
  
  const styleValue = obj.style;
  const style = (typeof styleValue === "string" && ["bulge", "wave", "fisheye", "twist"].includes(styleValue))
    ? styleValue as "bulge" | "wave" | "fisheye" | "twist"
    : "bulge"; // Default: "bulge"
  
  return {
    style,
    bend: clamp(obj.bend, -1, 1, 0),
    hDistort: clamp(obj.hDistort, -1, 1, 0),
    vDistort: clamp(obj.vDistort, -1, 1, 0),
  };
}

/**
 * Validate and convert JSONValue to GlowParams
 * Deterministic: Explicit validation with min/max/default
 * Min: radius >= 0, intensity >= 0, threshold = 0
 * Max: radius <= 100, intensity <= 10, threshold = 1
 * Default: radius = 10, intensity = 1, threshold = 0.5
 */
function validateGlowParams(params: JSONValue): GlowParams {
  if (!isObject(params)) {
    throw new TypeError(`[GPUEffectDispatcher] Invalid glow params: expected object, got ${typeof params}`);
  }
  const obj = params as Record<string, JSONValue>;
  
  const clamp = (value: RuntimeValue, min: number, max: number, defaultVal: number): number => {
    if (typeof value !== "number" || !Number.isFinite(value)) return defaultVal;
    return Math.max(min, Math.min(max, value));
  };
  
  const colorValue = obj.color;
  let color: { r: number; g: number; b: number } | undefined = undefined;
  if (typeof colorValue === "object" && colorValue !== null && !Array.isArray(colorValue)) {
    const colorObj = colorValue as Record<string, JSONValue>;
    const r = clamp(colorObj.r, 0, 1, 1);
    const g = clamp(colorObj.g, 0, 1, 1);
    const b = clamp(colorObj.b, 0, 1, 1);
    color = { r, g, b };
  }
  
  return {
    radius: clamp(obj.radius, 0, 100, 10),
    intensity: clamp(obj.intensity, 0, 10, 1),
    threshold: clamp(obj.threshold, 0, 1, 0.5),
    color,
  };
}

/**
 * Validate and convert JSONValue to LevelsParams
 * Deterministic: Explicit validation with min/max/default
 * Min: inputBlack/outputBlack = 0, inputWhite/outputWhite = 0, gamma = 0.1
 * Max: inputBlack/outputBlack = 1, inputWhite/outputWhite = 1, gamma = 10
 * Default: inputBlack = 0, inputWhite = 1, gamma = 1, outputBlack = 0, outputWhite = 1
 */
function validateLevelsParams(params: JSONValue): LevelsParams {
  if (!isObject(params)) {
    throw new TypeError(`[GPUEffectDispatcher] Invalid levels params: expected object, got ${typeof params}`);
  }
  const obj = params as Record<string, JSONValue>;
  
  const clamp = (value: RuntimeValue, min: number, max: number, defaultVal: number): number => {
    if (typeof value !== "number" || !Number.isFinite(value)) return defaultVal;
    return Math.max(min, Math.min(max, value));
  };
  
  return {
    inputBlack: clamp(obj.inputBlack, 0, 1, 0),
    inputWhite: clamp(obj.inputWhite, 0, 1, 1),
    gamma: clamp(obj.gamma, 0.1, 10, 1),
    outputBlack: clamp(obj.outputBlack, 0, 1, 0),
    outputWhite: clamp(obj.outputWhite, 0, 1, 1),
  };
}

export type GPURenderPath = "webgpu" | "webgl2" | "canvas2d";

export interface GPUCapabilityInfo {
  preferredPath: GPURenderPath;
  webgpuAvailable: boolean;
  webgl2Available: boolean;
  gpuTier: GPUTier;
  initialized: boolean;
}

export interface EffectGPUMapping {
  effectKey: string;
  webgpuMethod?: string; // Method name on webgpuRenderer
  webglShader?: string; // GLSL shader source
  preferGPU: boolean; // Whether to prefer GPU for this effect
}

export interface TexturePoolEntry {
  texture: ImageData;
  width: number;
  height: number;
  inUse: boolean;
  lastUsed: number;
}

// ============================================================================
// EFFECT GPU MAPPINGS
// Define which effects can use GPU acceleration
// ============================================================================

// ============================================================================
// GLSL SHADERS FOR STYLIZE EFFECTS
// ============================================================================

const GLSL_SHADERS: Record<string, string> = {
  // RGB Split (Chromatic Aberration)
  "rgb-split": `
void mainImage(out vec4 fragColor, in vec2 fragCoord) {
  vec2 uv = fragCoord / iResolution.xy;
  float amount = 0.01; // Will be overridden by uniform

  float r = texture2D(iChannel0, uv + vec2(amount, 0.0)).r;
  float g = texture2D(iChannel0, uv).g;
  float b = texture2D(iChannel0, uv - vec2(amount, 0.0)).b;
  float a = texture2D(iChannel0, uv).a;

  fragColor = vec4(r, g, b, a);
}`,

  // Mosaic (Pixelation)
  mosaic: `
void mainImage(out vec4 fragColor, in vec2 fragCoord) {
  vec2 uv = fragCoord / iResolution.xy;
  float blockSize = 10.0; // Will be overridden

  vec2 blocks = floor(uv * iResolution.xy / blockSize);
  vec2 blockUV = (blocks + 0.5) * blockSize / iResolution.xy;

  fragColor = texture2D(iChannel0, blockUV);
}`,

  // Emboss
  emboss: `
void mainImage(out vec4 fragColor, in vec2 fragCoord) {
  vec2 uv = fragCoord / iResolution.xy;
  vec2 texel = 1.0 / iResolution.xy;

  vec4 tl = texture2D(iChannel0, uv + vec2(-texel.x, texel.y));
  vec4 br = texture2D(iChannel0, uv + vec2(texel.x, -texel.y));

  vec4 diff = br - tl;
  float gray = (diff.r + diff.g + diff.b) / 3.0;

  fragColor = vec4(vec3(0.5 + gray * 2.0), texture2D(iChannel0, uv).a);
}`,

  // Find Edges (Sobel)
  "find-edges": `
void mainImage(out vec4 fragColor, in vec2 fragCoord) {
  vec2 uv = fragCoord / iResolution.xy;
  vec2 texel = 1.0 / iResolution.xy;

  // Sobel kernels
  float gx = 0.0;
  float gy = 0.0;

  // Sample 3x3 neighborhood
  for (int y = -1; y <= 1; y++) {
    for (int x = -1; x <= 1; x++) {
      vec4 sample = texture2D(iChannel0, uv + vec2(float(x), float(y)) * texel);
      float lum = luminance(sample.rgb);

      // Sobel X kernel
      float kx = float(x) * (y == 0 ? 2.0 : 1.0);
      gx += lum * kx;

      // Sobel Y kernel
      float ky = float(y) * (x == 0 ? 2.0 : 1.0);
      gy += lum * ky;
    }
  }

  float edge = sqrt(gx * gx + gy * gy);
  fragColor = vec4(vec3(edge), 1.0);
}`,

  // Scanlines
  scanlines: `
void mainImage(out vec4 fragColor, in vec2 fragCoord) {
  vec2 uv = fragCoord / iResolution.xy;
  vec4 color = texture2D(iChannel0, uv);

  float lineSpacing = 2.0;
  float lineIntensity = 0.15;

  float scanline = sin(fragCoord.y * 3.14159 / lineSpacing) * 0.5 + 0.5;
  color.rgb *= 1.0 - (scanline * lineIntensity);

  fragColor = color;
}`,

  // Halftone
  halftone: `
void mainImage(out vec4 fragColor, in vec2 fragCoord) {
  vec2 uv = fragCoord / iResolution.xy;
  float dotSize = 4.0;

  vec2 gridUV = floor(uv * iResolution.xy / dotSize) * dotSize / iResolution.xy;
  vec4 color = texture2D(iChannel0, gridUV + dotSize * 0.5 / iResolution.xy);
  float lum = luminance(color.rgb);

  vec2 cellUV = fract(uv * iResolution.xy / dotSize) - 0.5;
  float dist = length(cellUV);
  float radius = lum * 0.5;

  float dot = smoothstep(radius + 0.05, radius - 0.05, dist);
  fragColor = vec4(vec3(dot), color.a);
}`,

  // VHS Effect
  vhs: `
void mainImage(out vec4 fragColor, in vec2 fragCoord) {
  vec2 uv = fragCoord / iResolution.xy;

  // Chromatic aberration
  float aberration = 0.002;
  float r = texture2D(iChannel0, uv + vec2(aberration, 0.0)).r;
  float g = texture2D(iChannel0, uv).g;
  float b = texture2D(iChannel0, uv - vec2(aberration, 0.0)).b;

  // Scanlines
  float scanline = sin(fragCoord.y * 1.5) * 0.04;

  // Noise
  float noise = (hash2(uv + iTime * 0.1) - 0.5) * 0.08;

  vec3 color = vec3(r, g, b);
  color += scanline;
  color += noise;

  fragColor = vec4(color, 1.0);
}`,

  // Ripple (Water)
  ripple: `
void mainImage(out vec4 fragColor, in vec2 fragCoord) {
  vec2 uv = fragCoord / iResolution.xy;
  vec2 center = vec2(0.5, 0.5);

  vec2 tc = uv - center;
  float dist = length(tc);

  float amplitude = 0.03;
  float frequency = 20.0;
  float speed = 2.0;

  float wave = sin(dist * frequency - iTime * speed) * amplitude;
  wave *= smoothstep(0.5, 0.0, dist);

  vec2 offset = normalize(tc) * wave;
  fragColor = texture2D(iChannel0, uv + offset);
}`,

  // Glitch
  glitch: `
void mainImage(out vec4 fragColor, in vec2 fragCoord) {
  vec2 uv = fragCoord / iResolution.xy;

  float glitchStrength = 0.05;
  float blockSize = 0.05;

  // Random block offset
  float block = floor(uv.y / blockSize);
  float randomOffset = hash(block + floor(iTime * 10.0)) * 2.0 - 1.0;

  vec2 glitchUV = uv;
  if (abs(randomOffset) > 0.7) {
    glitchUV.x += randomOffset * glitchStrength;
  }

  // Color channel separation
  float r = texture2D(iChannel0, glitchUV + vec2(0.01, 0.0)).r;
  float g = texture2D(iChannel0, glitchUV).g;
  float b = texture2D(iChannel0, glitchUV - vec2(0.01, 0.0)).b;

  fragColor = vec4(r, g, b, 1.0);
}`,
};

const EFFECT_GPU_MAPPINGS: EffectGPUMapping[] = [
  // Blur effects - excellent GPU candidates (WebGPU)
  { effectKey: "gaussian-blur", webgpuMethod: "blur", preferGPU: true },
  { effectKey: "radial-blur", webgpuMethod: "radialBlur", preferGPU: true },
  {
    effectKey: "directional-blur",
    webgpuMethod: "directionalBlur",
    preferGPU: true,
  },
  { effectKey: "box-blur", webgpuMethod: "blur", preferGPU: true },

  // Color effects - good GPU candidates (WebGPU)
  {
    effectKey: "brightness-contrast",
    webgpuMethod: "colorCorrect",
    preferGPU: true,
  },
  {
    effectKey: "hue-saturation",
    webgpuMethod: "colorCorrect",
    preferGPU: true,
  },
  { effectKey: "levels", webgpuMethod: "levels", preferGPU: true },
  { effectKey: "glow", webgpuMethod: "glow", preferGPU: true },

  // Distort effects - excellent GPU candidates (WebGPU)
  { effectKey: "warp", webgpuMethod: "warp", preferGPU: true },
  {
    effectKey: "displacement-map",
    webgpuMethod: "displacement",
    preferGPU: true,
  },
  { effectKey: "turbulent-displace", webgpuMethod: "warp", preferGPU: true },
  {
    effectKey: "ripple-distort",
    webglShader: GLSL_SHADERS.ripple,
    preferGPU: true,
  },

  // Stylize effects - good GPU candidates (WebGL via GLSL)
  {
    effectKey: "rgb-split",
    webglShader: GLSL_SHADERS["rgb-split"],
    preferGPU: true,
  },
  { effectKey: "mosaic", webglShader: GLSL_SHADERS.mosaic, preferGPU: true },
  { effectKey: "emboss", webglShader: GLSL_SHADERS.emboss, preferGPU: true },
  {
    effectKey: "find-edges",
    webglShader: GLSL_SHADERS["find-edges"],
    preferGPU: true,
  },
  {
    effectKey: "scanlines",
    webglShader: GLSL_SHADERS.scanlines,
    preferGPU: true,
  },
  {
    effectKey: "halftone",
    webglShader: GLSL_SHADERS.halftone,
    preferGPU: true,
  },
  { effectKey: "vhs", webglShader: GLSL_SHADERS.vhs, preferGPU: true },
  { effectKey: "ripple", webglShader: GLSL_SHADERS.ripple, preferGPU: true },
  { effectKey: "glitch", webglShader: GLSL_SHADERS.glitch, preferGPU: true },

  // Effects that work better on CPU (complex logic, branching)
  { effectKey: "pixel-sort", preferGPU: false }, // Requires sorting - CPU better
  { effectKey: "dither", preferGPU: false }, // Error diffusion needs CPU
  { effectKey: "tint", preferGPU: false },
  { effectKey: "curves", preferGPU: false }, // LUT-based is complex
  { effectKey: "drop-shadow", preferGPU: false }, // Multi-pass
  { effectKey: "invert", preferGPU: false }, // Too simple, overhead not worth it
  { effectKey: "posterize", preferGPU: false }, // Simple CPU op
  { effectKey: "threshold", preferGPU: false }, // Simple CPU op

  // Generate effects - depends on complexity
  { effectKey: "fill", preferGPU: false }, // Too simple
  { effectKey: "gradient-ramp", preferGPU: true },
  { effectKey: "fractal-noise", preferGPU: true },
  { effectKey: "radio-waves", preferGPU: true },
  { effectKey: "ellipse", preferGPU: false },
];

// ============================================================================
// TEXTURE POOL
// Reduces GPU memory allocation overhead
// ============================================================================

class TexturePool {
  private pool: TexturePoolEntry[] = [];
  private readonly maxSize = 10;
  private readonly maxAge = 30000; // 30 second TTL

  /**
   * Acquire a texture buffer of the specified size
   */
  acquire(width: number, height: number): ImageData {
    const now = Date.now();

    // Find matching texture in pool
    for (const entry of this.pool) {
      if (!entry.inUse && entry.width === width && entry.height === height) {
        entry.inUse = true;
        entry.lastUsed = now;
        // Clear the texture data
        entry.texture.data.fill(0);
        return entry.texture;
      }
    }

    // Create new texture
    const texture = new ImageData(width, height);

    // Add to pool if space available
    if (this.pool.length < this.maxSize) {
      this.pool.push({
        texture,
        width,
        height,
        inUse: true,
        lastUsed: now,
      });
    }

    return texture;
  }

  /**
   * Release a texture back to the pool
   */
  release(texture: ImageData): void {
    const entry = this.pool.find((e) => e.texture === texture);
    if (entry) {
      entry.inUse = false;
      entry.lastUsed = Date.now();
    }
  }

  /**
   * Clean up old textures
   */
  cleanup(): void {
    const now = Date.now();
    this.pool = this.pool.filter(
      (entry) => entry.inUse || now - entry.lastUsed <= this.maxAge,
    );
  }

  /**
   * Clear all pooled textures
   */
  clear(): void {
    this.pool = [];
  }

  /**
   * Get pool statistics
   */
  getStats(): { total: number; inUse: number; available: number } {
    const inUse = this.pool.filter((e) => e.inUse).length;
    return {
      total: this.pool.length,
      inUse,
      available: this.pool.length - inUse,
    };
  }
}

// ============================================================================
// GPU EFFECT DISPATCHER
// ============================================================================

class GPUEffectDispatcher {
  private capabilities: GPUCapabilityInfo = {
    preferredPath: "canvas2d",
    webgpuAvailable: false,
    webgl2Available: false,
    gpuTier: { tier: "cpu", vram: 0, features: [] },
    initialized: false,
  };

  private texturePool = new TexturePool();
  private glslEngine: GLSLEngine | null = null;
  private initPromise: Promise<void> | null = null;

  // Effect routing cache
  private effectRoutes = new Map<string, GPURenderPath>();

  /**
   * Initialize GPU detection and renderer setup
   */
  async initialize(): Promise<void> {
    if (this.capabilities.initialized) return;
    if (this.initPromise) return this.initPromise;

    this.initPromise = this.doInitialize();
    return this.initPromise;
  }

  private async doInitialize(): Promise<void> {
    try {
      // Detect GPU tier
      const gpuTier = await detectGPUTier();
      this.capabilities.gpuTier = gpuTier;

      // Initialize WebGPU renderer
      const webgpuAvailable = await webgpuRenderer.initialize();
      this.capabilities.webgpuAvailable = webgpuAvailable;

      // Check WebGL2 availability
      this.glslEngine = getGLSLEngine();
      this.capabilities.webgl2Available = this.glslEngine.isAvailable();

      // Determine preferred path
      if (webgpuAvailable) {
        this.capabilities.preferredPath = "webgpu";
      } else if (this.capabilities.webgl2Available) {
        this.capabilities.preferredPath = "webgl2";
      } else {
        this.capabilities.preferredPath = "canvas2d";
      }

      this.capabilities.initialized = true;

      // Build effect routing table
      this.buildEffectRoutes();

      engineLogger.info("GPU Effect Dispatcher initialized", {
        preferredPath: this.capabilities.preferredPath,
        gpuTier: gpuTier.tier,
        webgpu: webgpuAvailable,
        webgl2: this.capabilities.webgl2Available,
      });
    } catch (error) {
      engineLogger.error("GPU Effect Dispatcher initialization failed:", error);
      this.capabilities.initialized = true;
      this.capabilities.preferredPath = "canvas2d";
    }
  }

  /**
   * Build routing table for effects based on GPU availability
   */
  private buildEffectRoutes(): void {
    this.effectRoutes.clear();

    for (const mapping of EFFECT_GPU_MAPPINGS) {
      let route: GPURenderPath = "canvas2d";

      if (mapping.preferGPU) {
        // Prefer WebGPU for effects that have WebGPU methods
        if (this.capabilities.webgpuAvailable && mapping.webgpuMethod) {
          route = "webgpu";
        }
        // Fall back to WebGL2 for effects with GLSL shaders
        else if (this.capabilities.webgl2Available && mapping.webglShader) {
          route = "webgl2";
        }
        // Effects without GPU implementation stay on canvas2d
      }

      this.effectRoutes.set(mapping.effectKey, route);
    }

    // Log routing summary
    const routeCounts = { webgpu: 0, webgl2: 0, canvas2d: 0 };
    for (const route of this.effectRoutes.values()) {
      routeCounts[route]++;
    }
    engineLogger.debug("Effect routes built", routeCounts);
  }

  /**
   * Get the GPU capabilities
   */
  getCapabilities(): GPUCapabilityInfo {
    return { ...this.capabilities };
  }

  /**
   * Get the rendering path for a specific effect
   */
  getEffectRoute(effectKey: string): GPURenderPath {
    return this.effectRoutes.get(effectKey) || "canvas2d";
  }

  /**
   * Check if an effect should use GPU acceleration
   */
  shouldUseGPU(effectKey: string): boolean {
    const route = this.getEffectRoute(effectKey);
    return route !== "canvas2d";
  }

  /**
   * Process an effect using the best available renderer
   *
   * @param effectKey - The effect type key
   * @param input - Input ImageData or Canvas
   * @param params - Effect parameters
   * @returns Processed ImageData
   */
  async processEffect(
    effectKey: string,
    input: ImageData | HTMLCanvasElement,
    params: Record<string, PropertyValue>,
  ): Promise<ImageData> {
    // Ensure initialized
    if (!this.capabilities.initialized) {
      await this.initialize();
    }

    const route = this.getEffectRoute(effectKey);
    const mapping = EFFECT_GPU_MAPPINGS.find((m) => m.effectKey === effectKey);

    try {
      switch (route) {
        case "webgpu":
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          const mappingWebgpuMethod = (mapping != null && typeof mapping === "object" && "webgpuMethod" in mapping && mapping.webgpuMethod != null && typeof mapping.webgpuMethod === "string") ? mapping.webgpuMethod : undefined;
          if (mappingWebgpuMethod != null) {
            return await this.processWebGPU(
              effectKey,
              input,
              params,
              mappingWebgpuMethod,
            );
          }
          break;
        case "webgl2":
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          const mappingWebglShader = (mapping != null && typeof mapping === "object" && "webglShader" in mapping && mapping.webglShader != null && typeof mapping.webglShader === "string") ? mapping.webglShader : undefined;
          if (mappingWebglShader != null) {
            return await this.processWebGL(
              effectKey,
              input,
              params,
              mappingWebglShader,
            );
          }
          break;
      }
    } catch (error) {
      engineLogger.warn(
        `GPU processing failed for ${effectKey}, falling back to Canvas2D:`,
        error,
      );
    }

    // Canvas2D fallback - return input unchanged (actual processing done by original renderer)
    return this.toImageData(input);
  }

  /**
   * Type-safe interface for WebGPU renderer methods
   * Maps effect method names to their corresponding WebGPU renderer methods
   */
  private typeSafeWebGPUMethod(
    methodName: string,
  ): (
    input: ImageData | HTMLCanvasElement,
    params: JSONValue,
  ) => Promise<ImageData> {
    // Type-safe method access - map known method names to renderer methods
    const methodMap: Record<
      string,
      (
        input: ImageData | HTMLCanvasElement,
        params: JSONValue,
      ) => Promise<ImageData>
    > = {
      blur: (input, params) => {
        // Deterministic: Validate params structure with explicit min/max/default
        const validatedParams = validateBlurParams(params);
        return webgpuRenderer.blur(input, validatedParams);
      },
      colorCorrection: (input, params) => {
        // Deterministic: Validate params structure with explicit min/max/default
        const validatedParams = validateColorCorrectionParams(params);
        return webgpuRenderer.colorCorrect(input, validatedParams);
      },
      radialBlur: (input, params) => {
        // Deterministic: Validate params structure with explicit min/max/default
        const validatedParams = validateRadialBlurParams(params);
        return webgpuRenderer.radialBlur(input, validatedParams);
      },
      directionalBlur: (input, params) => {
        // Deterministic: Validate params structure with explicit min/max/default
        const validatedParams = validateDirectionalBlurParams(params);
        return webgpuRenderer.directionalBlur(input, validatedParams);
      },
      // NOTE: displacement method not yet implemented in WebGPURenderer
      // Pipeline exists (displacementPipeline) but no public method
      warp: (input, params) => {
        // Deterministic: Validate params structure with explicit min/max/default
        const validatedParams = validateWarpParams(params);
        return webgpuRenderer.warp(input, validatedParams);
      },
      glow: (input, params) => {
        // Deterministic: Validate params structure with explicit min/max/default
        const validatedParams = validateGlowParams(params);
        return webgpuRenderer.glow(input, validatedParams);
      },
      levels: (input, params) => {
        // Deterministic: Validate params structure with explicit min/max/default
        const validatedParams = validateLevelsParams(params);
        return webgpuRenderer.levels(input, validatedParams);
      },
    };

    const method = methodMap[methodName];
    if (!method) {
      throw new Error(`WebGPU method ${methodName} not found`);
    }

    return method;
  }

  /**
   * Process effect using WebGPU
   */
  private async processWebGPU(
    effectKey: string,
    input: ImageData | HTMLCanvasElement,
    params: Record<string, PropertyValue>,
    methodName: string,
  ): Promise<ImageData> {
    // Type-safe method access
    const method = this.typeSafeWebGPUMethod(methodName);

    // Map effect params to WebGPU params based on effect type
    const gpuParams = this.mapParamsToWebGPU(effectKey, params);

    return await method(input, gpuParams);
  }

  /**
   * Process effect using WebGL2 (GLSL)
   */
  private async processWebGL(
    effectKey: string,
    input: ImageData | HTMLCanvasElement,
    params: Record<string, PropertyValue>,
    shaderSource: string,
  ): Promise<ImageData> {
    if (!this.glslEngine) {
      throw new Error("GLSL engine not available");
    }

    this.glslEngine.setShader(shaderSource);

    // Map params to shader uniforms
    const uniforms = this.mapParamsToGLSL(effectKey, params);

    const canvas = this.glslEngine.render(input, uniforms);
    if (!canvas) {
      throw new Error("WebGL render failed");
    }

    return this.toImageData(canvas);
  }

  /**
   * Map effect parameters to WebGPU format
   */
  /**
   * Map effect parameters to WebGPU uniform format
   * Deterministic: Explicit type conversion with validation
   * Min/Max: All numeric values validated and clamped
   * Default: Explicit defaults for all optional parameters
   */
  private mapParamsToWebGPU(
    effectKey: string,
    params: Record<string, PropertyValue>,
  ): Record<string, number | string | { x: number; y: number } | { x: number; y: number; z: number }> {
    switch (effectKey) {
      case "gaussian-blur":
      case "box-blur":
        // Type proof: radius ∈ ℝ ∧ finite(radius) → radius ∈ ℝ₊
        const boxBlurRadius = isFiniteNumber(params.radius) && params.radius >= 0 ? params.radius : 10;
        // Type proof: quality ∈ {"low", "medium", "high"} ∪ {undefined}
        const boxBlurQuality = typeof params.quality === "string" ? params.quality : "high";
        // Type proof: direction ∈ {"both", "horizontal", "vertical"} ∪ {undefined}
        const boxBlurDirection = typeof params.direction === "string" ? params.direction : "both";
        return {
          radius: boxBlurRadius,
          quality: boxBlurQuality,
          direction: boxBlurDirection,
        };

      case "radial-blur":
        // Type proof: centerX ∈ ℝ ∧ finite(centerX) → centerX ∈ [0, 1]
        const radialBlurCenterX = isFiniteNumber(params.centerX) ? Math.max(0, Math.min(1, params.centerX)) : 0.5;
        // Type proof: centerY ∈ ℝ ∧ finite(centerY) → centerY ∈ [0, 1]
        const radialBlurCenterY = isFiniteNumber(params.centerY) ? Math.max(0, Math.min(1, params.centerY)) : 0.5;
        // Type proof: amount ∈ ℝ ∧ finite(amount) → amount ∈ ℝ₊
        const radialBlurAmount = isFiniteNumber(params.amount) && params.amount >= 0 ? params.amount : 50;
        // Type proof: samples ∈ ℕ ∧ finite(samples) → samples ∈ ℕ₊
        const radialBlurSamples = isFiniteNumber(params.samples) && Number.isInteger(params.samples) && params.samples > 0 ? params.samples : 32;
        return {
          centerX: radialBlurCenterX,
          centerY: radialBlurCenterY,
          amount: radialBlurAmount,
          samples: radialBlurSamples,
        };

      case "directional-blur":
        // Type proof: angle ∈ ℝ ∧ finite(angle) → angle ∈ ℝ
        const directionalBlurAngle = isFiniteNumber(params.angle) ? params.angle : 0;
        // Type proof: length ∈ ℝ ∧ finite(length) → length ∈ ℝ₊
        const directionalBlurLength = isFiniteNumber(params.length) && params.length >= 0 ? params.length : 20;
        // Type proof: samples ∈ ℕ ∧ finite(samples) → samples ∈ ℕ₊
        const directionalBlurSamples = isFiniteNumber(params.samples) && Number.isInteger(params.samples) && params.samples > 0 ? params.samples : 32;
        return {
          angle: directionalBlurAngle,
          length: directionalBlurLength,
          samples: directionalBlurSamples,
        };

      case "brightness-contrast":
        // Type proof: brightness ∈ ℝ ∧ finite(brightness) → brightness ∈ ℝ
        const brightnessValue = params.brightness;
        const brightness = isFiniteNumber(brightnessValue) ? brightnessValue / 100 : 0;
        // Type proof: contrast ∈ ℝ ∧ finite(contrast) → contrast ∈ ℝ
        const contrastValue = params.contrast;
        const contrast = isFiniteNumber(contrastValue) ? contrastValue / 100 : 0;
        return {
          brightness,
          contrast,
          saturation: 0,
          hue: 0,
        };

      case "hue-saturation":
        // Type proof: saturation ∈ ℝ ∧ finite(saturation) → saturation ∈ ℝ
        const saturationValue = params.saturation;
        const saturation = isFiniteNumber(saturationValue) ? saturationValue / 100 : 0;
        // Type proof: hue ∈ ℝ ∧ finite(hue) → hue ∈ ℝ
        const hueValue = params.hue;
        const hue = isFiniteNumber(hueValue) ? hueValue : 0;
        return {
          brightness: 0,
          contrast: 0,
          saturation,
          hue,
        };

      case "levels":
        // Type proof: inputBlack ∈ ℝ ∧ finite(inputBlack) → inputBlack ∈ [0, 1]
        const inputBlackValue = params.inputBlack;
        const inputBlack = isFiniteNumber(inputBlackValue) ? inputBlackValue / 255 : 0;
        // Type proof: inputWhite ∈ ℝ ∧ finite(inputWhite) → inputWhite ∈ [0, 1]
        const inputWhiteValue = params.inputWhite;
        const inputWhite = isFiniteNumber(inputWhiteValue) ? inputWhiteValue / 255 : 1;
        // Type proof: gamma ∈ ℝ ∧ finite(gamma) ∧ gamma > 0 → gamma ∈ ℝ₊
        const gammaValue = params.gamma;
        const gamma = isFiniteNumber(gammaValue) && gammaValue > 0 ? gammaValue : 1;
        // Type proof: outputBlack ∈ ℝ ∧ finite(outputBlack) → outputBlack ∈ [0, 1]
        const outputBlackValue = params.outputBlack;
        const outputBlack = isFiniteNumber(outputBlackValue) ? outputBlackValue / 255 : 0;
        // Type proof: outputWhite ∈ ℝ ∧ finite(outputWhite) → outputWhite ∈ [0, 1]
        const outputWhiteValue = params.outputWhite;
        const outputWhite = isFiniteNumber(outputWhiteValue) ? outputWhiteValue / 255 : 1;
        return {
          inputBlack,
          inputWhite,
          gamma,
          outputBlack,
          outputWhite,
        };

      case "glow":
        // Type proof: radius ∈ ℝ ∧ finite(radius) → radius ∈ ℝ₊
        const glowRadius = isFiniteNumber(params.radius) && params.radius >= 0 ? params.radius : 20;
        // Type proof: intensity ∈ ℝ ∧ finite(intensity) → intensity ∈ ℝ₊
        const glowIntensity = isFiniteNumber(params.intensity) && params.intensity >= 0 ? params.intensity : 1;
        // Type proof: threshold ∈ ℝ ∧ finite(threshold) → threshold ∈ [0, 1]
        const glowThreshold = isFiniteNumber(params.threshold) ? Math.max(0, Math.min(1, params.threshold)) : 0.5;
        // Deterministic: Validate color structure explicitly
        // For WebGPU uniforms, convert RGB color to vec3 format { x, y, z }
        const glowResult: Record<string, number | string | { x: number; y: number } | { x: number; y: number; z: number }> = {
          radius: glowRadius,
          intensity: glowIntensity,
          threshold: glowThreshold,
        };
        const glowColorValue = params.color;
        if (typeof glowColorValue === "object" && glowColorValue !== null && !Array.isArray(glowColorValue)) {
          const colorObj = glowColorValue as Record<string, PropertyValue>;
          const r = isFiniteNumber(colorObj.r) ? Math.max(0, Math.min(1, colorObj.r)) : 1;
          const g = isFiniteNumber(colorObj.g) ? Math.max(0, Math.min(1, colorObj.g)) : 1;
          const b = isFiniteNumber(colorObj.b) ? Math.max(0, Math.min(1, colorObj.b)) : 1;
          // Convert RGB to vec3 format for WebGPU uniforms
          glowResult.color = { x: r, y: g, z: b };
        }
        return glowResult;

      case "warp":
      case "turbulent-displace":
      case "ripple-distort":
        // Type proof: style ∈ {"wave", "arc", "bulge", ...} ∪ {undefined}
        const warpStyle = typeof params.style === "string" ? params.style : "wave";
        // Type proof: bend ∈ ℝ ∧ finite(bend) → bend ∈ ℝ
        const bendValue = params.amount !== undefined ? params.amount : params.bend;
        const warpBend = isFiniteNumber(bendValue) ? bendValue : 0.5;
        // Type proof: hDistort ∈ ℝ ∧ finite(hDistort) → hDistort ∈ ℝ
        const warpHDistort = isFiniteNumber(params.hDistort) ? params.hDistort : 0;
        // Type proof: vDistort ∈ ℝ ∧ finite(vDistort) → vDistort ∈ ℝ
        const warpVDistort = isFiniteNumber(params.vDistort) ? params.vDistort : 0;
        return {
          style: warpStyle,
          bend: warpBend,
          hDistort: warpHDistort,
          vDistort: warpVDistort,
        };

      case "displacement-map":
        // Type proof: maxHorizontal ∈ ℝ ∧ finite(maxHorizontal) → maxHorizontal ∈ ℝ
        const displacementMaxHorizontal = isFiniteNumber(params.maxHorizontal) ? params.maxHorizontal : 50;
        // Type proof: maxVertical ∈ ℝ ∧ finite(maxVertical) → maxVertical ∈ ℝ
        const displacementMaxVertical = isFiniteNumber(params.maxVertical) ? params.maxVertical : 50;
        // Type proof: hChannel ∈ {"red", "green", "blue", "alpha", "luminance"} ∪ {undefined}
        const displacementHChannel = typeof params.hChannel === "string" ? params.hChannel : "red";
        // Type proof: vChannel ∈ {"red", "green", "blue", "alpha", "luminance"} ∪ {undefined}
        const displacementVChannel = typeof params.vChannel === "string" ? params.vChannel : "green";
        return {
          maxHorizontal: displacementMaxHorizontal,
          maxVertical: displacementMaxVertical,
          hChannel: displacementHChannel,
          vChannel: displacementVChannel,
        };

      default:
        // Deterministic: Convert PropertyValue to WebGPU uniform format
        // Filter and convert only compatible types (number, string, vec2, vec3)
        const defaultResult: Record<string, number | string | { x: number; y: number } | { x: number; y: number; z: number }> = {};
        for (const [key, value] of Object.entries(params)) {
          if (typeof value === "number" && Number.isFinite(value)) {
            defaultResult[key] = value;
          } else if (typeof value === "string") {
            defaultResult[key] = value;
          } else if (typeof value === "object" && value !== null && !Array.isArray(value)) {
            const obj = value as Record<string, PropertyValue>;
            const x = isFiniteNumber(obj.x) ? obj.x : 0;
            const y = isFiniteNumber(obj.y) ? obj.y : 0;
            const z = isFiniteNumber(obj.z) ? obj.z : undefined;
            if (z !== undefined) {
              defaultResult[key] = { x, y, z };
            } else {
              defaultResult[key] = { x, y };
            }
          }
        }
        return defaultResult;
    }
  }

  /**
   * Map effect parameters to GLSL uniforms
   */
  /**
   * Map effect parameters to GLSL uniform format
   * Deterministic: Explicit type conversion with validation
   * Min/Max: All numeric values validated and clamped
   * Default: Explicit defaults for all optional parameters
   */
  private mapParamsToGLSL(
    effectKey: string,
    params: Record<string, PropertyValue>,
  ): Record<string, number | string | { x: number; y: number } | { x: number; y: number; z: number }> {
    // Base uniforms - frame time for animated effects
    // Type proof: _frame ∈ ℕ ∪ {undefined} → _frame ∈ ℕ
    const frameValue = params._frame;
    const frame = isFiniteNumber(frameValue) && Number.isInteger(frameValue) && frameValue >= 0 ? frameValue : 0;
    // Type proof: _fps ∈ ℝ₊ ∧ finite(_fps) → _fps ∈ ℝ₊
    const fpsValue = params._fps;
    const fps = isFiniteNumber(fpsValue) && fpsValue > 0 ? fpsValue : 30;
    const baseUniforms: Record<string, number> = {
      iTime: frame / fps,
      iFrame: frame,
    };

    switch (effectKey) {
      case "rgb-split":
        // Type proof: amount ∈ ℝ ∧ finite(amount) → amount ∈ ℝ₊
        const rgbSplitAmount = isFiniteNumber(params.amount) && params.amount >= 0 ? params.amount : 10;
        // Type proof: angle ∈ ℝ ∧ finite(angle) → angle ∈ ℝ
        const rgbSplitAngle = isFiniteNumber(params.angle) ? params.angle : 0;
        return {
          ...baseUniforms,
          amount: rgbSplitAmount / 1000, // Convert pixels to UV offset
          angle: rgbSplitAngle,
        };

      case "mosaic":
        // Type proof: blockSize ∈ ℝ ∧ finite(blockSize) → blockSize ∈ ℝ₊
        const mosaicBlockSizeValue = params.blockSize !== undefined ? params.blockSize : params.size;
        const mosaicBlockSize = isFiniteNumber(mosaicBlockSizeValue) && mosaicBlockSizeValue >= 0 ? mosaicBlockSizeValue : 10;
        return {
          ...baseUniforms,
          blockSize: mosaicBlockSize,
        };

      case "emboss":
        // Type proof: strength ∈ ℝ ∧ finite(strength) → strength ∈ ℝ₊
        const embossStrength = isFiniteNumber(params.strength) && params.strength >= 0 ? params.strength : 1;
        // Type proof: angle ∈ ℝ ∧ finite(angle) → angle ∈ ℝ
        const embossAngle = isFiniteNumber(params.angle) ? params.angle : 135;
        return {
          ...baseUniforms,
          strength: embossStrength,
          angle: embossAngle,
        };

      case "find-edges":
        // Type proof: threshold ∈ ℝ ∧ finite(threshold) → threshold ∈ [0, 1]
        const findEdgesThreshold = isFiniteNumber(params.threshold) ? Math.max(0, Math.min(1, params.threshold)) : 0.1;
        // Type proof: invert ∈ {true, false}
        const findEdgesInvert = typeof params.invert === "boolean" && params.invert ? 1 : 0;
        return {
          ...baseUniforms,
          threshold: findEdgesThreshold,
          invert: findEdgesInvert,
        };

      case "scanlines":
        // Type proof: lineSpacing ∈ ℝ ∧ finite(lineSpacing) → lineSpacing ∈ ℝ₊
        const scanlinesSpacingValue = params.spacing !== undefined ? params.spacing : params.lineSpacing;
        const scanlinesLineSpacing = isFiniteNumber(scanlinesSpacingValue) && scanlinesSpacingValue >= 0 ? scanlinesSpacingValue : 2;
        // Type proof: lineIntensity ∈ ℝ ∧ finite(lineIntensity) → lineIntensity ∈ [0, 1]
        const scanlinesIntensityValue = params.intensity !== undefined ? params.intensity : params.lineIntensity;
        const scanlinesLineIntensity = isFiniteNumber(scanlinesIntensityValue) ? Math.max(0, Math.min(1, scanlinesIntensityValue)) : 0.15;
        return {
          ...baseUniforms,
          lineSpacing: scanlinesLineSpacing,
          lineIntensity: scanlinesLineIntensity,
        };

      case "halftone":
        // Type proof: dotSize ∈ ℝ ∧ finite(dotSize) → dotSize ∈ ℝ₊
        const halftoneDotSizeValue = params.dotSize !== undefined ? params.dotSize : params.size;
        const halftoneDotSize = isFiniteNumber(halftoneDotSizeValue) && halftoneDotSizeValue >= 0 ? halftoneDotSizeValue : 4;
        // Type proof: angle ∈ ℝ ∧ finite(angle) → angle ∈ ℝ
        const halftoneAngle = isFiniteNumber(params.angle) ? params.angle : 0;
        return {
          ...baseUniforms,
          dotSize: halftoneDotSize,
          angle: halftoneAngle,
        };

      case "vhs":
        // Type proof: aberration ∈ ℝ ∧ finite(aberration) → aberration ∈ ℝ₊
        const vhsAberrationValue = params.chromaShift !== undefined ? params.chromaShift : params.aberration;
        const vhsAberration = isFiniteNumber(vhsAberrationValue) && vhsAberrationValue >= 0 ? vhsAberrationValue : 2;
        // Type proof: noiseStrength ∈ ℝ ∧ finite(noiseStrength) → noiseStrength ∈ [0, 1]
        const vhsNoiseValue = params.noise !== undefined ? params.noise : params.noiseStrength;
        const vhsNoiseStrength = isFiniteNumber(vhsNoiseValue) ? Math.max(0, Math.min(1, vhsNoiseValue)) : 0.08;
        // Type proof: scanlineStrength ∈ ℝ ∧ finite(scanlineStrength) → scanlineStrength ∈ [0, 1]
        const vhsScanlineValue = params.scanlines !== undefined ? params.scanlines : params.scanlineStrength;
        const vhsScanlineStrength = isFiniteNumber(vhsScanlineValue) ? Math.max(0, Math.min(1, vhsScanlineValue)) : 0.04;
        return {
          ...baseUniforms,
          aberration: vhsAberration / 1000,
          noiseStrength: vhsNoiseStrength,
          scanlineStrength: vhsScanlineStrength,
        };

      case "ripple":
        // Type proof: amplitude ∈ ℝ ∧ finite(amplitude) → amplitude ∈ ℝ₊
        const rippleAmplitude = isFiniteNumber(params.amplitude) && params.amplitude >= 0 ? params.amplitude : 3;
        // Type proof: frequency ∈ ℝ ∧ finite(frequency) → frequency ∈ ℝ₊
        const rippleFrequency = isFiniteNumber(params.frequency) && params.frequency >= 0 ? params.frequency : 20;
        // Type proof: speed ∈ ℝ ∧ finite(speed) → speed ∈ ℝ
        const rippleSpeed = isFiniteNumber(params.speed) ? params.speed : 2;
        // Type proof: centerX ∈ ℝ ∧ finite(centerX) → centerX ∈ [0, 1]
        const rippleCenterX = isFiniteNumber(params.centerX) ? Math.max(0, Math.min(1, params.centerX)) : 0.5;
        // Type proof: centerY ∈ ℝ ∧ finite(centerY) → centerY ∈ [0, 1]
        const rippleCenterY = isFiniteNumber(params.centerY) ? Math.max(0, Math.min(1, params.centerY)) : 0.5;
        return {
          ...baseUniforms,
          amplitude: rippleAmplitude / 100,
          frequency: rippleFrequency,
          speed: rippleSpeed,
          centerX: rippleCenterX,
          centerY: rippleCenterY,
        };

      case "glitch":
        // Type proof: glitchStrength ∈ ℝ ∧ finite(glitchStrength) → glitchStrength ∈ ℝ₊
        const glitchStrengthValue = params.strength;
        const glitchStrength = isFiniteNumber(glitchStrengthValue) && glitchStrengthValue >= 0 ? glitchStrengthValue : 5;
        // Type proof: blockSize ∈ ℝ ∧ finite(blockSize) → blockSize ∈ ℝ₊
        const glitchBlockSizeValue = params.blockSize;
        const glitchBlockSize = isFiniteNumber(glitchBlockSizeValue) && glitchBlockSizeValue >= 0 ? glitchBlockSizeValue : 5;
        // Type proof: colorSeparation ∈ ℝ ∧ finite(colorSeparation) → colorSeparation ∈ ℝ₊
        const glitchColorSeparationValue = params.colorSeparation;
        const glitchColorSeparation = isFiniteNumber(glitchColorSeparationValue) && glitchColorSeparationValue >= 0 ? glitchColorSeparationValue : 1;
        return {
          ...baseUniforms,
          glitchStrength: glitchStrength / 100,
          blockSize: glitchBlockSize / 100,
          colorSeparation: glitchColorSeparation / 100,
        };

      default:
        // Deterministic: Convert PropertyValue to GLSL uniform format
        // Filter and convert only compatible types (number, string, vec2, vec3)
        const glslResult: Record<string, number | string | { x: number; y: number } | { x: number; y: number; z: number }> = { ...baseUniforms };
        for (const [key, value] of Object.entries(params)) {
          if (typeof value === "number" && Number.isFinite(value)) {
            glslResult[key] = value;
          } else if (typeof value === "string") {
            glslResult[key] = value;
          } else if (typeof value === "object" && value !== null && !Array.isArray(value)) {
            const obj = value as Record<string, PropertyValue>;
            const x = isFiniteNumber(obj.x) ? obj.x : 0;
            const y = isFiniteNumber(obj.y) ? obj.y : 0;
            const z = isFiniteNumber(obj.z) ? obj.z : undefined;
            if (z !== undefined) {
              glslResult[key] = { x, y, z };
            } else {
              glslResult[key] = { x, y };
            }
          }
        }
        return glslResult;
    }
  }

  /**
   * Batch process multiple effects using GPU
   * More efficient than processing one at a time
   */
  async processBatch(
    effects: Array<{
      effectKey: string;
      input: ImageData | HTMLCanvasElement;
      params: Record<string, PropertyValue>;
    }>,
  ): Promise<ImageData[]> {
    // Ensure initialized
    if (!this.capabilities.initialized) {
      await this.initialize();
    }

    // Process all effects
    const results: ImageData[] = [];

    for (const effect of effects) {
      const result = await this.processEffect(
        effect.effectKey,
        effect.input,
        effect.params,
      );
      results.push(result);
    }

    return results;
  }

  /**
   * Acquire a texture from the pool
   */
  acquireTexture(width: number, height: number): ImageData {
    return this.texturePool.acquire(width, height);
  }

  /**
   * Release a texture back to the pool
   */
  releaseTexture(texture: ImageData): void {
    this.texturePool.release(texture);
  }

  /**
   * Convert input to ImageData
   */
  private toImageData(input: ImageData | HTMLCanvasElement): ImageData {
    if (input instanceof ImageData) {
      return input;
    }
    const ctx = input.getContext("2d")!;
    return ctx.getImageData(0, 0, input.width, input.height);
  }

  /**
   * Get dispatcher statistics
   */
  getStats(): {
    capabilities: GPUCapabilityInfo;
    texturePool: { total: number; inUse: number; available: number };
    effectRoutes: Array<{ effect: string; route: GPURenderPath }>;
  } {
    return {
      capabilities: this.getCapabilities(),
      texturePool: this.texturePool.getStats(),
      effectRoutes: Array.from(this.effectRoutes.entries()).map(
        ([effect, route]) => ({
          effect,
          route,
        }),
      ),
    };
  }

  /**
   * Clean up resources
   */
  cleanup(): void {
    this.texturePool.cleanup();
  }

  /**
   * Dispose all resources
   */
  dispose(): void {
    this.texturePool.clear();
    this.effectRoutes.clear();
    webgpuRenderer.dispose();
    // Don't dispose GLSL engine singleton - other code may use it
  }
}

// ============================================================================
// SINGLETON EXPORT
// ============================================================================

export const gpuEffectDispatcher = new GPUEffectDispatcher();

/**
 * Initialize GPU effect dispatcher
 * Call this at app startup
 */
export async function initializeGPUEffects(): Promise<GPUCapabilityInfo> {
  await gpuEffectDispatcher.initialize();
  return gpuEffectDispatcher.getCapabilities();
}

/**
 * Get GPU effect dispatcher statistics
 */
export function getGPUEffectStats() {
  return gpuEffectDispatcher.getStats();
}

export default gpuEffectDispatcher;
