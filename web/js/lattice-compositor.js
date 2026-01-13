import { d as defineStore, a as defineComponent, o as onMounted, r as resolveComponent, c as createBlock, b as openBlock, e as createApp, f as createPinia } from './lattice-vue-vendor.js';
/* empty css                  */

const useThemeStore = defineStore("theme", {
  state: () => ({
    currentTheme: "violet"
  }),
  getters: {
    themeGradient: (state) => `var(--lattice-theme-${state.currentTheme}-gradient)`,
    themePrimary: (state) => `var(--lattice-theme-${state.currentTheme}-primary)`,
    themeSecondary: (state) => `var(--lattice-theme-${state.currentTheme}-secondary)`
  },
  actions: {
    setTheme(theme) {
      this.currentTheme = theme;
      const root = document.documentElement;
      root.style.setProperty(
        "--lattice-accent",
        `var(--lattice-theme-${theme}-primary)`
      );
      root.style.setProperty(
        "--lattice-accent-secondary",
        `var(--lattice-theme-${theme}-secondary)`
      );
      root.style.setProperty(
        "--lattice-accent-gradient",
        `var(--lattice-theme-${theme}-gradient)`
      );
      const glowColors = {
        violet: "rgba(139, 92, 246, 0.3)",
        ocean: "rgba(6, 182, 212, 0.3)",
        sunset: "rgba(251, 113, 133, 0.3)",
        forest: "rgba(16, 185, 129, 0.3)",
        ember: "rgba(239, 68, 68, 0.3)",
        mono: "rgba(107, 114, 128, 0.3)"
      };
      root.style.setProperty("--lattice-accent-glow", glowColors[theme]);
      localStorage.setItem("lattice-theme", theme);
    },
    loadSavedTheme() {
      const saved = localStorage.getItem("lattice-theme");
      if (saved && ["violet", "ocean", "sunset", "forest", "ember", "mono"].includes(saved)) {
        this.setTheme(saved);
      }
    }
  }
});

const _sfc_main = /* @__PURE__ */ defineComponent({
  __name: "App",
  setup(__props) {
    const themeStore = useThemeStore();
    onMounted(() => {
      themeStore.loadSavedTheme();
    });
    return (_ctx, _cache) => {
      const _component_WorkspaceLayout = resolveComponent("WorkspaceLayout");
      return openBlock(), createBlock(_component_WorkspaceLayout);
    };
  }
});

class CanvasPool {
  pool = [];
  maxSize = 20;
  // Max pooled canvases
  maxAge = 6e4;
  // 60 second TTL for unused canvases
  /**
   * Acquire a canvas of the specified dimensions
   */
  acquire(width, height) {
    const now = Date.now();
    for (const item of this.pool) {
      if (!item.inUse && item.width === width && item.height === height) {
        item.inUse = true;
        item.lastUsed = now;
        item.ctx.clearRect(0, 0, width, height);
        return { canvas: item.canvas, ctx: item.ctx };
      }
    }
    const canvas = document.createElement("canvas");
    canvas.width = width;
    canvas.height = height;
    const ctx = canvas.getContext("2d");
    if (this.pool.length < this.maxSize) {
      this.pool.push({
        canvas,
        ctx,
        width,
        height,
        inUse: true,
        lastUsed: now
      });
    }
    return { canvas, ctx };
  }
  /**
   * Release a canvas back to the pool
   * Call this when done with an effect result
   */
  release(canvas) {
    const item = this.pool.find((p) => p.canvas === canvas);
    if (item) {
      item.inUse = false;
      item.lastUsed = Date.now();
    }
  }
  /**
   * Clean up old unused canvases to free memory
   */
  cleanup() {
    const now = Date.now();
    this.pool = this.pool.filter((item) => {
      if (!item.inUse && now - item.lastUsed > this.maxAge) {
        return false;
      }
      return true;
    });
  }
  /**
   * Clear all pooled canvases
   */
  clear() {
    this.pool = [];
  }
  /**
   * Get pool statistics
   */
  getStats() {
    const inUse = this.pool.filter((p) => p.inUse).length;
    return {
      total: this.pool.length,
      inUse,
      available: this.pool.length - inUse
    };
  }
}
const canvasPool = new CanvasPool();

const LOG_LEVELS = {
  debug: 0,
  info: 1,
  warn: 2,
  error: 3,
  none: 4
};
const config = {
  level: "warn",
  prefix: "[Lattice]"};
function shouldLog(level) {
  return LOG_LEVELS[level] >= LOG_LEVELS[config.level];
}
function formatMessage(_level, context, message) {
  const parts = [];
  {
    parts.push(config.prefix);
  }
  if (context) {
    parts.push(`[${context}]`);
  }
  parts.push(message);
  return parts.join(" ");
}
function createLogger(context) {
  return {
    debug(message, ...args) {
      if (shouldLog("debug")) {
        console.log(formatMessage("DEBUG", context, message), ...args);
      }
    },
    info(message, ...args) {
      if (shouldLog("info")) {
        console.info(formatMessage("INFO", context, message), ...args);
      }
    },
    warn(message, ...args) {
      if (shouldLog("warn")) {
        console.warn(formatMessage("WARN", context, message), ...args);
      }
    },
    error(message, ...args) {
      if (shouldLog("error")) {
        console.error(formatMessage("ERROR", context, message), ...args);
      }
    },
    /**
     * Log with a specific level
     */
    log(level, message, ...args) {
      switch (level) {
        case "debug":
          this.debug(message, ...args);
          break;
        case "info":
          this.info(message, ...args);
          break;
        case "warn":
          this.warn(message, ...args);
          break;
        case "error":
          this.error(message, ...args);
          break;
      }
    },
    /**
     * Group related logs (collapsible in console)
     */
    group(label) {
      if (shouldLog("debug")) {
        console.group(formatMessage("", context, label));
      }
    },
    groupEnd() {
      if (shouldLog("debug")) {
        console.groupEnd();
      }
    },
    /**
     * Log a table (useful for arrays/objects)
     */
    table(data) {
      if (shouldLog("debug")) {
        console.log(formatMessage("", context, "Table:"));
        console.table(data);
      }
    },
    /**
     * Measure time for an operation
     */
    time(label) {
      if (shouldLog("debug")) {
        console.time(`${config.prefix} [${context}] ${label}`);
      }
    },
    timeEnd(label) {
      if (shouldLog("debug")) {
        console.timeEnd(`${config.prefix} [${context}] ${label}`);
      }
    }
  };
}
const engineLogger = createLogger("Engine");
const renderLogger = createLogger("Render");

const BLUR_COMPUTE_SHADER = (
  /* wgsl */
  `
@group(0) @binding(0) var inputTexture: texture_2d<f32>;
@group(0) @binding(1) var outputTexture: texture_storage_2d<rgba8unorm, write>;
@group(0) @binding(2) var<uniform> params: BlurParams;

struct BlurParams {
  radius: f32,
  direction: f32, // 0 = horizontal, 1 = vertical
  width: f32,
  height: f32,
}

fn gaussian(x: f32, sigma: f32) -> f32 {
  return exp(-(x * x) / (2.0 * sigma * sigma)) / (sqrt(2.0 * 3.14159265) * sigma);
}

@compute @workgroup_size(16, 16)
fn main(@builtin(global_invocation_id) global_id: vec3<u32>) {
  let coords = vec2<i32>(global_id.xy);
  let dims = vec2<i32>(textureDimensions(inputTexture));

  if (coords.x >= dims.x || coords.y >= dims.y) {
    return;
  }

  let radius = i32(params.radius);
  let sigma = params.radius / 3.0;
  var color = vec4<f32>(0.0);
  var totalWeight = 0.0;

  // Separable blur: horizontal or vertical pass
  let isHorizontal = params.direction < 0.5;

  for (var i = -radius; i <= radius; i++) {
    var sampleCoords: vec2<i32>;
    if (isHorizontal) {
      sampleCoords = vec2<i32>(clamp(coords.x + i, 0, dims.x - 1), coords.y);
    } else {
      sampleCoords = vec2<i32>(coords.x, clamp(coords.y + i, 0, dims.y - 1));
    }

    let weight = gaussian(f32(i), sigma);
    color += textureLoad(inputTexture, sampleCoords, 0) * weight;
    totalWeight += weight;
  }

  color /= totalWeight;
  textureStore(outputTexture, coords, color);
}
`
);
const COLOR_CORRECTION_SHADER = (
  /* wgsl */
  `
@group(0) @binding(0) var inputTexture: texture_2d<f32>;
@group(0) @binding(1) var outputTexture: texture_storage_2d<rgba8unorm, write>;
@group(0) @binding(2) var<uniform> params: ColorParams;

struct ColorParams {
  brightness: f32,
  contrast: f32,
  saturation: f32,
  hue: f32,
}

fn rgb_to_hsv(c: vec3<f32>) -> vec3<f32> {
  let K = vec4<f32>(0.0, -1.0 / 3.0, 2.0 / 3.0, -1.0);
  let p = mix(vec4<f32>(c.bg, K.wz), vec4<f32>(c.gb, K.xy), step(c.b, c.g));
  let q = mix(vec4<f32>(p.xyw, c.r), vec4<f32>(c.r, p.yzx), step(p.x, c.r));
  let d = q.x - min(q.w, q.y);
  let e = 1.0e-10;
  return vec3<f32>(abs(q.z + (q.w - q.y) / (6.0 * d + e)), d / (q.x + e), q.x);
}

fn hsv_to_rgb(c: vec3<f32>) -> vec3<f32> {
  let K = vec4<f32>(1.0, 2.0 / 3.0, 1.0 / 3.0, 3.0);
  let p = abs(fract(c.xxx + K.xyz) * 6.0 - K.www);
  return c.z * mix(K.xxx, clamp(p - K.xxx, vec3<f32>(0.0), vec3<f32>(1.0)), c.y);
}

@compute @workgroup_size(16, 16)
fn main(@builtin(global_invocation_id) global_id: vec3<u32>) {
  let coords = vec2<i32>(global_id.xy);
  let dims = vec2<i32>(textureDimensions(inputTexture));

  if (coords.x >= dims.x || coords.y >= dims.y) {
    return;
  }

  var color = textureLoad(inputTexture, coords, 0);

  // Brightness
  color = vec4<f32>(color.rgb + params.brightness, color.a);

  // Contrast
  color = vec4<f32>((color.rgb - 0.5) * (1.0 + params.contrast) + 0.5, color.a);

  // Saturation and Hue
  var hsv = rgb_to_hsv(color.rgb);
  hsv = vec3<f32>(fract(hsv.x + params.hue / 360.0), clamp(hsv.y * (1.0 + params.saturation), 0.0, 1.0), hsv.z);
  color = vec4<f32>(hsv_to_rgb(hsv), color.a);

  // Clamp final color
  color = clamp(color, vec4<f32>(0.0), vec4<f32>(1.0));

  textureStore(outputTexture, coords, color);
}
`
);
const RADIAL_BLUR_SHADER = (
  /* wgsl */
  `
@group(0) @binding(0) var inputTexture: texture_2d<f32>;
@group(0) @binding(1) var outputTexture: texture_storage_2d<rgba8unorm, write>;
@group(0) @binding(2) var<uniform> params: RadialBlurParams;

struct RadialBlurParams {
  centerX: f32,
  centerY: f32,
  amount: f32,
  samples: u32,
}

@compute @workgroup_size(16, 16)
fn main(@builtin(global_invocation_id) global_id: vec3<u32>) {
  let coords = vec2<i32>(global_id.xy);
  let dims = vec2<i32>(textureDimensions(inputTexture));

  if (coords.x >= dims.x || coords.y >= dims.y) {
    return;
  }

  let center = vec2<f32>(params.centerX * f32(dims.x), params.centerY * f32(dims.y));
  let pos = vec2<f32>(f32(coords.x), f32(coords.y));
  let dir = pos - center;
  let dist = length(dir);

  var color = vec4<f32>(0.0);
  let numSamples = params.samples;

  for (var i = 0u; i < numSamples; i++) {
    let t = f32(i) / f32(numSamples - 1u) - 0.5;
    let offset = dir * t * params.amount * 0.01;
    let samplePos = vec2<i32>(clamp(pos + offset, vec2<f32>(0.0), vec2<f32>(f32(dims.x - 1), f32(dims.y - 1))));
    color += textureLoad(inputTexture, samplePos, 0);
  }

  color /= f32(numSamples);
  textureStore(outputTexture, coords, color);
}
`
);
const DIRECTIONAL_BLUR_SHADER = (
  /* wgsl */
  `
@group(0) @binding(0) var inputTexture: texture_2d<f32>;
@group(0) @binding(1) var outputTexture: texture_storage_2d<rgba8unorm, write>;
@group(0) @binding(2) var<uniform> params: DirectionalBlurParams;

struct DirectionalBlurParams {
  angle: f32,
  length: f32,
  samples: u32,
  _pad: u32,
}

@compute @workgroup_size(16, 16)
fn main(@builtin(global_invocation_id) global_id: vec3<u32>) {
  let coords = vec2<i32>(global_id.xy);
  let dims = vec2<i32>(textureDimensions(inputTexture));

  if (coords.x >= dims.x || coords.y >= dims.y) {
    return;
  }

  let angleRad = params.angle * 3.14159265 / 180.0;
  let dir = vec2<f32>(cos(angleRad), sin(angleRad)) * params.length;

  var color = vec4<f32>(0.0);
  let numSamples = params.samples;

  for (var i = 0u; i < numSamples; i++) {
    let t = f32(i) / f32(numSamples - 1u) - 0.5;
    let offset = dir * t;
    let samplePos = vec2<i32>(clamp(
      vec2<f32>(f32(coords.x), f32(coords.y)) + offset,
      vec2<f32>(0.0),
      vec2<f32>(f32(dims.x - 1), f32(dims.y - 1))
    ));
    color += textureLoad(inputTexture, samplePos, 0);
  }

  color /= f32(numSamples);
  textureStore(outputTexture, coords, color);
}
`
);
const DISPLACEMENT_SHADER = (
  /* wgsl */
  `
@group(0) @binding(0) var inputTexture: texture_2d<f32>;
@group(0) @binding(1) var displacementMap: texture_2d<f32>;
@group(0) @binding(2) var outputTexture: texture_storage_2d<rgba8unorm, write>;
@group(0) @binding(3) var<uniform> params: DisplacementParams;

struct DisplacementParams {
  maxHorizontal: f32,
  maxVertical: f32,
  hChannel: u32,  // 0=red, 1=green, 2=blue, 3=alpha, 4=luminance
  vChannel: u32,
}

fn getChannelValue(color: vec4<f32>, channel: u32) -> f32 {
  switch channel {
    case 0u: { return color.r; }
    case 1u: { return color.g; }
    case 2u: { return color.b; }
    case 3u: { return color.a; }
    default: { return 0.299 * color.r + 0.587 * color.g + 0.114 * color.b; }
  }
}

@compute @workgroup_size(16, 16)
fn main(@builtin(global_invocation_id) global_id: vec3<u32>) {
  let coords = vec2<i32>(global_id.xy);
  let dims = vec2<i32>(textureDimensions(inputTexture));

  if (coords.x >= dims.x || coords.y >= dims.y) {
    return;
  }

  let mapColor = textureLoad(displacementMap, coords, 0);

  let hValue = getChannelValue(mapColor, params.hChannel);
  let vValue = getChannelValue(mapColor, params.vChannel);

  // Map 0-1 to -1 to 1, then scale by max displacement
  let dx = (hValue - 0.5) * 2.0 * params.maxHorizontal;
  let dy = (vValue - 0.5) * 2.0 * params.maxVertical;

  let srcPos = vec2<i32>(clamp(
    vec2<f32>(f32(coords.x) - dx, f32(coords.y) - dy),
    vec2<f32>(0.0),
    vec2<f32>(f32(dims.x - 1), f32(dims.y - 1))
  ));

  let color = textureLoad(inputTexture, srcPos, 0);
  textureStore(outputTexture, coords, color);
}
`
);
const WARP_SHADER = (
  /* wgsl */
  `
@group(0) @binding(0) var inputTexture: texture_2d<f32>;
@group(0) @binding(1) var outputTexture: texture_storage_2d<rgba8unorm, write>;
@group(0) @binding(2) var<uniform> params: WarpParams;

struct WarpParams {
  warpStyle: u32,  // 0=bulge, 1=wave, 2=fisheye, 3=twist
  bend: f32,
  hDistort: f32,
  vDistort: f32,
}

@compute @workgroup_size(16, 16)
fn main(@builtin(global_invocation_id) global_id: vec3<u32>) {
  let coords = vec2<i32>(global_id.xy);
  let dims = vec2<i32>(textureDimensions(inputTexture));

  if (coords.x >= dims.x || coords.y >= dims.y) {
    return;
  }

  let centerX = f32(dims.x) / 2.0;
  let centerY = f32(dims.y) / 2.0;

  // Normalize to -1 to 1
  let nx = (f32(coords.x) - centerX) / centerX;
  let ny = (f32(coords.y) - centerY) / centerY;

  var srcX = f32(coords.x);
  var srcY = f32(coords.y);

  switch params.warpStyle {
    case 0u: { // Bulge
      let r = sqrt(nx * nx + ny * ny);
      if (r < 1.0) {
        let factor = 1.0 + params.bend * (1.0 - r * r);
        srcX = centerX + (f32(coords.x) - centerX) / factor;
        srcY = centerY + (f32(coords.y) - centerY) / factor;
      }
    }
    case 1u: { // Wave
      srcX = f32(coords.x) + sin(ny * 3.14159265 * 2.0) * params.bend * f32(dims.x) * 0.1;
      srcY = f32(coords.y) + sin(nx * 3.14159265 * 2.0) * params.bend * f32(dims.y) * 0.1;
    }
    case 2u: { // Fisheye
      let r = sqrt(nx * nx + ny * ny);
      if (r > 0.0 && r < 1.0) {
        let theta = atan2(ny, nx);
        let newR = pow(r, 1.0 + params.bend);
        srcX = centerX + newR * cos(theta) * centerX;
        srcY = centerY + newR * sin(theta) * centerY;
      }
    }
    case 3u: { // Twist
      let r = sqrt(nx * nx + ny * ny);
      let angle = params.bend * 3.14159265 * (1.0 - r);
      let cosA = cos(angle);
      let sinA = sin(angle);
      srcX = centerX + (nx * cosA - ny * sinA) * centerX;
      srcY = centerY + (nx * sinA + ny * cosA) * centerY;
    }
    default: {}
  }

  // Apply additional distortion
  srcX += params.hDistort * centerX * (1.0 - ny * ny);
  srcY += params.vDistort * centerY * (1.0 - nx * nx);

  let srcPos = vec2<i32>(clamp(
    vec2<f32>(srcX, srcY),
    vec2<f32>(0.0),
    vec2<f32>(f32(dims.x - 1), f32(dims.y - 1))
  ));

  let color = textureLoad(inputTexture, srcPos, 0);
  textureStore(outputTexture, coords, color);
}
`
);
const GLOW_SHADER = (
  /* wgsl */
  `
@group(0) @binding(0) var inputTexture: texture_2d<f32>;
@group(0) @binding(1) var outputTexture: texture_storage_2d<rgba8unorm, write>;
@group(0) @binding(2) var<uniform> params: GlowParams;

struct GlowParams {
  radius: f32,
  intensity: f32,
  threshold: f32,
  _pad: f32,
  glowColor: vec4<f32>,
}

fn gaussian(x: f32, sigma: f32) -> f32 {
  return exp(-(x * x) / (2.0 * sigma * sigma));
}

@compute @workgroup_size(16, 16)
fn main(@builtin(global_invocation_id) global_id: vec3<u32>) {
  let coords = vec2<i32>(global_id.xy);
  let dims = vec2<i32>(textureDimensions(inputTexture));

  if (coords.x >= dims.x || coords.y >= dims.y) {
    return;
  }

  let originalColor = textureLoad(inputTexture, coords, 0);

  // Sample and blur bright areas
  let radius = i32(params.radius);
  let sigma = params.radius / 3.0;
  var glowAccum = vec4<f32>(0.0);
  var totalWeight = 0.0;

  for (var dy = -radius; dy <= radius; dy++) {
    for (var dx = -radius; dx <= radius; dx++) {
      let sampleCoords = vec2<i32>(
        clamp(coords.x + dx, 0, dims.x - 1),
        clamp(coords.y + dy, 0, dims.y - 1)
      );

      let sampleColor = textureLoad(inputTexture, sampleCoords, 0);
      let luminance = 0.299 * sampleColor.r + 0.587 * sampleColor.g + 0.114 * sampleColor.b;

      if (luminance > params.threshold) {
        let dist = sqrt(f32(dx * dx + dy * dy));
        let weight = gaussian(dist, sigma);
        glowAccum += sampleColor * weight;
        totalWeight += weight;
      }
    }
  }

  var glowColor = vec4<f32>(0.0);
  if (totalWeight > 0.0) {
    glowColor = glowAccum / totalWeight;
    // Tint with glow color if not white
    if (params.glowColor.r < 1.0 || params.glowColor.g < 1.0 || params.glowColor.b < 1.0) {
      glowColor = vec4<f32>(glowColor.rgb * params.glowColor.rgb, glowColor.a);
    }
  }

  // Composite: original + glow * intensity
  var finalColor = originalColor + glowColor * params.intensity;
  finalColor = clamp(finalColor, vec4<f32>(0.0), vec4<f32>(1.0));
  finalColor = vec4<f32>(finalColor.rgb, originalColor.a);

  textureStore(outputTexture, coords, finalColor);
}
`
);
const LEVELS_SHADER = (
  /* wgsl */
  `
@group(0) @binding(0) var inputTexture: texture_2d<f32>;
@group(0) @binding(1) var outputTexture: texture_storage_2d<rgba8unorm, write>;
@group(0) @binding(2) var<uniform> params: LevelsParams;

struct LevelsParams {
  inputBlack: f32,
  inputWhite: f32,
  gamma: f32,
  outputBlack: f32,
  outputWhite: f32,
  _pad1: f32,
  _pad2: f32,
  _pad3: f32,
}

@compute @workgroup_size(16, 16)
fn main(@builtin(global_invocation_id) global_id: vec3<u32>) {
  let coords = vec2<i32>(global_id.xy);
  let dims = vec2<i32>(textureDimensions(inputTexture));

  if (coords.x >= dims.x || coords.y >= dims.y) {
    return;
  }

  var color = textureLoad(inputTexture, coords, 0);

  // Input levels
  let inputRange = max(params.inputWhite - params.inputBlack, 0.001);
  color = vec4<f32>(clamp((color.rgb - params.inputBlack) / inputRange, vec3<f32>(0.0), vec3<f32>(1.0)), color.a);

  // Gamma
  let invGamma = 1.0 / params.gamma;
  color = vec4<f32>(pow(color.rgb, vec3<f32>(invGamma)), color.a);

  // Output levels
  let outputRange = params.outputWhite - params.outputBlack;
  color = vec4<f32>(params.outputBlack + color.rgb * outputRange, color.a);

  textureStore(outputTexture, coords, color);
}
`
);
class WebGPURenderer {
  capabilities = {
    available: false,
    adapter: null,
    device: null,
    features: [],
    limits: {}
  };
  initialized = false;
  initPromise = null;
  // Shader modules
  blurModule = null;
  colorModule = null;
  radialBlurModule = null;
  directionalBlurModule = null;
  displacementModule = null;
  warpModule = null;
  glowModule = null;
  levelsModule = null;
  // Pipelines
  blurPipeline = null;
  colorPipeline = null;
  radialBlurPipeline = null;
  directionalBlurPipeline = null;
  warpPipeline = null;
  glowPipeline = null;
  levelsPipeline = null;
  displacementPipeline = null;
  // Bind group layouts
  blurBindGroupLayout = null;
  colorBindGroupLayout = null;
  radialBlurBindGroupLayout = null;
  directionalBlurBindGroupLayout = null;
  warpBindGroupLayout = null;
  glowBindGroupLayout = null;
  levelsBindGroupLayout = null;
  displacementBindGroupLayout = null;
  /**
   * Initialize WebGPU renderer
   * Returns true if WebGPU is available and initialized
   */
  async initialize() {
    if (this.initialized) return this.capabilities.available;
    if (this.initPromise) return this.initPromise;
    this.initPromise = this.doInitialize();
    return this.initPromise;
  }
  async doInitialize() {
    try {
      if (!("gpu" in navigator)) {
        engineLogger.info("WebGPU not available - using Canvas2D fallback");
        this.initialized = true;
        return false;
      }
      const adapter = await navigator.gpu.requestAdapter({
        powerPreference: "high-performance"
      });
      if (!adapter) {
        engineLogger.warn("WebGPU adapter not available");
        this.initialized = true;
        return false;
      }
      const device = await adapter.requestDevice({
        requiredFeatures: [],
        requiredLimits: {}
      });
      this.capabilities = {
        available: true,
        adapter,
        device,
        features: [...adapter.features],
        limits: {
          maxBufferSize: device.limits.maxBufferSize,
          maxComputeWorkgroupSizeX: device.limits.maxComputeWorkgroupSizeX,
          maxComputeWorkgroupSizeY: device.limits.maxComputeWorkgroupSizeY
        }
      };
      await this.createShaderModules();
      await this.createPipelines();
      engineLogger.info("WebGPU initialized successfully", {
        features: this.capabilities.features.slice(0, 5)
      });
      this.initialized = true;
      return true;
    } catch (error) {
      engineLogger.error("WebGPU initialization failed:", error);
      this.initialized = true;
      return false;
    }
  }
  async createShaderModules() {
    if (!this.capabilities.device) return;
    const device = this.capabilities.device;
    this.blurModule = device.createShaderModule({ code: BLUR_COMPUTE_SHADER });
    this.colorModule = device.createShaderModule({
      code: COLOR_CORRECTION_SHADER
    });
    this.radialBlurModule = device.createShaderModule({
      code: RADIAL_BLUR_SHADER
    });
    this.directionalBlurModule = device.createShaderModule({
      code: DIRECTIONAL_BLUR_SHADER
    });
    this.displacementModule = device.createShaderModule({
      code: DISPLACEMENT_SHADER
    });
    this.warpModule = device.createShaderModule({ code: WARP_SHADER });
    this.glowModule = device.createShaderModule({ code: GLOW_SHADER });
    this.levelsModule = device.createShaderModule({ code: LEVELS_SHADER });
  }
  async createPipelines() {
    if (!this.capabilities.device || !this.blurModule || !this.colorModule)
      return;
    const device = this.capabilities.device;
    const standardLayout = device.createBindGroupLayout({
      entries: [
        {
          binding: 0,
          visibility: GPUShaderStage.COMPUTE,
          texture: { sampleType: "float" }
        },
        {
          binding: 1,
          visibility: GPUShaderStage.COMPUTE,
          storageTexture: { format: "rgba8unorm", access: "write-only" }
        },
        {
          binding: 2,
          visibility: GPUShaderStage.COMPUTE,
          buffer: { type: "uniform" }
        }
      ]
    });
    const displacementLayout = device.createBindGroupLayout({
      entries: [
        {
          binding: 0,
          visibility: GPUShaderStage.COMPUTE,
          texture: { sampleType: "float" }
        },
        {
          binding: 1,
          visibility: GPUShaderStage.COMPUTE,
          texture: { sampleType: "float" }
        },
        {
          binding: 2,
          visibility: GPUShaderStage.COMPUTE,
          storageTexture: { format: "rgba8unorm", access: "write-only" }
        },
        {
          binding: 3,
          visibility: GPUShaderStage.COMPUTE,
          buffer: { type: "uniform" }
        }
      ]
    });
    this.blurBindGroupLayout = standardLayout;
    this.colorBindGroupLayout = standardLayout;
    this.radialBlurBindGroupLayout = standardLayout;
    this.directionalBlurBindGroupLayout = standardLayout;
    this.warpBindGroupLayout = standardLayout;
    this.glowBindGroupLayout = standardLayout;
    this.levelsBindGroupLayout = standardLayout;
    this.displacementBindGroupLayout = displacementLayout;
    const createPipeline = (module, layout) => device.createComputePipeline({
      layout: device.createPipelineLayout({ bindGroupLayouts: [layout] }),
      compute: { module, entryPoint: "main" }
    });
    this.blurPipeline = createPipeline(this.blurModule, standardLayout);
    this.colorPipeline = createPipeline(this.colorModule, standardLayout);
    this.radialBlurPipeline = createPipeline(
      this.radialBlurModule,
      standardLayout
    );
    this.directionalBlurPipeline = createPipeline(
      this.directionalBlurModule,
      standardLayout
    );
    this.warpPipeline = createPipeline(this.warpModule, standardLayout);
    this.glowPipeline = createPipeline(this.glowModule, standardLayout);
    this.levelsPipeline = createPipeline(this.levelsModule, standardLayout);
    this.displacementPipeline = createPipeline(
      this.displacementModule,
      displacementLayout
    );
  }
  /**
   * Check if WebGPU is available
   */
  isAvailable() {
    return this.capabilities.available;
  }
  /**
   * Get WebGPU capabilities
   */
  getCapabilities() {
    return { ...this.capabilities };
  }
  /**
   * Apply Gaussian blur using GPU compute shader
   * Falls back to Canvas2D if WebGPU unavailable
   */
  async blur(source, params) {
    if (!this.capabilities.available || !this.capabilities.device) {
      return this.blurCanvas2D(source, params);
    }
    try {
      return await this.blurWebGPU(source, params);
    } catch (error) {
      engineLogger.warn("WebGPU blur failed, falling back to Canvas2D:", error);
      return this.blurCanvas2D(source, params);
    }
  }
  async blurWebGPU(source, params) {
    const device = this.capabilities.device;
    const imageData = this.toImageData(source);
    const { width, height } = imageData;
    const inputTexture = device.createTexture({
      size: [width, height],
      format: "rgba8unorm",
      usage: GPUTextureUsage.TEXTURE_BINDING | GPUTextureUsage.COPY_DST
    });
    device.queue.writeTexture(
      { texture: inputTexture },
      imageData.data,
      { bytesPerRow: width * 4, rowsPerImage: height },
      { width, height }
    );
    const outputTexture = device.createTexture({
      size: [width, height],
      format: "rgba8unorm",
      usage: GPUTextureUsage.STORAGE_BINDING | GPUTextureUsage.COPY_SRC
    });
    const paramsBuffer = device.createBuffer({
      size: 16,
      // 4 floats
      usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST,
      mappedAtCreation: true
    });
    new Float32Array(paramsBuffer.getMappedRange()).set([
      params.radius,
      params.direction === "vertical" ? 1 : 0,
      width,
      height
    ]);
    paramsBuffer.unmap();
    const bindGroup = device.createBindGroup({
      layout: this.blurBindGroupLayout,
      entries: [
        { binding: 0, resource: inputTexture.createView() },
        { binding: 1, resource: outputTexture.createView() },
        { binding: 2, resource: { buffer: paramsBuffer } }
      ]
    });
    const commandEncoder = device.createCommandEncoder();
    const passEncoder = commandEncoder.beginComputePass();
    passEncoder.setPipeline(this.blurPipeline);
    passEncoder.setBindGroup(0, bindGroup);
    passEncoder.dispatchWorkgroups(
      Math.ceil(width / 16),
      Math.ceil(height / 16)
    );
    passEncoder.end();
    const outputBuffer = device.createBuffer({
      size: width * height * 4,
      usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ
    });
    commandEncoder.copyTextureToBuffer(
      { texture: outputTexture },
      { buffer: outputBuffer, bytesPerRow: width * 4 },
      { width, height }
    );
    device.queue.submit([commandEncoder.finish()]);
    await outputBuffer.mapAsync(GPUMapMode.READ);
    const resultData = new Uint8ClampedArray(
      outputBuffer.getMappedRange().slice(0)
    );
    outputBuffer.unmap();
    inputTexture.destroy();
    outputTexture.destroy();
    paramsBuffer.destroy();
    outputBuffer.destroy();
    return new ImageData(resultData, width, height);
  }
  blurCanvas2D(source, params) {
    const imageData = this.toImageData(source);
    const canvas = new OffscreenCanvas(imageData.width, imageData.height);
    const ctx = canvas.getContext("2d");
    ctx.putImageData(imageData, 0, 0);
    ctx.filter = `blur(${params.radius}px)`;
    ctx.drawImage(canvas, 0, 0);
    return ctx.getImageData(0, 0, imageData.width, imageData.height);
  }
  /**
   * Apply color correction using GPU compute shader
   */
  async colorCorrect(source, params) {
    if (!this.capabilities.available || !this.capabilities.device) {
      return this.colorCorrectCanvas2D(source, params);
    }
    try {
      return await this.colorCorrectWebGPU(source, params);
    } catch (error) {
      engineLogger.warn("WebGPU color correction failed, falling back:", error);
      return this.colorCorrectCanvas2D(source, params);
    }
  }
  async colorCorrectWebGPU(source, params) {
    const device = this.capabilities.device;
    const imageData = this.toImageData(source);
    const { width, height } = imageData;
    const inputTexture = device.createTexture({
      size: [width, height],
      format: "rgba8unorm",
      usage: GPUTextureUsage.TEXTURE_BINDING | GPUTextureUsage.COPY_DST
    });
    device.queue.writeTexture(
      { texture: inputTexture },
      imageData.data,
      { bytesPerRow: width * 4, rowsPerImage: height },
      { width, height }
    );
    const outputTexture = device.createTexture({
      size: [width, height],
      format: "rgba8unorm",
      usage: GPUTextureUsage.STORAGE_BINDING | GPUTextureUsage.COPY_SRC
    });
    const paramsBuffer = device.createBuffer({
      size: 16,
      usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST,
      mappedAtCreation: true
    });
    new Float32Array(paramsBuffer.getMappedRange()).set([
      params.brightness,
      params.contrast,
      params.saturation,
      params.hue
    ]);
    paramsBuffer.unmap();
    const bindGroup = device.createBindGroup({
      layout: this.colorBindGroupLayout,
      entries: [
        { binding: 0, resource: inputTexture.createView() },
        { binding: 1, resource: outputTexture.createView() },
        { binding: 2, resource: { buffer: paramsBuffer } }
      ]
    });
    const commandEncoder = device.createCommandEncoder();
    const passEncoder = commandEncoder.beginComputePass();
    passEncoder.setPipeline(this.colorPipeline);
    passEncoder.setBindGroup(0, bindGroup);
    passEncoder.dispatchWorkgroups(
      Math.ceil(width / 16),
      Math.ceil(height / 16)
    );
    passEncoder.end();
    const outputBuffer = device.createBuffer({
      size: width * height * 4,
      usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ
    });
    commandEncoder.copyTextureToBuffer(
      { texture: outputTexture },
      { buffer: outputBuffer, bytesPerRow: width * 4 },
      { width, height }
    );
    device.queue.submit([commandEncoder.finish()]);
    await outputBuffer.mapAsync(GPUMapMode.READ);
    const resultData = new Uint8ClampedArray(
      outputBuffer.getMappedRange().slice(0)
    );
    outputBuffer.unmap();
    inputTexture.destroy();
    outputTexture.destroy();
    paramsBuffer.destroy();
    outputBuffer.destroy();
    return new ImageData(resultData, width, height);
  }
  colorCorrectCanvas2D(source, params) {
    const imageData = this.toImageData(source);
    const data = imageData.data;
    for (let i = 0; i < data.length; i += 4) {
      let r = data[i] / 255;
      let g = data[i + 1] / 255;
      let b = data[i + 2] / 255;
      r += params.brightness;
      g += params.brightness;
      b += params.brightness;
      r = (r - 0.5) * (1 + params.contrast) + 0.5;
      g = (g - 0.5) * (1 + params.contrast) + 0.5;
      b = (b - 0.5) * (1 + params.contrast) + 0.5;
      const gray = 0.299 * r + 0.587 * g + 0.114 * b;
      const satMult = 1 + params.saturation;
      r = gray + (r - gray) * satMult;
      g = gray + (g - gray) * satMult;
      b = gray + (b - gray) * satMult;
      data[i] = Math.max(0, Math.min(255, Math.round(r * 255)));
      data[i + 1] = Math.max(0, Math.min(255, Math.round(g * 255)));
      data[i + 2] = Math.max(0, Math.min(255, Math.round(b * 255)));
    }
    return imageData;
  }
  // ============================================================================
  // NEW GPU-ACCELERATED EFFECTS
  // ============================================================================
  /**
   * Apply radial blur (zoom blur) using GPU compute shader
   */
  async radialBlur(source, params) {
    if (!this.capabilities.available || !this.radialBlurPipeline) {
      return this.radialBlurCanvas2D(source, params);
    }
    return this.runStandardCompute(
      source,
      this.radialBlurPipeline,
      this.radialBlurBindGroupLayout,
      [params.centerX, params.centerY, params.amount, params.samples ?? 32]
    );
  }
  radialBlurCanvas2D(source, params) {
    const imageData = this.toImageData(source);
    const { width, height, data } = imageData;
    const output = new Uint8ClampedArray(data.length);
    const centerX = params.centerX * width;
    const centerY = params.centerY * height;
    const samples = params.samples ?? 32;
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const dx = x - centerX;
        const dy = y - centerY;
        let r = 0, g = 0, b = 0, a = 0;
        for (let s = 0; s < samples; s++) {
          const t = s / (samples - 1) - 0.5;
          const sx = Math.round(x + dx * t * params.amount * 0.01);
          const sy = Math.round(y + dy * t * params.amount * 0.01);
          const clampX = Math.max(0, Math.min(width - 1, sx));
          const clampY = Math.max(0, Math.min(height - 1, sy));
          const si = (clampY * width + clampX) * 4;
          r += data[si];
          g += data[si + 1];
          b += data[si + 2];
          a += data[si + 3];
        }
        const i = (y * width + x) * 4;
        output[i] = r / samples;
        output[i + 1] = g / samples;
        output[i + 2] = b / samples;
        output[i + 3] = a / samples;
      }
    }
    return new ImageData(output, width, height);
  }
  /**
   * Apply directional (motion) blur using GPU compute shader
   */
  async directionalBlur(source, params) {
    if (!this.capabilities.available || !this.directionalBlurPipeline) {
      return this.directionalBlurCanvas2D(source, params);
    }
    return this.runStandardCompute(
      source,
      this.directionalBlurPipeline,
      this.directionalBlurBindGroupLayout,
      [
        params.angle,
        params.length,
        params.samples ?? 32,
        0
        // padding
      ]
    );
  }
  directionalBlurCanvas2D(source, params) {
    const imageData = this.toImageData(source);
    const { width, height, data } = imageData;
    const output = new Uint8ClampedArray(data.length);
    const angleRad = params.angle * Math.PI / 180;
    const dirX = Math.cos(angleRad) * params.length;
    const dirY = Math.sin(angleRad) * params.length;
    const samples = params.samples ?? 32;
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        let r = 0, g = 0, b = 0, a = 0;
        for (let s = 0; s < samples; s++) {
          const t = s / (samples - 1) - 0.5;
          const sx = Math.max(0, Math.min(width - 1, Math.round(x + dirX * t)));
          const sy = Math.max(
            0,
            Math.min(height - 1, Math.round(y + dirY * t))
          );
          const si = (sy * width + sx) * 4;
          r += data[si];
          g += data[si + 1];
          b += data[si + 2];
          a += data[si + 3];
        }
        const i = (y * width + x) * 4;
        output[i] = r / samples;
        output[i + 1] = g / samples;
        output[i + 2] = b / samples;
        output[i + 3] = a / samples;
      }
    }
    return new ImageData(output, width, height);
  }
  /**
   * Apply warp distortion using GPU compute shader
   */
  async warp(source, params) {
    if (!this.capabilities.available || !this.warpPipeline) {
      return this.warpCanvas2D(source, params);
    }
    const styleMap = { bulge: 0, wave: 1, fisheye: 2, twist: 3 };
    return this.runStandardCompute(
      source,
      this.warpPipeline,
      this.warpBindGroupLayout,
      [
        styleMap[params.style] ?? 0,
        params.bend,
        params.hDistort ?? 0,
        params.vDistort ?? 0
      ]
    );
  }
  warpCanvas2D(source, _params) {
    const imageData = this.toImageData(source);
    return imageData;
  }
  /**
   * Apply glow effect using GPU compute shader
   */
  async glow(source, params) {
    if (!this.capabilities.available || !this.glowPipeline) {
      return this.glowCanvas2D(source, params);
    }
    this.toImageData(source);
    const paramsData = new Float32Array([
      params.radius,
      params.intensity,
      params.threshold ?? 0.5,
      0,
      // padding
      params.color?.r ?? 1,
      params.color?.g ?? 1,
      params.color?.b ?? 1,
      1
      // alpha
    ]);
    return this.runStandardComputeWithParams(
      source,
      this.glowPipeline,
      this.glowBindGroupLayout,
      paramsData
    );
  }
  glowCanvas2D(source, _params) {
    return this.toImageData(source);
  }
  /**
   * Apply levels adjustment using GPU compute shader
   */
  async levels(source, params) {
    if (!this.capabilities.available || !this.levelsPipeline) {
      return this.levelsCanvas2D(source, params);
    }
    return this.runStandardComputeWithParams(
      source,
      this.levelsPipeline,
      this.levelsBindGroupLayout,
      new Float32Array([
        params.inputBlack,
        params.inputWhite,
        params.gamma,
        params.outputBlack,
        params.outputWhite,
        0,
        0,
        0
        // padding to 32 bytes
      ])
    );
  }
  levelsCanvas2D(source, params) {
    const imageData = this.toImageData(source);
    const data = imageData.data;
    const inputRange = Math.max(params.inputWhite - params.inputBlack, 1e-3);
    const outputRange = params.outputWhite - params.outputBlack;
    const invGamma = 1 / params.gamma;
    for (let i = 0; i < data.length; i += 4) {
      for (let c = 0; c < 3; c++) {
        let v = data[i + c] / 255;
        v = Math.max(0, Math.min(1, (v - params.inputBlack) / inputRange));
        v = v ** invGamma;
        v = params.outputBlack + v * outputRange;
        data[i + c] = Math.max(0, Math.min(255, Math.round(v * 255)));
      }
    }
    return imageData;
  }
  // ============================================================================
  // HELPER METHODS
  // ============================================================================
  /**
   * Run a standard compute shader with 4 float params
   */
  async runStandardCompute(source, pipeline, layout, params) {
    return this.runStandardComputeWithParams(
      source,
      pipeline,
      layout,
      new Float32Array(params)
    );
  }
  /**
   * Run a standard compute shader with arbitrary params buffer
   */
  async runStandardComputeWithParams(source, pipeline, layout, paramsData) {
    const device = this.capabilities.device;
    const imageData = this.toImageData(source);
    const { width, height } = imageData;
    const inputTexture = device.createTexture({
      size: [width, height],
      format: "rgba8unorm",
      usage: GPUTextureUsage.TEXTURE_BINDING | GPUTextureUsage.COPY_DST
    });
    device.queue.writeTexture(
      { texture: inputTexture },
      imageData.data,
      { bytesPerRow: width * 4, rowsPerImage: height },
      { width, height }
    );
    const outputTexture = device.createTexture({
      size: [width, height],
      format: "rgba8unorm",
      usage: GPUTextureUsage.STORAGE_BINDING | GPUTextureUsage.COPY_SRC
    });
    const bufferSize = Math.max(16, Math.ceil(paramsData.byteLength / 16) * 16);
    const paramsBuffer = device.createBuffer({
      size: bufferSize,
      usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST,
      mappedAtCreation: true
    });
    new Float32Array(paramsBuffer.getMappedRange()).set(paramsData);
    paramsBuffer.unmap();
    const bindGroup = device.createBindGroup({
      layout,
      entries: [
        { binding: 0, resource: inputTexture.createView() },
        { binding: 1, resource: outputTexture.createView() },
        { binding: 2, resource: { buffer: paramsBuffer } }
      ]
    });
    const commandEncoder = device.createCommandEncoder();
    const passEncoder = commandEncoder.beginComputePass();
    passEncoder.setPipeline(pipeline);
    passEncoder.setBindGroup(0, bindGroup);
    passEncoder.dispatchWorkgroups(
      Math.ceil(width / 16),
      Math.ceil(height / 16)
    );
    passEncoder.end();
    const outputBuffer = device.createBuffer({
      size: width * height * 4,
      usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ
    });
    commandEncoder.copyTextureToBuffer(
      { texture: outputTexture },
      { buffer: outputBuffer, bytesPerRow: width * 4 },
      { width, height }
    );
    device.queue.submit([commandEncoder.finish()]);
    await outputBuffer.mapAsync(GPUMapMode.READ);
    const resultData = new Uint8ClampedArray(
      outputBuffer.getMappedRange().slice(0)
    );
    outputBuffer.unmap();
    inputTexture.destroy();
    outputTexture.destroy();
    paramsBuffer.destroy();
    outputBuffer.destroy();
    return new ImageData(resultData, width, height);
  }
  /**
   * Convert source to ImageData
   */
  toImageData(source) {
    if (source instanceof ImageData) {
      return source;
    }
    const ctx = source.getContext("2d");
    return ctx.getImageData(0, 0, source.width, source.height);
  }
  /**
   * Dispose of WebGPU resources
   */
  dispose() {
    if (this.capabilities.device) {
      this.capabilities.device.destroy();
    }
    this.capabilities = {
      available: false,
      adapter: null,
      device: null,
      features: [],
      limits: {}
    };
    this.initialized = false;
    this.initPromise = null;
    this.blurModule = null;
    this.colorModule = null;
    this.radialBlurModule = null;
    this.directionalBlurModule = null;
    this.displacementModule = null;
    this.warpModule = null;
    this.glowModule = null;
    this.levelsModule = null;
    this.blurPipeline = null;
    this.colorPipeline = null;
    this.radialBlurPipeline = null;
    this.directionalBlurPipeline = null;
    this.displacementPipeline = null;
    this.warpPipeline = null;
    this.glowPipeline = null;
    this.levelsPipeline = null;
    this.blurBindGroupLayout = null;
    this.colorBindGroupLayout = null;
    this.radialBlurBindGroupLayout = null;
    this.directionalBlurBindGroupLayout = null;
    this.displacementBindGroupLayout = null;
    this.warpBindGroupLayout = null;
    this.glowBindGroupLayout = null;
    this.levelsBindGroupLayout = null;
    engineLogger.info("WebGPU renderer disposed");
  }
}
const webgpuRenderer = new WebGPURenderer();

const DEFAULT_FPS = 16;
const MIN_FPS = 1;
const MAX_FPS = 120;
function validateFps(fps, fallback = DEFAULT_FPS) {
  if (fps === null || fps === void 0 || !Number.isFinite(fps) || fps <= 0) {
    return fallback;
  }
  return Math.max(MIN_FPS, Math.min(MAX_FPS, fps));
}

const PI = Math.PI;
const c1$1 = 1.70158;
const c2$1 = c1$1 * 1.525;
const c3$1 = c1$1 + 1;
const c4$1 = 2 * PI / 3;
const c5$1 = 2 * PI / 4.5;
const easings = {
  // Linear - no easing
  linear: (t) => t,
  // Sine easing
  // FIX: Handle boundary conditions explicitly for floating point precision
  easeInSine: (t) => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    return 1 - Math.cos(t * PI / 2);
  },
  easeOutSine: (t) => Math.sin(t * PI / 2),
  easeInOutSine: (t) => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    return -(Math.cos(PI * t) - 1) / 2;
  },
  // Quad (power of 2)
  easeInQuad: (t) => t * t,
  easeOutQuad: (t) => 1 - (1 - t) * (1 - t),
  easeInOutQuad: (t) => t < 0.5 ? 2 * t * t : 1 - (-2 * t + 2) ** 2 / 2,
  // Cubic (power of 3)
  easeInCubic: (t) => t * t * t,
  easeOutCubic: (t) => 1 - (1 - t) ** 3,
  easeInOutCubic: (t) => t < 0.5 ? 4 * t * t * t : 1 - (-2 * t + 2) ** 3 / 2,
  // Quart (power of 4)
  easeInQuart: (t) => t * t * t * t,
  easeOutQuart: (t) => 1 - (1 - t) ** 4,
  easeInOutQuart: (t) => t < 0.5 ? 8 * t * t * t * t : 1 - (-2 * t + 2) ** 4 / 2,
  // Quint (power of 5)
  easeInQuint: (t) => t * t * t * t * t,
  easeOutQuint: (t) => 1 - (1 - t) ** 5,
  easeInOutQuint: (t) => t < 0.5 ? 16 * t * t * t * t * t : 1 - (-2 * t + 2) ** 5 / 2,
  // Expo (exponential)
  easeInExpo: (t) => t === 0 ? 0 : 2 ** (10 * t - 10),
  easeOutExpo: (t) => t === 1 ? 1 : 1 - 2 ** (-10 * t),
  easeInOutExpo: (t) => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    if (t < 0.5) return 2 ** (20 * t - 10) / 2;
    return (2 - 2 ** (-20 * t + 10)) / 2;
  },
  // Circ (circular)
  easeInCirc: (t) => 1 - Math.sqrt(1 - t ** 2),
  easeOutCirc: (t) => Math.sqrt(1 - (t - 1) ** 2),
  easeInOutCirc: (t) => t < 0.5 ? (1 - Math.sqrt(1 - (2 * t) ** 2)) / 2 : (Math.sqrt(1 - (-2 * t + 2) ** 2) + 1) / 2,
  // Back (overshoot)
  // FIX: Handle boundary conditions explicitly for floating point precision
  easeInBack: (t) => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    return c3$1 * t * t * t - c1$1 * t * t;
  },
  easeOutBack: (t) => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    return 1 + c3$1 * (t - 1) ** 3 + c1$1 * (t - 1) ** 2;
  },
  easeInOutBack: (t) => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    return t < 0.5 ? (2 * t) ** 2 * ((c2$1 + 1) * 2 * t - c2$1) / 2 : ((2 * t - 2) ** 2 * ((c2$1 + 1) * (t * 2 - 2) + c2$1) + 2) / 2;
  },
  // Elastic
  easeInElastic: (t) => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    return -(2 ** (10 * t - 10)) * Math.sin((t * 10 - 10.75) * c4$1);
  },
  easeOutElastic: (t) => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    return 2 ** (-10 * t) * Math.sin((t * 10 - 0.75) * c4$1) + 1;
  },
  easeInOutElastic: (t) => {
    if (t === 0) return 0;
    if (t === 1) return 1;
    if (t < 0.5) {
      return -(2 ** (20 * t - 10) * Math.sin((20 * t - 11.125) * c5$1)) / 2;
    }
    return 2 ** (-20 * t + 10) * Math.sin((20 * t - 11.125) * c5$1) / 2 + 1;
  },
  // Bounce
  easeOutBounce: (t) => {
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
  },
  easeInBounce: (t) => 1 - easings.easeOutBounce(1 - t),
  easeInOutBounce: (t) => t < 0.5 ? (1 - easings.easeOutBounce(1 - 2 * t)) / 2 : (1 + easings.easeOutBounce(2 * t - 1)) / 2
};
function getEasing(name) {
  if (name in easings) {
    return easings[name];
  }
  return easings.linear;
}

function normalizeT(t) {
  if (!Number.isFinite(t)) return 0;
  return Math.max(0, Math.min(1, t));
}
const easeInSine = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - Math.cos(t * Math.PI / 2);
};
const easeOutSine = (rawT) => {
  const t = normalizeT(rawT);
  return Math.sin(t * Math.PI / 2);
};
const easeInOutSine = (rawT) => {
  const t = normalizeT(rawT);
  return -(Math.cos(Math.PI * t) - 1) / 2;
};
const easeInQuad = (rawT) => {
  const t = normalizeT(rawT);
  return t * t;
};
const easeOutQuad = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - (1 - t) * (1 - t);
};
const easeInOutQuad = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5 ? 2 * t * t : 1 - (-2 * t + 2) ** 2 / 2;
};
const easeInCubic = (rawT) => {
  const t = normalizeT(rawT);
  return t * t * t;
};
const easeOutCubic = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - (1 - t) ** 3;
};
const easeInOutCubic = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5 ? 4 * t * t * t : 1 - (-2 * t + 2) ** 3 / 2;
};
const easeInQuart = (rawT) => {
  const t = normalizeT(rawT);
  return t * t * t * t;
};
const easeOutQuart = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - (1 - t) ** 4;
};
const easeInOutQuart = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5 ? 8 * t * t * t * t : 1 - (-2 * t + 2) ** 4 / 2;
};
const easeInQuint = (rawT) => {
  const t = normalizeT(rawT);
  return t * t * t * t * t;
};
const easeOutQuint = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - (1 - t) ** 5;
};
const easeInOutQuint = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5 ? 16 * t * t * t * t * t : 1 - (-2 * t + 2) ** 5 / 2;
};
const easeInExpo = (rawT) => {
  const t = normalizeT(rawT);
  return t === 0 ? 0 : 2 ** (10 * t - 10);
};
const easeOutExpo = (rawT) => {
  const t = normalizeT(rawT);
  return t === 1 ? 1 : 1 - 2 ** (-10 * t);
};
const easeInOutExpo = (rawT) => {
  const t = normalizeT(rawT);
  return t === 0 ? 0 : t === 1 ? 1 : t < 0.5 ? 2 ** (20 * t - 10) / 2 : (2 - 2 ** (-20 * t + 10)) / 2;
};
const easeInCirc = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - Math.sqrt(1 - t * t);
};
const easeOutCirc = (rawT) => {
  const t = normalizeT(rawT);
  return Math.sqrt(1 - (t - 1) * (t - 1));
};
const easeInOutCirc = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5 ? (1 - Math.sqrt(1 - (2 * t) ** 2)) / 2 : (Math.sqrt(1 - (-2 * t + 2) ** 2) + 1) / 2;
};
const c1 = 1.70158;
const c2 = c1 * 1.525;
const c3 = c1 + 1;
const easeInBack = (rawT) => {
  const t = normalizeT(rawT);
  return c3 * t * t * t - c1 * t * t;
};
const easeOutBack = (rawT) => {
  const t = normalizeT(rawT);
  return 1 + c3 * (t - 1) ** 3 + c1 * (t - 1) ** 2;
};
const easeInOutBack = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5 ? (2 * t) ** 2 * ((c2 + 1) * 2 * t - c2) / 2 : ((2 * t - 2) ** 2 * ((c2 + 1) * (t * 2 - 2) + c2) + 2) / 2;
};
const c4 = 2 * Math.PI / 3;
const c5 = 2 * Math.PI / 4.5;
const easeInElastic = (rawT) => {
  const t = normalizeT(rawT);
  return t === 0 ? 0 : t === 1 ? 1 : -(2 ** (10 * t - 10)) * Math.sin((t * 10 - 10.75) * c4);
};
const easeOutElastic = (rawT) => {
  const t = normalizeT(rawT);
  return t === 0 ? 0 : t === 1 ? 1 : 2 ** (-10 * t) * Math.sin((t * 10 - 0.75) * c4) + 1;
};
const easeInOutElastic = (rawT) => {
  const t = normalizeT(rawT);
  return t === 0 ? 0 : t === 1 ? 1 : t < 0.5 ? -(2 ** (20 * t - 10) * Math.sin((20 * t - 11.125) * c5)) / 2 : 2 ** (-20 * t + 10) * Math.sin((20 * t - 11.125) * c5) / 2 + 1;
};
function bounceOut(t) {
  const n1 = 7.5625;
  const d1 = 2.75;
  if (t < 1 / d1) {
    return n1 * t * t;
  } else if (t < 2 / d1) {
    const adjusted = t - 1.5 / d1;
    return n1 * adjusted * adjusted + 0.75;
  } else if (t < 2.5 / d1) {
    const adjusted = t - 2.25 / d1;
    return n1 * adjusted * adjusted + 0.9375;
  } else {
    const adjusted = t - 2.625 / d1;
    return n1 * adjusted * adjusted + 0.984375;
  }
}
const easeOutBounce = (rawT) => {
  const t = normalizeT(rawT);
  return bounceOut(t);
};
const easeInBounce = (rawT) => {
  const t = normalizeT(rawT);
  return 1 - bounceOut(1 - t);
};
const easeInOutBounce = (rawT) => {
  const t = normalizeT(rawT);
  return t < 0.5 ? (1 - bounceOut(1 - 2 * t)) / 2 : (1 + bounceOut(2 * t - 1)) / 2;
};
const linear = (rawT) => {
  const t = normalizeT(rawT);
  return t;
};
const stepStart = (rawT) => {
  if (!Number.isFinite(rawT)) return 0;
  return rawT <= 0 ? 0 : 1;
};
const stepEnd = (rawT) => {
  if (!Number.isFinite(rawT)) return 0;
  return rawT >= 1 ? 1 : 0;
};
const EASING_FUNCTIONS = {
  // Linear
  linear,
  // Sine
  easeInSine,
  easeOutSine,
  easeInOutSine,
  // Quad
  easeInQuad,
  easeOutQuad,
  easeInOutQuad,
  // Cubic
  easeInCubic,
  easeOutCubic,
  easeInOutCubic,
  // Quart
  easeInQuart,
  easeOutQuart,
  easeInOutQuart,
  // Quint
  easeInQuint,
  easeOutQuint,
  easeInOutQuint,
  // Expo
  easeInExpo,
  easeOutExpo,
  easeInOutExpo,
  // Circ
  easeInCirc,
  easeOutCirc,
  easeInOutCirc,
  // Back
  easeInBack,
  easeOutBack,
  easeInOutBack,
  // Elastic
  easeInElastic,
  easeOutElastic,
  easeInOutElastic,
  // Bounce
  easeInBounce,
  easeOutBounce,
  easeInOutBounce,
  // Step
  stepStart,
  stepEnd
};

function jitter(ctx, frequency = 5, amplitude = 50, octaves = 1, amplitudeMultiplier = 0.5, time) {
  const t = ctx.time;
  const { value } = ctx;
  if (!Number.isFinite(octaves) || octaves < 1) {
    octaves = 1;
  } else if (octaves > 10) {
    octaves = 10;
  }
  octaves = Math.floor(octaves);
  const noise = (seed, t2) => {
    let result = 0;
    let amp = 1;
    let freq = 1;
    for (let i = 0; i < octaves; i++) {
      result += amp * Math.sin(t2 * frequency * freq * Math.PI * 2 + seed * 1e3);
      result += amp * 0.5 * Math.sin(t2 * frequency * freq * Math.PI * 2 * 1.5 + seed * 500);
      amp *= amplitudeMultiplier;
      freq *= 2;
    }
    const denominator = 1 + (octaves - 1) * amplitudeMultiplier;
    if (!Number.isFinite(denominator) || denominator === 0) {
      return result;
    }
    return result / denominator;
  };
  if (typeof value === "number") {
    return value + noise(0, t) * amplitude;
  }
  return value.map((v, i) => v + noise(i, t) * amplitude);
}

function subtractValues(a, b) {
  if (typeof a === "number" && typeof b === "number") {
    return a - b;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    return a.map((v, i) => v - b[i]);
  }
  return 0;
}
function addValues(a, b) {
  if (typeof a === "number" && typeof b === "number") {
    return a + b;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    return a.map((v, i) => v + b[i]);
  }
  return a;
}
function scaleValue(v, s) {
  if (typeof v === "number") {
    return v * s;
  }
  if (Array.isArray(v)) {
    return v.map((x) => x * s);
  }
  return 0;
}
function lerpValues(a, b, t) {
  if (typeof a === "number" && typeof b === "number") {
    return a + (b - a) * t;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    return a.map((v, i) => v + (b[i] - v) * t);
  }
  return a;
}
function applyEasing(t, interpolation) {
  const fn = EASING_FUNCTIONS[interpolation];
  return fn ? fn(t) : t;
}
function interpolateAtTime(keyframes, time, fps) {
  const frame = time * fps;
  let before = null;
  let after = null;
  for (const kf of keyframes) {
    if (kf.frame <= frame) {
      before = kf;
    } else if (!after) {
      after = kf;
      break;
    }
  }
  if (!before) return keyframes.length > 0 ? keyframes[0].value : 0;
  if (!after) return before.value;
  const frameDelta = after.frame - before.frame;
  if (!Number.isFinite(frameDelta) || frameDelta === 0) return before.value;
  const t = (frame - before.frame) / frameDelta;
  const easedT = applyEasing(t, before.interpolation);
  return lerpValues(before.value, after.value, easedT);
}

function repeatAfter(ctx, type = "cycle", numKeyframes = 0) {
  const { time, keyframes, fps } = ctx;
  if (keyframes.length < 2) return ctx.value;
  const startIdx = numKeyframes > 0 ? Math.max(0, keyframes.length - numKeyframes) : 0;
  const startKey = keyframes[startIdx];
  const endKey = keyframes[keyframes.length - 1];
  const startTime = startKey.frame / fps;
  const endTime = endKey.frame / fps;
  const duration = endTime - startTime;
  if (duration <= 0 || time <= endTime) return ctx.value;
  const elapsed = time - endTime;
  switch (type) {
    case "cycle": {
      const cycleTime = startTime + elapsed % duration;
      return interpolateAtTime(keyframes, cycleTime, fps);
    }
    case "pingpong": {
      const cycles = Math.floor(elapsed / duration);
      const cycleProgress = elapsed % duration / duration;
      const isReverse = cycles % 2 === 1;
      const t = isReverse ? 1 - cycleProgress : cycleProgress;
      const cycleTime = startTime + t * duration;
      return interpolateAtTime(keyframes, cycleTime, fps);
    }
    case "offset": {
      const cycles = Math.floor(elapsed / duration);
      const cycleTime = startTime + elapsed % duration;
      const baseValue = interpolateAtTime(keyframes, cycleTime, fps);
      const delta = subtractValues(endKey.value, startKey.value);
      return addValues(baseValue, scaleValue(delta, cycles + 1));
    }
    case "continue": {
      const velocity = ctx.velocity;
      const value = ctx.value;
      if (typeof velocity === "number" && typeof value === "number") {
        return value + velocity * elapsed;
      }
      if (Array.isArray(velocity) && Array.isArray(value)) {
        return value.map((v, i) => v + (velocity[i] ?? 0) * elapsed);
      }
      console.warn(
        "[Expressions] Type mismatch between value and velocity in repeatAfter"
      );
      return value;
    }
    default: {
      console.warn(`[Expressions] Unknown loop type in repeatAfter: ${type}`);
      return ctx.value;
    }
  }
}
function repeatBefore(ctx, type = "cycle", numKeyframes = 0) {
  const { time, keyframes, fps } = ctx;
  if (keyframes.length < 2) return ctx.value;
  const endIdx = numKeyframes > 0 ? Math.min(keyframes.length - 1, numKeyframes - 1) : keyframes.length - 1;
  const startKey = keyframes[0];
  const endKey = keyframes[endIdx];
  const startTime = startKey.frame / fps;
  const endTime = endKey.frame / fps;
  const duration = endTime - startTime;
  if (duration <= 0 || time >= startTime) return ctx.value;
  const elapsed = startTime - time;
  switch (type) {
    case "cycle": {
      const cycleTime = endTime - elapsed % duration;
      return interpolateAtTime(keyframes, cycleTime, fps);
    }
    case "pingpong": {
      const cycles = Math.floor(elapsed / duration);
      const cycleProgress = elapsed % duration / duration;
      const isReverse = cycles % 2 === 1;
      const t = isReverse ? cycleProgress : 1 - cycleProgress;
      const cycleTime = startTime + t * duration;
      return interpolateAtTime(keyframes, cycleTime, fps);
    }
    case "offset": {
      const cycles = Math.floor(elapsed / duration);
      const cycleTime = endTime - elapsed % duration;
      const baseValue = interpolateAtTime(keyframes, cycleTime, fps);
      const delta = subtractValues(startKey.value, endKey.value);
      return addValues(baseValue, scaleValue(delta, cycles + 1));
    }
    case "continue": {
      const velocity = ctx.velocity;
      const value = ctx.value;
      if (typeof velocity === "number" && typeof value === "number") {
        return value - velocity * elapsed;
      }
      if (Array.isArray(velocity) && Array.isArray(value)) {
        return value.map((v, i) => v - (velocity[i] ?? 0) * elapsed);
      }
      console.warn(
        "[Expressions] Type mismatch between value and velocity in repeatBefore"
      );
      return value;
    }
    default: {
      console.warn(`[Expressions] Unknown loop type in repeatBefore: ${type}`);
      return ctx.value;
    }
  }
}

function toArray(value) {
  if (typeof value === "number") {
    return [value];
  }
  if (Array.isArray(value)) {
    return value;
  }
  if (typeof value === "object" && value !== null && "x" in value && "y" in value) {
    const arr = [value.x, value.y];
    if ("z" in value && value.z !== void 0) {
      arr.push(value.z);
    }
    return arr;
  }
  return [0];
}
function fromArray(arr, originalValue) {
  if (typeof originalValue === "number") {
    return arr[0] ?? 0;
  }
  if (Array.isArray(originalValue)) {
    return arr;
  }
  if (typeof originalValue === "object" && originalValue !== null && "x" in originalValue) {
    const result = {
      x: arr[0] ?? 0,
      y: arr[1] ?? 0
    };
    if ("z" in originalValue && originalValue.z !== void 0) {
      result.z = arr[2] ?? 0;
    }
    return result;
  }
  return arr;
}
function inertia(ctx, amplitude = 0.1, frequency = 2, decay = 2) {
  const { time, keyframes, value, velocity } = ctx;
  const safeAmplitude = Number.isFinite(amplitude) ? amplitude : 0.1;
  const safeFrequency = Number.isFinite(frequency) ? frequency : 2;
  const safeDecay = Number.isFinite(decay) ? Math.max(1e-3, decay) : 2;
  if (keyframes.length === 0) return value;
  const fps = ctx.fps ?? 16;
  const currentFrame = time * fps;
  let nearestKey = null;
  for (let i = keyframes.length - 1; i >= 0; i--) {
    if (keyframes[i].frame <= currentFrame) {
      nearestKey = keyframes[i];
      break;
    }
  }
  if (!nearestKey) return value;
  const keyTime = nearestKey.frame / fps;
  const t = time - keyTime;
  if (t <= 0) return value;
  const valueArr = toArray(value);
  const velocityArr = toArray(velocity);
  const resultArr = valueArr.map((v, i) => {
    const componentVel = velocityArr[i] ?? 0;
    const oscillation = componentVel * safeAmplitude * Math.sin(safeFrequency * t * 2 * Math.PI) / Math.exp(safeDecay * t);
    return v + oscillation;
  });
  return fromArray(resultArr, value);
}
function bounce(ctx, elasticity = 0.7, gravity = 4e3) {
  const { time, keyframes, value } = ctx;
  const safeElasticity = Number.isFinite(elasticity) ? Math.max(0, Math.min(1, elasticity)) : 0.7;
  const safeGravity = Number.isFinite(gravity) && gravity > 0 ? gravity : 4e3;
  if (keyframes.length === 0) return value;
  const fps = ctx.fps ?? 16;
  const currentFrame = time * fps;
  let lastKey = null;
  for (let i = keyframes.length - 1; i >= 0; i--) {
    if (keyframes[i].frame <= currentFrame) {
      lastKey = keyframes[i];
      break;
    }
  }
  if (!lastKey) return value;
  const keyTime = lastKey.frame / fps;
  const t = time - keyTime;
  if (t <= 0) return value;
  let bounceTime = t;
  let bounceHeight = 1;
  let totalBounces = 0;
  const maxBounces = 10;
  while (bounceTime > 0 && totalBounces < maxBounces) {
    const bounceDuration2 = Math.sqrt(2 * bounceHeight / safeGravity);
    if (bounceTime < bounceDuration2 * 2) {
      break;
    }
    bounceTime -= bounceDuration2 * 2;
    bounceHeight *= safeElasticity * safeElasticity;
    totalBounces++;
  }
  const bounceDuration = Math.sqrt(2 * bounceHeight / safeGravity);
  const bounceT = bounceTime / (bounceDuration * 2);
  const bounceOffset = bounceHeight * 4 * bounceT * (1 - bounceT);
  const valueArr = toArray(value);
  const resultArr = valueArr.map((v) => v - bounceOffset * (1 - safeElasticity));
  return fromArray(resultArr, value);
}
function elastic(ctx, amplitude = 1, period = 0.3) {
  const { time, keyframes, value } = ctx;
  const safeAmplitude = Number.isFinite(amplitude) ? amplitude : 1;
  const safePeriod = Number.isFinite(period) && period > 0 ? period : 0.3;
  if (keyframes.length === 0) return value;
  const fps = ctx.fps ?? 16;
  const currentFrame = time * fps;
  let lastKey = null;
  for (let i = keyframes.length - 1; i >= 0; i--) {
    if (keyframes[i].frame <= currentFrame) {
      lastKey = keyframes[i];
      break;
    }
  }
  if (!lastKey) return value;
  const keyTime = lastKey.frame / fps;
  const t = time - keyTime;
  if (t <= 0) return value;
  const s = safePeriod / 4;
  const decay = 2 ** (-10 * t);
  const oscillation = decay * Math.sin((t - s) * (2 * Math.PI) / safePeriod);
  const valueArr = toArray(value);
  const resultArr = valueArr.map((v) => v + safeAmplitude * oscillation);
  return fromArray(resultArr, value);
}

let sesInitialized$1 = false;
const MAX_EXPRESSION_LENGTH = 10240;
async function initializeSES() {
  if (sesInitialized$1) {
    return true;
  }
  sesInitialized$1 = true;
  console.log(
    "[SES] Expression security via worker sandbox - main thread lockdown disabled for Vue/Three.js compatibility"
  );
  return true;
}
function createExpressionCompartment(ctx) {
  if (!sesInitialized$1) {
    throw new Error(
      "[SES] Not initialized. Call initializeSES() at app startup."
    );
  }
  if (!globalThis.Compartment || !globalThis.harden) {
    throw new Error(
      "[SES] Compartment not available. Ensure lockdown() was called."
    );
  }
  const { Compartment, harden } = globalThis;
  const safeMath = harden({
    PI: Math.PI,
    E: Math.E,
    abs: Math.abs,
    acos: Math.acos,
    asin: Math.asin,
    atan: Math.atan,
    atan2: Math.atan2,
    ceil: Math.ceil,
    cos: Math.cos,
    exp: Math.exp,
    floor: Math.floor,
    log: Math.log,
    log10: Math.log10,
    log2: Math.log2,
    max: Math.max,
    min: Math.min,
    pow: Math.pow,
    // random: EXCLUDED - use seeded random() for determinism
    round: Math.round,
    sign: Math.sign,
    sin: Math.sin,
    sqrt: Math.sqrt,
    tan: Math.tan,
    trunc: Math.trunc,
    hypot: Math.hypot,
    cbrt: Math.cbrt,
    expm1: Math.expm1,
    log1p: Math.log1p,
    sinh: Math.sinh,
    cosh: Math.cosh,
    tanh: Math.tanh,
    asinh: Math.asinh,
    acosh: Math.acosh,
    atanh: Math.atanh
  });
  const safeNumber = harden({
    isFinite: Number.isFinite,
    isNaN: Number.isNaN,
    isInteger: Number.isInteger,
    parseFloat: Number.parseFloat,
    parseInt: Number.parseInt,
    MAX_VALUE: Number.MAX_VALUE,
    MIN_VALUE: Number.MIN_VALUE,
    MAX_SAFE_INTEGER: Number.MAX_SAFE_INTEGER,
    MIN_SAFE_INTEGER: Number.MIN_SAFE_INTEGER,
    EPSILON: Number.EPSILON,
    POSITIVE_INFINITY: Number.POSITIVE_INFINITY,
    NEGATIVE_INFINITY: Number.NEGATIVE_INFINITY,
    NaN: Number.NaN
  });
  const utilities = harden({
    // Linear interpolation
    linear: (t, tMin, tMax, vMin, vMax) => {
      if (t <= tMin) return vMin;
      if (t >= tMax) return vMax;
      return vMin + (vMax - vMin) * ((t - tMin) / (tMax - tMin));
    },
    // Clamp value
    clamp: (val, min, max) => {
      return Math.max(min, Math.min(max, val));
    },
    // Seeded random (deterministic)
    random: (seed) => {
      const s = seed !== void 0 ? seed : ctx.frame;
      const x = Math.sin(s * 12.9898) * 43758.5453;
      return x - Math.floor(x);
    },
    // Angle conversion
    radiansToDegrees: (rad) => rad * 180 / Math.PI,
    degreesToRadians: (deg) => deg * Math.PI / 180,
    // Time conversion
    timeToFrames: (t = ctx.time) => Math.round(t * ctx.fps),
    framesToTime: (f) => f / ctx.fps,
    // Degree-based trig
    sinDeg: (deg) => Math.sin(deg * Math.PI / 180),
    cosDeg: (deg) => Math.cos(deg * Math.PI / 180),
    tanDeg: (deg) => Math.tan(deg * Math.PI / 180),
    // Vector operations (basic)
    length: (a, b) => {
      if (b === void 0) {
        if (typeof a === "number") return Math.abs(a);
        return Math.sqrt(a.reduce((sum2, v) => sum2 + v * v, 0));
      }
      if (typeof a === "number" && typeof b === "number") {
        return Math.abs(a - b);
      }
      const arrA = Array.isArray(a) ? a : [a];
      const arrB = Array.isArray(b) ? b : [b];
      let sum = 0;
      for (let i = 0; i < Math.max(arrA.length, arrB.length); i++) {
        const diff = (arrA[i] ?? 0) - (arrB[i] ?? 0);
        sum += diff * diff;
      }
      return Math.sqrt(sum);
    },
    // Vector add
    add: (a, b) => {
      if (typeof a === "number" && typeof b === "number") return a + b;
      const arrA = Array.isArray(a) ? a : [a];
      const arrB = Array.isArray(b) ? b : [b];
      const len = Math.max(arrA.length, arrB.length);
      const result = [];
      for (let i = 0; i < len; i++) {
        result.push((arrA[i] ?? 0) + (arrB[i] ?? 0));
      }
      return result;
    },
    // Vector subtract
    sub: (a, b) => {
      if (typeof a === "number" && typeof b === "number") return a - b;
      const arrA = Array.isArray(a) ? a : [a];
      const arrB = Array.isArray(b) ? b : [b];
      const len = Math.max(arrA.length, arrB.length);
      const result = [];
      for (let i = 0; i < len; i++) {
        result.push((arrA[i] ?? 0) - (arrB[i] ?? 0));
      }
      return result;
    },
    // Vector multiply
    mul: (a, b) => {
      if (typeof a === "number" && typeof b === "number") return a * b;
      if (typeof b === "number" && Array.isArray(a)) {
        return a.map((v) => v * b);
      }
      if (typeof a === "number" && Array.isArray(b)) {
        return b.map((v) => v * a);
      }
      const arrA = a;
      const arrB = b;
      const len = Math.max(arrA.length, arrB.length);
      const result = [];
      for (let i = 0; i < len; i++) {
        result.push((arrA[i] ?? 0) * (arrB[i] ?? 0));
      }
      return result;
    },
    // Vector divide
    div: (a, b) => {
      if (typeof a === "number" && typeof b === "number") {
        return b !== 0 ? a / b : 0;
      }
      if (typeof b === "number" && Array.isArray(a)) {
        return b !== 0 ? a.map((v) => v / b) : a.map(() => 0);
      }
      if (typeof a === "number" && Array.isArray(b)) {
        return b.map((v) => v !== 0 ? a / v : 0);
      }
      const arrA = a;
      const arrB = b;
      const len = Math.max(arrA.length, arrB.length);
      const result = [];
      for (let i = 0; i < len; i++) {
        const divisor = arrB[i] ?? 1;
        result.push(divisor !== 0 ? (arrA[i] ?? 0) / divisor : 0);
      }
      return result;
    }
  });
  const compartment = new Compartment({
    // Safe Math
    Math: safeMath,
    // Safe Number utilities
    Number: safeNumber,
    // Basic type checking
    isNaN: Number.isNaN,
    isFinite: Number.isFinite,
    parseInt: Number.parseInt,
    parseFloat: Number.parseFloat,
    // Constants
    Infinity: Infinity,
    NaN: NaN,
    undefined: void 0,
    // Context values (frozen)
    time: ctx.time,
    frame: ctx.frame,
    fps: ctx.fps,
    duration: ctx.duration,
    // Layer info
    index: ctx.layerIndex,
    layerName: ctx.layerName,
    inPoint: ctx.inPoint,
    outPoint: ctx.outPoint,
    // Property value (frozen if array)
    value: Array.isArray(ctx.value) ? harden([...ctx.value]) : ctx.value,
    velocity: Array.isArray(ctx.velocity) ? harden([...ctx.velocity]) : ctx.velocity,
    numKeys: ctx.numKeys,
    // Utility functions
    ...utilities,
    // Console for debugging (limited)
    console: harden({
      log: (...args) => console.log("[Expression]", ...args),
      warn: (...args) => console.warn("[Expression]", ...args)
    }),
    // SECURITY: Explicitly block dangerous intrinsics
    // Even though SES sandboxes these, we block them for defense-in-depth
    Function: void 0,
    eval: void 0,
    globalThis: void 0,
    window: void 0,
    document: void 0,
    setTimeout: void 0,
    setInterval: void 0,
    setImmediate: void 0,
    fetch: void 0,
    XMLHttpRequest: void 0,
    WebSocket: void 0,
    Worker: void 0,
    importScripts: void 0,
    require: void 0,
    process: void 0,
    Deno: void 0,
    Bun: void 0
  });
  return compartment;
}
function evaluateInSES(code, ctx) {
  if (typeof code !== "string") {
    console.warn("[SECURITY] evaluateInSES: code is not a string");
    return ctx.value;
  }
  if (!code || code.trim() === "") {
    return ctx.value;
  }
  if (!sesInitialized$1) {
    console.error(
      "[SECURITY] SES not initialized - expression evaluation DISABLED for security"
    );
    console.error(
      "[SECURITY] Call initializeSES() at app startup to enable expressions"
    );
    return ctx.value;
  }
  if (code.length > MAX_EXPRESSION_LENGTH) {
    console.warn(
      `[SECURITY] Expression too long (${code.length} bytes, max ${MAX_EXPRESSION_LENGTH})`
    );
    return ctx.value;
  }
  try {
    const compartment = createExpressionCompartment(ctx);
    const needsReturn = !code.includes("return ") && !code.includes("return;");
    const processedCode = needsReturn ? code.trim().split("\n").map(
      (line, i, arr) => i === arr.length - 1 && !line.trim().startsWith("//") && line.trim().length > 0 ? `return ${line}` : line
    ).join("\n") : code;
    const wrappedCode = `(function() { ${processedCode} })()`;
    const result = compartment.evaluate(wrappedCode);
    return result;
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.warn("[SES] Expression error:", message);
    return ctx.value;
  }
}

const timeExpressions = {
  timeRamp(startTime, endTime, startValue, endValue, time) {
    if (time <= startTime) return startValue;
    if (time >= endTime) return endValue;
    const duration = endTime - startTime;
    if (!Number.isFinite(duration) || duration === 0) return startValue;
    const t = (time - startTime) / duration;
    return startValue + (endValue - startValue) * t;
  },
  periodic(time, period) {
    if (!Number.isFinite(period) || period === 0) return 0;
    return time % period / period;
  },
  sawtooth(time, frequency, amplitude = 1) {
    if (!Number.isFinite(time) || !Number.isFinite(frequency) || !Number.isFinite(amplitude))
      return 0;
    const t = time * frequency;
    return amplitude * 2 * (t - Math.floor(t + 0.5));
  },
  triangle(time, frequency, amplitude = 1) {
    if (!Number.isFinite(time) || !Number.isFinite(frequency) || !Number.isFinite(amplitude))
      return 0;
    const t = time * frequency;
    return amplitude * (2 * Math.abs(2 * (t - Math.floor(t + 0.5))) - 1);
  },
  square(time, frequency, amplitude = 1) {
    if (!Number.isFinite(time) || !Number.isFinite(frequency) || !Number.isFinite(amplitude))
      return 0;
    const t = time * frequency;
    return amplitude * (t - Math.floor(t) < 0.5 ? 1 : -1);
  },
  sine(time, frequency, amplitude = 1, phase = 0) {
    return amplitude * Math.sin(2 * Math.PI * frequency * time + phase);
  },
  pulse(time, frequency, dutyCycle = 0.5, amplitude = 1) {
    const t = time * frequency % 1;
    return amplitude * (t < dutyCycle ? 1 : 0);
  }
};
const mathExpressions = {
  lerp(a, b, t) {
    return a + (b - a) * t;
  },
  clamp(value, min, max) {
    return Math.min(max, Math.max(min, value));
  },
  map(value, inMin, inMax, outMin, outMax) {
    const range = inMax - inMin;
    if (!Number.isFinite(range) || range === 0) return outMin;
    return outMin + (outMax - outMin) * ((value - inMin) / range);
  },
  normalize(value, min, max) {
    const range = max - min;
    if (!Number.isFinite(range) || range === 0) return 0;
    return (value - min) / range;
  },
  smoothstep(edge0, edge1, x) {
    const range = edge1 - edge0;
    if (!Number.isFinite(range) || range === 0) {
      return x < edge0 ? 0 : 1;
    }
    const t = mathExpressions.clamp((x - edge0) / range, 0, 1);
    return t * t * (3 - 2 * t);
  },
  smootherstep(edge0, edge1, x) {
    const range = edge1 - edge0;
    if (!Number.isFinite(range) || range === 0) {
      return x < edge0 ? 0 : 1;
    }
    const t = mathExpressions.clamp((x - edge0) / range, 0, 1);
    return t * t * t * (t * (t * 6 - 15) + 10);
  },
  mod(a, b) {
    if (!Number.isFinite(b) || b === 0) return 0;
    if (!Number.isFinite(a)) return 0;
    return (a % b + b) % b;
  },
  distance(x1, y1, x2, y2) {
    const dx = x2 - x1;
    const dy = y2 - y1;
    return Math.sqrt(dx * dx + dy * dy);
  },
  angleBetween(x1, y1, x2, y2) {
    return Math.atan2(y2 - y1, x2 - x1);
  },
  degreesToRadians(degrees) {
    return degrees * Math.PI / 180;
  },
  radiansToDegrees(radians) {
    return radians * 180 / Math.PI;
  },
  seedRandom(seed, min = 0, max = 1) {
    const x = Math.sin(seed * 12.9898) * 43758.5453;
    const rand = x - Math.floor(x);
    return min + rand * (max - min);
  },
  gaussRandom(mean = 0, stdDev = 1, seed = 12345) {
    if (!Number.isFinite(mean) || !Number.isFinite(stdDev) || !Number.isFinite(seed)) {
      return 0;
    }
    const seededRand = (s) => {
      const x = Math.sin(s * 12.9898) * 43758.5453;
      return x - Math.floor(x);
    };
    const u1Raw = seededRand(seed);
    const u1 = Number.isFinite(u1Raw) ? Math.max(1e-4, u1Raw) : 1e-4;
    const u2Raw = seededRand(seed + 1);
    const u2 = Number.isFinite(u2Raw) ? u2Raw : 0;
    const z0 = Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
    return mean + z0 * stdDev;
  }
};
function evaluateExpression(expression, ctx) {
  if (!expression.enabled) return ctx.value;
  switch (expression.type) {
    case "preset":
      return evaluatePreset(expression.name, ctx, expression.params);
    case "function":
      return evaluateFunction(expression.name, ctx, expression.params);
    case "custom":
      return evaluateCustomExpression(expression.code || "", ctx);
    default:
      return ctx.value;
  }
}
function evaluatePreset(name, ctx, params) {
  switch (name) {
    case "inertia": {
      const amplitude = typeof params.amplitude === "number" ? params.amplitude : 0.1;
      const frequency = typeof params.frequency === "number" ? params.frequency : 2;
      const decay = typeof params.decay === "number" ? params.decay : 2;
      return inertia(ctx, amplitude, frequency, decay);
    }
    case "bounce": {
      const elasticity = typeof params.elasticity === "number" ? params.elasticity : 0.7;
      const gravity = typeof params.gravity === "number" ? params.gravity : 4e3;
      return bounce(ctx, elasticity, gravity);
    }
    case "elastic": {
      const amplitude = typeof params.amplitude === "number" ? params.amplitude : 1;
      const period = typeof params.period === "number" ? params.period : 0.3;
      return elastic(ctx, amplitude, period);
    }
    case "jitter": {
      const frequency = typeof params.frequency === "number" ? params.frequency : 10;
      const amplitude = typeof params.amplitude === "number" ? params.amplitude : 5;
      const octaves = typeof params.octaves === "number" ? params.octaves : 1;
      return jitter(ctx, frequency, amplitude, octaves);
    }
    case "repeatAfter": {
      const type = typeof params.type === "string" && (params.type === "cycle" || params.type === "pingpong" || params.type === "offset" || params.type === "continue") ? params.type : "cycle";
      const numKeyframes = typeof params.numKeyframes === "number" ? params.numKeyframes : 0;
      return repeatAfter(ctx, type, numKeyframes);
    }
    case "repeatBefore": {
      const type = typeof params.type === "string" && (params.type === "cycle" || params.type === "pingpong" || params.type === "offset" || params.type === "continue") ? params.type : "cycle";
      const numKeyframes = typeof params.numKeyframes === "number" ? params.numKeyframes : 0;
      return repeatBefore(ctx, type, numKeyframes);
    }
    default:
      return ctx.value;
  }
}
function evaluateFunction(name, ctx, params) {
  if (name in timeExpressions) {
    const timeExprs = timeExpressions;
    const fn = timeExprs[name];
    if (fn) {
      return fn(ctx.time, ...Object.values(params));
    }
  }
  if (name in mathExpressions) {
    const mathExprs = mathExpressions;
    const fn = mathExprs[name];
    if (fn) {
      const val = typeof ctx.value === "number" ? ctx.value : ctx.value[0];
      return fn(val, ...Object.values(params));
    }
  }
  return ctx.value;
}
function evaluateCustomExpression(code, ctx) {
  if (typeof code !== "string") {
    console.warn("[SECURITY] Expression code is not a string:", typeof code);
    return ctx.value;
  }
  if (!code || code.trim() === "") {
    return ctx.value;
  }
  return evaluateInSES(code, ctx);
}

const logger$2 = createLogger("PathMorphing");
const DEFAULT_MORPH_CONFIG = {
  pointMatchingStrategy: "subdivide-shorter",
  correspondenceMethod: "nearest-rotation"
};
function clonePoint(p) {
  return { x: p.x, y: p.y };
}
function cloneVertex(v) {
  return {
    point: clonePoint(v.point),
    inHandle: clonePoint(v.inHandle),
    outHandle: clonePoint(v.outHandle)
  };
}
function clonePath(path) {
  return {
    vertices: path.vertices.map(cloneVertex),
    closed: path.closed
  };
}
function distance(a, b) {
  const dx = b.x - a.x;
  const dy = b.y - a.y;
  return Math.sqrt(dx * dx + dy * dy);
}
function lerp(a, b, t) {
  return a + (b - a) * t;
}
function lerpPoint(a, b, t) {
  return {
    x: lerp(a.x, b.x, t),
    y: lerp(a.y, b.y, t)
  };
}
function addPoints(a, b) {
  return { x: a.x + b.x, y: a.y + b.y };
}
function subtractPoints(a, b) {
  return { x: a.x - b.x, y: a.y - b.y };
}
function scalePoint(p, s) {
  return { x: p.x * s, y: p.y * s };
}
function cubicBezierPoint(p0, p1, p2, p3, t) {
  const mt = 1 - t;
  const mt2 = mt * mt;
  const mt3 = mt2 * mt;
  const t2 = t * t;
  const t3 = t2 * t;
  return {
    x: mt3 * p0.x + 3 * mt2 * t * p1.x + 3 * mt * t2 * p2.x + t3 * p3.x,
    y: mt3 * p0.y + 3 * mt2 * t * p1.y + 3 * mt * t2 * p2.y + t3 * p3.y
  };
}
function splitCubicBezier(p0, p1, p2, p3, t) {
  const q0 = lerpPoint(p0, p1, t);
  const q1 = lerpPoint(p1, p2, t);
  const q2 = lerpPoint(p2, p3, t);
  const r0 = lerpPoint(q0, q1, t);
  const r1 = lerpPoint(q1, q2, t);
  const s = lerpPoint(r0, r1, t);
  return [
    [p0, q0, r0, s],
    // Left segment
    [s, r1, q2, p3]
    // Right segment
  ];
}
function estimateSegmentLength(p0, p1, p2, p3, samples = 10) {
  let length = 0;
  let prev = p0;
  for (let i = 1; i <= samples; i++) {
    const t = i / samples;
    const curr = cubicBezierPoint(p0, p1, p2, p3, t);
    length += distance(prev, curr);
    prev = curr;
  }
  return length;
}
function getSegmentControlPoints(path, segmentIndex) {
  const v0 = path.vertices[segmentIndex];
  const v1 = path.vertices[(segmentIndex + 1) % path.vertices.length];
  return {
    p0: v0.point,
    p1: addPoints(v0.point, v0.outHandle),
    p2: addPoints(v1.point, v1.inHandle),
    p3: v1.point
  };
}
function getSegmentLengths(path, samplesPerSegment = 10) {
  const numSegments = path.closed ? path.vertices.length : path.vertices.length - 1;
  const lengths = [];
  for (let i = 0; i < numSegments; i++) {
    const { p0, p1, p2, p3 } = getSegmentControlPoints(path, i);
    lengths.push(estimateSegmentLength(p0, p1, p2, p3, samplesPerSegment));
  }
  return lengths;
}
function getPointAtArcLength(path, targetLength, segmentLengths) {
  let accumulated = 0;
  for (let i = 0; i < segmentLengths.length; i++) {
    const segmentLength = segmentLengths[i];
    if (accumulated + segmentLength >= targetLength || i === segmentLengths.length - 1) {
      const localT = segmentLength > 0 ? (targetLength - accumulated) / segmentLength : 0;
      const { p0, p1, p2, p3 } = getSegmentControlPoints(path, i);
      const point = cubicBezierPoint(
        p0,
        p1,
        p2,
        p3,
        Math.max(0, Math.min(1, localT))
      );
      return { point, segmentIndex: i, t: localT };
    }
    accumulated += segmentLength;
  }
  const lastVertex = path.vertices[path.vertices.length - 1];
  return {
    point: clonePoint(lastVertex.point),
    segmentIndex: segmentLengths.length - 1,
    t: 1
  };
}
function subdivideSegmentAt(path, segmentIndex, t) {
  const result = clonePath(path);
  const v0 = result.vertices[segmentIndex];
  const nextIdx = (segmentIndex + 1) % result.vertices.length;
  const v1 = result.vertices[nextIdx];
  const p0 = v0.point;
  const p1 = addPoints(v0.point, v0.outHandle);
  const p2 = addPoints(v1.point, v1.inHandle);
  const p3 = v1.point;
  const [left, right] = splitCubicBezier(p0, p1, p2, p3, t);
  v0.outHandle = subtractPoints(left[1], left[0]);
  const newVertex = {
    point: clonePoint(left[3]),
    inHandle: subtractPoints(left[2], left[3]),
    outHandle: subtractPoints(right[1], right[0])
  };
  v1.inHandle = subtractPoints(right[2], right[3]);
  result.vertices.splice(segmentIndex + 1, 0, newVertex);
  return result;
}
function subdivideToVertexCount(path, targetCount) {
  if (path.vertices.length >= targetCount) {
    return clonePath(path);
  }
  let current = clonePath(path);
  const segmentLengths = getSegmentLengths(current);
  segmentLengths.reduce((sum, l) => sum + l, 0);
  while (current.vertices.length < targetCount) {
    const currentLengths = getSegmentLengths(current);
    let maxLength = 0;
    let maxIndex = 0;
    for (let i = 0; i < currentLengths.length; i++) {
      if (currentLengths[i] > maxLength) {
        maxLength = currentLengths[i];
        maxIndex = i;
      }
    }
    current = subdivideSegmentAt(current, maxIndex, 0.5);
  }
  return current;
}
function resamplePath(path, vertexCount) {
  if (vertexCount < 2) {
    return clonePath(path);
  }
  const segmentLengths = getSegmentLengths(path);
  const totalLength = segmentLengths.reduce((sum, l) => sum + l, 0);
  if (totalLength === 0) {
    const vertices2 = [];
    for (let i = 0; i < vertexCount; i++) {
      const srcIdx = Math.floor(i * path.vertices.length / vertexCount);
      vertices2.push(cloneVertex(path.vertices[srcIdx]));
    }
    return { vertices: vertices2, closed: path.closed };
  }
  const spacing = totalLength / (path.closed ? vertexCount : vertexCount - 1);
  const vertices = [];
  for (let i = 0; i < vertexCount; i++) {
    const targetLength = i * spacing;
    const { point } = getPointAtArcLength(path, targetLength, segmentLengths);
    const prevLength = Math.max(0, targetLength - spacing * 0.33);
    const nextLength = Math.min(totalLength, targetLength + spacing * 0.33);
    const prevPoint = getPointAtArcLength(
      path,
      prevLength,
      segmentLengths
    ).point;
    const nextPoint = getPointAtArcLength(
      path,
      nextLength,
      segmentLengths
    ).point;
    const tangent = {
      x: (nextPoint.x - prevPoint.x) * 0.5,
      y: (nextPoint.y - prevPoint.y) * 0.5
    };
    const handleScale = 0.33;
    vertices.push({
      point: clonePoint(point),
      inHandle: scalePoint(tangent, -handleScale),
      outHandle: scalePoint(tangent, handleScale)
    });
  }
  return { vertices, closed: path.closed };
}
function calculateTravelDistance(source, target, rotationOffset = 0, reversed = false) {
  const n = source.vertices.length;
  let total = 0;
  for (let i = 0; i < n; i++) {
    const srcIdx = i;
    let tgtIdx = (i + rotationOffset + n) % n;
    if (reversed) {
      tgtIdx = (n - 1 - i + rotationOffset + n) % n;
    }
    total += distance(
      source.vertices[srcIdx].point,
      target.vertices[tgtIdx].point
    );
  }
  return total;
}
function findOptimalRotation(source, target) {
  const n = source.vertices.length;
  let bestOffset = 0;
  let bestReversed = false;
  let bestDistance = Infinity;
  for (let offset = 0; offset < n; offset++) {
    const dist = calculateTravelDistance(source, target, offset, false);
    if (dist < bestDistance) {
      bestDistance = dist;
      bestOffset = offset;
      bestReversed = false;
    }
    if (source.closed && target.closed) {
      const distRev = calculateTravelDistance(source, target, offset, true);
      if (distRev < bestDistance) {
        bestDistance = distRev;
        bestOffset = offset;
        bestReversed = true;
      }
    }
  }
  return { offset: bestOffset, reversed: bestReversed };
}
function rotateVertices(path, offset, reverse = false) {
  const n = path.vertices.length;
  const vertices = [];
  for (let i = 0; i < n; i++) {
    let srcIdx = (i + offset + n) % n;
    if (reverse) {
      srcIdx = (n - 1 - i + offset + n) % n;
    }
    const srcVertex = path.vertices[srcIdx];
    if (reverse) {
      vertices.push({
        point: clonePoint(srcVertex.point),
        inHandle: clonePoint(srcVertex.outHandle),
        outHandle: clonePoint(srcVertex.inHandle)
      });
    } else {
      vertices.push(cloneVertex(srcVertex));
    }
  }
  return { vertices, closed: path.closed };
}
function prepareMorphPaths(source, target, config = {}) {
  const cfg = { ...DEFAULT_MORPH_CONFIG, ...config };
  if (source.vertices.length === 0 || target.vertices.length === 0) {
    logger$2.warn("Cannot morph empty paths");
    return {
      source: clonePath(source),
      target: clonePath(target),
      rotationOffset: 0,
      reversed: false
    };
  }
  let preparedSource = clonePath(source);
  let preparedTarget = clonePath(target);
  const sourceCount = preparedSource.vertices.length;
  const targetCount = preparedTarget.vertices.length;
  if (sourceCount !== targetCount) {
    switch (cfg.pointMatchingStrategy) {
      case "subdivide-shorter":
        if (sourceCount < targetCount) {
          preparedSource = subdivideToVertexCount(preparedSource, targetCount);
        } else {
          preparedTarget = subdivideToVertexCount(preparedTarget, sourceCount);
        }
        break;
      case "subdivide-both": {
        const maxCount = Math.max(sourceCount, targetCount);
        preparedSource = subdivideToVertexCount(preparedSource, maxCount);
        preparedTarget = subdivideToVertexCount(preparedTarget, maxCount);
        break;
      }
      case "resample": {
        const count = cfg.resampleCount ?? Math.max(sourceCount, targetCount);
        preparedSource = resamplePath(preparedSource, count);
        preparedTarget = resamplePath(preparedTarget, count);
        break;
      }
    }
  }
  let rotationOffset = 0;
  let reversed = false;
  if (preparedSource.closed && preparedTarget.closed) {
    switch (cfg.correspondenceMethod) {
      case "nearest-rotation":
      case "nearest-distance": {
        const result = findOptimalRotation(preparedSource, preparedTarget);
        rotationOffset = result.offset;
        reversed = result.reversed;
        break;
      }
    }
  }
  if (rotationOffset !== 0 || reversed) {
    preparedTarget = rotateVertices(preparedTarget, rotationOffset, reversed);
  }
  return {
    source: preparedSource,
    target: preparedTarget,
    rotationOffset,
    reversed
  };
}
function morphPaths(source, target, t) {
  t = Math.max(0, Math.min(1, t));
  if (t === 0) return clonePath(source);
  if (t === 1) return clonePath(target);
  if (source.vertices.length !== target.vertices.length) {
    logger$2.warn(
      "Paths have different vertex counts - use prepareMorphPaths() first"
    );
    const count = Math.min(source.vertices.length, target.vertices.length);
    source = {
      vertices: source.vertices.slice(0, count),
      closed: source.closed
    };
    target = {
      vertices: target.vertices.slice(0, count),
      closed: target.closed
    };
  }
  const vertices = [];
  for (let i = 0; i < source.vertices.length; i++) {
    const srcV = source.vertices[i];
    const tgtV = target.vertices[i];
    vertices.push({
      point: lerpPoint(srcV.point, tgtV.point, t),
      inHandle: lerpPoint(srcV.inHandle, tgtV.inHandle, t),
      outHandle: lerpPoint(srcV.outHandle, tgtV.outHandle, t)
    });
  }
  return { vertices, closed: source.closed };
}
function isBezierPath(value) {
  if (typeof value !== "object" || value === null) {
    return false;
  }
  const obj = value;
  if (!Array.isArray(obj.vertices) || typeof obj.closed !== "boolean") {
    return false;
  }
  if (obj.vertices.length > 0) {
    const v = obj.vertices[0];
    if (typeof v !== "object" || v === null) return false;
    if (typeof v.point?.x !== "number") return false;
    if (typeof v.point?.y !== "number") return false;
  }
  return true;
}

function ensureFinite(value, fallback) {
  if (typeof value !== "number") return fallback;
  if (!Number.isFinite(value)) return fallback;
  return value;
}
function clamp(value, min, max) {
  if (Number.isNaN(value)) return min;
  if (value < min) return min;
  if (value > max) return max;
  return value;
}
function clamp01(value) {
  return clamp(value, 0, 1);
}
function safeLerp(a, b, t) {
  const safeA = ensureFinite(a, 0);
  const safeB = ensureFinite(b, 0);
  const safeT = clamp01(ensureFinite(t, 0));
  const diff = safeB - safeA;
  if (!Number.isFinite(diff)) {
    const result = safeA * (1 - safeT) + safeB * safeT;
    return ensureFinite(result, safeA);
  }
  return safeA + diff * safeT;
}

class BezierCache {
  cache = /* @__PURE__ */ new Map();
  maxSize = 500;
  /**
   * Generate cache key from bezier parameters
   * Uses fixed precision to avoid floating point key variations
   */
  makeKey(outHandle, inHandle, frameDuration, valueDelta) {
    const round = (n) => Math.round(n * 1e4);
    return `${round(outHandle.frame)},${round(outHandle.value)},${round(inHandle.frame)},${round(inHandle.value)},${round(frameDuration)},${round(valueDelta)}`;
  }
  /**
   * Get cached normalized bezier or compute and cache it
   */
  get(outHandle, inHandle, frameDuration, valueDelta) {
    const key = this.makeKey(outHandle, inHandle, frameDuration, valueDelta);
    const cached = this.cache.get(key);
    if (cached) {
      this.cache.delete(key);
      this.cache.set(key, cached);
      return cached;
    }
    const x1 = frameDuration > 0 ? Math.abs(outHandle.frame) / frameDuration : 0.33;
    const y1 = valueDelta !== 0 ? outHandle.value / valueDelta : 0.33;
    const x2 = frameDuration > 0 ? 1 - Math.abs(inHandle.frame) / frameDuration : 0.67;
    const y2 = valueDelta !== 0 ? 1 - inHandle.value / valueDelta : 0.67;
    const normalized = { x1, y1, x2, y2 };
    if (this.cache.size >= this.maxSize) {
      const firstKey = this.cache.keys().next().value;
      if (firstKey) this.cache.delete(firstKey);
    }
    this.cache.set(key, normalized);
    return normalized;
  }
  /**
   * Clear the cache (call on project load)
   */
  clear() {
    this.cache.clear();
  }
  /**
   * Get cache statistics for debugging
   */
  getStats() {
    return { size: this.cache.size, maxSize: this.maxSize };
  }
}
const bezierCache = new BezierCache();
function findKeyframeIndex(keyframes, frame) {
  let low = 0;
  let high = keyframes.length - 2;
  while (low <= high) {
    const mid = low + high >>> 1;
    const midFrame = keyframes[mid].frame;
    const nextFrame = keyframes[mid + 1].frame;
    if (frame >= midFrame && frame <= nextFrame) {
      return mid;
    } else if (frame < midFrame) {
      high = mid - 1;
    } else {
      low = mid + 1;
    }
  }
  return Math.max(0, Math.min(low, keyframes.length - 2));
}
function getValueDelta(v1, v2) {
  if (typeof v1 === "number" && typeof v2 === "number") {
    return v2 - v1;
  }
  if (typeof v1 === "object" && v1 !== null && "x" in v1 && "y" in v1 && typeof v2 === "object" && v2 !== null && "x" in v2 && "y" in v2) {
    const v1Vec = v1;
    const v2Vec = v2;
    const dx = v2Vec.x - v1Vec.x;
    const dy = v2Vec.y - v1Vec.y;
    const distance = Math.sqrt(dx * dx + dy * dy);
    return Number.isFinite(distance) && distance > 0 ? distance : 1;
  }
  return 1;
}
function interpolateProperty(property, frame, fps = 16, layerId = "", compDuration) {
  let value;
  if (!property.animated || property.keyframes.length === 0) {
    value = property.value;
  } else {
    const keyframes = property.keyframes;
    if (frame <= keyframes[0].frame) {
      value = keyframes[0].value;
    } else if (frame >= keyframes[keyframes.length - 1].frame) {
      value = keyframes[keyframes.length - 1].value;
    } else {
      const idx = findKeyframeIndex(keyframes, frame);
      const k1 = keyframes[idx];
      const k2 = keyframes[idx + 1];
      const duration = k2.frame - k1.frame;
      const elapsed = frame - k1.frame;
      let t = duration > 0 ? elapsed / duration : 0;
      const interpolation = k1.interpolation || "linear";
      if (interpolation === "hold") {
        value = k1.value;
      } else {
        if (interpolation === "bezier") {
          const valueDelta = getValueDelta(k1.value, k2.value);
          t = cubicBezierEasing(
            t,
            k1.outHandle,
            k2.inHandle,
            duration,
            valueDelta
          );
        } else if (interpolation !== "linear" && interpolation in easings) {
          const easingFn = getEasing(interpolation);
          t = easingFn(t);
        } else if (interpolation !== "linear") {
          renderLogger.warn(
            `Unknown interpolation type: ${interpolation}, using linear`
          );
        }
        value = interpolateValue(k1.value, k2.value, t);
      }
    }
  }
  if (property.expression?.enabled) {
    value = applyPropertyExpression(
      property,
      value,
      frame,
      fps,
      layerId,
      compDuration
    );
  }
  return value;
}
function applyPropertyExpression(property, value, frame, fps, layerId, compDuration) {
  const expr = property.expression;
  if (!expr || !expr.enabled) return value;
  const safeFps = validateFps(fps, 16);
  const time = frame / safeFps;
  const velocity = calculateVelocity(property, frame, safeFps);
  const duration = compDuration ?? 81 / safeFps;
  const frameCount = Math.round(duration * safeFps);
  const ctx = {
    time,
    frame,
    fps: safeFps,
    duration,
    layerIndex: 0,
    layerName: "",
    inPoint: 0,
    outPoint: frameCount,
    value,
    velocity,
    numKeys: property.keyframes.length,
    // Type assertion: expressions only work with numeric keyframes (number or number[])
    keyframes: property.keyframes};
  const expression = {
    type: expr.type,
    name: expr.name,
    params: expr.params,
    enabled: expr.enabled
  };
  const result = evaluateExpression(expression, ctx);
  return result;
}
function calculateVelocity(property, frame, fps) {
  const delta = 0.5;
  const valueBefore = interpolatePropertyBase(property, frame - delta);
  const valueAfter = interpolatePropertyBase(property, frame + delta);
  if (typeof valueBefore === "number" && typeof valueAfter === "number") {
    return (valueAfter - valueBefore) * fps;
  }
  if (typeof valueBefore === "object" && typeof valueAfter === "object") {
    if (valueBefore !== null && valueAfter !== null && "x" in valueBefore && "y" in valueBefore && "x" in valueAfter && "y" in valueAfter) {
      const vb = valueBefore;
      const va = valueAfter;
      const result = [(va.x - vb.x) * fps, (va.y - vb.y) * fps];
      if ("z" in vb && "z" in va) {
        result.push((va.z - vb.z) * fps);
      }
      return result;
    }
  }
  return 0;
}
function interpolatePropertyBase(property, frame) {
  if (!property.animated || property.keyframes.length === 0) {
    return property.value;
  }
  const keyframes = property.keyframes;
  if (frame <= keyframes[0].frame) {
    return keyframes[0].value;
  }
  if (frame >= keyframes[keyframes.length - 1].frame) {
    return keyframes[keyframes.length - 1].value;
  }
  const idx = findKeyframeIndex(keyframes, frame);
  const k1 = keyframes[idx];
  const k2 = keyframes[idx + 1];
  const duration = k2.frame - k1.frame;
  const elapsed = frame - k1.frame;
  let t = duration > 0 ? elapsed / duration : 0;
  const interpolation = k1.interpolation || "linear";
  if (interpolation === "hold") {
    return k1.value;
  } else if (interpolation === "bezier") {
    const valueDelta = getValueDelta(k1.value, k2.value);
    t = cubicBezierEasing(t, k1.outHandle, k2.inHandle, duration, valueDelta);
  } else if (interpolation !== "linear" && interpolation in easings) {
    const easingFn = getEasing(interpolation);
    t = easingFn(t);
  }
  return interpolateValue(k1.value, k2.value, t);
}
function cubicBezierEasing(t, outHandle, inHandle, frameDuration = 1, valueDelta = 1) {
  if (!outHandle.enabled && !inHandle.enabled) {
    return t;
  }
  const { x1, y1, x2, y2 } = bezierCache.get(
    outHandle,
    inHandle,
    frameDuration,
    valueDelta
  );
  let guessT = t;
  const EPSILON = 1e-6;
  const MAX_ITERATIONS = 8;
  for (let i = 0; i < MAX_ITERATIONS; i++) {
    const currentX = bezierPoint(guessT, 0, x1, x2, 1);
    const error = currentX - t;
    if (Math.abs(error) < EPSILON) break;
    const currentSlope = bezierDerivative(guessT, 0, x1, x2, 1);
    if (Math.abs(currentSlope) < EPSILON) break;
    guessT -= error / currentSlope;
    guessT = Math.max(0, Math.min(1, guessT));
  }
  return bezierPoint(guessT, 0, y1, y2, 1);
}
function bezierPoint(t, p0, p1, p2, p3) {
  const mt = 1 - t;
  return mt * mt * mt * p0 + 3 * mt * mt * t * p1 + 3 * mt * t * t * p2 + t * t * t * p3;
}
function bezierDerivative(t, p0, p1, p2, p3) {
  const mt = 1 - t;
  return 3 * mt * mt * (p1 - p0) + 6 * mt * t * (p2 - p1) + 3 * t * t * (p3 - p2);
}
function interpolateValue(v1, v2, t) {
  if (typeof v1 === "number" && typeof v2 === "number") {
    return safeLerp(v1, v2, t);
  }
  if (typeof v1 === "object" && v1 !== null && typeof v2 === "object" && v2 !== null && "x" in v1 && "y" in v1 && "x" in v2 && "y" in v2) {
    const val1 = v1;
    const val2 = v2;
    const result = {
      x: safeLerp(val1.x, val2.x, t),
      y: safeLerp(val1.y, val2.y, t)
    };
    if ("z" in val1 && "z" in val2) {
      result.z = safeLerp(val1.z, val2.z, t);
    } else if ("z" in val1) {
      result.z = safeLerp(val1.z, 0, t);
    } else if ("z" in val2) {
      result.z = safeLerp(0, val2.z, t);
    }
    return result;
  }
  if (typeof v1 === "string" && typeof v2 === "string" && v1.startsWith("#") && v2.startsWith("#")) {
    return interpolateColor(v1, v2, t);
  }
  if (isBezierPath(v1) && isBezierPath(v2)) {
    return interpolatePath(v1, v2, t);
  }
  return t < 0.5 ? v1 : v2;
}
function normalizeHexColor(hex) {
  if (!hex || !hex.startsWith("#")) return "#000000";
  const h = hex.slice(1);
  if (h.length === 3) {
    return `#${h[0]}${h[0]}${h[1]}${h[1]}${h[2]}${h[2]}`;
  }
  if (h.length === 4) {
    return `#${h[0]}${h[0]}${h[1]}${h[1]}${h[2]}${h[2]}${h[3]}${h[3]}`;
  }
  if (h.length === 6 || h.length === 8) {
    return hex;
  }
  return "#000000";
}
function parseHexComponent(hex, start, end) {
  const val = parseInt(hex.slice(start, end), 16);
  return Number.isNaN(val) ? 0 : Math.max(0, Math.min(255, val));
}
function interpolateColor(c1, c2, t) {
  const n1 = normalizeHexColor(c1);
  const n2 = normalizeHexColor(c2);
  const r1 = parseHexComponent(n1, 1, 3);
  const g1 = parseHexComponent(n1, 3, 5);
  const b1 = parseHexComponent(n1, 5, 7);
  const a1 = n1.length === 9 ? parseHexComponent(n1, 7, 9) : 255;
  const r2 = parseHexComponent(n2, 1, 3);
  const g2 = parseHexComponent(n2, 3, 5);
  const b2 = parseHexComponent(n2, 5, 7);
  const a2 = n2.length === 9 ? parseHexComponent(n2, 7, 9) : 255;
  const r = Math.round(r1 + (r2 - r1) * t);
  const g = Math.round(g1 + (g2 - g1) * t);
  const b = Math.round(b1 + (b2 - b1) * t);
  if (n1.length === 9 || n2.length === 9) {
    const a = Math.round(a1 + (a2 - a1) * t);
    return `#${r.toString(16).padStart(2, "0")}${g.toString(16).padStart(2, "0")}${b.toString(16).padStart(2, "0")}${a.toString(16).padStart(2, "0")}`;
  }
  return `#${r.toString(16).padStart(2, "0")}${g.toString(16).padStart(2, "0")}${b.toString(16).padStart(2, "0")}`;
}
const pathMorphCache = /* @__PURE__ */ new Map();
const PATH_MORPH_CACHE_MAX = 100;
function hashBezierPath(path) {
  const v = path.vertices;
  if (v.length === 0) return "empty";
  const first = v[0];
  const last = v[v.length - 1];
  return `${v.length}_${first.point.x.toFixed(1)}_${first.point.y.toFixed(1)}_${last.point.x.toFixed(1)}_${last.point.y.toFixed(1)}_${path.closed ? "c" : "o"}`;
}
function interpolatePath(p1, p2, t) {
  if (t <= 0) return p1;
  if (t >= 1) return p2;
  const key = `${hashBezierPath(p1)}|${hashBezierPath(p2)}`;
  let prepared = pathMorphCache.get(key);
  if (!prepared) {
    prepared = prepareMorphPaths(p1, p2);
    if (pathMorphCache.size >= PATH_MORPH_CACHE_MAX) {
      const firstKey = pathMorphCache.keys().next().value;
      if (firstKey) pathMorphCache.delete(firstKey);
    }
    pathMorphCache.set(key, prepared);
  }
  return morphPaths(prepared.source, prepared.target, t);
}

function cleanupEffectResources() {
  canvasPool.cleanup();
}
const effectRenderers = /* @__PURE__ */ new Map();
function registerEffectRenderer(effectKey, renderer) {
  effectRenderers.set(effectKey, renderer);
}
function createMatchingCanvas(source) {
  return canvasPool.acquire(source.width, source.height);
}

function renderAudioSpectrum(input, params, frame, audioData) {
  const { canvas, ctx } = createMatchingCanvas(input.canvas);
  ctx.drawImage(input.canvas, 0, 0);
  const {
    startPointX = 0,
    startPointY = canvas.height / 2,
    endPointX = canvas.width,
    endPointY = canvas.height / 2,
    frequencyBands = 64,
    maxHeight = 100,
    displayMode = "digital",
    sideOptions = "side_a",
    thickness = 3,
    softness = 0,
    insideColor = "#ffffff",
    outsideColor = "#ffffff"
  } = params;
  const spectrumData = generateSpectrumData(frame, frequencyBands);
  const dx = endPointX - startPointX;
  const dy = endPointY - startPointY;
  const length = Math.sqrt(dx * dx + dy * dy);
  if (length === 0) {
    return { canvas, ctx };
  }
  const perpX = -dy / length;
  const perpY = dx / length;
  ctx.save();
  if (softness > 0) {
    ctx.filter = `blur(${softness}px)`;
  }
  for (let i = 0; i < frequencyBands; i++) {
    const t = (i + 0.5) / frequencyBands;
    const x = startPointX + dx * t;
    const y = startPointY + dy * t;
    const amplitude = spectrumData[i];
    const barHeight = amplitude * maxHeight;
    const gradient = ctx.createLinearGradient(
      x,
      y,
      x + perpX * barHeight,
      y + perpY * barHeight
    );
    gradient.addColorStop(0, insideColor);
    gradient.addColorStop(1, outsideColor);
    ctx.fillStyle = gradient;
    ctx.strokeStyle = gradient;
    ctx.lineWidth = thickness;
    if (displayMode === "digital") {
      const segments = Math.ceil(barHeight / 4);
      for (let s = 0; s < segments; s++) {
        const segY = s * 4;
        if (segY < barHeight) {
          ctx.fillRect(
            x - thickness / 2 + perpX * segY,
            y + perpY * segY,
            thickness,
            3
          );
          if (sideOptions === "side_a_b" || sideOptions === "side_b") {
            ctx.fillRect(
              x - thickness / 2 - perpX * segY,
              y - perpY * segY,
              thickness,
              3
            );
          }
        }
      }
    } else if (displayMode === "analog_lines") {
      ctx.beginPath();
      ctx.moveTo(x, y);
      ctx.lineTo(x + perpX * barHeight, y + perpY * barHeight);
      ctx.stroke();
      if (sideOptions === "side_a_b" || sideOptions === "side_b") {
        ctx.beginPath();
        ctx.moveTo(x, y);
        ctx.lineTo(x - perpX * barHeight, y - perpY * barHeight);
        ctx.stroke();
      }
    } else {
      const dotSpacing = 4;
      const dots = Math.ceil(barHeight / dotSpacing);
      for (let d = 0; d < dots; d++) {
        const dotY = d * dotSpacing;
        ctx.beginPath();
        ctx.arc(
          x + perpX * dotY,
          y + perpY * dotY,
          thickness / 2,
          0,
          Math.PI * 2
        );
        ctx.fill();
        if (sideOptions === "side_a_b" || sideOptions === "side_b") {
          ctx.beginPath();
          ctx.arc(
            x - perpX * dotY,
            y - perpY * dotY,
            thickness / 2,
            0,
            Math.PI * 2
          );
          ctx.fill();
        }
      }
    }
  }
  ctx.restore();
  return { canvas, ctx };
}
function generateSpectrumData(frame, bands, audioData) {
  const spectrum = new Array(bands).fill(0);
  {
    for (let i = 0; i < bands; i++) {
      const t = i / bands;
      const baseFreq = 0.1 + t * 0.05;
      const phase = frame * baseFreq;
      const decay = 1 - t * 0.5;
      spectrum[i] = (Math.sin(phase) * 0.5 + 0.5) * decay * 0.6;
    }
  }
  return spectrum;
}
function renderAudioWaveform(input, params, frame, audioData) {
  const { canvas, ctx } = createMatchingCanvas(input.canvas);
  ctx.drawImage(input.canvas, 0, 0);
  const {
    startPointX = 0,
    startPointY = canvas.height / 2,
    endPointX = canvas.width,
    endPointY = canvas.height / 2,
    displayedSamples = 200,
    maxHeight = 100,
    displayMode = "analog_lines",
    thickness = 2,
    softness = 0,
    insideColor = "#ffffff",
    outsideColor = "#ffffff"
  } = params;
  const waveformData = generateWaveformData(frame, displayedSamples);
  const dx = endPointX - startPointX;
  const dy = endPointY - startPointY;
  const length = Math.sqrt(dx * dx + dy * dy);
  if (length === 0) {
    return { canvas, ctx };
  }
  const perpX = -dy / length;
  const perpY = dx / length;
  ctx.save();
  if (softness > 0) {
    ctx.filter = `blur(${softness}px)`;
  }
  const gradient = ctx.createLinearGradient(
    startPointX + perpX * maxHeight,
    startPointY + perpY * maxHeight,
    startPointX - perpX * maxHeight,
    startPointY - perpY * maxHeight
  );
  gradient.addColorStop(0, outsideColor);
  gradient.addColorStop(0.5, insideColor);
  gradient.addColorStop(1, outsideColor);
  ctx.strokeStyle = gradient;
  ctx.fillStyle = gradient;
  ctx.lineWidth = thickness;
  ctx.lineCap = "round";
  ctx.lineJoin = "round";
  if (displayMode === "analog_lines") {
    ctx.beginPath();
    for (let i = 0; i < displayedSamples; i++) {
      const t = i / (displayedSamples - 1);
      const x = startPointX + dx * t;
      const y = startPointY + dy * t;
      const amplitude = waveformData[i];
      const offset = amplitude * maxHeight;
      const px = x + perpX * offset;
      const py = y + perpY * offset;
      if (i === 0) {
        ctx.moveTo(px, py);
      } else {
        ctx.lineTo(px, py);
      }
    }
    ctx.stroke();
  } else if (displayMode === "digital") {
    for (let i = 0; i < displayedSamples; i++) {
      const t = i / (displayedSamples - 1);
      const x = startPointX + dx * t;
      const y = startPointY + dy * t;
      const amplitude = waveformData[i];
      const offset = amplitude * maxHeight;
      ctx.beginPath();
      ctx.moveTo(x - perpX * offset, y - perpY * offset);
      ctx.lineTo(x + perpX * offset, y + perpY * offset);
      ctx.stroke();
    }
  } else {
    for (let i = 0; i < displayedSamples; i++) {
      const t = i / (displayedSamples - 1);
      const x = startPointX + dx * t;
      const y = startPointY + dy * t;
      const amplitude = waveformData[i];
      const offset = amplitude * maxHeight;
      ctx.beginPath();
      ctx.arc(
        x + perpX * offset,
        y + perpY * offset,
        thickness,
        0,
        Math.PI * 2
      );
      ctx.fill();
    }
  }
  ctx.restore();
  return { canvas, ctx };
}
function generateWaveformData(frame, samples, audioData) {
  const waveform = new Array(samples).fill(0);
  {
    for (let i = 0; i < samples; i++) {
      const freq1 = Math.sin((frame + i) * 0.2) * 0.4;
      const freq2 = Math.sin((frame + i) * 0.07) * 0.3;
      const freq3 = Math.sin((frame + i) * 0.02) * 0.2;
      waveform[i] = freq1 + freq2 + freq3;
    }
  }
  return waveform;
}
function registerAudioVisualizerEffects() {
  registerEffectRenderer(
    "audio-spectrum",
    (input, params) => {
      return renderAudioSpectrum(
        input,
        params,
        0
      );
    }
  );
  registerEffectRenderer(
    "audio-waveform",
    (input, params) => {
      return renderAudioWaveform(
        input,
        params,
        0
      );
    }
  );
}

class WebGLBlurContext {
  gl = null;
  canvas = null;
  program = null;
  positionBuffer = null;
  texCoordBuffer = null;
  texture = null;
  framebuffer = null;
  pingPongTextures = [];
  _isAvailable = null;
  currentWidth = 0;
  currentHeight = 0;
  /**
   * Vertex shader for fullscreen quad
   */
  vertexShaderSource = `
    attribute vec2 a_position;
    attribute vec2 a_texCoord;
    varying vec2 v_texCoord;
    void main() {
      gl_Position = vec4(a_position, 0.0, 1.0);
      v_texCoord = a_texCoord;
    }
  `;
  /**
   * Fragment shader for separable Gaussian blur
   * Uses 9-tap kernel approximation
   */
  fragmentShaderSource = `
    precision mediump float;
    uniform sampler2D u_image;
    uniform vec2 u_direction;
    uniform vec2 u_resolution;
    uniform float u_radius;
    varying vec2 v_texCoord;

    void main() {
      vec2 texelSize = 1.0 / u_resolution;
      vec4 color = vec4(0.0);
      float total = 0.0;

      // Dynamic kernel based on radius
      int samples = int(min(u_radius * 2.0 + 1.0, 25.0));
      float sigma = max(u_radius / 2.0, 1.0);

      for (int i = -12; i <= 12; i++) {
        if (abs(float(i)) > u_radius) continue;

        float x = float(i);
        float weight = exp(-(x * x) / (2.0 * sigma * sigma));
        vec2 offset = u_direction * texelSize * x;
        color += texture2D(u_image, v_texCoord + offset) * weight;
        total += weight;
      }

      gl_FragColor = color / total;
    }
  `;
  /**
   * Check if WebGL blur is available
   */
  isAvailable() {
    if (this._isAvailable !== null) {
      return this._isAvailable;
    }
    try {
      const testCanvas = document.createElement("canvas");
      testCanvas.width = 1;
      testCanvas.height = 1;
      const gl = testCanvas.getContext("webgl") || testCanvas.getContext("experimental-webgl");
      this._isAvailable = gl !== null;
    } catch {
      this._isAvailable = false;
    }
    return this._isAvailable;
  }
  /**
   * Initialize WebGL context and shaders
   */
  init(width, height) {
    if (!this.isAvailable()) return false;
    if (!this.canvas) {
      this.canvas = document.createElement("canvas");
    }
    if (this.currentWidth !== width || this.currentHeight !== height) {
      this.canvas.width = width;
      this.canvas.height = height;
      this.currentWidth = width;
      this.currentHeight = height;
      this.pingPongTextures = [];
    }
    if (!this.gl) {
      this.gl = this.canvas.getContext("webgl", {
        alpha: true,
        premultipliedAlpha: false,
        preserveDrawingBuffer: true
      });
      if (!this.gl) return false;
    }
    const gl = this.gl;
    if (!this.program) {
      const vertexShader = this.compileShader(
        gl,
        gl.VERTEX_SHADER,
        this.vertexShaderSource
      );
      const fragmentShader = this.compileShader(
        gl,
        gl.FRAGMENT_SHADER,
        this.fragmentShaderSource
      );
      if (!vertexShader || !fragmentShader) return false;
      this.program = gl.createProgram();
      gl.attachShader(this.program, vertexShader);
      gl.attachShader(this.program, fragmentShader);
      gl.linkProgram(this.program);
      if (!gl.getProgramParameter(this.program, gl.LINK_STATUS)) {
        console.warn(
          "[WebGLBlur] Program link failed:",
          gl.getProgramInfoLog(this.program)
        );
        return false;
      }
      this.positionBuffer = gl.createBuffer();
      gl.bindBuffer(gl.ARRAY_BUFFER, this.positionBuffer);
      gl.bufferData(
        gl.ARRAY_BUFFER,
        new Float32Array([-1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1]),
        gl.STATIC_DRAW
      );
      this.texCoordBuffer = gl.createBuffer();
      gl.bindBuffer(gl.ARRAY_BUFFER, this.texCoordBuffer);
      gl.bufferData(
        gl.ARRAY_BUFFER,
        new Float32Array([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1]),
        gl.STATIC_DRAW
      );
    }
    if (this.pingPongTextures.length < 2) {
      for (let i = 0; i < 2; i++) {
        const tex = gl.createTexture();
        gl.bindTexture(gl.TEXTURE_2D, tex);
        gl.texImage2D(
          gl.TEXTURE_2D,
          0,
          gl.RGBA,
          width,
          height,
          0,
          gl.RGBA,
          gl.UNSIGNED_BYTE,
          null
        );
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
        this.pingPongTextures.push(tex);
      }
      this.framebuffer = gl.createFramebuffer();
    }
    return true;
  }
  /**
   * Compile a shader
   */
  compileShader(gl, type, source) {
    const shader = gl.createShader(type);
    gl.shaderSource(shader, source);
    gl.compileShader(shader);
    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
      console.warn(
        "[WebGLBlur] Shader compile failed:",
        gl.getShaderInfoLog(shader)
      );
      gl.deleteShader(shader);
      return null;
    }
    return shader;
  }
  /**
   * Apply Gaussian blur using WebGL
   */
  blur(input, radiusX, radiusY) {
    const { width, height } = input;
    if (!this.init(width, height)) {
      return null;
    }
    const gl = this.gl;
    const program = this.program;
    gl.useProgram(program);
    gl.viewport(0, 0, width, height);
    const positionLoc = gl.getAttribLocation(program, "a_position");
    const texCoordLoc = gl.getAttribLocation(program, "a_texCoord");
    const imageLoc = gl.getUniformLocation(program, "u_image");
    const directionLoc = gl.getUniformLocation(program, "u_direction");
    const resolutionLoc = gl.getUniformLocation(program, "u_resolution");
    const radiusLoc = gl.getUniformLocation(program, "u_radius");
    gl.bindBuffer(gl.ARRAY_BUFFER, this.positionBuffer);
    gl.enableVertexAttribArray(positionLoc);
    gl.vertexAttribPointer(positionLoc, 2, gl.FLOAT, false, 0, 0);
    gl.bindBuffer(gl.ARRAY_BUFFER, this.texCoordBuffer);
    gl.enableVertexAttribArray(texCoordLoc);
    gl.vertexAttribPointer(texCoordLoc, 2, gl.FLOAT, false, 0, 0);
    gl.uniform1i(imageLoc, 0);
    gl.uniform2f(resolutionLoc, width, height);
    if (!this.texture) {
      this.texture = gl.createTexture();
    }
    gl.activeTexture(gl.TEXTURE0);
    gl.bindTexture(gl.TEXTURE_2D, this.texture);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, input);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    let sourceTexture = this.texture;
    let destIdx = 0;
    if (radiusX > 0) {
      gl.bindFramebuffer(gl.FRAMEBUFFER, this.framebuffer);
      gl.framebufferTexture2D(
        gl.FRAMEBUFFER,
        gl.COLOR_ATTACHMENT0,
        gl.TEXTURE_2D,
        this.pingPongTextures[destIdx],
        0
      );
      gl.bindTexture(gl.TEXTURE_2D, sourceTexture);
      gl.uniform2f(directionLoc, 1, 0);
      gl.uniform1f(radiusLoc, radiusX);
      gl.drawArrays(gl.TRIANGLES, 0, 6);
      sourceTexture = this.pingPongTextures[destIdx];
      destIdx = 1 - destIdx;
    }
    if (radiusY > 0) {
      gl.bindFramebuffer(gl.FRAMEBUFFER, this.framebuffer);
      gl.framebufferTexture2D(
        gl.FRAMEBUFFER,
        gl.COLOR_ATTACHMENT0,
        gl.TEXTURE_2D,
        this.pingPongTextures[destIdx],
        0
      );
      gl.bindTexture(gl.TEXTURE_2D, sourceTexture);
      gl.uniform2f(directionLoc, 0, 1);
      gl.uniform1f(radiusLoc, radiusY);
      gl.drawArrays(gl.TRIANGLES, 0, 6);
      sourceTexture = this.pingPongTextures[destIdx];
    }
    gl.bindFramebuffer(gl.FRAMEBUFFER, this.framebuffer);
    gl.framebufferTexture2D(
      gl.FRAMEBUFFER,
      gl.COLOR_ATTACHMENT0,
      gl.TEXTURE_2D,
      sourceTexture,
      0
    );
    const pixels = new Uint8Array(width * height * 4);
    gl.readPixels(0, 0, width, height, gl.RGBA, gl.UNSIGNED_BYTE, pixels);
    gl.bindFramebuffer(gl.FRAMEBUFFER, null);
    const outputCanvas = document.createElement("canvas");
    outputCanvas.width = width;
    outputCanvas.height = height;
    const ctx = outputCanvas.getContext("2d");
    const imageData = ctx.createImageData(width, height);
    for (let y = 0; y < height; y++) {
      const srcRow = (height - 1 - y) * width * 4;
      const dstRow = y * width * 4;
      for (let x = 0; x < width * 4; x++) {
        imageData.data[dstRow + x] = pixels[srcRow + x];
      }
    }
    ctx.putImageData(imageData, 0, 0);
    return outputCanvas;
  }
  /**
   * Clean up WebGL resources
   */
  dispose() {
    if (this.gl) {
      if (this.program) this.gl.deleteProgram(this.program);
      if (this.texture) this.gl.deleteTexture(this.texture);
      if (this.positionBuffer) this.gl.deleteBuffer(this.positionBuffer);
      if (this.texCoordBuffer) this.gl.deleteBuffer(this.texCoordBuffer);
      if (this.framebuffer) this.gl.deleteFramebuffer(this.framebuffer);
      for (const tex of this.pingPongTextures) {
        this.gl.deleteTexture(tex);
      }
    }
    this.gl = null;
    this.canvas = null;
    this.program = null;
    this._isAvailable = null;
  }
}
const webglBlurContext = new WebGLBlurContext();
const GPU_BLUR_THRESHOLD = 15;
const MUL_TABLE = [
  512,
  512,
  456,
  512,
  328,
  456,
  335,
  512,
  405,
  328,
  271,
  456,
  388,
  335,
  292,
  512,
  454,
  405,
  364,
  328,
  298,
  271,
  496,
  456,
  420,
  388,
  360,
  335,
  312,
  292,
  273,
  512,
  482,
  454,
  428,
  405,
  383,
  364,
  345,
  328,
  312,
  298,
  284,
  271,
  259,
  496,
  475,
  456,
  437,
  420,
  404,
  388,
  374,
  360,
  347,
  335,
  323,
  312,
  302,
  292,
  282,
  273,
  265,
  512,
  497,
  482,
  468,
  454,
  441,
  428,
  417,
  405,
  394,
  383,
  373,
  364,
  354,
  345,
  337,
  328,
  320,
  312,
  305,
  298,
  291,
  284,
  278,
  271,
  265,
  259,
  507,
  496,
  485,
  475,
  465,
  456,
  446,
  437,
  428,
  420,
  412,
  404,
  396,
  388,
  381,
  374,
  367,
  360,
  354,
  347,
  341,
  335,
  329,
  323,
  318,
  312,
  307,
  302,
  297,
  292,
  287,
  282,
  278,
  273,
  269,
  265,
  261,
  512,
  505,
  497,
  489,
  482,
  475,
  468,
  461,
  454,
  447,
  441,
  435,
  428,
  422,
  417,
  411,
  405,
  399,
  394,
  389,
  383,
  378,
  373,
  368,
  364,
  359,
  354,
  350,
  345,
  341,
  337,
  332,
  328,
  324,
  320,
  316,
  312,
  309,
  305,
  301,
  298,
  294,
  291,
  287,
  284,
  281,
  278,
  274,
  271,
  268,
  265,
  262,
  259,
  257,
  507,
  501,
  496,
  491,
  485,
  480,
  475,
  470,
  465,
  460,
  456,
  451,
  446,
  442,
  437,
  433,
  428,
  424,
  420,
  416,
  412,
  408,
  404,
  400,
  396,
  392,
  388,
  385,
  381,
  377,
  374,
  370,
  367,
  363,
  360,
  357,
  354,
  350,
  347,
  344,
  341,
  338,
  335,
  332,
  329,
  326,
  323,
  320,
  318,
  315,
  312,
  310,
  307,
  304,
  302,
  299,
  297,
  294,
  292,
  289,
  287,
  285,
  282,
  280,
  278,
  275,
  273,
  271,
  269,
  267,
  265,
  263,
  261,
  259
];
const SHG_TABLE = [
  9,
  11,
  12,
  13,
  13,
  14,
  14,
  15,
  15,
  15,
  15,
  16,
  16,
  16,
  16,
  17,
  17,
  17,
  17,
  17,
  17,
  17,
  18,
  18,
  18,
  18,
  18,
  18,
  18,
  18,
  18,
  19,
  19,
  19,
  19,
  19,
  19,
  19,
  19,
  19,
  19,
  19,
  19,
  19,
  19,
  20,
  20,
  20,
  20,
  20,
  20,
  20,
  20,
  20,
  20,
  20,
  20,
  20,
  20,
  20,
  20,
  20,
  20,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  21,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  22,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  23,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24,
  24
];
function createBlurStack(size) {
  const first = { r: 0, g: 0, b: 0, a: 0, next: null };
  let current = first;
  for (let i = 1; i < size; i++) {
    current.next = { r: 0, g: 0, b: 0, a: 0, next: null };
    current = current.next;
  }
  current.next = first;
  return first;
}
function stackBlur(imageData, radiusX, radiusY) {
  const pixels = imageData.data;
  const width = imageData.width;
  const height = imageData.height;
  radiusX = Math.round(radiusX);
  radiusY = Math.round(radiusY);
  if (!Number.isFinite(radiusX)) radiusX = 0;
  if (!Number.isFinite(radiusY)) radiusY = 0;
  radiusX = Math.max(0, Math.min(255, radiusX));
  radiusY = Math.max(0, Math.min(255, radiusY));
  if (radiusX === 0 && radiusY === 0) return;
  if (radiusX > 0) {
    stackBlurHorizontal(pixels, width, height, radiusX);
  }
  if (radiusY > 0) {
    stackBlurVertical(pixels, width, height, radiusY);
  }
}
function stackBlurHorizontal(pixels, width, height, radius) {
  const div = radius + radius + 1;
  const widthMinus1 = width - 1;
  const mulSum = MUL_TABLE[radius];
  const shgSum = SHG_TABLE[radius];
  const stack = createBlurStack(div);
  for (let y = 0; y < height; y++) {
    let rInSum = 0, gInSum = 0, bInSum = 0, aInSum = 0;
    let rOutSum = 0, gOutSum = 0, bOutSum = 0, aOutSum = 0;
    let rSum = 0, gSum = 0, bSum = 0, aSum = 0;
    const yOffset = y * width;
    let stackIn = stack;
    let stackOut = stack;
    const pr = pixels[yOffset * 4];
    const pg = pixels[yOffset * 4 + 1];
    const pb = pixels[yOffset * 4 + 2];
    const pa = pixels[yOffset * 4 + 3];
    for (let i = 0; i <= radius; i++) {
      stackIn.r = pr;
      stackIn.g = pg;
      stackIn.b = pb;
      stackIn.a = pa;
      const rbs = radius + 1 - i;
      rSum += pr * rbs;
      gSum += pg * rbs;
      bSum += pb * rbs;
      aSum += pa * rbs;
      if (i > 0) {
        rInSum += pr;
        gInSum += pg;
        bInSum += pb;
        aInSum += pa;
      } else {
        rOutSum += pr;
        gOutSum += pg;
        bOutSum += pb;
        aOutSum += pa;
      }
      stackIn = stackIn.next;
    }
    for (let i = 1; i <= radius; i++) {
      const p = Math.min(i, widthMinus1);
      const pOffset = (yOffset + p) * 4;
      const pr2 = pixels[pOffset];
      const pg2 = pixels[pOffset + 1];
      const pb2 = pixels[pOffset + 2];
      const pa2 = pixels[pOffset + 3];
      stackIn.r = pr2;
      stackIn.g = pg2;
      stackIn.b = pb2;
      stackIn.a = pa2;
      const rbs = radius + 1 - i;
      rSum += pr2 * rbs;
      gSum += pg2 * rbs;
      bSum += pb2 * rbs;
      aSum += pa2 * rbs;
      rInSum += pr2;
      gInSum += pg2;
      bInSum += pb2;
      aInSum += pa2;
      stackIn = stackIn.next;
    }
    let stackStart = stack;
    for (let i = 0; i < radius; i++) {
      stackStart = stackStart.next;
    }
    stackOut = stackStart.next;
    for (let x = 0; x < width; x++) {
      const pOffset = (yOffset + x) * 4;
      pixels[pOffset] = rSum * mulSum >>> shgSum;
      pixels[pOffset + 1] = gSum * mulSum >>> shgSum;
      pixels[pOffset + 2] = bSum * mulSum >>> shgSum;
      pixels[pOffset + 3] = aSum * mulSum >>> shgSum;
      rSum -= rOutSum;
      gSum -= gOutSum;
      bSum -= bOutSum;
      aSum -= aOutSum;
      rOutSum -= stackStart.r;
      gOutSum -= stackStart.g;
      bOutSum -= stackStart.b;
      aOutSum -= stackStart.a;
      const p = Math.min(x + radius + 1, widthMinus1);
      const pIn = (yOffset + p) * 4;
      stackStart.r = pixels[pIn];
      stackStart.g = pixels[pIn + 1];
      stackStart.b = pixels[pIn + 2];
      stackStart.a = pixels[pIn + 3];
      rInSum += stackStart.r;
      gInSum += stackStart.g;
      bInSum += stackStart.b;
      aInSum += stackStart.a;
      rSum += rInSum;
      gSum += gInSum;
      bSum += bInSum;
      aSum += aInSum;
      stackStart = stackStart.next;
      rOutSum += stackOut.r;
      gOutSum += stackOut.g;
      bOutSum += stackOut.b;
      aOutSum += stackOut.a;
      rInSum -= stackOut.r;
      gInSum -= stackOut.g;
      bInSum -= stackOut.b;
      aInSum -= stackOut.a;
      stackOut = stackOut.next;
    }
  }
}
function stackBlurVertical(pixels, width, height, radius) {
  const div = radius + radius + 1;
  const heightMinus1 = height - 1;
  const mulSum = MUL_TABLE[radius];
  const shgSum = SHG_TABLE[radius];
  const stack = createBlurStack(div);
  for (let x = 0; x < width; x++) {
    let rInSum = 0, gInSum = 0, bInSum = 0, aInSum = 0;
    let rOutSum = 0, gOutSum = 0, bOutSum = 0, aOutSum = 0;
    let rSum = 0, gSum = 0, bSum = 0, aSum = 0;
    let stackIn = stack;
    let stackOut = stack;
    const pr = pixels[x * 4];
    const pg = pixels[x * 4 + 1];
    const pb = pixels[x * 4 + 2];
    const pa = pixels[x * 4 + 3];
    for (let i = 0; i <= radius; i++) {
      stackIn.r = pr;
      stackIn.g = pg;
      stackIn.b = pb;
      stackIn.a = pa;
      const rbs = radius + 1 - i;
      rSum += pr * rbs;
      gSum += pg * rbs;
      bSum += pb * rbs;
      aSum += pa * rbs;
      if (i > 0) {
        rInSum += pr;
        gInSum += pg;
        bInSum += pb;
        aInSum += pa;
      } else {
        rOutSum += pr;
        gOutSum += pg;
        bOutSum += pb;
        aOutSum += pa;
      }
      stackIn = stackIn.next;
    }
    for (let i = 1; i <= radius; i++) {
      const p = Math.min(i, heightMinus1);
      const pOffset = (p * width + x) * 4;
      const pr2 = pixels[pOffset];
      const pg2 = pixels[pOffset + 1];
      const pb2 = pixels[pOffset + 2];
      const pa2 = pixels[pOffset + 3];
      stackIn.r = pr2;
      stackIn.g = pg2;
      stackIn.b = pb2;
      stackIn.a = pa2;
      const rbs = radius + 1 - i;
      rSum += pr2 * rbs;
      gSum += pg2 * rbs;
      bSum += pb2 * rbs;
      aSum += pa2 * rbs;
      rInSum += pr2;
      gInSum += pg2;
      bInSum += pb2;
      aInSum += pa2;
      stackIn = stackIn.next;
    }
    let stackStart = stack;
    for (let i = 0; i < radius; i++) {
      stackStart = stackStart.next;
    }
    stackOut = stackStart.next;
    for (let y = 0; y < height; y++) {
      const pOffset = (y * width + x) * 4;
      pixels[pOffset] = rSum * mulSum >>> shgSum;
      pixels[pOffset + 1] = gSum * mulSum >>> shgSum;
      pixels[pOffset + 2] = bSum * mulSum >>> shgSum;
      pixels[pOffset + 3] = aSum * mulSum >>> shgSum;
      rSum -= rOutSum;
      gSum -= gOutSum;
      bSum -= bOutSum;
      aSum -= aOutSum;
      rOutSum -= stackStart.r;
      gOutSum -= stackStart.g;
      bOutSum -= stackStart.b;
      aOutSum -= stackStart.a;
      const p = Math.min(y + radius + 1, heightMinus1);
      const pIn = (p * width + x) * 4;
      stackStart.r = pixels[pIn];
      stackStart.g = pixels[pIn + 1];
      stackStart.b = pixels[pIn + 2];
      stackStart.a = pixels[pIn + 3];
      rInSum += stackStart.r;
      gInSum += stackStart.g;
      bInSum += stackStart.b;
      aInSum += stackStart.a;
      rSum += rInSum;
      gSum += gInSum;
      bSum += bInSum;
      aSum += aInSum;
      stackStart = stackStart.next;
      rOutSum += stackOut.r;
      gOutSum += stackOut.g;
      bOutSum += stackOut.b;
      aOutSum += stackOut.a;
      rInSum -= stackOut.r;
      gInSum -= stackOut.g;
      bInSum -= stackOut.b;
      aInSum -= stackOut.a;
      stackOut = stackOut.next;
    }
  }
}
let webgpuInitialized = false;
let webgpuInitializing = false;
async function ensureWebGPUInitialized() {
  if (webgpuInitialized) return webgpuRenderer.isAvailable();
  if (webgpuInitializing) return false;
  webgpuInitializing = true;
  try {
    await webgpuRenderer.initialize();
    webgpuInitialized = true;
    return webgpuRenderer.isAvailable();
  } catch {
    webgpuInitialized = true;
    return false;
  } finally {
    webgpuInitializing = false;
  }
}
ensureWebGPUInitialized();
function gaussianBlurRenderer(input, params) {
  const blurrinessRaw = params.blurriness ?? 10;
  const blurriness = Number.isFinite(blurrinessRaw) ? Math.max(0, blurrinessRaw) : 0;
  const dimensions = params.blur_dimensions ?? "both";
  const useGpu = params.use_gpu !== false;
  if (blurriness <= 0) {
    return input;
  }
  let radiusX = 0;
  let radiusY = 0;
  switch (dimensions) {
    case "horizontal":
      radiusX = blurriness;
      break;
    case "vertical":
      radiusY = blurriness;
      break;
    default:
      radiusX = blurriness;
      radiusY = blurriness;
      break;
  }
  const maxRadius = Math.max(radiusX, radiusY);
  if (useGpu && maxRadius > GPU_BLUR_THRESHOLD && webgpuInitialized && webgpuRenderer.isAvailable()) ;
  if (useGpu && maxRadius > GPU_BLUR_THRESHOLD && webglBlurContext.isAvailable()) {
    const gpuResult = webglBlurContext.blur(input.canvas, radiusX, radiusY);
    if (gpuResult) {
      const output2 = createMatchingCanvas(input.canvas);
      output2.ctx.drawImage(gpuResult, 0, 0);
      return output2;
    }
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  stackBlur(imageData, radiusX, radiusY);
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function directionalBlurRenderer(input, params) {
  const directionRaw = params.direction ?? 0;
  const direction = Number.isFinite(directionRaw) ? directionRaw * Math.PI / 180 : 0;
  const blurLengthRaw = params.blur_length ?? 10;
  const blurLength = Number.isFinite(blurLengthRaw) ? Math.max(0, Math.min(500, blurLengthRaw)) : 0;
  if (blurLength <= 0) {
    return input;
  }
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const outputData = output.ctx.createImageData(width, height);
  const src = inputData.data;
  const dst = outputData.data;
  const dx = Math.cos(direction);
  const dy = Math.sin(direction);
  const samples = Math.max(3, Math.ceil(blurLength));
  const halfSamples = Math.floor(samples / 2);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let r = 0, g = 0, b = 0, a = 0;
      let count = 0;
      for (let i = -halfSamples; i <= halfSamples; i++) {
        const sampleX = Math.round(x + dx * i * (blurLength / samples));
        const sampleY = Math.round(y + dy * i * (blurLength / samples));
        const sx = Math.max(0, Math.min(width - 1, sampleX));
        const sy = Math.max(0, Math.min(height - 1, sampleY));
        const idx = (sy * width + sx) * 4;
        r += src[idx];
        g += src[idx + 1];
        b += src[idx + 2];
        a += src[idx + 3];
        count++;
      }
      const outIdx = (y * width + x) * 4;
      dst[outIdx] = Math.round(r / count);
      dst[outIdx + 1] = Math.round(g / count);
      dst[outIdx + 2] = Math.round(b / count);
      dst[outIdx + 3] = Math.round(a / count);
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function radialBlurRenderer(input, params) {
  const type = params.type ?? "spin";
  const amountRaw = params.amount ?? 10;
  const amount = Number.isFinite(amountRaw) ? Math.max(0, Math.min(100, amountRaw)) : 0;
  const center = params.center;
  const centerXRaw = center?.x ?? (params.center_x ?? 50) / 100;
  const centerYRaw = center?.y ?? (params.center_y ?? 50) / 100;
  const centerX = Number.isFinite(centerXRaw) ? centerXRaw : 0.5;
  const centerY = Number.isFinite(centerYRaw) ? centerYRaw : 0.5;
  const antialiasing = params.antialiasing ?? params.quality ?? "high";
  const quality = antialiasing === "low" ? "draft" : antialiasing === "medium" ? "good" : "best";
  if (amount <= 0) {
    return input;
  }
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const outputData = output.ctx.createImageData(width, height);
  const src = inputData.data;
  const dst = outputData.data;
  const cx = centerX * width;
  const cy = centerY * height;
  const samples = quality === "best" ? 32 : quality === "good" ? 16 : 8;
  if (type === "spin") {
    const maxAngle = amount / 100 * Math.PI * 0.5;
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        let r = 0, g = 0, b = 0, a = 0;
        const dx = x - cx;
        const dy = y - cy;
        const dist = Math.sqrt(dx * dx + dy * dy);
        const baseAngle = Math.atan2(dy, dx);
        for (let i = 0; i < samples; i++) {
          const t = i / (samples - 1) - 0.5;
          const angle = baseAngle + t * maxAngle;
          const sampleX = Math.round(cx + Math.cos(angle) * dist);
          const sampleY = Math.round(cy + Math.sin(angle) * dist);
          const sx = Math.max(0, Math.min(width - 1, sampleX));
          const sy = Math.max(0, Math.min(height - 1, sampleY));
          const idx = (sy * width + sx) * 4;
          r += src[idx];
          g += src[idx + 1];
          b += src[idx + 2];
          a += src[idx + 3];
        }
        const outIdx = (y * width + x) * 4;
        dst[outIdx] = Math.round(r / samples);
        dst[outIdx + 1] = Math.round(g / samples);
        dst[outIdx + 2] = Math.round(b / samples);
        dst[outIdx + 3] = Math.round(a / samples);
      }
    }
  } else {
    const maxZoom = amount / 100;
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        let r = 0, g = 0, b = 0, a = 0;
        const dx = x - cx;
        const dy = y - cy;
        for (let i = 0; i < samples; i++) {
          const t = i / (samples - 1);
          const scale = 1 - t * maxZoom;
          const sampleX = Math.round(cx + dx * scale);
          const sampleY = Math.round(cy + dy * scale);
          const sx = Math.max(0, Math.min(width - 1, sampleX));
          const sy = Math.max(0, Math.min(height - 1, sampleY));
          const idx = (sy * width + sx) * 4;
          r += src[idx];
          g += src[idx + 1];
          b += src[idx + 2];
          a += src[idx + 3];
        }
        const outIdx = (y * width + x) * 4;
        dst[outIdx] = Math.round(r / samples);
        dst[outIdx + 1] = Math.round(g / samples);
        dst[outIdx + 2] = Math.round(b / samples);
        dst[outIdx + 3] = Math.round(a / samples);
      }
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function boxBlurRenderer(input, params) {
  const radiusRaw = Math.round(params.blur_radius ?? params.radius ?? 5);
  const radius = Number.isFinite(radiusRaw) ? Math.max(0, Math.min(100, radiusRaw)) : 0;
  const iterationsRaw = params.iterations ?? 1;
  const iterations = Number.isFinite(iterationsRaw) ? Math.max(1, Math.min(5, iterationsRaw)) : 1;
  if (radius <= 0) {
    return input;
  }
  const { width, height } = input.canvas;
  const current = createMatchingCanvas(input.canvas);
  current.ctx.drawImage(input.canvas, 0, 0);
  for (let iter = 0; iter < iterations; iter++) {
    const imageData = current.ctx.getImageData(0, 0, width, height);
    const src = imageData.data;
    const dst = new Uint8ClampedArray(src.length);
    const size = radius * 2 + 1;
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        let r = 0, g = 0, b = 0, a = 0;
        for (let dx = -radius; dx <= radius; dx++) {
          const sx = Math.max(0, Math.min(width - 1, x + dx));
          const idx = (y * width + sx) * 4;
          r += src[idx];
          g += src[idx + 1];
          b += src[idx + 2];
          a += src[idx + 3];
        }
        const outIdx = (y * width + x) * 4;
        dst[outIdx] = Math.round(r / size);
        dst[outIdx + 1] = Math.round(g / size);
        dst[outIdx + 2] = Math.round(b / size);
        dst[outIdx + 3] = Math.round(a / size);
      }
    }
    src.set(dst);
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        let r = 0, g = 0, b = 0, a = 0;
        for (let dy = -radius; dy <= radius; dy++) {
          const sy = Math.max(0, Math.min(height - 1, y + dy));
          const idx = (sy * width + x) * 4;
          r += src[idx];
          g += src[idx + 1];
          b += src[idx + 2];
          a += src[idx + 3];
        }
        const outIdx = (y * width + x) * 4;
        dst[outIdx] = Math.round(r / size);
        dst[outIdx + 1] = Math.round(g / size);
        dst[outIdx + 2] = Math.round(b / size);
        dst[outIdx + 3] = Math.round(a / size);
      }
    }
    imageData.data.set(dst);
    current.ctx.putImageData(imageData, 0, 0);
  }
  return current;
}
function sharpenRenderer(input, params) {
  const amountRaw = (params.sharpen_amount ?? params.amount ?? 50) / 100;
  const amount = Number.isFinite(amountRaw) ? amountRaw : 0;
  const radiusRaw = params.radius ?? 1;
  const radius = Number.isFinite(radiusRaw) ? Math.max(1, Math.min(100, radiusRaw)) : 1;
  const thresholdRaw = params.threshold ?? 0;
  const threshold = Number.isFinite(thresholdRaw) ? Math.max(0, Math.min(255, thresholdRaw)) : 0;
  if (amount <= 0) {
    return input;
  }
  const { width, height } = input.canvas;
  const blurred = createMatchingCanvas(input.canvas);
  blurred.ctx.drawImage(input.canvas, 0, 0);
  const blurredData = blurred.ctx.getImageData(0, 0, width, height);
  stackBlur(blurredData, radius, radius);
  const output = createMatchingCanvas(input.canvas);
  const originalData = input.ctx.getImageData(0, 0, width, height);
  const orig = originalData.data;
  const blur = blurredData.data;
  for (let i = 0; i < orig.length; i += 4) {
    for (let c = 0; c < 3; c++) {
      const diff = orig[i + c] - blur[i + c];
      if (Math.abs(diff) >= threshold) {
        const sharpened = orig[i + c] + diff * amount;
        orig[i + c] = Math.max(0, Math.min(255, Math.round(sharpened)));
      }
    }
  }
  output.ctx.putImageData(originalData, 0, 0);
  return output;
}
function registerBlurEffects() {
  registerEffectRenderer("gaussian-blur", gaussianBlurRenderer);
  registerEffectRenderer("directional-blur", directionalBlurRenderer);
  registerEffectRenderer("radial-blur", radialBlurRenderer);
  registerEffectRenderer("box-blur", boxBlurRenderer);
  registerEffectRenderer("sharpen", sharpenRenderer);
}

function tonemapACES(x) {
  const a = 2.51;
  const b = 0.03;
  const c = 2.43;
  const d = 0.59;
  const e = 0.14;
  return Math.max(0, Math.min(1, x * (a * x + b) / (x * (c * x + d) + e)));
}
function tonemapReinhard(x, whitePoint = 4) {
  const numerator = x * (1 + x / (whitePoint * whitePoint));
  return numerator / (1 + x);
}
function tonemapHable(x) {
  const A = 0.15;
  const B = 0.5;
  const C = 0.1;
  const D = 0.2;
  const E = 0.02;
  const F = 0.3;
  return (x * (A * x + C * B) + D * E) / (x * (A * x + B) + D * F) - E / F;
}
function applyTonemap(r, g, b, operator) {
  switch (operator) {
    case "aces":
      return [tonemapACES(r), tonemapACES(g), tonemapACES(b)];
    case "reinhard":
      return [tonemapReinhard(r), tonemapReinhard(g), tonemapReinhard(b)];
    case "hable": {
      const W = 11.2;
      const whiteScale = 1 / tonemapHable(W);
      return [
        tonemapHable(r) * whiteScale,
        tonemapHable(g) * whiteScale,
        tonemapHable(b) * whiteScale
      ];
    }
    default:
      return [Math.min(1, r), Math.min(1, g), Math.min(1, b)];
  }
}
function generateInverseSquareKernel(radius) {
  const size = Math.ceil(radius) * 2 + 1;
  const kernel = new Float32Array(size);
  const center = Math.floor(size / 2);
  const sigma = radius / 3;
  let sum = 0;
  for (let i = 0; i < size; i++) {
    const x = i - center;
    const weight = 1 / (1 + x * x / (sigma * sigma));
    kernel[i] = weight;
    sum += weight;
  }
  for (let i = 0; i < size; i++) {
    kernel[i] /= sum;
  }
  return kernel;
}
function generateExponentialKernel(radius, exponent) {
  const size = Math.ceil(radius) * 2 + 1;
  const kernel = new Float32Array(size);
  const center = Math.floor(size / 2);
  const sigma = radius / 3;
  let sum = 0;
  for (let i = 0; i < size; i++) {
    const x = Math.abs(i - center);
    const weight = Math.exp(-(x ** exponent) / (sigma * sigma));
    kernel[i] = weight;
    sum += weight;
  }
  for (let i = 0; i < size; i++) {
    kernel[i] /= sum;
  }
  return kernel;
}
function generateGaussianKernel(radius) {
  const size = Math.ceil(radius) * 2 + 1;
  const kernel = new Float32Array(size);
  const center = Math.floor(size / 2);
  const sigma = radius / 3;
  let sum = 0;
  for (let i = 0; i < size; i++) {
    const x = i - center;
    const weight = Math.exp(-(x * x) / (2 * sigma * sigma));
    kernel[i] = weight;
    sum += weight;
  }
  for (let i = 0; i < size; i++) {
    kernel[i] /= sum;
  }
  return kernel;
}
function applyBlur1D(src, dst, width, height, kernel, horizontal, channel) {
  const kernelSize = kernel.length;
  const kernelHalf = Math.floor(kernelSize / 2);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let sum = 0;
      for (let k = 0; k < kernelSize; k++) {
        const offset = k - kernelHalf;
        let sx, sy;
        if (horizontal) {
          sx = Math.max(0, Math.min(width - 1, x + offset));
          sy = y;
        } else {
          sx = x;
          sy = Math.max(0, Math.min(height - 1, y + offset));
        }
        const idx = (sy * width + sx) * 4 + channel;
        sum += src[idx] * kernel[k];
      }
      dst[(y * width + x) * 4 + channel] = sum;
    }
  }
}
function applyBloomBlur(imageData, width, height, radiusR, radiusG, radiusB, falloffMode, falloffExponent) {
  const result = new Float32Array(imageData.length);
  const temp = new Float32Array(imageData.length);
  result.set(imageData);
  const radii = [radiusR, radiusG, radiusB];
  for (let channel = 0; channel < 3; channel++) {
    const radius = radii[channel];
    if (radius <= 0) continue;
    let kernel;
    switch (falloffMode) {
      case "inverse_square":
        kernel = generateInverseSquareKernel(radius);
        break;
      case "exponential":
        kernel = generateExponentialKernel(radius, falloffExponent);
        break;
      default:
        kernel = generateGaussianKernel(radius);
        break;
    }
    applyBlur1D(result, temp, width, height, kernel, true, channel);
    applyBlur1D(temp, result, width, height, kernel, false, channel);
  }
  for (let i = 3; i < imageData.length; i += 4) {
    result[i] = imageData[i];
  }
  return result;
}
function extractBrightAreas(imageData, threshold, exposure) {
  const { data, width, height } = imageData;
  const result = new Float32Array(width * height * 4);
  const exposureMult = 2 ** exposure;
  for (let i = 0; i < data.length; i += 4) {
    const r = (data[i] / 255) ** 2.2 * exposureMult;
    const g = (data[i + 1] / 255) ** 2.2 * exposureMult;
    const b = (data[i + 2] / 255) ** 2.2 * exposureMult;
    const a = data[i + 3] / 255;
    const luminance = 0.2126 * r + 0.7152 * g + 0.0722 * b;
    const knee = 0.1;
    const soft = luminance - threshold + knee;
    const contribution = Math.max(0, soft * soft / (4 * knee));
    const factor = luminance > threshold ? 1 : threshold - knee < luminance ? contribution / luminance : 0;
    result[i] = r * factor;
    result[i + 1] = g * factor;
    result[i + 2] = b * factor;
    result[i + 3] = a;
  }
  return result;
}
function applyChromaticAberration(imageData, amount) {
  if (amount <= 0) return imageData;
  const { width, height, data } = imageData;
  const result = new ImageData(width, height);
  const dst = result.data;
  const centerX = width / 2;
  const centerY = height / 2;
  const maxDist = Math.sqrt(centerX * centerX + centerY * centerY);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const idx = (y * width + x) * 4;
      const dx = x - centerX;
      const dy = y - centerY;
      const dist = Math.sqrt(dx * dx + dy * dy);
      const normalizedDist = dist / maxDist;
      const offset = amount * normalizedDist;
      const rxR = Math.round(x + dx * offset / dist);
      const ryR = Math.round(y + dy * offset / dist);
      const rxB = Math.round(x - dx * offset / dist);
      const ryB = Math.round(y - dy * offset / dist);
      const clampX = (v) => Math.max(0, Math.min(width - 1, v));
      const clampY = (v) => Math.max(0, Math.min(height - 1, v));
      const idxR = (clampY(ryR) * width + clampX(rxR)) * 4;
      const idxB = (clampY(ryB) * width + clampX(rxB)) * 4;
      dst[idx] = data[idxR];
      dst[idx + 1] = data[idx + 1];
      dst[idx + 2] = data[idxB + 2];
      dst[idx + 3] = data[idx + 3];
    }
  }
  return result;
}
function generateLensDirt(width, height, scale, seed = 12345) {
  const result = new Float32Array(width * height);
  let state = seed;
  const random = () => {
    state = state * 1103515245 + 12345 & 2147483647;
    return state / 2147483647;
  };
  for (let i = 0; i < result.length; i++) {
    result[i] = random() * 0.1;
  }
  const numSpots = Math.floor(50 * scale);
  for (let i = 0; i < numSpots; i++) {
    const cx = random() * width;
    const cy = random() * height;
    const r = (5 + random() * 20) * scale;
    const brightness = 0.3 + random() * 0.7;
    const minX = Math.max(0, Math.floor(cx - r));
    const maxX = Math.min(width - 1, Math.ceil(cx + r));
    const minY = Math.max(0, Math.floor(cy - r));
    const maxY = Math.min(height - 1, Math.ceil(cy + r));
    for (let y = minY; y <= maxY; y++) {
      for (let x = minX; x <= maxX; x++) {
        const dx = x - cx;
        const dy = y - cy;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist < r) {
          const falloff = 1 - dist / r;
          const idx = y * width + x;
          result[idx] = Math.max(result[idx], falloff * falloff * brightness);
        }
      }
    }
  }
  const numSmudges = Math.floor(10 * scale);
  for (let i = 0; i < numSmudges; i++) {
    const cx = random() * width;
    const cy = random() * height;
    const rx = (30 + random() * 60) * scale;
    const ry = (20 + random() * 40) * scale;
    const brightness = 0.15 + random() * 0.25;
    const angle = random() * Math.PI;
    const cosA = Math.cos(angle);
    const sinA = Math.sin(angle);
    const maxR = Math.max(rx, ry);
    const minX = Math.max(0, Math.floor(cx - maxR));
    const maxX = Math.min(width - 1, Math.ceil(cx + maxR));
    const minY = Math.max(0, Math.floor(cy - maxR));
    const maxY = Math.min(height - 1, Math.ceil(cy + maxR));
    for (let y = minY; y <= maxY; y++) {
      for (let x = minX; x <= maxX; x++) {
        const dx = x - cx;
        const dy = y - cy;
        const rx2 = dx * cosA + dy * sinA;
        const ry2 = -dx * sinA + dy * cosA;
        const dist = Math.sqrt(
          rx2 * rx2 / (rx * rx) + ry2 * ry2 / (ry * ry)
        );
        if (dist < 1) {
          const falloff = 1 - dist;
          const idx = y * width + x;
          result[idx] = Math.max(result[idx], falloff * falloff * brightness);
        }
      }
    }
  }
  return result;
}
function applyLensDirt(bloom, dirt, width, height, intensity) {
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const dirtIdx = y * width + x;
      const bloomIdx = dirtIdx * 4;
      const dirtValue = dirt[dirtIdx] * intensity;
      bloom[bloomIdx] *= 1 + dirtValue;
      bloom[bloomIdx + 1] *= 1 + dirtValue;
      bloom[bloomIdx + 2] *= 1 + dirtValue;
    }
  }
}
function blendScreen(base, blend) {
  return 1 - (1 - base) * (1 - blend);
}
function blendOverlay(base, blend) {
  return base < 0.5 ? 2 * base * blend : 1 - 2 * (1 - base) * (1 - blend);
}
function blendSoftLight(base, blend) {
  if (blend <= 0.5) {
    return base - (1 - 2 * blend) * base * (1 - base);
  } else {
    const d = base <= 0.25 ? ((16 * base - 12) * base + 4) * base : Math.sqrt(base);
    return base + (2 * blend - 1) * (d - base);
  }
}
function blendBloom(original, bloom, intensity, mode, tonemap) {
  const { width, height, data } = original;
  const result = new ImageData(width, height);
  const dst = result.data;
  for (let i = 0; i < data.length; i += 4) {
    const origR = (data[i] / 255) ** 2.2;
    const origG = (data[i + 1] / 255) ** 2.2;
    const origB = (data[i + 2] / 255) ** 2.2;
    const bloomR = bloom[i] * intensity;
    const bloomG = bloom[i + 1] * intensity;
    const bloomB = bloom[i + 2] * intensity;
    let finalR, finalG, finalB;
    switch (mode) {
      case "screen":
        finalR = blendScreen(origR, bloomR);
        finalG = blendScreen(origG, bloomG);
        finalB = blendScreen(origB, bloomB);
        break;
      case "overlay":
        finalR = blendOverlay(origR, bloomR);
        finalG = blendOverlay(origG, bloomG);
        finalB = blendOverlay(origB, bloomB);
        break;
      case "soft_light":
        finalR = blendSoftLight(origR, bloomR);
        finalG = blendSoftLight(origG, bloomG);
        finalB = blendSoftLight(origB, bloomB);
        break;
      default:
        finalR = origR + bloomR;
        finalG = origG + bloomG;
        finalB = origB + bloomB;
        break;
    }
    [finalR, finalG, finalB] = applyTonemap(finalR, finalG, finalB, tonemap);
    dst[i] = Math.round(Math.max(0, Math.min(1, finalR)) ** (1 / 2.2) * 255);
    dst[i + 1] = Math.round(
      Math.max(0, Math.min(1, finalG)) ** (1 / 2.2) * 255
    );
    dst[i + 2] = Math.round(
      Math.max(0, Math.min(1, finalB)) ** (1 / 2.2) * 255
    );
    dst[i + 3] = data[i + 3];
  }
  return result;
}
let cachedLensDirt = null;
let cachedLensDirtWidth = 0;
let cachedLensDirtHeight = 0;
let cachedLensDirtScale = 0;
function cinematicBloomRenderer(input, params) {
  const intensity = Math.max(0, Math.min(10, params.intensity ?? 1));
  const threshold = Math.max(0, Math.min(1, params.threshold ?? 0.8));
  const radius = Math.max(0, Math.min(200, params.radius ?? 50));
  const falloffMode = params.falloff_mode ?? "inverse_square";
  const falloffExponent = Math.max(
    1,
    Math.min(4, params.falloff_exponent ?? 2)
  );
  const radiusR = Math.max(0, Math.min(2, params.radius_r ?? 1)) * radius;
  const radiusG = Math.max(0, Math.min(2, params.radius_g ?? 1)) * radius;
  const radiusB = Math.max(0, Math.min(2, params.radius_b ?? 1)) * radius;
  const tonemap = params.tonemap ?? "aces";
  const exposure = Math.max(-5, Math.min(5, params.exposure ?? 0));
  const chromaticAberration = Math.max(
    0,
    Math.min(20, params.chromatic_aberration ?? 0)
  );
  const lensDirtEnabled = params.lens_dirt_enabled ?? false;
  const lensDirtIntensity = Math.max(
    0,
    Math.min(1, params.lens_dirt_intensity ?? 0.5)
  );
  const lensDirtScale = Math.max(0.5, Math.min(2, params.lens_dirt_scale ?? 1));
  const blendMode = params.blend_mode ?? "add";
  if (intensity <= 0 || radius <= 0) {
    return input;
  }
  const { width, height } = input.canvas;
  const sourceCanvas = params._sourceCanvas;
  const sourceCtx = sourceCanvas?.getContext("2d");
  let originalData = sourceCtx ? sourceCtx.getImageData(0, 0, width, height) : input.ctx.getImageData(0, 0, width, height);
  if (chromaticAberration > 0) {
    originalData = applyChromaticAberration(originalData, chromaticAberration);
  }
  const brightAreas = extractBrightAreas(originalData, threshold, exposure);
  const blurred = applyBloomBlur(
    brightAreas,
    width,
    height,
    radiusR,
    radiusG,
    radiusB,
    falloffMode,
    falloffExponent
  );
  if (lensDirtEnabled) {
    if (!cachedLensDirt || cachedLensDirtWidth !== width || cachedLensDirtHeight !== height || cachedLensDirtScale !== lensDirtScale) {
      cachedLensDirt = generateLensDirt(width, height, lensDirtScale);
      cachedLensDirtWidth = width;
      cachedLensDirtHeight = height;
      cachedLensDirtScale = lensDirtScale;
    }
    applyLensDirt(blurred, cachedLensDirt, width, height, lensDirtIntensity);
  }
  const result = blendBloom(
    originalData,
    blurred,
    intensity,
    blendMode,
    tonemap
  );
  const output = createMatchingCanvas(input.canvas);
  output.ctx.putImageData(result, 0, 0);
  return output;
}
function glowRenderer$1(input, params) {
  const threshold = (params.glow_threshold ?? 50) / 100;
  const radius = params.glow_radius ?? 25;
  const intensity = (params.glow_intensity ?? 100) / 100;
  if (intensity <= 0 || radius <= 0) {
    return input;
  }
  return cinematicBloomRenderer(input, {
    intensity,
    threshold,
    radius,
    falloff_mode: "gaussian",
    falloff_exponent: 2,
    radius_r: 1,
    radius_g: 1,
    radius_b: 1,
    tonemap: "none",
    exposure: 0,
    chromatic_aberration: 0,
    lens_dirt_enabled: false,
    lens_dirt_intensity: 0,
    lens_dirt_scale: 1,
    blend_mode: "add",
    _sourceCanvas: params._sourceCanvas
  });
}
function registerCinematicBloomEffects() {
  registerEffectRenderer("cinematic-bloom", cinematicBloomRenderer);
  registerEffectRenderer("glow", glowRenderer$1);
}

function liftGammaGainRenderer(input, params) {
  const liftRRaw = params.lift_red ?? 0;
  const liftGRaw = params.lift_green ?? 0;
  const liftBRaw = params.lift_blue ?? 0;
  const liftR = Number.isFinite(liftRRaw) ? Math.max(-1, Math.min(1, liftRRaw)) : 0;
  const liftG = Number.isFinite(liftGRaw) ? Math.max(-1, Math.min(1, liftGRaw)) : 0;
  const liftB = Number.isFinite(liftBRaw) ? Math.max(-1, Math.min(1, liftBRaw)) : 0;
  const gammaRRaw = params.gamma_red ?? 1;
  const gammaGRaw = params.gamma_green ?? 1;
  const gammaBRaw = params.gamma_blue ?? 1;
  const gammaR = Number.isFinite(gammaRRaw) ? Math.max(0.1, Math.min(4, gammaRRaw)) : 1;
  const gammaG = Number.isFinite(gammaGRaw) ? Math.max(0.1, Math.min(4, gammaGRaw)) : 1;
  const gammaB = Number.isFinite(gammaBRaw) ? Math.max(0.1, Math.min(4, gammaBRaw)) : 1;
  const gainRRaw = params.gain_red ?? 1;
  const gainGRaw = params.gain_green ?? 1;
  const gainBRaw = params.gain_blue ?? 1;
  const gainR = Number.isFinite(gainRRaw) ? Math.max(0, Math.min(4, gainRRaw)) : 1;
  const gainG = Number.isFinite(gainGRaw) ? Math.max(0, Math.min(4, gainGRaw)) : 1;
  const gainB = Number.isFinite(gainBRaw) ? Math.max(0, Math.min(4, gainBRaw)) : 1;
  if (liftR === 0 && liftG === 0 && liftB === 0 && gammaR === 1 && gammaG === 1 && gammaB === 1 && gainR === 1 && gainG === 1 && gainB === 1) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  const lutR = new Uint8Array(256);
  const lutG = new Uint8Array(256);
  const lutB = new Uint8Array(256);
  const sRGBToLinear = (v) => {
    const normalized = v / 255;
    return normalized <= 0.04045 ? normalized / 12.92 : ((normalized + 0.055) / 1.055) ** 2.4;
  };
  const linearToSRGB = (v) => {
    const clamped = Math.max(0, Math.min(1, v));
    return clamped <= 31308e-7 ? Math.round(clamped * 12.92 * 255) : Math.round((1.055 * clamped ** (1 / 2.4) - 0.055) * 255);
  };
  for (let i = 0; i < 256; i++) {
    const linearR = sRGBToLinear(i);
    const linearG = sRGBToLinear(i);
    const linearB = sRGBToLinear(i);
    const gradedR = Math.max(0, linearR * gainR + liftR) ** (1 / Math.max(0.1, gammaR));
    const gradedG = Math.max(0, linearG * gainG + liftG) ** (1 / Math.max(0.1, gammaG));
    const gradedB = Math.max(0, linearB * gainB + liftB) ** (1 / Math.max(0.1, gammaB));
    lutR[i] = linearToSRGB(gradedR);
    lutG[i] = linearToSRGB(gradedG);
    lutB[i] = linearToSRGB(gradedB);
  }
  for (let i = 0; i < data.length; i += 4) {
    data[i] = lutR[data[i]];
    data[i + 1] = lutG[data[i + 1]];
    data[i + 2] = lutB[data[i + 2]];
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function hslSecondaryRenderer(input, params) {
  const safeNum = (val, def, min, max) => {
    const num = typeof val === "number" && Number.isFinite(val) ? val : def;
    if (min !== void 0 && max !== void 0)
      return Math.max(min, Math.min(max, num));
    return num;
  };
  const hueCenter = safeNum(params.hue_center, 0, 0, 360);
  const hueWidth = safeNum(params.hue_width, 30, 0, 180);
  const hueFalloff = safeNum(params.hue_falloff, 10, 0, 90);
  const satMin = safeNum(params.sat_min, 0, 0, 100) / 100;
  const satMax = safeNum(params.sat_max, 100, 0, 100) / 100;
  const satFalloff = safeNum(params.sat_falloff, 10, 0, 50) / 100;
  const lumMin = safeNum(params.lum_min, 0, 0, 100) / 100;
  const lumMax = safeNum(params.lum_max, 100, 0, 100) / 100;
  const lumFalloff = safeNum(params.lum_falloff, 10, 0, 50) / 100;
  const hueShift = safeNum(params.hue_shift, 0, -180, 180);
  const satAdjust = safeNum(params.sat_adjust, 0, -100, 100) / 100;
  const lumAdjust = safeNum(params.lum_adjust, 0, -100, 100) / 100;
  const showMask = params.show_mask ?? false;
  if (!showMask && hueShift === 0 && satAdjust === 0 && lumAdjust === 0) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  const rgbToHsl = (r, g, b) => {
    const rn = r / 255;
    const gn = g / 255;
    const bn = b / 255;
    const max = Math.max(rn, gn, bn);
    const min = Math.min(rn, gn, bn);
    const l = (max + min) / 2;
    if (max === min) return [0, 0, l];
    const d = max - min;
    const s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
    let h;
    switch (max) {
      case rn:
        h = ((gn - bn) / d + (gn < bn ? 6 : 0)) / 6;
        break;
      case gn:
        h = ((bn - rn) / d + 2) / 6;
        break;
      default:
        h = ((rn - gn) / d + 4) / 6;
        break;
    }
    return [h * 360, s, l];
  };
  const hslToRgb = (h, s, l) => {
    h = (h % 360 + 360) % 360 / 360;
    if (s === 0) {
      const v = Math.round(l * 255);
      return [v, v, v];
    }
    const hue2rgb = (p2, q2, t) => {
      if (t < 0) t += 1;
      if (t > 1) t -= 1;
      if (t < 1 / 6) return p2 + (q2 - p2) * 6 * t;
      if (t < 1 / 2) return q2;
      if (t < 2 / 3) return p2 + (q2 - p2) * (2 / 3 - t) * 6;
      return p2;
    };
    const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
    const p = 2 * l - q;
    return [
      Math.round(hue2rgb(p, q, h + 1 / 3) * 255),
      Math.round(hue2rgb(p, q, h) * 255),
      Math.round(hue2rgb(p, q, h - 1 / 3) * 255)
    ];
  };
  const softRange = (value, min, max, falloff) => {
    if (value < min - falloff || value > max + falloff) return 0;
    if (value >= min && value <= max) return 1;
    if (value < min) {
      return falloff > 0 ? (value - (min - falloff)) / falloff : 0;
    } else {
      return falloff > 0 ? 1 - (value - max) / falloff : 0;
    }
  };
  const hueMatch = (hue, center, width, falloff) => {
    let diff = Math.abs(hue - center);
    if (diff > 180) diff = 360 - diff;
    const halfWidth = width / 2;
    if (diff <= halfWidth) return 1;
    if (diff > halfWidth + falloff) return 0;
    return 1 - (diff - halfWidth) / falloff;
  };
  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    const [h, s, l] = rgbToHsl(r, g, b);
    const hMatch = hueMatch(h, hueCenter, hueWidth, hueFalloff);
    const sMatch = softRange(s, satMin, satMax, satFalloff);
    const lMatch = softRange(l, lumMin, lumMax, lumFalloff);
    const qualification = hMatch * sMatch * lMatch;
    if (showMask) {
      const maskValue = Math.round(qualification * 255);
      data[i] = maskValue;
      data[i + 1] = maskValue;
      data[i + 2] = maskValue;
    } else if (qualification > 0) {
      const newH = h + hueShift * qualification;
      const newS = Math.max(0, Math.min(1, s + satAdjust * qualification));
      const newL = Math.max(0, Math.min(1, l + lumAdjust * qualification));
      const [newR, newG, newB] = hslToRgb(newH, newS, newL);
      data[i] = Math.round(r + (newR - r) * qualification);
      data[i + 1] = Math.round(g + (newG - g) * qualification);
      data[i + 2] = Math.round(b + (newB - b) * qualification);
    }
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function hueVsCurvesRenderer(input, params) {
  const hueVsHue = params.hue_vs_hue ?? [];
  const hueVsSat = params.hue_vs_sat ?? [];
  const hueVsLum = params.hue_vs_lum ?? [];
  const lumVsSat = params.lum_vs_sat ?? [];
  const satVsSat = params.sat_vs_sat ?? [];
  if (hueVsHue.length === 0 && hueVsSat.length === 0 && hueVsLum.length === 0 && lumVsSat.length === 0 && satVsSat.length === 0) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  const buildCurveLUT = (points, inputRange, outputRange, isDelta = true) => {
    const lut = new Float32Array(Math.ceil(inputRange) + 1);
    if (points.length === 0) {
      for (let i = 0; i <= inputRange; i++) {
        lut[i] = isDelta ? 0 : i;
      }
      return lut;
    }
    const sorted = [...points].sort((a, b) => a.x - b.x);
    for (let i = 0; i <= inputRange; i++) {
      const x = i;
      let p0 = sorted[0];
      let p1 = sorted[sorted.length - 1];
      for (let j = 0; j < sorted.length - 1; j++) {
        if (x >= sorted[j].x && x <= sorted[j + 1].x) {
          p0 = sorted[j];
          p1 = sorted[j + 1];
          break;
        }
      }
      if (p0.x === p1.x) {
        lut[i] = p0.y;
      } else {
        const t = (x - p0.x) / (p1.x - p0.x);
        lut[i] = p0.y + (p1.y - p0.y) * t;
      }
      if (isDelta) {
        lut[i] = Math.max(-outputRange, Math.min(outputRange, lut[i]));
      } else {
        lut[i] = Math.max(0, Math.min(outputRange, lut[i]));
      }
    }
    return lut;
  };
  const hueVsHueLUT = buildCurveLUT(hueVsHue, 360, 180, true);
  const hueVsSatLUT = buildCurveLUT(hueVsSat, 360, 100, true);
  const hueVsLumLUT = buildCurveLUT(hueVsLum, 360, 100, true);
  const lumVsSatLUT = buildCurveLUT(lumVsSat, 100, 100, true);
  const satVsSatLUT = buildCurveLUT(satVsSat, 100, 100, false);
  const rgbToHsl = (r, g, b) => {
    const rn = r / 255, gn = g / 255, bn = b / 255;
    const max = Math.max(rn, gn, bn), min = Math.min(rn, gn, bn);
    const l = (max + min) / 2;
    if (max === min) return [0, 0, l];
    const d = max - min;
    const s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
    let h;
    switch (max) {
      case rn:
        h = ((gn - bn) / d + (gn < bn ? 6 : 0)) / 6;
        break;
      case gn:
        h = ((bn - rn) / d + 2) / 6;
        break;
      default:
        h = ((rn - gn) / d + 4) / 6;
        break;
    }
    return [h * 360, s * 100, l * 100];
  };
  const hslToRgb = (h, s, l) => {
    h = (h % 360 + 360) % 360 / 360;
    s = s / 100;
    l = l / 100;
    if (s === 0) {
      const v = Math.round(l * 255);
      return [v, v, v];
    }
    const hue2rgb = (p2, q2, t) => {
      if (t < 0) t += 1;
      if (t > 1) t -= 1;
      if (t < 1 / 6) return p2 + (q2 - p2) * 6 * t;
      if (t < 1 / 2) return q2;
      if (t < 2 / 3) return p2 + (q2 - p2) * (2 / 3 - t) * 6;
      return p2;
    };
    const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
    const p = 2 * l - q;
    return [
      Math.round(hue2rgb(p, q, h + 1 / 3) * 255),
      Math.round(hue2rgb(p, q, h) * 255),
      Math.round(hue2rgb(p, q, h - 1 / 3) * 255)
    ];
  };
  for (let i = 0; i < data.length; i += 4) {
    let [h, s, l] = rgbToHsl(data[i], data[i + 1], data[i + 2]);
    const hueIdx = Math.round(h) % 360;
    const lumIdx = Math.round(l);
    if (hueVsHue.length > 0) {
      h = h + hueVsHueLUT[hueIdx];
    }
    if (hueVsSat.length > 0) {
      s = s + hueVsSatLUT[hueIdx];
    }
    if (hueVsLum.length > 0) {
      l = l + hueVsLumLUT[hueIdx];
    }
    if (lumVsSat.length > 0) {
      s = s + lumVsSatLUT[lumIdx];
    }
    if (satVsSat.length > 0) {
      s = satVsSatLUT[Math.round(Math.max(0, Math.min(100, s)))];
    }
    h = (h % 360 + 360) % 360;
    s = Math.max(0, Math.min(100, s));
    l = Math.max(0, Math.min(100, l));
    const [r, g, b] = hslToRgb(h, s, l);
    data[i] = r;
    data[i + 1] = g;
    data[i + 2] = b;
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function colorMatchRenderer(input, params) {
  const refHistR = params.reference_histogram_r;
  const refHistG = params.reference_histogram_g;
  const refHistB = params.reference_histogram_b;
  const refPixelsRaw = params.reference_pixels;
  const refPixels = typeof refPixelsRaw === "number" && Number.isFinite(refPixelsRaw) && refPixelsRaw > 0 ? refPixelsRaw : 0;
  const strengthRaw = (params.strength ?? 100) / 100;
  const strength = Number.isFinite(strengthRaw) ? Math.max(0, Math.min(1, strengthRaw)) : 0;
  const matchLuminance = params.match_luminance ?? true;
  const matchColor = params.match_color ?? true;
  if (!refHistR || !refHistG || !refHistB || refPixels <= 0 || strength === 0) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  const pixelCount = input.canvas.width * input.canvas.height;
  if (pixelCount <= 0) {
    return input;
  }
  const srcHistR = new Uint32Array(256);
  const srcHistG = new Uint32Array(256);
  const srcHistB = new Uint32Array(256);
  for (let i = 0; i < data.length; i += 4) {
    srcHistR[data[i]]++;
    srcHistG[data[i + 1]]++;
    srcHistB[data[i + 2]]++;
  }
  const buildMatchingLUT = (srcHist, refHist) => {
    const lut = new Uint8Array(256);
    const srcCDF = new Float32Array(256);
    const refCDF = new Float32Array(256);
    srcCDF[0] = srcHist[0] / pixelCount;
    refCDF[0] = refHist[0] / refPixels;
    for (let i = 1; i < 256; i++) {
      srcCDF[i] = srcCDF[i - 1] + srcHist[i] / pixelCount;
      refCDF[i] = refCDF[i - 1] + refHist[i] / refPixels;
    }
    for (let i = 0; i < 256; i++) {
      const srcVal = srcCDF[i];
      let bestMatch = 0;
      let bestDiff = Math.abs(refCDF[0] - srcVal);
      for (let j = 1; j < 256; j++) {
        const diff = Math.abs(refCDF[j] - srcVal);
        if (diff < bestDiff) {
          bestDiff = diff;
          bestMatch = j;
        }
      }
      lut[i] = bestMatch;
    }
    return lut;
  };
  let lutR = null;
  let lutG = null;
  let lutB = null;
  if (matchColor) {
    lutR = buildMatchingLUT(srcHistR, refHistR);
    lutG = buildMatchingLUT(srcHistG, refHistG);
    lutB = buildMatchingLUT(srcHistB, refHistB);
  }
  let lumLUT = null;
  if (matchLuminance && !matchColor) {
    const srcLumHist = new Uint32Array(256);
    const refLumHist = new Uint32Array(256);
    for (let i = 0; i < data.length; i += 4) {
      const lum = Math.round(
        data[i] * 0.2126 + data[i + 1] * 0.7152 + data[i + 2] * 0.0722
      );
      srcLumHist[Math.min(255, lum)]++;
    }
    for (let i = 0; i < 256; i++) {
      const avgCount = (refHistR[i] + refHistG[i] + refHistB[i]) / 3;
      refLumHist[i] = Math.round(avgCount);
    }
    lumLUT = buildMatchingLUT(srcLumHist, refLumHist);
  }
  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    let newR = r, newG = g, newB = b;
    if (matchColor && lutR && lutG && lutB) {
      newR = lutR[r];
      newG = lutG[g];
      newB = lutB[b];
    } else if (matchLuminance && lumLUT) {
      const lum = r * 0.2126 + g * 0.7152 + b * 0.0722;
      const newLum = lumLUT[Math.round(lum)];
      const lumRatio = lum > 0 ? newLum / lum : 1;
      newR = Math.min(255, Math.round(r * lumRatio));
      newG = Math.min(255, Math.round(g * lumRatio));
      newB = Math.min(255, Math.round(b * lumRatio));
    }
    data[i] = Math.round(r + (newR - r) * strength);
    data[i + 1] = Math.round(g + (newG - g) * strength);
    data[i + 2] = Math.round(b + (newB - b) * strength);
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function registerColorGradingEffects() {
  registerEffectRenderer("lift-gamma-gain", liftGammaGainRenderer);
  registerEffectRenderer("hsl-secondary", hslSecondaryRenderer);
  registerEffectRenderer("hue-vs-curves", hueVsCurvesRenderer);
  registerEffectRenderer("color-match", colorMatchRenderer);
}

function brightnessContrastRenderer(input, params) {
  const rawBrightness = params.brightness ?? 0;
  const brightness = Number.isFinite(rawBrightness) ? rawBrightness / 100 : 0;
  const rawContrast = params.contrast ?? 0;
  const contrast = Number.isFinite(rawContrast) ? rawContrast / 100 : 0;
  const useLegacy = params.use_legacy ?? false;
  if (brightness === 0 && contrast === 0) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  const contrastFactor = useLegacy ? 1 + contrast : 259 * (contrast * 255 + 255) / (255 * (259 - contrast * 255));
  for (let i = 0; i < data.length; i += 4) {
    let r = data[i];
    let g = data[i + 1];
    let b = data[i + 2];
    r += brightness * 255;
    g += brightness * 255;
    b += brightness * 255;
    r = contrastFactor * (r - 128) + 128;
    g = contrastFactor * (g - 128) + 128;
    b = contrastFactor * (b - 128) + 128;
    data[i] = Math.max(0, Math.min(255, r));
    data[i + 1] = Math.max(0, Math.min(255, g));
    data[i + 2] = Math.max(0, Math.min(255, b));
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function rgbToHsl(r, g, b) {
  r /= 255;
  g /= 255;
  b /= 255;
  const max = Math.max(r, g, b);
  const min = Math.min(r, g, b);
  const l = (max + min) / 2;
  let h = 0;
  let s = 0;
  if (max !== min) {
    const d = max - min;
    s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
    switch (max) {
      case r:
        h = ((g - b) / d + (g < b ? 6 : 0)) / 6;
        break;
      case g:
        h = ((b - r) / d + 2) / 6;
        break;
      case b:
        h = ((r - g) / d + 4) / 6;
        break;
    }
  }
  return [h, s, l];
}
function hslToRgb(h, s, l) {
  let r, g, b;
  if (s === 0) {
    r = g = b = l;
  } else {
    const hue2rgb = (p2, q2, t) => {
      if (t < 0) t += 1;
      if (t > 1) t -= 1;
      if (t < 1 / 6) return p2 + (q2 - p2) * 6 * t;
      if (t < 1 / 2) return q2;
      if (t < 2 / 3) return p2 + (q2 - p2) * (2 / 3 - t) * 6;
      return p2;
    };
    const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
    const p = 2 * l - q;
    r = hue2rgb(p, q, h + 1 / 3);
    g = hue2rgb(p, q, h);
    b = hue2rgb(p, q, h - 1 / 3);
  }
  return [Math.round(r * 255), Math.round(g * 255), Math.round(b * 255)];
}
function hueSaturationRenderer(input, params) {
  const rawHue = params.master_hue ?? 0;
  const hueShift = Number.isFinite(rawHue) ? rawHue / 360 : 0;
  const rawSat = params.master_saturation ?? 0;
  const saturationShift = Number.isFinite(rawSat) ? rawSat / 100 : 0;
  const rawLight = params.master_lightness ?? 0;
  const lightnessShift = Number.isFinite(rawLight) ? rawLight / 100 : 0;
  const colorize = params.colorize ?? false;
  if (hueShift === 0 && saturationShift === 0 && lightnessShift === 0 && !colorize) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    let [h, s, l] = rgbToHsl(r, g, b);
    if (colorize) {
      h = hueShift;
      s = Math.abs(saturationShift) + 0.25;
    } else {
      h = (h + hueShift) % 1;
      if (h < 0) h += 1;
      s = s + s * saturationShift;
    }
    l = l + l * lightnessShift;
    s = Math.max(0, Math.min(1, s));
    l = Math.max(0, Math.min(1, l));
    const [newR, newG, newB] = hslToRgb(h, s, l);
    data[i] = newR;
    data[i + 1] = newG;
    data[i + 2] = newB;
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function levelsRenderer(input, params) {
  const rawInputBlack = params.input_black ?? 0;
  const inputBlack = Number.isFinite(rawInputBlack) ? rawInputBlack : 0;
  const rawInputWhite = params.input_white ?? 255;
  const inputWhite = Number.isFinite(rawInputWhite) ? rawInputWhite : 255;
  const rawGamma = params.gamma ?? 1;
  const gamma = Number.isFinite(rawGamma) && rawGamma > 0 ? rawGamma : 1;
  const rawOutputBlack = params.output_black ?? 0;
  const outputBlack = Number.isFinite(rawOutputBlack) ? rawOutputBlack : 0;
  const rawOutputWhite = params.output_white ?? 255;
  const outputWhite = Number.isFinite(rawOutputWhite) ? rawOutputWhite : 255;
  if (inputBlack === 0 && inputWhite === 255 && gamma === 1 && outputBlack === 0 && outputWhite === 255) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  const lut = new Uint8Array(256);
  const inputRange = inputWhite - inputBlack;
  const outputRange = outputWhite - outputBlack;
  for (let i = 0; i < 256; i++) {
    let value = (i - inputBlack) / inputRange;
    value = Math.max(0, Math.min(1, value));
    value = value ** (1 / gamma);
    value = outputBlack + value * outputRange;
    value = Math.max(0, Math.min(255, value));
    lut[i] = Math.round(value);
  }
  for (let i = 0; i < data.length; i += 4) {
    data[i] = lut[data[i]];
    data[i + 1] = lut[data[i + 1]];
    data[i + 2] = lut[data[i + 2]];
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function tintRenderer(input, params) {
  const blackColor = params.map_black_to ?? { r: 0, g: 0, b: 0 };
  const whiteColor = params.map_white_to ?? { r: 255, g: 255, b: 255 };
  const rawAmount = params.amount_to_tint ?? 100;
  const amount = Number.isFinite(rawAmount) ? rawAmount / 100 : 1;
  if (amount === 0) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    const lum = (r * 0.299 + g * 0.587 + b * 0.114) / 255;
    const tintR = blackColor.r + (whiteColor.r - blackColor.r) * lum;
    const tintG = blackColor.g + (whiteColor.g - blackColor.g) * lum;
    const tintB = blackColor.b + (whiteColor.b - blackColor.b) * lum;
    data[i] = Math.round(r + (tintR - r) * amount);
    data[i + 1] = Math.round(g + (tintG - g) * amount);
    data[i + 2] = Math.round(b + (tintB - b) * amount);
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function cubicBezier(p0, p1, p2, p3, t) {
  const t2 = t * t;
  const t3 = t2 * t;
  const mt = 1 - t;
  const mt2 = mt * mt;
  const mt3 = mt2 * mt;
  return mt3 * p0 + 3 * mt2 * t * p1 + 3 * mt * t2 * p2 + t3 * p3;
}
function buildCurveLUT(points) {
  const lut = new Uint8Array(256);
  if (!points || points.length === 0) {
    for (let i = 0; i < 256; i++) {
      lut[i] = i;
    }
    return lut;
  }
  if (points.length === 1) {
    for (let i = 0; i < 256; i++) {
      lut[i] = Math.max(0, Math.min(255, Math.round(points[0].y)));
    }
    return lut;
  }
  const sortedPoints = [...points].sort((a, b) => a.x - b.x);
  if (sortedPoints[0].x > 0) {
    sortedPoints.unshift({ x: 0, y: sortedPoints[0].y });
  }
  if (sortedPoints[sortedPoints.length - 1].x < 255) {
    sortedPoints.push({ x: 255, y: sortedPoints[sortedPoints.length - 1].y });
  }
  for (let i = 0; i < 256; i++) {
    let segmentIndex = 0;
    for (let j = 0; j < sortedPoints.length - 1; j++) {
      if (i >= sortedPoints[j].x && i <= sortedPoints[j + 1].x) {
        segmentIndex = j;
        break;
      }
    }
    const p0 = sortedPoints[segmentIndex];
    const p1 = sortedPoints[segmentIndex + 1];
    const t = (i - p0.x) / (p1.x - p0.x || 1);
    let tangent0 = 0;
    let tangent1 = 0;
    if (segmentIndex > 0) {
      const pPrev = sortedPoints[segmentIndex - 1];
      tangent0 = (p1.y - pPrev.y) / (p1.x - pPrev.x || 1) * (p1.x - p0.x);
    }
    if (segmentIndex < sortedPoints.length - 2) {
      const pNext = sortedPoints[segmentIndex + 2];
      tangent1 = (pNext.y - p0.y) / (pNext.x - p0.x || 1) * (p1.x - p0.x);
    }
    const cp1y = p0.y + tangent0 / 3;
    const cp2y = p1.y - tangent1 / 3;
    const value = cubicBezier(p0.y, cp1y, cp2y, p1.y, t);
    lut[i] = Math.max(0, Math.min(255, Math.round(value)));
  }
  return lut;
}
function curvesRenderer(input, params) {
  const masterCurve = params.master_curve;
  const redCurve = params.red_curve;
  const greenCurve = params.green_curve;
  const blueCurve = params.blue_curve;
  const alphaCurve = params.alpha_curve;
  const rawBlend = params.blend_with_original ?? 100;
  const blend = Number.isFinite(rawBlend) ? rawBlend / 100 : 1;
  const hasCurves = masterCurve || redCurve || greenCurve || blueCurve || alphaCurve;
  if (!hasCurves || blend === 0) {
    return input;
  }
  const masterLUT = buildCurveLUT(
    masterCurve ?? [
      { x: 0, y: 0 },
      { x: 255, y: 255 }
    ]
  );
  const redLUT = buildCurveLUT(
    redCurve ?? [
      { x: 0, y: 0 },
      { x: 255, y: 255 }
    ]
  );
  const greenLUT = buildCurveLUT(
    greenCurve ?? [
      { x: 0, y: 0 },
      { x: 255, y: 255 }
    ]
  );
  const blueLUT = buildCurveLUT(
    blueCurve ?? [
      { x: 0, y: 0 },
      { x: 255, y: 255 }
    ]
  );
  const alphaLUT = alphaCurve ? buildCurveLUT(alphaCurve) : null;
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  for (let i = 0; i < data.length; i += 4) {
    const origR = data[i];
    const origG = data[i + 1];
    const origB = data[i + 2];
    const origA = data[i + 3];
    let r = masterLUT[origR];
    let g = masterLUT[origG];
    let b = masterLUT[origB];
    r = redLUT[r];
    g = greenLUT[g];
    b = blueLUT[b];
    const a = alphaLUT ? alphaLUT[origA] : origA;
    if (blend < 1) {
      r = Math.round(origR + (r - origR) * blend);
      g = Math.round(origG + (g - origG) * blend);
      b = Math.round(origB + (b - origB) * blend);
    }
    data[i] = r;
    data[i + 1] = g;
    data[i + 2] = b;
    data[i + 3] = a;
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function glowRenderer(input, params, frame) {
  const rawThreshold = params.glow_threshold ?? 128;
  const threshold = Number.isFinite(rawThreshold) ? rawThreshold : 128;
  const rawRadius = params.glow_radius ?? 20;
  const radius = Number.isFinite(rawRadius) ? Math.max(0, rawRadius) : 20;
  const rawIntensity = params.glow_intensity ?? 100;
  const validIntensity = Number.isFinite(rawIntensity) ? rawIntensity : 100;
  const intensity = validIntensity <= 10 ? validIntensity : validIntensity / 100;
  const composite = params.composite_original ?? "on-top";
  const operation = params.glow_operation ?? (composite === "on-top" ? "add" : "lighten");
  const glowColors = params.glow_colors ?? "original";
  const colorA = params.color_a ?? { r: 255, g: 255, b: 255};
  const colorB = params.color_b ?? { r: 255, g: 128, b: 0};
  const colorLooping = params.color_looping ?? "none";
  const rawLoopSpeed = params.color_looping_speed ?? 1;
  const colorLoopingSpeed = Number.isFinite(rawLoopSpeed) ? rawLoopSpeed : 1;
  const glowDimensions = params.glow_dimensions ?? "both";
  if (intensity === 0 || radius === 0) {
    return input;
  }
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  let colorBlend = 0;
  if (colorLooping !== "none" && frame !== void 0) {
    const fps = Number.isFinite(params._fps) && params._fps > 0 ? params._fps : 16;
    const time = frame / fps;
    const cycle = time * colorLoopingSpeed % 1;
    switch (colorLooping) {
      case "sawtooth_ab":
        colorBlend = cycle;
        break;
      case "sawtooth_ba":
        colorBlend = 1 - cycle;
        break;
      case "triangle":
        colorBlend = cycle < 0.5 ? cycle * 2 : 2 - cycle * 2;
        break;
      default:
        colorBlend = 0;
    }
  }
  const effectiveColor = glowColors === "ab" ? {
    r: colorA.r + (colorB.r - colorA.r) * colorBlend,
    g: colorA.g + (colorB.g - colorA.g) * colorBlend,
    b: colorA.b + (colorB.b - colorA.b) * colorBlend} : null;
  const sourceCanvas = params._sourceCanvas;
  const thresholdCanvas = document.createElement("canvas");
  thresholdCanvas.width = width;
  thresholdCanvas.height = height;
  const thresholdCtx = thresholdCanvas.getContext("2d");
  const sourceCtx = sourceCanvas?.getContext("2d");
  const inputData = sourceCtx ? sourceCtx.getImageData(0, 0, width, height) : input.ctx.getImageData(0, 0, width, height);
  const thresholdData = thresholdCtx.createImageData(width, height);
  for (let i = 0; i < inputData.data.length; i += 4) {
    const r = inputData.data[i];
    const g = inputData.data[i + 1];
    const b = inputData.data[i + 2];
    const a = inputData.data[i + 3];
    const lum = r * 0.299 + g * 0.587 + b * 0.114;
    if (lum > threshold) {
      const scale = (lum - threshold) / (255 - threshold) * intensity;
      if (effectiveColor) {
        thresholdData.data[i] = Math.min(255, effectiveColor.r * scale);
        thresholdData.data[i + 1] = Math.min(255, effectiveColor.g * scale);
        thresholdData.data[i + 2] = Math.min(255, effectiveColor.b * scale);
      } else {
        thresholdData.data[i] = Math.min(255, r * scale);
        thresholdData.data[i + 1] = Math.min(255, g * scale);
        thresholdData.data[i + 2] = Math.min(255, b * scale);
      }
      thresholdData.data[i + 3] = a;
    } else {
      thresholdData.data[i] = 0;
      thresholdData.data[i + 1] = 0;
      thresholdData.data[i + 2] = 0;
      thresholdData.data[i + 3] = 0;
    }
  }
  thresholdCtx.putImageData(thresholdData, 0, 0);
  const blurCanvas = document.createElement("canvas");
  blurCanvas.width = width;
  blurCanvas.height = height;
  const blurCtx = blurCanvas.getContext("2d");
  if (glowDimensions === "horizontal") {
    const tempCanvas = document.createElement("canvas");
    tempCanvas.width = width;
    tempCanvas.height = 1;
    const tempCtx = tempCanvas.getContext("2d");
    tempCtx.drawImage(thresholdCanvas, 0, 0, width, 1);
    const blurTemp = document.createElement("canvas");
    blurTemp.width = width;
    blurTemp.height = 1;
    const blurTempCtx = blurTemp.getContext("2d");
    blurTempCtx.filter = `blur(${radius}px)`;
    blurTempCtx.drawImage(tempCanvas, 0, 0);
    blurCtx.drawImage(blurTemp, 0, 0, width, height);
    blurCtx.globalCompositeOperation = "multiply";
    blurCtx.filter = `blur(${radius}px)`;
    blurCtx.drawImage(thresholdCanvas, 0, 0);
    blurCtx.globalCompositeOperation = "source-over";
  } else if (glowDimensions === "vertical") {
    const tempCanvas = document.createElement("canvas");
    tempCanvas.width = 1;
    tempCanvas.height = height;
    const tempCtx = tempCanvas.getContext("2d");
    tempCtx.drawImage(thresholdCanvas, 0, 0, 1, height);
    const blurTemp = document.createElement("canvas");
    blurTemp.width = 1;
    blurTemp.height = height;
    const blurTempCtx = blurTemp.getContext("2d");
    blurTempCtx.filter = `blur(${radius}px)`;
    blurTempCtx.drawImage(tempCanvas, 0, 0);
    blurCtx.drawImage(blurTemp, 0, 0, width, height);
    blurCtx.globalCompositeOperation = "multiply";
    blurCtx.filter = `blur(${radius}px)`;
    blurCtx.drawImage(thresholdCanvas, 0, 0);
    blurCtx.globalCompositeOperation = "source-over";
  } else {
    blurCtx.filter = `blur(${radius}px)`;
    blurCtx.drawImage(thresholdCanvas, 0, 0);
  }
  if (composite === "none") {
    output.ctx.drawImage(blurCanvas, 0, 0);
  } else if (composite === "behind") {
    output.ctx.drawImage(blurCanvas, 0, 0);
    output.ctx.globalCompositeOperation = "source-over";
    output.ctx.drawImage(input.canvas, 0, 0);
  } else {
    output.ctx.drawImage(input.canvas, 0, 0);
    switch (operation) {
      case "screen":
        output.ctx.globalCompositeOperation = "screen";
        break;
      case "lighten":
        output.ctx.globalCompositeOperation = "lighten";
        break;
      default:
        output.ctx.globalCompositeOperation = "lighter";
        break;
    }
    output.ctx.drawImage(blurCanvas, 0, 0);
  }
  output.ctx.globalCompositeOperation = "source-over";
  return output;
}
function dropShadowRenderer(input, params) {
  const shadowColor = params.shadow_color ?? { r: 0, g: 0, b: 0};
  const rawOpacity = params.opacity ?? 50;
  const opacity = Number.isFinite(rawOpacity) ? rawOpacity / 100 : 0.5;
  const rawDirection = params.direction ?? 135;
  const direction = Number.isFinite(rawDirection) ? rawDirection * Math.PI / 180 : 135 * Math.PI / 180;
  const rawDistance = params.distance ?? 5;
  const distance = Number.isFinite(rawDistance) ? rawDistance : 5;
  const rawSoftness = params.softness ?? 5;
  const softness = Number.isFinite(rawSoftness) ? rawSoftness : 5;
  const shadowOnly = params.shadow_only ?? false;
  const output = createMatchingCanvas(input.canvas);
  const offsetX = Math.cos(direction) * distance;
  const offsetY = Math.sin(direction) * distance;
  output.ctx.shadowColor = `rgba(${shadowColor.r}, ${shadowColor.g}, ${shadowColor.b}, ${opacity})`;
  output.ctx.shadowBlur = softness;
  output.ctx.shadowOffsetX = offsetX;
  output.ctx.shadowOffsetY = offsetY;
  output.ctx.drawImage(input.canvas, 0, 0);
  output.ctx.shadowColor = "transparent";
  output.ctx.shadowBlur = 0;
  output.ctx.shadowOffsetX = 0;
  output.ctx.shadowOffsetY = 0;
  if (!shadowOnly) {
    output.ctx.drawImage(input.canvas, 0, 0);
  }
  return output;
}
function colorBalanceRenderer(input, params) {
  const safeDiv100 = (val, def) => {
    const raw = val ?? def;
    return Number.isFinite(raw) ? raw / 100 : def / 100;
  };
  const shadowR = safeDiv100(params.shadow_red, 0);
  const shadowG = safeDiv100(params.shadow_green, 0);
  const shadowB = safeDiv100(params.shadow_blue, 0);
  const midtoneR = safeDiv100(params.midtone_red, 0);
  const midtoneG = safeDiv100(params.midtone_green, 0);
  const midtoneB = safeDiv100(params.midtone_blue, 0);
  const highlightR = safeDiv100(params.highlight_red, 0);
  const highlightG = safeDiv100(params.highlight_green, 0);
  const highlightB = safeDiv100(params.highlight_blue, 0);
  const preserveLuminosity = params.preserve_luminosity ?? true;
  if (shadowR === 0 && shadowG === 0 && shadowB === 0 && midtoneR === 0 && midtoneG === 0 && midtoneB === 0 && highlightR === 0 && highlightG === 0 && highlightB === 0) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  for (let i = 0; i < data.length; i += 4) {
    let r = data[i];
    let g = data[i + 1];
    let b = data[i + 2];
    const lum = (r * 0.299 + g * 0.587 + b * 0.114) / 255;
    const shadowWeight = Math.max(0, 1 - lum * 3);
    const highlightWeight = Math.max(0, (lum - 0.67) * 3);
    const midtoneWeight = 1 - shadowWeight - highlightWeight;
    const rAdjust = shadowR * shadowWeight + midtoneR * midtoneWeight + highlightR * highlightWeight;
    const gAdjust = shadowG * shadowWeight + midtoneG * midtoneWeight + highlightG * highlightWeight;
    const bAdjust = shadowB * shadowWeight + midtoneB * midtoneWeight + highlightB * highlightWeight;
    r = r + rAdjust * 255;
    g = g + gAdjust * 255;
    b = b + bAdjust * 255;
    if (preserveLuminosity) {
      const newLum = (r * 0.299 + g * 0.587 + b * 0.114) / 255;
      if (newLum > 1e-3) {
        const lumRatio = lum / newLum;
        r *= lumRatio;
        g *= lumRatio;
        b *= lumRatio;
      }
    }
    data[i] = Math.max(0, Math.min(255, Math.round(r)));
    data[i + 1] = Math.max(0, Math.min(255, Math.round(g)));
    data[i + 2] = Math.max(0, Math.min(255, Math.round(b)));
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function exposureRenderer(input, params) {
  const rawExposure = params.exposure ?? 0;
  const exposure = Number.isFinite(rawExposure) ? rawExposure : 0;
  const rawOffset = params.offset ?? 0;
  const offset = Number.isFinite(rawOffset) ? rawOffset : 0;
  const rawGamma = params.gamma ?? 1;
  const gamma = Number.isFinite(rawGamma) && rawGamma > 0 ? rawGamma : 1;
  if (exposure === 0 && offset === 0 && gamma === 1) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  const lut = new Uint8Array(256);
  const exposureMultiplier = 2 ** exposure;
  const gammaInv = 1 / gamma;
  for (let i = 0; i < 256; i++) {
    let value = i / 255;
    value *= exposureMultiplier;
    value += offset;
    value = Math.max(0, Math.min(1, value));
    value = value ** gammaInv;
    lut[i] = Math.round(value * 255);
  }
  for (let i = 0; i < data.length; i += 4) {
    data[i] = lut[data[i]];
    data[i + 1] = lut[data[i + 1]];
    data[i + 2] = lut[data[i + 2]];
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function vibranceRenderer(input, params) {
  const rawVibrance = params.vibrance ?? 0;
  const vibrance = Number.isFinite(rawVibrance) ? rawVibrance / 100 : 0;
  const rawSaturation = params.saturation ?? 0;
  const saturation = Number.isFinite(rawSaturation) ? rawSaturation / 100 : 0;
  if (vibrance === 0 && saturation === 0) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  for (let i = 0; i < data.length; i += 4) {
    let r = data[i] / 255;
    let g = data[i + 1] / 255;
    let b = data[i + 2] / 255;
    const max = Math.max(r, g, b);
    const min = Math.min(r, g, b);
    const currentSat = max - min;
    const lum = r * 0.299 + g * 0.587 + b * 0.114;
    const skinProtection = 1 - Math.max(
      0,
      Math.min(
        1,
        Math.abs(r - 0.8) * 2 + Math.abs(g - 0.5) * 2 + Math.abs(b - 0.3) * 3
      )
    );
    const vibranceAmount = vibrance * (1 - currentSat) * (1 - skinProtection * 0.5);
    const satAdjust = 1 + saturation + vibranceAmount;
    r = lum + (r - lum) * satAdjust;
    g = lum + (g - lum) * satAdjust;
    b = lum + (b - lum) * satAdjust;
    data[i] = Math.max(0, Math.min(255, Math.round(r * 255)));
    data[i + 1] = Math.max(0, Math.min(255, Math.round(g * 255)));
    data[i + 2] = Math.max(0, Math.min(255, Math.round(b * 255)));
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function invertRenderer(input, params) {
  const rawBlend = params.blend ?? 100;
  const blend = Number.isFinite(rawBlend) ? rawBlend / 100 : 1;
  const channel = params.channel ?? "rgb";
  if (blend === 0) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  for (let i = 0; i < data.length; i += 4) {
    const origR = data[i];
    const origG = data[i + 1];
    const origB = data[i + 2];
    let r = origR;
    let g = origG;
    let b = origB;
    switch (channel) {
      case "rgb":
        r = 255 - r;
        g = 255 - g;
        b = 255 - b;
        break;
      case "red":
        r = 255 - r;
        break;
      case "green":
        g = 255 - g;
        break;
      case "blue":
        b = 255 - b;
        break;
      case "hue":
      case "saturation":
      case "lightness": {
        let [h, s, l] = rgbToHsl(r, g, b);
        if (channel === "hue") h = (h + 0.5) % 1;
        else if (channel === "saturation") s = 1 - s;
        else if (channel === "lightness") l = 1 - l;
        [r, g, b] = hslToRgb(h, s, l);
        break;
      }
    }
    if (blend < 1) {
      r = Math.round(origR + (r - origR) * blend);
      g = Math.round(origG + (g - origG) * blend);
      b = Math.round(origB + (b - origB) * blend);
    }
    data[i] = r;
    data[i + 1] = g;
    data[i + 2] = b;
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function posterizeRenderer(input, params) {
  const rawLevels = params.levels ?? 6;
  const levels = Number.isFinite(rawLevels) ? Math.max(2, Math.min(256, rawLevels)) : 6;
  if (levels === 256) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  const lut = new Uint8Array(256);
  const step = 255 / (levels - 1);
  for (let i = 0; i < 256; i++) {
    const level = Math.round(i / 255 * (levels - 1));
    lut[i] = Math.round(level * step);
  }
  for (let i = 0; i < data.length; i += 4) {
    data[i] = lut[data[i]];
    data[i + 1] = lut[data[i + 1]];
    data[i + 2] = lut[data[i + 2]];
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function thresholdRenderer(input, params) {
  const rawThreshold = params.threshold ?? 128;
  const threshold = Number.isFinite(rawThreshold) ? rawThreshold : 128;
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    const lum = r * 0.299 + g * 0.587 + b * 0.114;
    const value = lum >= threshold ? 255 : 0;
    data[i] = value;
    data[i + 1] = value;
    data[i + 2] = value;
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function vignetteRenderer(input, params) {
  const rawAmount = params.amount ?? 0;
  const amount = Number.isFinite(rawAmount) ? rawAmount / 100 : 0;
  const rawMidpoint = params.midpoint ?? 50;
  const midpoint = Number.isFinite(rawMidpoint) ? rawMidpoint / 100 : 0.5;
  const rawRoundness = params.roundness ?? 0;
  const roundness = Number.isFinite(rawRoundness) ? rawRoundness / 100 : 0;
  const rawFeather = params.feather ?? 50;
  const feather = Number.isFinite(rawFeather) ? rawFeather / 100 : 0.5;
  if (amount === 0) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  const width = input.canvas.width;
  const height = input.canvas.height;
  const centerX = width / 2;
  const centerY = height / 2;
  const aspectX = 1 + (roundness > 0 ? roundness * 0.5 : 0);
  const aspectY = 1 + (roundness < 0 ? -roundness * 0.5 : 0);
  const maxDist = Math.sqrt(centerX * centerX + centerY * centerY);
  const featherMult = Math.max(0.01, feather);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const idx = (y * width + x) * 4;
      const dx = (x - centerX) * aspectX;
      const dy = (y - centerY) * aspectY;
      const dist = Math.sqrt(dx * dx + dy * dy) / maxDist;
      let factor = 0;
      if (dist > midpoint) {
        const t = (dist - midpoint) / (1 - midpoint + 1e-3);
        const smoothT = t * t * (3 - 2 * t);
        factor = smoothT ** (1 / featherMult);
      }
      const multiplier = 1 - factor * amount;
      data[idx] = Math.max(0, Math.min(255, data[idx] * multiplier));
      data[idx + 1] = Math.max(0, Math.min(255, data[idx + 1] * multiplier));
      data[idx + 2] = Math.max(0, Math.min(255, data[idx + 2] * multiplier));
    }
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
const lutCache = /* @__PURE__ */ new Map();
function parseCubeLUT(content) {
  const lines = content.split("\n");
  let title = "Untitled";
  let size = 0;
  let domainMin = [0, 0, 0];
  let domainMax = [1, 1, 1];
  const dataLines = [];
  for (const line of lines) {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith("#")) continue;
    if (trimmed.startsWith("TITLE")) {
      title = trimmed.replace(/^TITLE\s*"?|"?\s*$/g, "");
    } else if (trimmed.startsWith("LUT_3D_SIZE")) {
      size = parseInt(trimmed.split(/\s+/)[1], 10);
    } else if (trimmed.startsWith("DOMAIN_MIN")) {
      const parts = trimmed.split(/\s+/).slice(1).map(Number);
      domainMin = [parts[0] ?? 0, parts[1] ?? 0, parts[2] ?? 0];
    } else if (trimmed.startsWith("DOMAIN_MAX")) {
      const parts = trimmed.split(/\s+/).slice(1).map(Number);
      domainMax = [parts[0] ?? 1, parts[1] ?? 1, parts[2] ?? 1];
    } else if (/^[\d.\-e]+\s+[\d.\-e]+\s+[\d.\-e]+/.test(trimmed)) {
      dataLines.push(trimmed);
    }
  }
  if (size === 0) {
    throw new Error("Invalid .cube file: missing LUT_3D_SIZE");
  }
  const data = new Float32Array(size * size * size * 3);
  for (let i = 0; i < dataLines.length && i < size * size * size; i++) {
    const parts = dataLines[i].split(/\s+/).map(Number);
    data[i * 3] = parts[0] ?? 0;
    data[i * 3 + 1] = parts[1] ?? 0;
    data[i * 3 + 2] = parts[2] ?? 0;
  }
  return { title, size, domainMin, domainMax, data };
}
function sampleLUT3D(lut, r, g, b) {
  const size = lut.size;
  const maxIdx = size - 1;
  const rIdx = r * maxIdx;
  const gIdx = g * maxIdx;
  const bIdx = b * maxIdx;
  const r0 = Math.floor(rIdx);
  const g0 = Math.floor(gIdx);
  const b0 = Math.floor(bIdx);
  const r1 = Math.min(r0 + 1, maxIdx);
  const g1 = Math.min(g0 + 1, maxIdx);
  const b1 = Math.min(b0 + 1, maxIdx);
  const rFrac = rIdx - r0;
  const gFrac = gIdx - g0;
  const bFrac = bIdx - b0;
  const getLUT = (ri, gi, bi, channel) => {
    const idx = ((bi * size + gi) * size + ri) * 3 + channel;
    return lut.data[idx] ?? 0;
  };
  const result = [0, 0, 0];
  for (let c = 0; c < 3; c++) {
    const c000 = getLUT(r0, g0, b0, c);
    const c100 = getLUT(r1, g0, b0, c);
    const c010 = getLUT(r0, g1, b0, c);
    const c110 = getLUT(r1, g1, b0, c);
    const c001 = getLUT(r0, g0, b1, c);
    const c101 = getLUT(r1, g0, b1, c);
    const c011 = getLUT(r0, g1, b1, c);
    const c111 = getLUT(r1, g1, b1, c);
    const c00 = c000 + (c100 - c000) * rFrac;
    const c10 = c010 + (c110 - c010) * rFrac;
    const c01 = c001 + (c101 - c001) * rFrac;
    const c11 = c011 + (c111 - c011) * rFrac;
    const c0 = c00 + (c10 - c00) * gFrac;
    const c1 = c01 + (c11 - c01) * gFrac;
    result[c] = c0 + (c1 - c0) * bFrac;
  }
  return result;
}
function lutRenderer(input, params) {
  const lutData = params.lutData;
  const rawIntensity = params.intensity ?? 100;
  const intensity = Number.isFinite(rawIntensity) ? rawIntensity / 100 : 1;
  if (!lutData || intensity === 0) {
    return input;
  }
  let lut;
  if (lutCache.has(lutData)) {
    lut = lutCache.get(lutData);
  } else {
    try {
      const content = atob(lutData);
      lut = parseCubeLUT(content);
      lutCache.set(lutData, lut);
    } catch (e) {
      console.warn("Failed to parse LUT:", e);
      return input;
    }
  }
  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height
  );
  const data = imageData.data;
  for (let i = 0; i < data.length; i += 4) {
    const r = data[i] / 255;
    const g = data[i + 1] / 255;
    const b = data[i + 2] / 255;
    const [lr, lg, lb] = sampleLUT3D(lut, r, g, b);
    data[i] = Math.max(
      0,
      Math.min(255, (r * (1 - intensity) + lr * intensity) * 255)
    );
    data[i + 1] = Math.max(
      0,
      Math.min(255, (g * (1 - intensity) + lg * intensity) * 255)
    );
    data[i + 2] = Math.max(
      0,
      Math.min(255, (b * (1 - intensity) + lb * intensity) * 255)
    );
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function registerColorEffects() {
  registerEffectRenderer("brightness-contrast", brightnessContrastRenderer);
  registerEffectRenderer("hue-saturation", hueSaturationRenderer);
  registerEffectRenderer("levels", levelsRenderer);
  registerEffectRenderer("tint", tintRenderer);
  registerEffectRenderer("curves", curvesRenderer);
  registerEffectRenderer("glow", glowRenderer);
  registerEffectRenderer("drop-shadow", dropShadowRenderer);
  registerEffectRenderer("color-balance", colorBalanceRenderer);
  registerEffectRenderer("exposure", exposureRenderer);
  registerEffectRenderer("vibrance", vibranceRenderer);
  registerEffectRenderer("invert", invertRenderer);
  registerEffectRenderer("posterize", posterizeRenderer);
  registerEffectRenderer("threshold", thresholdRenderer);
  registerEffectRenderer("vignette", vignetteRenderer);
  registerEffectRenderer("lut", lutRenderer);
  registerColorGradingEffects();
}

class SimplexNoise {
  perm = [];
  permMod12 = [];
  static grad3 = [
    [1, 1, 0],
    [-1, 1, 0],
    [1, -1, 0],
    [-1, -1, 0],
    [1, 0, 1],
    [-1, 0, 1],
    [1, 0, -1],
    [-1, 0, -1],
    [0, 1, 1],
    [0, -1, 1],
    [0, 1, -1],
    [0, -1, -1]
  ];
  constructor(seed) {
    this.initializePermutationTable(seed);
  }
  initializePermutationTable(seed) {
    const mulberry32 = (s) => {
      return () => {
        let t = s += 1831565813;
        t = Math.imul(t ^ t >>> 15, t | 1);
        t ^= t + Math.imul(t ^ t >>> 7, t | 61);
        return ((t ^ t >>> 14) >>> 0) / 4294967296;
      };
    };
    const random = mulberry32(seed);
    const p = [];
    for (let i = 0; i < 256; i++) {
      p[i] = i;
    }
    for (let i = 255; i > 0; i--) {
      const j = Math.floor(random() * (i + 1));
      [p[i], p[j]] = [p[j], p[i]];
    }
    for (let i = 0; i < 512; i++) {
      this.perm[i] = p[i & 255];
      this.permMod12[i] = this.perm[i] % 12;
    }
  }
  /**
   * 2D Simplex noise
   * Returns value in range [-1, 1]
   */
  noise2D(xin, yin) {
    const F2 = 0.5 * (Math.sqrt(3) - 1);
    const G2 = (3 - Math.sqrt(3)) / 6;
    const s = (xin + yin) * F2;
    const i = Math.floor(xin + s);
    const j = Math.floor(yin + s);
    const t = (i + j) * G2;
    const X0 = i - t;
    const Y0 = j - t;
    const x0 = xin - X0;
    const y0 = yin - Y0;
    let i1, j1;
    if (x0 > y0) {
      i1 = 1;
      j1 = 0;
    } else {
      i1 = 0;
      j1 = 1;
    }
    const x1 = x0 - i1 + G2;
    const y1 = y0 - j1 + G2;
    const x2 = x0 - 1 + 2 * G2;
    const y2 = y0 - 1 + 2 * G2;
    const ii = i & 255;
    const jj = j & 255;
    const gi0 = this.permMod12[ii + this.perm[jj]];
    const gi1 = this.permMod12[ii + i1 + this.perm[jj + j1]];
    const gi2 = this.permMod12[ii + 1 + this.perm[jj + 1]];
    let n0 = 0, n1 = 0, n2 = 0;
    let t0 = 0.5 - x0 * x0 - y0 * y0;
    if (t0 >= 0) {
      t0 *= t0;
      n0 = t0 * t0 * this.dot2D(SimplexNoise.grad3[gi0], x0, y0);
    }
    let t1 = 0.5 - x1 * x1 - y1 * y1;
    if (t1 >= 0) {
      t1 *= t1;
      n1 = t1 * t1 * this.dot2D(SimplexNoise.grad3[gi1], x1, y1);
    }
    let t2 = 0.5 - x2 * x2 - y2 * y2;
    if (t2 >= 0) {
      t2 *= t2;
      n2 = t2 * t2 * this.dot2D(SimplexNoise.grad3[gi2], x2, y2);
    }
    return 70 * (n0 + n1 + n2);
  }
  dot2D(g, x, y) {
    return g[0] * x + g[1] * y;
  }
}
function safeNum(val, def, min, max) {
  const num = typeof val === "number" && Number.isFinite(val) ? val : def;
  if (min !== void 0 && max !== void 0) {
    return Math.max(min, Math.min(max, num));
  }
  if (min !== void 0) return Math.max(min, num);
  if (max !== void 0) return Math.min(max, num);
  return num;
}
function transformRenderer(input, params) {
  const anchorPoint = params.anchor_point ?? { x: 0.5, y: 0.5 };
  const position = params.position ?? { x: 0.5, y: 0.5 };
  const anchorX_norm = safeNum(anchorPoint.x, 0.5, 0, 1);
  const anchorY_norm = safeNum(anchorPoint.y, 0.5, 0, 1);
  const posX_norm = safeNum(position.x, 0.5, 0, 1);
  const posY_norm = safeNum(position.y, 0.5, 0, 1);
  const scaleWidth = safeNum(params.scale_width, 100, 0.01, 1e4) / 100;
  const scaleHeight = safeNum(params.scale_height, 100, 0.01, 1e4) / 100;
  const skew = safeNum(params.skew, 0, -85, 85) * Math.PI / 180;
  const skewAxis = safeNum(params.skew_axis, 0, -360, 360) * Math.PI / 180;
  const rotation = safeNum(params.rotation, 0) * Math.PI / 180;
  const opacity = safeNum(params.opacity, 100, 0, 100) / 100;
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  const anchorX = anchorX_norm * width;
  const anchorY = anchorY_norm * height;
  const posX = posX_norm * width;
  const posY = posY_norm * height;
  output.ctx.globalAlpha = opacity;
  output.ctx.translate(posX, posY);
  output.ctx.rotate(rotation);
  if (skew !== 0) {
    const skewX = Math.tan(skew) * Math.cos(skewAxis);
    const skewY = Math.tan(skew) * Math.sin(skewAxis);
    output.ctx.transform(1, skewY, skewX, 1, 0, 0);
  }
  output.ctx.scale(scaleWidth, scaleHeight);
  output.ctx.translate(-anchorX, -anchorY);
  output.ctx.drawImage(input.canvas, 0, 0);
  output.ctx.setTransform(1, 0, 0, 1, 0, 0);
  output.ctx.globalAlpha = 1;
  return output;
}
function warpRenderer(input, params) {
  const warpStyle = params.warp_style ?? "arc";
  const bend = safeNum(params.bend, 0, -100, 100) / 100;
  const hDistort = safeNum(params.horizontal_distortion, 0, -100, 100) / 100;
  const vDistort = safeNum(params.vertical_distortion, 0, -100, 100) / 100;
  if (bend === 0 && hDistort === 0 && vDistort === 0) {
    return input;
  }
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const outputData = output.ctx.createImageData(width, height);
  const src = inputData.data;
  const dst = outputData.data;
  const centerX = width / 2;
  const centerY = height / 2;
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const nx = (x - centerX) / centerX;
      const ny = (y - centerY) / centerY;
      let srcX = x;
      let srcY = y;
      switch (warpStyle) {
        case "arc": {
          const arcBend = bend * ny * ny;
          srcX = x + arcBend * centerX * nx;
          break;
        }
        case "bulge": {
          const r = Math.sqrt(nx * nx + ny * ny);
          if (r < 1) {
            const factor = 1 + bend * (1 - r * r);
            srcX = centerX + (x - centerX) / factor;
            srcY = centerY + (y - centerY) / factor;
          }
          break;
        }
        case "wave": {
          srcX = x + Math.sin(ny * Math.PI * 2) * bend * width * 0.1;
          srcY = y + Math.sin(nx * Math.PI * 2) * bend * height * 0.1;
          break;
        }
        case "fisheye": {
          const r = Math.sqrt(nx * nx + ny * ny);
          if (r > 0 && r < 1) {
            const theta = Math.atan2(ny, nx);
            const newR = r ** (1 + bend);
            srcX = centerX + newR * Math.cos(theta) * centerX;
            srcY = centerY + newR * Math.sin(theta) * centerY;
          }
          break;
        }
        case "twist": {
          const r = Math.sqrt(nx * nx + ny * ny);
          const angle = bend * Math.PI * (1 - r);
          const cos = Math.cos(angle);
          const sin = Math.sin(angle);
          srcX = centerX + (nx * cos - ny * sin) * centerX;
          srcY = centerY + (nx * sin + ny * cos) * centerY;
          break;
        }
      }
      srcX += hDistort * centerX * (1 - ny * ny);
      srcY += vDistort * centerY * (1 - nx * nx);
      srcX = Math.max(0, Math.min(width - 1, srcX));
      srcY = Math.max(0, Math.min(height - 1, srcY));
      const x0 = Math.floor(srcX);
      const y0 = Math.floor(srcY);
      const x1 = Math.min(x0 + 1, width - 1);
      const y1 = Math.min(y0 + 1, height - 1);
      const fx = srcX - x0;
      const fy = srcY - y0;
      const idx00 = (y0 * width + x0) * 4;
      const idx01 = (y0 * width + x1) * 4;
      const idx10 = (y1 * width + x0) * 4;
      const idx11 = (y1 * width + x1) * 4;
      const outIdx = (y * width + x) * 4;
      for (let c = 0; c < 4; c++) {
        const v00 = src[idx00 + c];
        const v01 = src[idx01 + c];
        const v10 = src[idx10 + c];
        const v11 = src[idx11 + c];
        dst[outIdx + c] = Math.round(
          v00 * (1 - fx) * (1 - fy) + v01 * fx * (1 - fy) + v10 * (1 - fx) * fy + v11 * fx * fy
        );
      }
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function getChannelValue(r, g, b, a, channel) {
  switch (channel) {
    case "red":
      return r;
    case "green":
      return g;
    case "blue":
      return b;
    case "alpha":
      return a;
    default:
      return 0.299 * r + 0.587 * g + 0.114 * b;
  }
}
function generateProceduralMap(width, height, mapType, scale, seed = 12345) {
  const canvas = document.createElement("canvas");
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext("2d");
  const imageData = ctx.createImageData(width, height);
  const data = imageData.data;
  const mulberry32 = (s) => {
    return () => {
      let t = s += 1831565813;
      t = Math.imul(t ^ t >>> 15, t | 1);
      t ^= t + Math.imul(t ^ t >>> 7, t | 61);
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
  };
  const random = mulberry32(seed);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;
      let value = 128;
      switch (mapType) {
        case "noise":
          value = Math.floor(random() * 256);
          break;
        case "gradient-h":
          value = Math.floor(x / width * 255);
          break;
        case "gradient-v":
          value = Math.floor(y / height * 255);
          break;
        case "radial": {
          const cx = width / 2;
          const cy = height / 2;
          const dist = Math.sqrt((x - cx) ** 2 + (y - cy) ** 2);
          const maxDist = Math.sqrt(cx ** 2 + cy ** 2);
          value = Math.floor((1 - dist / maxDist) * 255);
          break;
        }
        case "sine-h":
          value = Math.floor(
            128 + 127 * Math.sin(x / width * Math.PI * 2 * scale)
          );
          break;
        case "sine-v":
          value = Math.floor(
            128 + 127 * Math.sin(y / height * Math.PI * 2 * scale)
          );
          break;
        case "checker": {
          const tileSize = Math.max(1, Math.floor(width / (scale * 10)));
          const checkX = Math.floor(x / tileSize) % 2;
          const checkY = Math.floor(y / tileSize) % 2;
          value = (checkX + checkY) % 2 === 0 ? 255 : 0;
          break;
        }
        default:
          value = 128;
      }
      data[i] = value;
      data[i + 1] = value;
      data[i + 2] = value;
      data[i + 3] = 255;
    }
  }
  return imageData;
}
function applyMapBehavior(x, y, targetWidth, targetHeight, mapWidth, mapHeight, behavior) {
  switch (behavior) {
    case "center": {
      const offsetX = (targetWidth - mapWidth) / 2;
      const offsetY = (targetHeight - mapHeight) / 2;
      const mapX = x - offsetX;
      const mapY = y - offsetY;
      if (mapX < 0 || mapX >= mapWidth || mapY < 0 || mapY >= mapHeight) {
        return { mapX: -1, mapY: -1 };
      }
      return { mapX, mapY };
    }
    case "stretch": {
      const mapX = x / targetWidth * mapWidth;
      const mapY = y / targetHeight * mapHeight;
      return { mapX, mapY };
    }
    case "tile": {
      const mapX = (x % mapWidth + mapWidth) % mapWidth;
      const mapY = (y % mapHeight + mapHeight) % mapHeight;
      return { mapX, mapY };
    }
    default:
      return {
        mapX: x / targetWidth * mapWidth,
        mapY: y / targetHeight * mapHeight
      };
  }
}
function displacementMapRenderer(input, params) {
  const mapType = params.map_type ?? "layer";
  const mapBehavior = params.displacement_map_behavior ?? "stretch";
  const useHorizontal = params.use_for_horizontal ?? "red";
  const useVertical = params.use_for_vertical ?? "green";
  const maxHorizontal = safeNum(params.max_horizontal, 0, -4e3, 4e3);
  const maxVertical = safeNum(params.max_vertical, 0, -4e3, 4e3);
  const wrapMode = params.edge_behavior ?? "off";
  const mapScale = safeNum(params.map_scale, 1, 0.1, 10);
  const mapLayerCanvas = params._mapLayerCanvas;
  if ((useHorizontal === "off" || maxHorizontal === 0) && (useVertical === "off" || maxVertical === 0)) {
    return input;
  }
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const src = inputData.data;
  let mapData;
  let mapWidth;
  let mapHeight;
  if (mapType === "layer" && mapLayerCanvas) {
    const mapCtx = mapLayerCanvas.getContext("2d");
    if (mapCtx) {
      mapWidth = mapLayerCanvas.width;
      mapHeight = mapLayerCanvas.height;
      const mapImageData = mapCtx.getImageData(0, 0, mapWidth, mapHeight);
      mapData = mapImageData.data;
    } else {
      const dispMap = generateProceduralMap(width, height, "noise", mapScale);
      mapData = dispMap.data;
      mapWidth = width;
      mapHeight = height;
    }
  } else if (mapType !== "layer") {
    const dispMap = generateProceduralMap(width, height, mapType, mapScale);
    mapData = dispMap.data;
    mapWidth = width;
    mapHeight = height;
  } else {
    const dispMap = generateProceduralMap(width, height, "radial", mapScale);
    mapData = dispMap.data;
    mapWidth = width;
    mapHeight = height;
  }
  const outputData = output.ctx.createImageData(width, height);
  const dst = outputData.data;
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;
      const { mapX, mapY } = applyMapBehavior(
        x,
        y,
        width,
        height,
        mapWidth,
        mapHeight,
        mapBehavior
      );
      if (mapX < 0 || mapY < 0) {
        dst[i] = src[i];
        dst[i + 1] = src[i + 1];
        dst[i + 2] = src[i + 2];
        dst[i + 3] = src[i + 3];
        continue;
      }
      const mx0 = Math.floor(mapX);
      const my0 = Math.floor(mapY);
      const mx1 = Math.min(mx0 + 1, mapWidth - 1);
      const my1 = Math.min(my0 + 1, mapHeight - 1);
      const mfx = mapX - mx0;
      const mfy = mapY - my0;
      const mi00 = (my0 * mapWidth + mx0) * 4;
      const mi10 = (my0 * mapWidth + mx1) * 4;
      const mi01 = (my1 * mapWidth + mx0) * 4;
      const mi11 = (my1 * mapWidth + mx1) * 4;
      const interpChannel = (channel) => {
        return Math.round(
          mapData[mi00 + channel] * (1 - mfx) * (1 - mfy) + mapData[mi10 + channel] * mfx * (1 - mfy) + mapData[mi01 + channel] * (1 - mfx) * mfy + mapData[mi11 + channel] * mfx * mfy
        );
      };
      const mapR = interpChannel(0);
      const mapG = interpChannel(1);
      const mapB = interpChannel(2);
      const mapA = interpChannel(3);
      let dx = 0;
      let dy = 0;
      if (useHorizontal !== "off" && maxHorizontal !== 0) {
        const hValue = getChannelValue(mapR, mapG, mapB, mapA, useHorizontal);
        dx = (hValue - 128) / 128 * maxHorizontal;
      }
      if (useVertical !== "off" && maxVertical !== 0) {
        const vValue = getChannelValue(mapR, mapG, mapB, mapA, useVertical);
        dy = (vValue - 128) / 128 * maxVertical;
      }
      let srcX = x - dx;
      let srcY = y - dy;
      if (wrapMode === "tiles") {
        srcX = (srcX % width + width) % width;
        srcY = (srcY % height + height) % height;
      } else if (wrapMode === "mirror") {
        srcX = Math.abs(srcX);
        srcY = Math.abs(srcY);
        if (Math.floor(srcX / width) % 2 === 1)
          srcX = width - 1 - srcX % width;
        else srcX = srcX % width;
        if (Math.floor(srcY / height) % 2 === 1)
          srcY = height - 1 - srcY % height;
        else srcY = srcY % height;
      } else {
        srcX = Math.max(0, Math.min(width - 1, srcX));
        srcY = Math.max(0, Math.min(height - 1, srcY));
      }
      const x0 = Math.floor(srcX);
      const y0 = Math.floor(srcY);
      const x1 = Math.min(x0 + 1, width - 1);
      const y1 = Math.min(y0 + 1, height - 1);
      const fx = srcX - x0;
      const fy = srcY - y0;
      const i00 = (y0 * width + x0) * 4;
      const i10 = (y0 * width + x1) * 4;
      const i01 = (y1 * width + x0) * 4;
      const i11 = (y1 * width + x1) * 4;
      for (let c = 0; c < 4; c++) {
        const v00 = src[i00 + c];
        const v10 = src[i10 + c];
        const v01 = src[i01 + c];
        const v11 = src[i11 + c];
        dst[i + c] = Math.round(
          v00 * (1 - fx) * (1 - fy) + v10 * fx * (1 - fy) + v01 * (1 - fx) * fy + v11 * fx * fy
        );
      }
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function turbulentDisplaceRenderer(input, params) {
  const displacementType = params.displacement ?? "turbulent";
  const amount = safeNum(params.amount, 50, 0, 1e3);
  const size = safeNum(params.size, 100, 1, 1e3);
  const complexityRaw = safeNum(params.complexity, 3, 1, 10);
  const complexity = Math.floor(complexityRaw);
  const evolutionDeg = safeNum(params.evolution, 0);
  const cycleEvolution = params.cycle_evolution ?? false;
  const cycleRevolutions = safeNum(params.cycle_revolutions, 1, 1, 100);
  const randomSeed = safeNum(params.random_seed, 0, 0, 99999);
  const offsetRaw = params.offset ?? { x: 0, y: 0 };
  const offset = {
    x: safeNum(offsetRaw.x, 0),
    y: safeNum(offsetRaw.y, 0)
  };
  const pinning = params.pinning ?? "none";
  if (amount === 0) {
    return input;
  }
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const src = inputData.data;
  const outputData = output.ctx.createImageData(width, height);
  const dst = outputData.data;
  let evolutionPhase = evolutionDeg * Math.PI / 180;
  if (cycleEvolution && cycleRevolutions > 0) {
    evolutionPhase = evolutionPhase % (2 * Math.PI * cycleRevolutions);
  }
  const effectiveSeed = randomSeed + Math.floor(evolutionPhase * 1e3);
  const noise = new SimplexNoise(effectiveSeed);
  new SimplexNoise(randomSeed + 12345);
  const centerX = width / 2;
  const centerY = height / 2;
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let pinFactorH = 1;
      let pinFactorV = 1;
      if (pinning === "all" || pinning === "horizontal") {
        const edgeDist = Math.min(y, height - 1 - y);
        const edgeThreshold = height * 0.1;
        pinFactorV = Math.min(1, edgeDist / edgeThreshold);
      }
      if (pinning === "all" || pinning === "vertical") {
        const edgeDist = Math.min(x, width - 1 - x);
        const edgeThreshold = width * 0.1;
        pinFactorH = Math.min(1, edgeDist / edgeThreshold);
      }
      const nx = (x + offset.x) / size;
      const ny = (y + offset.y) / size;
      let dx = 0;
      let dy = 0;
      switch (displacementType) {
        case "turbulent": {
          let noiseX = 0;
          let noiseY = 0;
          let amplitude = 1;
          let frequency = 1;
          let maxAmp = 0;
          for (let octave = 0; octave < complexity; octave++) {
            const timeOffset = evolutionPhase * 0.1;
            noiseX += noise.noise2D(nx * frequency + timeOffset, ny * frequency) * amplitude;
            noiseY += noise.noise2D(nx * frequency + 100, ny * frequency + timeOffset) * amplitude;
            maxAmp += amplitude;
            amplitude *= 0.5;
            frequency *= 2;
          }
          dx = noiseX / maxAmp * amount * pinFactorH;
          dy = noiseY / maxAmp * amount * pinFactorV;
          break;
        }
        case "turbulent-smoother": {
          let noiseX = 0;
          let noiseY = 0;
          let amplitude = 1;
          let frequency = 0.5;
          let maxAmp = 0;
          const smoothComplexity = Math.max(1, complexity - 2);
          for (let octave = 0; octave < smoothComplexity; octave++) {
            const timeOffset = evolutionPhase * 0.05;
            noiseX += noise.noise2D(nx * frequency + timeOffset, ny * frequency) * amplitude;
            noiseY += noise.noise2D(nx * frequency + 100, ny * frequency + timeOffset) * amplitude;
            maxAmp += amplitude;
            amplitude *= 0.6;
            frequency *= 1.5;
          }
          dx = noiseX / maxAmp * amount * pinFactorH;
          dy = noiseY / maxAmp * amount * pinFactorV;
          break;
        }
        case "bulge": {
          const noiseVal = noise.noise2D(nx + evolutionPhase * 0.1, ny);
          const fromCenterX = x - centerX;
          const fromCenterY = y - centerY;
          const dist = Math.sqrt(
            fromCenterX * fromCenterX + fromCenterY * fromCenterY
          );
          if (dist > 0) {
            const bulgeFactor = noiseVal * (amount / 100) * (1 - dist / Math.max(centerX, centerY));
            dx = fromCenterX / dist * bulgeFactor * amount * 0.5 * pinFactorH;
            dy = fromCenterY / dist * bulgeFactor * amount * 0.5 * pinFactorV;
          }
          break;
        }
        case "twist": {
          const fromCenterX = x - centerX;
          const fromCenterY = y - centerY;
          const dist = Math.sqrt(
            fromCenterX * fromCenterX + fromCenterY * fromCenterY
          );
          const maxDist = Math.sqrt(centerX * centerX + centerY * centerY);
          const noiseVal = noise.noise2D(nx + evolutionPhase * 0.1, ny);
          const twistAngle = noiseVal * (amount / 50) * Math.PI * (1 - dist / maxDist);
          const cos = Math.cos(twistAngle);
          const sin = Math.sin(twistAngle);
          dx = (fromCenterX * cos - fromCenterY * sin - fromCenterX) * pinFactorH;
          dy = (fromCenterX * sin + fromCenterY * cos - fromCenterY) * pinFactorV;
          break;
        }
        case "horizontal": {
          let noiseX = 0;
          let amplitude = 1;
          let frequency = 1;
          let maxAmp = 0;
          for (let octave = 0; octave < complexity; octave++) {
            noiseX += noise.noise2D(
              nx * frequency + evolutionPhase * 0.1,
              ny * frequency
            ) * amplitude;
            maxAmp += amplitude;
            amplitude *= 0.5;
            frequency *= 2;
          }
          dx = noiseX / maxAmp * amount * pinFactorH;
          dy = 0;
          break;
        }
        case "vertical": {
          let noiseY = 0;
          let amplitude = 1;
          let frequency = 1;
          let maxAmp = 0;
          for (let octave = 0; octave < complexity; octave++) {
            noiseY += noise.noise2D(
              nx * frequency + 100,
              ny * frequency + evolutionPhase * 0.1
            ) * amplitude;
            maxAmp += amplitude;
            amplitude *= 0.5;
            frequency *= 2;
          }
          dx = 0;
          dy = noiseY / maxAmp * amount * pinFactorV;
          break;
        }
        case "cross": {
          let noiseVal = 0;
          let amplitude = 1;
          let frequency = 1;
          let maxAmp = 0;
          for (let octave = 0; octave < complexity; octave++) {
            noiseVal += noise.noise2D(
              nx * frequency + evolutionPhase * 0.1,
              ny * frequency
            ) * amplitude;
            maxAmp += amplitude;
            amplitude *= 0.5;
            frequency *= 2;
          }
          const normalized = noiseVal / maxAmp;
          dx = normalized * amount * pinFactorH;
          dy = normalized * amount * pinFactorV;
          break;
        }
      }
      let srcX = x - dx;
      let srcY = y - dy;
      srcX = Math.max(0, Math.min(width - 1, srcX));
      srcY = Math.max(0, Math.min(height - 1, srcY));
      const x0 = Math.floor(srcX);
      const y0 = Math.floor(srcY);
      const x1 = Math.min(x0 + 1, width - 1);
      const y1 = Math.min(y0 + 1, height - 1);
      const fx = srcX - x0;
      const fy = srcY - y0;
      const i00 = (y0 * width + x0) * 4;
      const i10 = (y0 * width + x1) * 4;
      const i01 = (y1 * width + x0) * 4;
      const i11 = (y1 * width + x1) * 4;
      const outIdx = (y * width + x) * 4;
      for (let c = 0; c < 4; c++) {
        const v00 = src[i00 + c];
        const v10 = src[i10 + c];
        const v01 = src[i01 + c];
        const v11 = src[i11 + c];
        dst[outIdx + c] = Math.round(
          v00 * (1 - fx) * (1 - fy) + v10 * fx * (1 - fy) + v01 * (1 - fx) * fy + v11 * fx * fy
        );
      }
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function rippleDistortRenderer(input, params) {
  const centerRaw = params.center ?? { x: 0.5, y: 0.5 };
  const center = {
    x: safeNum(centerRaw.x, 0.5, 0, 1),
    y: safeNum(centerRaw.y, 0.5, 0, 1)
  };
  const radius = safeNum(params.radius, 200, 0, 1e4);
  const wavelength = safeNum(params.wavelength, 50, 1, 1e3);
  const amplitude = safeNum(params.amplitude, 20, 0, 1e3);
  const phaseDeg = safeNum(params.phase, 0);
  const decay = safeNum(params.decay, 50, 0, 100) / 100;
  if (amplitude === 0) {
    return input;
  }
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const src = inputData.data;
  const outputData = output.ctx.createImageData(width, height);
  const dst = outputData.data;
  const centerX = center.x * width;
  const centerY = center.y * height;
  const phase = phaseDeg * Math.PI / 180;
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const dx = x - centerX;
      const dy = y - centerY;
      const dist = Math.sqrt(dx * dx + dy * dy);
      let srcX = x;
      let srcY = y;
      if (dist > 0 && dist < radius) {
        const ripple = Math.sin(dist / wavelength * 2 * Math.PI + phase);
        const falloff = (1 - dist / radius) ** decay;
        const displacement = ripple * amplitude * falloff;
        const nx = dx / dist;
        const ny = dy / dist;
        srcX = x - nx * displacement;
        srcY = y - ny * displacement;
      }
      srcX = Math.max(0, Math.min(width - 1, srcX));
      srcY = Math.max(0, Math.min(height - 1, srcY));
      const x0 = Math.floor(srcX);
      const y0 = Math.floor(srcY);
      const x1 = Math.min(x0 + 1, width - 1);
      const y1 = Math.min(y0 + 1, height - 1);
      const fx = srcX - x0;
      const fy = srcY - y0;
      const i00 = (y0 * width + x0) * 4;
      const i10 = (y0 * width + x1) * 4;
      const i01 = (y1 * width + x0) * 4;
      const i11 = (y1 * width + x1) * 4;
      const outIdx = (y * width + x) * 4;
      for (let c = 0; c < 4; c++) {
        const v00 = src[i00 + c];
        const v10 = src[i10 + c];
        const v01 = src[i01 + c];
        const v11 = src[i11 + c];
        dst[outIdx + c] = Math.round(
          v00 * (1 - fx) * (1 - fy) + v10 * fx * (1 - fy) + v01 * (1 - fx) * fy + v11 * fx * fy
        );
      }
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function registerDistortEffects() {
  registerEffectRenderer("transform", transformRenderer);
  registerEffectRenderer("warp", warpRenderer);
  registerEffectRenderer("displacement-map", displacementMapRenderer);
  registerEffectRenderer("turbulent-displace", turbulentDisplaceRenderer);
  registerEffectRenderer("ripple-distort", rippleDistortRenderer);
}

function sliderControlRenderer(input, _params) {
  return input;
}
function checkboxControlRenderer(input, _params) {
  return input;
}
function dropdownMenuControlRenderer(input, _params) {
  return input;
}
function colorControlRenderer(input, _params) {
  return input;
}
function pointControlRenderer(input, _params) {
  return input;
}
function point3DControlRenderer(input, _params) {
  return input;
}
function angleControlRenderer(input, _params) {
  return input;
}
function layerControlRenderer(input, _params) {
  return input;
}
function registerExpressionControlRenderers() {
  registerEffectRenderer("slider-control", sliderControlRenderer);
  registerEffectRenderer("checkbox-control", checkboxControlRenderer);
  registerEffectRenderer("dropdown-menu-control", dropdownMenuControlRenderer);
  registerEffectRenderer("color-control", colorControlRenderer);
  registerEffectRenderer("point-control", pointControlRenderer);
  registerEffectRenderer("3d-point-control", point3DControlRenderer);
  registerEffectRenderer("angle-control", angleControlRenderer);
  registerEffectRenderer("layer-control", layerControlRenderer);
}

class NoiseTileCache {
  cache = /* @__PURE__ */ new Map();
  maxSize = 32;
  // Max cached tiles
  maxAgeMs = 3e4;
  // 30 second TTL
  /**
   * Generate cache key from parameters
   */
  makeKey(width, height, scale, octave, seed) {
    const quantizedSeed = Math.round(seed * 100) / 100;
    return `${width}:${height}:${scale}:${octave}:${quantizedSeed}`;
  }
  /**
   * Get cached noise tile or null if not found/expired
   */
  get(width, height, scale, octave, seed) {
    const key = this.makeKey(width, height, scale, octave, seed);
    const entry = this.cache.get(key);
    if (!entry) return null;
    const now = Date.now();
    if (now - entry.timestamp > this.maxAgeMs) {
      this.cache.delete(key);
      return null;
    }
    this.cache.delete(key);
    this.cache.set(key, { ...entry, timestamp: now });
    return entry.tile;
  }
  /**
   * Store noise tile in cache
   */
  set(width, height, scale, octave, seed, tile) {
    while (this.cache.size >= this.maxSize) {
      const firstKey = this.cache.keys().next().value;
      if (firstKey) this.cache.delete(firstKey);
    }
    const key = this.makeKey(width, height, scale, octave, seed);
    this.cache.set(key, {
      tile,
      width,
      height,
      scale,
      octave,
      seed,
      timestamp: Date.now()
    });
  }
  /**
   * Clear all cached tiles
   */
  clear() {
    this.cache.clear();
  }
  /**
   * Get cache statistics
   */
  getStats() {
    return { size: this.cache.size, maxSize: this.maxSize };
  }
}
const noiseTileCache = new NoiseTileCache();
function fillRenderer(input, params) {
  const color = params.color ?? { r: 255, g: 0, b: 0, a: 1 };
  const rawOpacity = params.opacity ?? 100;
  const opacity = Number.isFinite(rawOpacity) ? rawOpacity / 100 : 1;
  const invert = params.invert ?? false;
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const outputData = output.ctx.createImageData(width, height);
  const src = inputData.data;
  const dst = outputData.data;
  const r = color.r ?? 255;
  const g = color.g ?? 0;
  const b = color.b ?? 0;
  const a = (color.a ?? 1) * 255 * opacity;
  for (let i = 0; i < src.length; i += 4) {
    const srcAlpha = src[i + 3] / 255;
    if (invert) {
      const fillAmount = 1 - srcAlpha;
      dst[i] = Math.round(r * fillAmount + src[i] * (1 - fillAmount));
      dst[i + 1] = Math.round(g * fillAmount + src[i + 1] * (1 - fillAmount));
      dst[i + 2] = Math.round(b * fillAmount + src[i + 2] * (1 - fillAmount));
      dst[i + 3] = Math.max(src[i + 3], Math.round(a * fillAmount));
    } else {
      dst[i] = Math.round(r * srcAlpha * opacity + src[i] * (1 - opacity));
      dst[i + 1] = Math.round(
        g * srcAlpha * opacity + src[i + 1] * (1 - opacity)
      );
      dst[i + 2] = Math.round(
        b * srcAlpha * opacity + src[i + 2] * (1 - opacity)
      );
      dst[i + 3] = src[i + 3];
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function gradientRampRenderer(input, params) {
  const startPoint = params.start_of_ramp ?? { x: 0, y: 0.5 };
  const startColor = params.start_color ?? { r: 0, g: 0, b: 0, a: 1 };
  const endPoint = params.end_of_ramp ?? { x: 1, y: 0.5 };
  const endColor = params.end_color ?? { r: 255, g: 255, b: 255, a: 1 };
  const rampShape = params.ramp_shape ?? "linear";
  const scatter = (params.ramp_scatter ?? 0) / 100;
  const blend = (params.blend_with_original ?? 0) / 100;
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  let gradient;
  if (rampShape === "radial") {
    const cx = startPoint.x * width;
    const cy = startPoint.y * height;
    const dx = (endPoint.x - startPoint.x) * width;
    const dy = (endPoint.y - startPoint.y) * height;
    const radius = Math.sqrt(dx * dx + dy * dy);
    gradient = output.ctx.createRadialGradient(cx, cy, 0, cx, cy, radius);
  } else {
    gradient = output.ctx.createLinearGradient(
      startPoint.x * width,
      startPoint.y * height,
      endPoint.x * width,
      endPoint.y * height
    );
  }
  const startRgba = `rgba(${startColor.r}, ${startColor.g}, ${startColor.b}, ${startColor.a ?? 1})`;
  const endRgba = `rgba(${endColor.r}, ${endColor.g}, ${endColor.b}, ${endColor.a ?? 1})`;
  gradient.addColorStop(0, startRgba);
  gradient.addColorStop(1, endRgba);
  output.ctx.fillStyle = gradient;
  output.ctx.fillRect(0, 0, width, height);
  if (scatter > 0) {
    const outputData = output.ctx.getImageData(0, 0, width, height);
    const dst = outputData.data;
    const scatterAmount = scatter * 25;
    const frame = params._frame ?? 0;
    const seededRandom = (seed) => {
      let t = seed + 1831565813;
      t = Math.imul(t ^ t >>> 15, t | 1);
      t ^= t + Math.imul(t ^ t >>> 7, t | 61);
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
    for (let i = 0; i < dst.length; i += 4) {
      const pixelSeed = frame * 1000003 + i / 4;
      const noise = (seededRandom(pixelSeed) - 0.5) * scatterAmount;
      dst[i] = Math.max(0, Math.min(255, dst[i] + noise));
      dst[i + 1] = Math.max(0, Math.min(255, dst[i + 1] + noise));
      dst[i + 2] = Math.max(0, Math.min(255, dst[i + 2] + noise));
    }
    output.ctx.putImageData(outputData, 0, 0);
  }
  if (blend > 0) {
    output.ctx.globalAlpha = blend;
    output.ctx.drawImage(input.canvas, 0, 0);
    output.ctx.globalAlpha = 1;
  }
  return output;
}
function noise2D(x, y, seed) {
  const n = Math.sin(x * 12.9898 + y * 78.233 + seed) * 43758.5453;
  return n - Math.floor(n);
}
function smoothNoise(x, y, seed) {
  const x0 = Math.floor(x);
  const y0 = Math.floor(y);
  const fx = x - x0;
  const fy = y - y0;
  const v00 = noise2D(x0, y0, seed);
  const v10 = noise2D(x0 + 1, y0, seed);
  const v01 = noise2D(x0, y0 + 1, seed);
  const v11 = noise2D(x0 + 1, y0 + 1, seed);
  const sx = fx * fx * (3 - 2 * fx);
  const sy = fy * fy * (3 - 2 * fy);
  return v00 * (1 - sx) * (1 - sy) + v10 * sx * (1 - sy) + v01 * (1 - sx) * sy + v11 * sx * sy;
}
function getOctaveTile(width, height, scale, octave, seed, frequency, isTurbulent) {
  const octaveSeed = seed + octave * 100;
  const cached = noiseTileCache.get(width, height, scale, octave, octaveSeed);
  if (cached) {
    return cached;
  }
  const tile = new Float32Array(width * height);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const sampleX = x / scale * frequency;
      const sampleY = y / scale * frequency;
      let noiseValue = smoothNoise(sampleX, sampleY, octaveSeed);
      if (isTurbulent) {
        noiseValue = Math.abs(noiseValue * 2 - 1);
      }
      tile[y * width + x] = noiseValue;
    }
  }
  noiseTileCache.set(width, height, scale, octave, octaveSeed, tile);
  return tile;
}
function fractalNoiseRenderer(input, params) {
  const fractalType = params.fractal_type ?? "basic";
  const invert = params.invert ?? false;
  const contrast = (params.contrast ?? 100) / 100;
  const brightness = (params.brightness ?? 0) / 100;
  const scale = params.scale ?? 100;
  const complexity = Math.max(1, Math.min(20, params.complexity ?? 6));
  const evolution = (params.evolution ?? 0) * Math.PI / 180;
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  const outputData = output.ctx.createImageData(width, height);
  const dst = outputData.data;
  const seed = evolution * 1e3;
  const isTurbulent = fractalType.includes("turbulent");
  const octaveTiles = [];
  const amplitudes = [];
  let frequency = 1;
  let amplitude = 1;
  let maxValue = 0;
  for (let octave = 0; octave < complexity; octave++) {
    octaveTiles.push(
      getOctaveTile(width, height, scale, octave, seed, frequency, isTurbulent)
    );
    amplitudes.push(amplitude);
    maxValue += amplitude;
    amplitude *= 0.5;
    frequency *= 2;
  }
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let value = 0;
      const pixelIdx = y * width + x;
      for (let octave = 0; octave < complexity; octave++) {
        value += octaveTiles[octave][pixelIdx] * amplitudes[octave];
      }
      value /= maxValue;
      value = (value - 0.5) * contrast + 0.5 + brightness;
      if (invert) {
        value = 1 - value;
      }
      value = Math.max(0, Math.min(1, value));
      const pixelValue = Math.round(value * 255);
      const idx = pixelIdx * 4;
      dst[idx] = pixelValue;
      dst[idx + 1] = pixelValue;
      dst[idx + 2] = pixelValue;
      dst[idx + 3] = 255;
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function addGrainRenderer(input, params, frame) {
  const intensity = params.intensity ?? 0.5;
  const size = params.size ?? 1;
  const softness = params.softness ?? 0;
  const animate = params.animate ?? true;
  const colorGrain = params.color ?? false;
  if (intensity === 0) {
    return input;
  }
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  output.ctx.drawImage(input.canvas, 0, 0);
  const grainScale = Math.max(1, Math.round(size));
  const grainWidth = Math.ceil(width / grainScale);
  const grainHeight = Math.ceil(height / grainScale);
  const grainCanvas = document.createElement("canvas");
  grainCanvas.width = grainWidth;
  grainCanvas.height = grainHeight;
  const grainCtx = grainCanvas.getContext("2d");
  const grainData = grainCtx.createImageData(grainWidth, grainHeight);
  const grain = grainData.data;
  const seed = animate ? (frame ?? 0) * 12345 : 42;
  let rngState = seed;
  const seededRandom = () => {
    rngState = rngState * 1103515245 + 12345 & 2147483647;
    return rngState / 2147483647;
  };
  for (let i = 0; i < grain.length; i += 4) {
    if (colorGrain) {
      grain[i] = Math.round((seededRandom() - 0.5) * 255 * intensity + 128);
      grain[i + 1] = Math.round((seededRandom() - 0.5) * 255 * intensity + 128);
      grain[i + 2] = Math.round((seededRandom() - 0.5) * 255 * intensity + 128);
    } else {
      const grainValue = Math.round(
        (seededRandom() - 0.5) * 255 * intensity + 128
      );
      grain[i] = grainValue;
      grain[i + 1] = grainValue;
      grain[i + 2] = grainValue;
    }
    grain[i + 3] = 255;
  }
  grainCtx.putImageData(grainData, 0, 0);
  if (softness > 0) {
    const blurAmount = softness * 2;
    grainCtx.filter = `blur(${blurAmount}px)`;
    grainCtx.drawImage(grainCanvas, 0, 0);
    grainCtx.filter = "none";
  }
  output.ctx.globalCompositeOperation = "overlay";
  output.ctx.globalAlpha = intensity;
  if (grainScale > 1) {
    output.ctx.imageSmoothingEnabled = false;
    output.ctx.drawImage(grainCanvas, 0, 0, width, height);
    output.ctx.imageSmoothingEnabled = true;
  } else {
    output.ctx.drawImage(grainCanvas, 0, 0);
  }
  output.ctx.globalCompositeOperation = "source-over";
  output.ctx.globalAlpha = 1;
  return output;
}
function radioWavesRenderer(input, params) {
  const center = params.center ?? { x: 0.5, y: 0.5 };
  const frequency = Math.max(1, params.frequency ?? 4);
  const expansion = (params.expansion ?? 50) / 100;
  const waveWidth = Math.max(1, params.wave_width ?? 20);
  const strokeColor = params.stroke_color ?? { r: 255, g: 255, b: 255, a: 1 };
  const backgroundColor = params.background_color ?? {
    r: 128,
    g: 128,
    b: 128,
    a: 1
  };
  const fadeStart = (params.fade_start ?? 0) / 100;
  const fadeEnd = (params.fade_end ?? 100) / 100;
  const invert = params.invert ?? false;
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  const outputData = output.ctx.createImageData(width, height);
  const dst = outputData.data;
  const centerX = center.x * width;
  const centerY = center.y * height;
  const maxRadius = Math.sqrt(width * width + height * height);
  const currentMaxRadius = maxRadius * expansion;
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const dx = x - centerX;
      const dy = y - centerY;
      const dist = Math.sqrt(dx * dx + dy * dy);
      const waveSpacing = currentMaxRadius / frequency;
      let waveValue = 0;
      if (waveSpacing > 0 && dist <= currentMaxRadius) {
        const phase = dist % waveSpacing / waveSpacing;
        const ringThickness = waveWidth / 100;
        if (phase < ringThickness || phase > 1 - ringThickness / 2) {
          waveValue = 1;
        }
        const normalizedDist = dist / currentMaxRadius;
        let fadeMultiplier = 1;
        if (normalizedDist < fadeStart) {
          fadeMultiplier = normalizedDist / Math.max(1e-3, fadeStart);
        } else if (normalizedDist > fadeEnd) {
          fadeMultiplier = 1 - (normalizedDist - fadeEnd) / Math.max(1e-3, 1 - fadeEnd);
        }
        waveValue *= Math.max(0, Math.min(1, fadeMultiplier));
      }
      if (invert) {
        waveValue = 1 - waveValue;
      }
      const i = (y * width + x) * 4;
      dst[i] = Math.round(
        backgroundColor.r * (1 - waveValue) + strokeColor.r * waveValue
      );
      dst[i + 1] = Math.round(
        backgroundColor.g * (1 - waveValue) + strokeColor.g * waveValue
      );
      dst[i + 2] = Math.round(
        backgroundColor.b * (1 - waveValue) + strokeColor.b * waveValue
      );
      dst[i + 3] = Math.round(
        ((backgroundColor.a ?? 1) * (1 - waveValue) + (strokeColor.a ?? 1) * waveValue) * 255
      );
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function ellipseRenderer(input, params) {
  const center = params.center ?? { x: 0.5, y: 0.5 };
  const ellipseWidth = params.ellipse_width ?? 200;
  const ellipseHeight = params.ellipse_height ?? 200;
  const softness = (params.softness ?? 0) / 100;
  const strokeWidth = params.stroke_width ?? 0;
  const strokeColor = params.stroke_color ?? { r: 255, g: 255, b: 255, a: 1 };
  const backgroundColor = params.background_color ?? { r: 0, g: 0, b: 0, a: 1 };
  const invertShape = params.invert ?? false;
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  const outputData = output.ctx.createImageData(width, height);
  const dst = outputData.data;
  const centerX = center.x * width;
  const centerY = center.y * height;
  const radiusX = ellipseWidth / 2;
  const radiusY = ellipseHeight / 2;
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const dx = x - centerX;
      const dy = y - centerY;
      const normalizedDist = Math.sqrt(
        dx * dx / (radiusX * radiusX) + dy * dy / (radiusY * radiusY)
      );
      let shapeValue = 0;
      if (strokeWidth > 0) {
        const innerRadius = 1 - strokeWidth / Math.min(radiusX, radiusY);
        const outerRadius = 1;
        if (normalizedDist >= innerRadius && normalizedDist <= outerRadius) {
          shapeValue = 1;
        }
        if (softness > 0) {
          const featherNorm = softness * 0.3;
          if (normalizedDist < innerRadius && normalizedDist >= innerRadius - featherNorm) {
            shapeValue = (normalizedDist - (innerRadius - featherNorm)) / featherNorm;
          } else if (normalizedDist > outerRadius && normalizedDist <= outerRadius + featherNorm) {
            shapeValue = 1 - (normalizedDist - outerRadius) / featherNorm;
          }
        }
      } else {
        if (normalizedDist <= 1) {
          shapeValue = 1;
        }
        if (softness > 0) {
          const featherNorm = softness * 0.3;
          if (normalizedDist > 1 - featherNorm && normalizedDist <= 1 + featherNorm) {
            shapeValue = 1 - Math.max(
              0,
              (normalizedDist - (1 - featherNorm)) / (featherNorm * 2)
            );
          } else if (normalizedDist > 1) {
            shapeValue = 0;
          }
        }
      }
      shapeValue = Math.max(0, Math.min(1, shapeValue));
      if (invertShape) {
        shapeValue = 1 - shapeValue;
      }
      const i = (y * width + x) * 4;
      dst[i] = Math.round(
        backgroundColor.r * (1 - shapeValue) + strokeColor.r * shapeValue
      );
      dst[i + 1] = Math.round(
        backgroundColor.g * (1 - shapeValue) + strokeColor.g * shapeValue
      );
      dst[i + 2] = Math.round(
        backgroundColor.b * (1 - shapeValue) + strokeColor.b * shapeValue
      );
      dst[i + 3] = Math.round(
        ((backgroundColor.a ?? 1) * (1 - shapeValue) + (strokeColor.a ?? 1) * shapeValue) * 255
      );
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function registerGenerateEffects() {
  registerEffectRenderer("fill", fillRenderer);
  registerEffectRenderer("gradient-ramp", gradientRampRenderer);
  registerEffectRenderer("fractal-noise", fractalNoiseRenderer);
  registerEffectRenderer("add-grain", addGrainRenderer);
  registerEffectRenderer("radio-waves", radioWavesRenderer);
  registerEffectRenderer("ellipse", ellipseRenderer);
}

const logger$1 = createLogger("AlphaToMesh");
function generateMeshFromAlpha(imageData, options = {}) {
  const {
    triangleCount: targetTriangles = 200,
    expansion = 3,
    alphaThreshold = 128,
    minBoundarySpacing = 5
  } = options;
  const { width, height, data } = imageData;
  logger$1.debug(
    `Generating mesh from alpha: ${width}x${height}, target triangles: ${targetTriangles}`
  );
  const alphaMask = extractAlphaMask(data, width, height, alphaThreshold);
  const bounds = findAlphaBounds(alphaMask, width, height);
  if (bounds.width === 0 || bounds.height === 0) {
    logger$1.warn("No alpha content found, creating full-image mesh");
    return createFullImageMesh(width, height);
  }
  const boundaryPoints = extractBoundaryPoints(
    alphaMask,
    width,
    height,
    bounds,
    minBoundarySpacing
  );
  const expandedBoundary = expandBoundary(
    boundaryPoints,
    alphaMask,
    width,
    height,
    expansion
  );
  const interiorPoints = generateInteriorPoints(
    alphaMask,
    width,
    height,
    bounds,
    targetTriangles,
    expandedBoundary.length
  );
  const allPoints = [...expandedBoundary, ...interiorPoints];
  if (allPoints.length < 3) {
    logger$1.warn("Not enough points for triangulation, creating minimal mesh");
    return createFullImageMesh(width, height);
  }
  const triangles = delaunayTriangulate(allPoints);
  if (triangles.length === 0) {
    logger$1.warn("Triangulation failed, creating minimal mesh");
    return createFullImageMesh(width, height);
  }
  const vertices = new Float32Array(allPoints.length * 2);
  for (let i = 0; i < allPoints.length; i++) {
    vertices[i * 2] = allPoints[i].x;
    vertices[i * 2 + 1] = allPoints[i].y;
  }
  const triangleIndices = new Uint32Array(triangles.length * 3);
  for (let i = 0; i < triangles.length; i++) {
    triangleIndices[i * 3] = triangles[i].a;
    triangleIndices[i * 3 + 1] = triangles[i].b;
    triangleIndices[i * 3 + 2] = triangles[i].c;
  }
  logger$1.debug(
    `Mesh generated: ${allPoints.length} vertices, ${triangles.length} triangles`
  );
  return {
    vertices,
    triangles: triangleIndices,
    bounds: {
      x: bounds.minX,
      y: bounds.minY,
      width: bounds.width,
      height: bounds.height
    },
    vertexCount: allPoints.length,
    triangleCount: triangles.length
  };
}
function extractAlphaMask(data, width, height, threshold) {
  const mask = new Array(width * height);
  for (let i = 0; i < width * height; i++) {
    mask[i] = data[i * 4 + 3] >= threshold;
  }
  return mask;
}
function findAlphaBounds(mask, width, height) {
  let minX = width;
  let minY = height;
  let maxX = 0;
  let maxY = 0;
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      if (mask[y * width + x]) {
        minX = Math.min(minX, x);
        minY = Math.min(minY, y);
        maxX = Math.max(maxX, x);
        maxY = Math.max(maxY, y);
      }
    }
  }
  return {
    minX,
    minY,
    maxX,
    maxY,
    width: maxX > minX ? maxX - minX + 1 : 0,
    height: maxY > minY ? maxY - minY + 1 : 0
  };
}
function extractBoundaryPoints(mask, width, height, bounds, minSpacing) {
  const boundaryPixels = [];
  for (let y = bounds.minY; y <= bounds.maxY; y++) {
    for (let x = bounds.minX; x <= bounds.maxX; x++) {
      const idx = y * width + x;
      if (!mask[idx]) continue;
      const hasEmptyNeighbor = x === 0 || !mask[idx - 1] || // left
      x === width - 1 || !mask[idx + 1] || // right
      y === 0 || !mask[idx - width] || // top
      y === height - 1 || !mask[idx + width];
      if (hasEmptyNeighbor) {
        boundaryPixels.push({ x, y });
      }
    }
  }
  return subsamplePoints(boundaryPixels, minSpacing);
}
function subsamplePoints(points, minSpacing) {
  if (points.length === 0) return [];
  const result = [points[0]];
  const spacingSq = minSpacing * minSpacing;
  for (let i = 1; i < points.length; i++) {
    const p = points[i];
    let tooClose = false;
    for (let j = Math.max(0, result.length - 20); j < result.length; j++) {
      const r = result[j];
      const dx = p.x - r.x;
      const dy = p.y - r.y;
      if (dx * dx + dy * dy < spacingSq) {
        tooClose = true;
        break;
      }
    }
    if (!tooClose) {
      result.push(p);
    }
  }
  return result;
}
function expandBoundary(points, mask, width, height, expansion) {
  if (expansion <= 0) return points;
  return points.map((p) => {
    const normal = calculateOutwardNormal(p, mask, width, height);
    return {
      x: Math.max(0, Math.min(width - 1, p.x + normal.x * expansion)),
      y: Math.max(0, Math.min(height - 1, p.y + normal.y * expansion))
    };
  });
}
function calculateOutwardNormal(point, mask, width, height) {
  const { x, y } = point;
  let nx = 0;
  let ny = 0;
  const radius = 3;
  for (let dy = -radius; dy <= radius; dy++) {
    for (let dx = -radius; dx <= radius; dx++) {
      if (dx === 0 && dy === 0) continue;
      const sx = x + dx;
      const sy = y + dy;
      if (sx < 0 || sx >= width || sy < 0 || sy >= height) {
        nx += dx;
        ny += dy;
      } else if (!mask[sy * width + sx]) {
        nx += dx;
        ny += dy;
      }
    }
  }
  const len = Math.sqrt(nx * nx + ny * ny);
  if (len < 1e-3) {
    return { x: 0, y: -1 };
  }
  return { x: nx / len, y: ny / len };
}
function generateInteriorPoints(mask, width, height, bounds, targetTriangles, boundaryPointCount) {
  const targetVertices = Math.ceil((targetTriangles + 5) / 2);
  const neededInterior = Math.max(0, targetVertices - boundaryPointCount);
  if (neededInterior === 0) return [];
  const area = bounds.width * bounds.height;
  const spacing = Math.sqrt(area / (neededInterior * 1.5));
  const points = [];
  for (let y = bounds.minY + spacing / 2; y < bounds.maxY; y += spacing) {
    for (let x = bounds.minX + spacing / 2; x < bounds.maxX; x += spacing) {
      const jx = x + (Math.random() - 0.5) * spacing * 0.5;
      const jy = y + (Math.random() - 0.5) * spacing * 0.5;
      const ix = Math.round(jx);
      const iy = Math.round(jy);
      if (ix >= 0 && ix < width && iy >= 0 && iy < height) {
        if (mask[iy * width + ix]) {
          points.push({ x: jx, y: jy });
        }
      }
      if (points.length >= neededInterior) break;
    }
    if (points.length >= neededInterior) break;
  }
  return points;
}
function delaunayTriangulate(points) {
  if (points.length < 3) {
    return [];
  }
  const minX = Math.min(...points.map((p) => p.x));
  const maxX = Math.max(...points.map((p) => p.x));
  const minY = Math.min(...points.map((p) => p.y));
  const maxY = Math.max(...points.map((p) => p.y));
  const dx = maxX - minX;
  const dy = maxY - minY;
  const deltaMax = Math.max(dx, dy) * 2;
  const superA = { x: minX - deltaMax, y: minY - deltaMax };
  const superB = { x: minX + deltaMax * 2, y: minY - deltaMax };
  const superC = { x: minX + deltaMax / 2, y: maxY + deltaMax * 2 };
  const allPoints = [...points, superA, superB, superC];
  const superIndices = [points.length, points.length + 1, points.length + 2];
  let triangles = [
    { a: superIndices[0], b: superIndices[1], c: superIndices[2] }
  ];
  for (let i = 0; i < points.length; i++) {
    const point = points[i];
    const badTriangles = [];
    const polygon = [];
    for (const tri of triangles) {
      if (isPointInCircumcircle(
        point,
        allPoints[tri.a],
        allPoints[tri.b],
        allPoints[tri.c]
      )) {
        badTriangles.push(tri);
      }
    }
    for (const tri of badTriangles) {
      const edges = [
        { a: tri.a, b: tri.b },
        { a: tri.b, b: tri.c },
        { a: tri.c, b: tri.a }
      ];
      for (const edge of edges) {
        let isShared = false;
        for (const other of badTriangles) {
          if (other === tri) continue;
          const otherEdges = [
            { a: other.a, b: other.b },
            { a: other.b, b: other.c },
            { a: other.c, b: other.a }
          ];
          for (const otherEdge of otherEdges) {
            if (edge.a === otherEdge.a && edge.b === otherEdge.b || edge.a === otherEdge.b && edge.b === otherEdge.a) {
              isShared = true;
              break;
            }
          }
          if (isShared) break;
        }
        if (!isShared) {
          polygon.push(edge);
        }
      }
    }
    triangles = triangles.filter((t) => !badTriangles.includes(t));
    for (const edge of polygon) {
      triangles.push({ a: edge.a, b: edge.b, c: i });
    }
  }
  return triangles.filter(
    (t) => !superIndices.includes(t.a) && !superIndices.includes(t.b) && !superIndices.includes(t.c)
  );
}
function isPointInCircumcircle(point, a, b, c) {
  const ax = a.x - point.x;
  const ay = a.y - point.y;
  const bx = b.x - point.x;
  const by = b.y - point.y;
  const cx = c.x - point.x;
  const cy = c.y - point.y;
  const det = (ax * ax + ay * ay) * (bx * cy - cx * by) - (bx * bx + by * by) * (ax * cy - cx * ay) + (cx * cx + cy * cy) * (ax * by - bx * ay);
  const orientation = (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
  return orientation > 0 ? det > 0 : det < 0;
}
function createFullImageMesh(width, height) {
  const cols = 4;
  const rows = 4;
  const points = [];
  for (let y = 0; y <= rows; y++) {
    for (let x = 0; x <= cols; x++) {
      points.push({
        x: x / cols * width,
        y: y / rows * height
      });
    }
  }
  const triangles = [];
  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {
      const i = y * (cols + 1) + x;
      triangles.push({ a: i, b: i + 1, c: i + cols + 1 });
      triangles.push({ a: i + 1, b: i + cols + 2, c: i + cols + 1 });
    }
  }
  const vertices = new Float32Array(points.length * 2);
  for (let i = 0; i < points.length; i++) {
    vertices[i * 2] = points[i].x;
    vertices[i * 2 + 1] = points[i].y;
  }
  const triangleIndices = new Uint32Array(triangles.length * 3);
  for (let i = 0; i < triangles.length; i++) {
    triangleIndices[i * 3] = triangles[i].a;
    triangleIndices[i * 3 + 1] = triangles[i].b;
    triangleIndices[i * 3 + 2] = triangles[i].c;
  }
  return {
    vertices,
    triangles: triangleIndices,
    bounds: { x: 0, y: 0, width, height },
    vertexCount: points.length,
    triangleCount: triangles.length
  };
}

const logger = createLogger("MeshDeformRenderer");
const meshCaches = /* @__PURE__ */ new Map();
function hashCanvas(canvas) {
  const ctx = canvas.getContext("2d");
  if (!ctx) return "";
  const { width, height } = canvas;
  const samples = [width, height];
  for (let y = 0; y < 3; y++) {
    for (let x = 0; x < 3; x++) {
      const px = Math.floor((x + 0.5) * width / 3);
      const py = Math.floor((y + 0.5) * height / 3);
      const data = ctx.getImageData(px, py, 1, 1).data;
      samples.push(data[3]);
    }
  }
  return samples.join(",");
}
function getOrGenerateMesh(effectId, inputCanvas, params, pins) {
  const triangleCount = params.triangle_count ?? 200;
  const expansion = params.expansion ?? 3;
  const alphaThreshold = params.alpha_threshold ?? 128;
  const inputHash = hashCanvas(inputCanvas);
  const cached = meshCaches.get(effectId);
  if (cached && cached.inputHash === inputHash && cached.params.triangleCount === triangleCount && cached.params.expansion === expansion && cached.params.alphaThreshold === alphaThreshold) {
    if (pins.length > 0 && cached.weights.length !== cached.mesh.vertexCount * pins.length) {
      cached.weights = calculatePinWeights(cached.mesh, pins, params);
    }
    return { mesh: cached.mesh, weights: cached.weights };
  }
  const ctx = inputCanvas.getContext("2d");
  const imageData = ctx.getImageData(
    0,
    0,
    inputCanvas.width,
    inputCanvas.height
  );
  const mesh = generateMeshFromAlpha(imageData, {
    triangleCount,
    expansion,
    alphaThreshold
  });
  const weights = calculatePinWeights(mesh, pins, params);
  meshCaches.set(effectId, {
    mesh,
    weights,
    inputHash,
    params: { triangleCount, expansion, alphaThreshold }
  });
  logger.debug(
    `Generated mesh for ${effectId}: ${mesh.vertexCount} vertices, ${mesh.triangleCount} triangles`
  );
  return { mesh, weights };
}
function calculatePinWeights(mesh, pins, params) {
  if (pins.length === 0) {
    return new Float32Array(0);
  }
  const falloffMethod = params.pin_falloff ?? "inverse-distance";
  const falloffPower = params.falloff_power ?? 2;
  const weights = new Float32Array(mesh.vertexCount * pins.length);
  for (let v = 0; v < mesh.vertexCount; v++) {
    const vx = mesh.vertices[v * 2];
    const vy = mesh.vertices[v * 2 + 1];
    let totalWeight = 0;
    for (let p = 0; p < pins.length; p++) {
      const pin = pins[p];
      const px = pin.position.value.x;
      const py = pin.position.value.y;
      const radius = pin.radius;
      const dx = vx - px;
      const dy = vy - py;
      const dist = Math.sqrt(dx * dx + dy * dy);
      let weight = 0;
      if (falloffMethod === "radial-basis") {
        const sigma = radius / 3;
        weight = Math.exp(-(dist * dist) / (2 * sigma * sigma));
      } else {
        if (dist < 1e-3) {
          weight = 1e3;
        } else if (dist < radius) {
          weight = (1 - dist / radius) ** falloffPower;
        } else {
          weight = 0;
        }
      }
      if (pin.type === "starch") {
        weight = 0;
      }
      weights[v * pins.length + p] = weight;
      totalWeight += weight;
    }
    if (totalWeight > 1e-3) {
      for (let p = 0; p < pins.length; p++) {
        weights[v * pins.length + p] /= totalWeight;
      }
    }
    for (let p = 0; p < pins.length; p++) {
      const pin = pins[p];
      if (pin.type === "starch" && pin.stiffness > 0) {
        const px = pin.position.value.x;
        const py = pin.position.value.y;
        const dx = vx - px;
        const dy = vy - py;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist < pin.radius) {
          const stiffFactor = 1 - pin.stiffness * (1 - dist / pin.radius);
          for (let q = 0; q < pins.length; q++) {
            weights[v * pins.length + q] *= stiffFactor;
          }
        }
      }
    }
  }
  return weights;
}
function evaluatePinAtFrame(pin, frame) {
  const position = interpolateProperty(pin.position, frame);
  const rotation = interpolateProperty(pin.rotation, frame);
  const scale = interpolateProperty(pin.scale, frame);
  return { position, rotation, scale };
}
function deformMesh(mesh, pins, weights, frame) {
  const deformed = new Float32Array(mesh.vertices.length);
  if (pins.length === 0) {
    deformed.set(mesh.vertices);
    return deformed;
  }
  const pinStates = pins.map((pin) => {
    const current = evaluatePinAtFrame(pin, frame);
    const rest = { x: pin.position.value.x, y: pin.position.value.y };
    return {
      pin,
      current,
      rest,
      delta: {
        x: current.position.x - rest.x,
        y: current.position.y - rest.y
      }
    };
  });
  for (let v = 0; v < mesh.vertexCount; v++) {
    const vx = mesh.vertices[v * 2];
    const vy = mesh.vertices[v * 2 + 1];
    let dx = 0;
    let dy = 0;
    for (let p = 0; p < pins.length; p++) {
      const state = pinStates[p];
      const weight = weights[v * pins.length + p];
      if (weight < 1e-4) continue;
      const { pin, current, rest, delta } = state;
      if (pin.type === "overlap") continue;
      let pinDx = 0;
      let pinDy = 0;
      if (pin.type === "position" || pin.type === "advanced") {
        pinDx += delta.x;
        pinDy += delta.y;
      }
      if (pin.type === "bend" || pin.type === "rotation" || pin.type === "advanced") {
        const rotationRad = current.rotation * Math.PI / 180;
        if (Math.abs(rotationRad) > 1e-4) {
          const relX = vx - rest.x;
          const relY = vy - rest.y;
          const cos = Math.cos(rotationRad);
          const sin = Math.sin(rotationRad);
          const rotatedX = relX * cos - relY * sin;
          const rotatedY = relX * sin + relY * cos;
          pinDx += rotatedX - relX;
          pinDy += rotatedY - relY;
        }
      }
      if (pin.type === "bend" || pin.type === "advanced") {
        if (Math.abs(current.scale - 1) > 1e-4) {
          const relX = vx - rest.x;
          const relY = vy - rest.y;
          pinDx += relX * (current.scale - 1);
          pinDy += relY * (current.scale - 1);
        }
      }
      dx += pinDx * weight;
      dy += pinDy * weight;
    }
    deformed[v * 2] = vx + dx;
    deformed[v * 2 + 1] = vy + dy;
  }
  return deformed;
}
function renderTriangle(outputData, inputData, srcA, srcB, srcC, dstA, dstB, dstC) {
  const { width, height, data: dst } = outputData;
  const { width: srcWidth, height: srcHeight, data: src } = inputData;
  const minX = Math.max(0, Math.floor(Math.min(dstA.x, dstB.x, dstC.x)));
  const maxX = Math.min(width - 1, Math.ceil(Math.max(dstA.x, dstB.x, dstC.x)));
  const minY = Math.max(0, Math.floor(Math.min(dstA.y, dstB.y, dstC.y)));
  const maxY = Math.min(
    height - 1,
    Math.ceil(Math.max(dstA.y, dstB.y, dstC.y))
  );
  const denom = (dstB.y - dstC.y) * (dstA.x - dstC.x) + (dstC.x - dstB.x) * (dstA.y - dstC.y);
  if (Math.abs(denom) < 1e-4) return;
  for (let y = minY; y <= maxY; y++) {
    for (let x = minX; x <= maxX; x++) {
      const w1 = ((dstB.y - dstC.y) * (x - dstC.x) + (dstC.x - dstB.x) * (y - dstC.y)) / denom;
      const w2 = ((dstC.y - dstA.y) * (x - dstC.x) + (dstA.x - dstC.x) * (y - dstC.y)) / denom;
      const w3 = 1 - w1 - w2;
      if (w1 < 0 || w2 < 0 || w3 < 0) continue;
      const srcX = w1 * srcA.x + w2 * srcB.x + w3 * srcC.x;
      const srcY = w1 * srcA.y + w2 * srcB.y + w3 * srcC.y;
      if (srcX < 0 || srcX >= srcWidth - 1 || srcY < 0 || srcY >= srcHeight - 1)
        continue;
      const x0 = Math.floor(srcX);
      const y0 = Math.floor(srcY);
      const x1 = Math.min(x0 + 1, srcWidth - 1);
      const y1 = Math.min(y0 + 1, srcHeight - 1);
      const fx = srcX - x0;
      const fy = srcY - y0;
      const i00 = (y0 * srcWidth + x0) * 4;
      const i10 = (y0 * srcWidth + x1) * 4;
      const i01 = (y1 * srcWidth + x0) * 4;
      const i11 = (y1 * srcWidth + x1) * 4;
      const outIdx = (y * width + x) * 4;
      for (let c = 0; c < 4; c++) {
        const v00 = src[i00 + c];
        const v10 = src[i10 + c];
        const v01 = src[i01 + c];
        const v11 = src[i11 + c];
        const value = Math.round(
          v00 * (1 - fx) * (1 - fy) + v10 * fx * (1 - fy) + v01 * (1 - fx) * fy + v11 * fx * fy
        );
        if (c === 3) {
          dst[outIdx + c] = Math.max(dst[outIdx + c], value);
        } else {
          const alpha = value / 255;
          dst[outIdx + c] = Math.round(
            dst[outIdx + c] * (1 - alpha) + value * alpha
          );
        }
      }
    }
  }
}
function calculateTriangleDepths(mesh, deformedVertices, pins, frame) {
  const overlapPins = pins.filter((p) => p.type === "overlap");
  if (overlapPins.length === 0) {
    return Array.from({ length: mesh.triangleCount }, (_, i) => ({
      index: i,
      depth: 0
    }));
  }
  const depths = [];
  for (let t = 0; t < mesh.triangleCount; t++) {
    const i0 = mesh.triangles[t * 3];
    const i1 = mesh.triangles[t * 3 + 1];
    const i2 = mesh.triangles[t * 3 + 2];
    const cx = (deformedVertices[i0 * 2] + deformedVertices[i1 * 2] + deformedVertices[i2 * 2]) / 3;
    const cy = (deformedVertices[i0 * 2 + 1] + deformedVertices[i1 * 2 + 1] + deformedVertices[i2 * 2 + 1]) / 3;
    let totalDepth = 0;
    let totalWeight = 0;
    for (const pin of overlapPins) {
      const inFront = pin.inFront ? interpolateProperty(pin.inFront, frame) : 0;
      const px = pin.position.value.x;
      const py = pin.position.value.y;
      const dx = cx - px;
      const dy = cy - py;
      const dist = Math.sqrt(dx * dx + dy * dy);
      if (dist < pin.radius) {
        const weight = 1 - dist / pin.radius;
        totalDepth += inFront * weight;
        totalWeight += weight;
      }
    }
    const depth = totalWeight > 0 ? totalDepth / totalWeight : 0;
    depths.push({ index: t, depth });
  }
  return depths;
}
function renderDeformedMesh(outputCtx, inputCanvas, mesh, deformedVertices, pins = [], frame = 0, enableOverlap = false) {
  const { width, height } = outputCtx.canvas;
  const inputCtx = inputCanvas.getContext("2d");
  const inputData = inputCtx.getImageData(
    0,
    0,
    inputCanvas.width,
    inputCanvas.height
  );
  const outputData = outputCtx.createImageData(width, height);
  let triangleOrder;
  if (enableOverlap) {
    const depths = calculateTriangleDepths(mesh, deformedVertices, pins, frame);
    depths.sort((a, b) => a.depth - b.depth);
    triangleOrder = depths.map((d) => d.index);
  } else {
    triangleOrder = Array.from({ length: mesh.triangleCount }, (_, i) => i);
  }
  for (const t of triangleOrder) {
    const i0 = mesh.triangles[t * 3];
    const i1 = mesh.triangles[t * 3 + 1];
    const i2 = mesh.triangles[t * 3 + 2];
    const srcA = { x: mesh.vertices[i0 * 2], y: mesh.vertices[i0 * 2 + 1] };
    const srcB = { x: mesh.vertices[i1 * 2], y: mesh.vertices[i1 * 2 + 1] };
    const srcC = { x: mesh.vertices[i2 * 2], y: mesh.vertices[i2 * 2 + 1] };
    const dstA = {
      x: deformedVertices[i0 * 2],
      y: deformedVertices[i0 * 2 + 1]
    };
    const dstB = {
      x: deformedVertices[i1 * 2],
      y: deformedVertices[i1 * 2 + 1]
    };
    const dstC = {
      x: deformedVertices[i2 * 2],
      y: deformedVertices[i2 * 2 + 1]
    };
    renderTriangle(outputData, inputData, srcA, srcB, srcC, dstA, dstB, dstC);
  }
  outputCtx.putImageData(outputData, 0, 0);
}
function renderMeshWireframe(ctx, vertices, triangles, _vertexCount, triangleCount) {
  ctx.strokeStyle = "rgba(0, 255, 0, 0.5)";
  ctx.lineWidth = 1;
  for (let t = 0; t < triangleCount; t++) {
    const i0 = triangles[t * 3];
    const i1 = triangles[t * 3 + 1];
    const i2 = triangles[t * 3 + 2];
    const ax = vertices[i0 * 2];
    const ay = vertices[i0 * 2 + 1];
    const bx = vertices[i1 * 2];
    const by = vertices[i1 * 2 + 1];
    const cx = vertices[i2 * 2];
    const cy = vertices[i2 * 2 + 1];
    ctx.beginPath();
    ctx.moveTo(ax, ay);
    ctx.lineTo(bx, by);
    ctx.lineTo(cx, cy);
    ctx.closePath();
    ctx.stroke();
  }
}
function renderPins(ctx, pins, frame) {
  for (const pin of pins) {
    const { position, rotation} = evaluatePinAtFrame(pin, frame);
    let color;
    switch (pin.type) {
      case "position":
        color = "yellow";
        break;
      case "bend":
        color = "orange";
        break;
      case "starch":
        color = "cyan";
        break;
      case "overlap":
        color = "magenta";
        break;
      case "advanced":
        color = "white";
        break;
      default:
        color = "gray";
    }
    ctx.fillStyle = color;
    ctx.strokeStyle = "black";
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.arc(position.x, position.y, 6, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();
    ctx.strokeStyle = `${color}40`;
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.arc(position.x, position.y, pin.radius, 0, Math.PI * 2);
    ctx.stroke();
    if (pin.type === "bend" || pin.type === "rotation" || pin.type === "advanced") {
      const rad = rotation * Math.PI / 180;
      const indicatorLen = 15;
      ctx.strokeStyle = color;
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.moveTo(position.x, position.y);
      ctx.lineTo(
        position.x + Math.cos(rad) * indicatorLen,
        position.y + Math.sin(rad) * indicatorLen
      );
      ctx.stroke();
    }
  }
}
function meshDeformRenderer(input, params) {
  const effectInstance = params._effectInstance;
  const frame = params._frame ?? 0;
  const showMesh = params.show_mesh ?? false;
  const showPins = params.show_pins ?? true;
  const pins = effectInstance?.pins ?? [];
  if (pins.length === 0) {
    if (showMesh || showPins) {
      const output2 = createMatchingCanvas(input.canvas);
      output2.ctx.drawImage(input.canvas, 0, 0);
      if (showMesh) {
        const effectId2 = effectInstance?.id ?? "temp";
        const { mesh: mesh2 } = getOrGenerateMesh(effectId2, input.canvas, params, []);
        renderMeshWireframe(
          output2.ctx,
          mesh2.vertices,
          mesh2.triangles,
          mesh2.vertexCount,
          mesh2.triangleCount
        );
      }
      return output2;
    }
    return input;
  }
  const effectId = effectInstance?.id ?? `temp-${Date.now()}`;
  const { mesh, weights } = getOrGenerateMesh(
    effectId,
    input.canvas,
    params,
    pins
  );
  const deformedVertices = deformMesh(mesh, pins, weights, frame);
  const enableOverlap = params.enable_overlap ?? false;
  const output = createMatchingCanvas(input.canvas);
  renderDeformedMesh(
    output.ctx,
    input.canvas,
    mesh,
    deformedVertices,
    pins,
    frame,
    enableOverlap
  );
  if (showMesh) {
    renderMeshWireframe(
      output.ctx,
      deformedVertices,
      mesh.triangles,
      mesh.vertexCount,
      mesh.triangleCount
    );
  }
  if (showPins) {
    renderPins(output.ctx, pins, frame);
  }
  return output;
}
function registerMeshDeformEffect() {
  registerEffectRenderer("mesh-deform", meshDeformRenderer);
}

class SeededRandom {
  state;
  initialSeed;
  constructor(seed = 12345) {
    this.initialSeed = seed;
    this.state = seed;
  }
  /** Reset to initial seed */
  reset() {
    this.state = this.initialSeed;
  }
  /** Reset to a new seed */
  setSeed(seed) {
    this.initialSeed = seed;
    this.state = seed;
  }
  /** Get current state for checkpointing */
  getState() {
    return this.state;
  }
  /** Restore state from checkpoint */
  setState(state) {
    this.state = state;
  }
  /** Get initial seed */
  getSeed() {
    return this.initialSeed;
  }
  /**
   * Get next random number in [0, 1)
   * Uses mulberry32 algorithm
   */
  next() {
    let t = this.state += 1831565813;
    t = Math.imul(t ^ t >>> 15, t | 1);
    t ^= t + Math.imul(t ^ t >>> 7, t | 61);
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  }
  /** Get random in range [min, max] */
  range(min, max) {
    return min + this.next() * (max - min);
  }
  /** Get random integer in range [min, max] inclusive */
  int(min, max) {
    return Math.floor(this.range(min, max + 1));
  }
  /** Get random value with variance: base + random(-variance, +variance) */
  variance(base, variance) {
    return base + (this.next() - 0.5) * 2 * variance;
  }
  /** Get random boolean with given probability of true */
  bool(probability = 0.5) {
    return this.next() < probability;
  }
  /** Get random angle in radians [0, 2*PI) */
  angle() {
    return this.next() * Math.PI * 2;
  }
  /** Get random point in unit circle */
  inCircle() {
    const angle = this.angle();
    const r = Math.sqrt(this.next());
    return { x: r * Math.cos(angle), y: r * Math.sin(angle) };
  }
  /** Get random point on unit sphere */
  onSphere() {
    const theta = this.angle();
    const phi = Math.acos(2 * this.next() - 1);
    return {
      x: Math.sin(phi) * Math.cos(theta),
      y: Math.sin(phi) * Math.sin(theta),
      z: Math.cos(phi)
    };
  }
  /**
   * Get random number from Gaussian/normal distribution
   * Uses Box-Muller transform for deterministic gaussian sampling
   */
  gaussian(mean = 0, stdDev = 1) {
    const u1 = this.next();
    const u2 = this.next();
    const z = Math.sqrt(-2 * Math.log(u1 || 1e-10)) * Math.cos(2 * Math.PI * u2);
    return mean + z * stdDev;
  }
}

function pixelSortRenderer(input, params) {
  const direction = params.direction ?? "horizontal";
  const rawThreshold = params.threshold ?? 0.25;
  const threshold = Number.isFinite(rawThreshold) ? rawThreshold : 0.25;
  const rawSmoothing = params.smoothing ?? 0.1;
  const smoothing = Number.isFinite(rawSmoothing) ? rawSmoothing : 0.1;
  const sortBy = params.sort_by ?? "saturation";
  const reverse = params.reverse ?? false;
  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const imageData = input.ctx.getImageData(0, 0, width, height);
  const data = imageData.data;
  const getSortValue = (r, g, b) => {
    const max = Math.max(r, g, b);
    const min = Math.min(r, g, b);
    switch (sortBy) {
      case "brightness":
        return (r + g + b) / 3;
      case "hue": {
        if (max === min) return 0;
        let h = 0;
        if (max === r) h = (g - b) / (max - min);
        else if (max === g) h = 2 + (b - r) / (max - min);
        else h = 4 + (r - g) / (max - min);
        return (h * 60 + 360) % 360;
      }
      default: {
        const l = (max + min) / 2;
        if (max === min) return 0;
        return l > 0.5 ? (max - min) / (2 - max - min) : (max - min) / (max + min);
      }
    }
  };
  const isVertical = direction === "vertical";
  const outerSize = isVertical ? width : height;
  const innerSize = isVertical ? height : width;
  for (let outer = 0; outer < outerSize; outer++) {
    const pixels = [];
    for (let inner = 0; inner < innerSize; inner++) {
      const x = isVertical ? outer : inner;
      const y = isVertical ? inner : outer;
      const idx = (y * width + x) * 4;
      const r = data[idx] / 255;
      const g = data[idx + 1] / 255;
      const b = data[idx + 2] / 255;
      const a = data[idx + 3];
      pixels.push({
        r: data[idx],
        g: data[idx + 1],
        b: data[idx + 2],
        a,
        sortVal: getSortValue(r, g, b)
      });
    }
    const intervals = [];
    let intervalStart = 0;
    for (let i = 1; i < pixels.length; i++) {
      const diff = Math.abs(pixels[i].sortVal - pixels[i - 1].sortVal);
      if (diff > threshold * (1 - smoothing)) {
        if (i > intervalStart + 1) {
          intervals.push({ start: intervalStart, end: i });
        }
        intervalStart = i;
      }
    }
    if (intervalStart < pixels.length - 1) {
      intervals.push({ start: intervalStart, end: pixels.length });
    }
    for (const interval of intervals) {
      const segment = pixels.slice(interval.start, interval.end);
      segment.sort(
        (a, b) => reverse ? b.sortVal - a.sortVal : a.sortVal - b.sortVal
      );
      for (let i = 0; i < segment.length; i++) {
        pixels[interval.start + i] = segment[i];
      }
    }
    for (let inner = 0; inner < innerSize; inner++) {
      const x = isVertical ? outer : inner;
      const y = isVertical ? inner : outer;
      const idx = (y * width + x) * 4;
      data[idx] = pixels[inner].r;
      data[idx + 1] = pixels[inner].g;
      data[idx + 2] = pixels[inner].b;
      data[idx + 3] = pixels[inner].a;
    }
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function glitchRenderer(input, params, frame) {
  const rawGlitchAmount = params.glitch_amount ?? 5;
  const glitchAmount = Number.isFinite(rawGlitchAmount) ? rawGlitchAmount : 5;
  const colorOffset = params.color_offset ?? true;
  const rawBlockSize = params.block_size ?? 8;
  const blockSize = Number.isFinite(rawBlockSize) ? Math.max(1, rawBlockSize) : 8;
  const rawSeed = params.seed ?? 12345;
  const seed = Number.isFinite(rawSeed) ? rawSeed : 12345;
  const scanlines = params.scanlines ?? true;
  if (glitchAmount === 0) return input;
  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  output.ctx.drawImage(input.canvas, 0, 0);
  const imageData = output.ctx.getImageData(0, 0, width, height);
  const data = imageData.data;
  const rng = new SeededRandom(seed + (frame ?? 0));
  const numBlocks = Math.floor(glitchAmount * 3);
  for (let b = 0; b < numBlocks; b++) {
    const y = Math.floor(rng.next() * height);
    const blockHeight = Math.floor(rng.next() * blockSize) + 1;
    const shift = Math.floor((rng.next() - 0.5) * glitchAmount * 20);
    for (let row = y; row < Math.min(y + blockHeight, height); row++) {
      const rowData = [];
      for (let x = 0; x < width; x++) {
        const idx = (row * width + x) * 4;
        rowData.push(data[idx], data[idx + 1], data[idx + 2], data[idx + 3]);
      }
      for (let x = 0; x < width; x++) {
        const srcX = ((x - shift) % width + width) % width;
        const dstIdx = (row * width + x) * 4;
        const srcIdx = srcX * 4;
        data[dstIdx] = rowData[srcIdx];
        data[dstIdx + 1] = rowData[srcIdx + 1];
        data[dstIdx + 2] = rowData[srcIdx + 2];
        data[dstIdx + 3] = rowData[srcIdx + 3];
      }
    }
  }
  if (colorOffset) {
    const offsetX = Math.floor(glitchAmount * 2);
    const outputData = new Uint8ClampedArray(data.length);
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const idx = (y * width + x) * 4;
        const redX = Math.max(0, Math.min(width - 1, x - offsetX));
        const redIdx = (y * width + redX) * 4;
        outputData[idx] = data[redIdx];
        outputData[idx + 1] = data[idx + 1];
        const blueX = Math.max(0, Math.min(width - 1, x + offsetX));
        const blueIdx = (y * width + blueX) * 4;
        outputData[idx + 2] = data[blueIdx + 2];
        outputData[idx + 3] = data[idx + 3];
      }
    }
    for (let i = 0; i < data.length; i++) {
      data[i] = outputData[i];
    }
  }
  if (scanlines) {
    for (let y = 0; y < height; y += 2) {
      if (rng.next() > 0.7) {
        for (let x = 0; x < width; x++) {
          const idx = (y * width + x) * 4;
          data[idx] = Math.min(255, data[idx] * 1.1);
          data[idx + 1] = Math.min(255, data[idx + 1] * 1.1);
          data[idx + 2] = Math.min(255, data[idx + 2] * 1.1);
        }
      }
    }
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function vhsRenderer(input, params, frame) {
  const tracking = params.tracking ?? 0.5;
  const noise = params.noise ?? 0.3;
  const colorBleed = params.color_bleed ?? 3;
  const jitter = params.jitter ?? 0.5;
  const rollingBands = params.rolling_bands ?? true;
  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  output.ctx.drawImage(input.canvas, 0, 0);
  const imageData = output.ctx.getImageData(0, 0, width, height);
  const data = imageData.data;
  const rng = new SeededRandom(12345 + (frame ?? 0));
  if (colorBleed > 0) {
    for (let y = 0; y < height; y++) {
      for (let x = colorBleed; x < width; x++) {
        const idx = (y * width + x) * 4;
        const prevIdx = (y * width + (x - colorBleed)) * 4;
        data[idx] = Math.floor(data[idx] * 0.7 + data[prevIdx] * 0.3);
      }
    }
  }
  if (tracking > 0) {
    const numLines = Math.floor(tracking * 20);
    for (let i = 0; i < numLines; i++) {
      const y = Math.floor(rng.next() * height);
      const lineHeight = Math.floor(rng.next() * 3) + 1;
      const shift = Math.floor((rng.next() - 0.5) * tracking * 30);
      for (let row = y; row < Math.min(y + lineHeight, height); row++) {
        const rowData = [];
        for (let x = 0; x < width; x++) {
          const idx = (row * width + x) * 4;
          rowData.push(data[idx], data[idx + 1], data[idx + 2], data[idx + 3]);
        }
        for (let x = 0; x < width; x++) {
          const srcX = ((x - shift) % width + width) % width;
          const dstIdx = (row * width + x) * 4;
          const srcIdx = srcX * 4;
          data[dstIdx] = rowData[srcIdx];
          data[dstIdx + 1] = rowData[srcIdx + 1];
          data[dstIdx + 2] = rowData[srcIdx + 2];
        }
      }
    }
  }
  if (noise > 0) {
    for (let i = 0; i < data.length; i += 4) {
      if (rng.next() < noise * 0.1) {
        const noiseVal = Math.floor(rng.next() * 255);
        data[i] = noiseVal;
        data[i + 1] = noiseVal;
        data[i + 2] = noiseVal;
      }
    }
  }
  if (rollingBands && frame !== void 0) {
    const bandY = frame * 3 % height;
    const bandHeight = 20;
    for (let y = bandY; y < Math.min(bandY + bandHeight, height); y++) {
      for (let x = 0; x < width; x++) {
        const idx = (y * width + x) * 4;
        const factor = 0.7 + (y - bandY) / bandHeight * 0.3;
        data[idx] = Math.floor(data[idx] * factor);
        data[idx + 1] = Math.floor(data[idx + 1] * factor);
        data[idx + 2] = Math.floor(data[idx + 2] * factor);
      }
    }
  }
  if (jitter > 0) {
    const jitterAmount = Math.floor(rng.next() * jitter * 2);
    if (jitterAmount !== 0) {
      const jitteredData = new Uint8ClampedArray(data.length);
      for (let y = 0; y < height; y++) {
        const srcY = Math.max(0, Math.min(height - 1, y + jitterAmount));
        for (let x = 0; x < width; x++) {
          const dstIdx = (y * width + x) * 4;
          const srcIdx = (srcY * width + x) * 4;
          jitteredData[dstIdx] = data[srcIdx];
          jitteredData[dstIdx + 1] = data[srcIdx + 1];
          jitteredData[dstIdx + 2] = data[srcIdx + 2];
          jitteredData[dstIdx + 3] = data[srcIdx + 3];
        }
      }
      for (let i = 0; i < data.length; i++) {
        data[i] = jitteredData[i];
      }
    }
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function rgbSplitRenderer(input, params) {
  const redOffsetX = params.red_offset_x ?? 5;
  const redOffsetY = params.red_offset_y ?? 0;
  const greenOffsetX = params.green_offset_x ?? 0;
  const greenOffsetY = params.green_offset_y ?? 0;
  const blueOffsetX = params.blue_offset_x ?? -5;
  const blueOffsetY = params.blue_offset_y ?? 0;
  const blendMode = params.blend_mode ?? "screen";
  if (redOffsetX === 0 && redOffsetY === 0 && greenOffsetX === 0 && greenOffsetY === 0 && blueOffsetX === 0 && blueOffsetY === 0) {
    return input;
  }
  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const data = inputData.data;
  const outputData = new Uint8ClampedArray(data.length);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const idx = (y * width + x) * 4;
      const redX = Math.max(0, Math.min(width - 1, x + redOffsetX));
      const redY = Math.max(0, Math.min(height - 1, y + redOffsetY));
      const redIdx = (redY * width + redX) * 4;
      const greenX = Math.max(0, Math.min(width - 1, x + greenOffsetX));
      const greenY = Math.max(0, Math.min(height - 1, y + greenOffsetY));
      const greenIdx = (greenY * width + greenX) * 4;
      const blueX = Math.max(0, Math.min(width - 1, x + blueOffsetX));
      const blueY = Math.max(0, Math.min(height - 1, y + blueOffsetY));
      const blueIdx = (blueY * width + blueX) * 4;
      let r = data[redIdx];
      let g = data[greenIdx + 1];
      let b = data[blueIdx + 2];
      if (blendMode === "screen") {
        r = 255 - (255 - r) * (255 - data[idx]) / 255;
        g = 255 - (255 - g) * (255 - data[idx + 1]) / 255;
        b = 255 - (255 - b) * (255 - data[idx + 2]) / 255;
      } else if (blendMode === "add") {
        r = Math.min(255, r + data[idx] * 0.3);
        g = Math.min(255, g + data[idx + 1] * 0.3);
        b = Math.min(255, b + data[idx + 2] * 0.3);
      }
      outputData[idx] = r;
      outputData[idx + 1] = g;
      outputData[idx + 2] = b;
      outputData[idx + 3] = data[idx + 3];
    }
  }
  const outputImageData = new ImageData(outputData, width, height);
  output.ctx.putImageData(outputImageData, 0, 0);
  return output;
}
function scanlinesRenderer(input, params, frame) {
  const lineWidth = params.line_width ?? 2;
  const lineSpacing = params.line_spacing ?? 2;
  const opacity = params.opacity ?? 0.3;
  const direction = params.direction ?? "horizontal";
  const animate = params.animate ?? false;
  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  output.ctx.drawImage(input.canvas, 0, 0);
  const imageData = output.ctx.getImageData(0, 0, width, height);
  const data = imageData.data;
  const totalWidth = lineWidth + lineSpacing;
  const offset = animate && frame !== void 0 ? frame % totalWidth : 0;
  const isHorizontal = direction === "horizontal";
  const outerSize = isHorizontal ? height : width;
  for (let outer = 0; outer < outerSize; outer++) {
    const adjustedPos = (outer + offset) % totalWidth;
    const inLine = adjustedPos < lineWidth;
    if (inLine) {
      const innerSize = isHorizontal ? width : height;
      for (let inner = 0; inner < innerSize; inner++) {
        const x = isHorizontal ? inner : outer;
        const y = isHorizontal ? outer : inner;
        const idx = (y * width + x) * 4;
        data[idx] = Math.floor(data[idx] * (1 - opacity));
        data[idx + 1] = Math.floor(data[idx + 1] * (1 - opacity));
        data[idx + 2] = Math.floor(data[idx + 2] * (1 - opacity));
      }
    }
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function halftoneRenderer(input, params) {
  const dotSize = Math.max(2, params.dot_size ?? 6);
  const colorMode = params.color_mode ?? "grayscale";
  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const data = inputData.data;
  output.ctx.fillStyle = "#ffffff";
  output.ctx.fillRect(0, 0, width, height);
  for (let gy = 0; gy < height + dotSize; gy += dotSize) {
    for (let gx = 0; gx < width + dotSize; gx += dotSize) {
      const cx = gx + dotSize / 2;
      const cy = gy + dotSize / 2;
      let totalR = 0, totalG = 0, totalB = 0, count = 0;
      for (let sy = gy; sy < Math.min(gy + dotSize, height); sy++) {
        for (let sx = gx; sx < Math.min(gx + dotSize, width); sx++) {
          const idx = (sy * width + sx) * 4;
          totalR += data[idx];
          totalG += data[idx + 1];
          totalB += data[idx + 2];
          count++;
        }
      }
      if (count === 0) continue;
      const avgR = totalR / count;
      const avgG = totalG / count;
      const avgB = totalB / count;
      if (colorMode === "grayscale") {
        const brightness = (avgR + avgG + avgB) / 3 / 255;
        const radius = (1 - brightness) * dotSize / 2;
        if (radius > 0.5) {
          output.ctx.beginPath();
          output.ctx.arc(cx, cy, radius, 0, Math.PI * 2);
          output.ctx.fillStyle = "#000000";
          output.ctx.fill();
        }
      } else if (colorMode === "rgb") {
        const offsets = [
          { color: `rgb(${Math.floor(avgR)}, 0, 0)`, dx: -1, dy: 0 },
          { color: `rgb(0, ${Math.floor(avgG)}, 0)`, dx: 0, dy: 1 },
          { color: `rgb(0, 0, ${Math.floor(avgB)})`, dx: 1, dy: 0 }
        ];
        for (const { color, dx, dy } of offsets) {
          const brightness = color === offsets[0].color ? avgR : color === offsets[1].color ? avgG : avgB;
          const radius = brightness / 255 * dotSize / 3;
          if (radius > 0.3) {
            output.ctx.beginPath();
            output.ctx.arc(cx + dx * 2, cy + dy * 2, radius, 0, Math.PI * 2);
            output.ctx.fillStyle = color;
            output.ctx.globalCompositeOperation = "multiply";
            output.ctx.fill();
            output.ctx.globalCompositeOperation = "source-over";
          }
        }
      } else if (colorMode === "cmyk") {
        const r = avgR / 255, g = avgG / 255, b = avgB / 255;
        const k = 1 - Math.max(r, g, b);
        const c = k < 1 ? (1 - r - k) / (1 - k) : 0;
        const m = k < 1 ? (1 - g - k) / (1 - k) : 0;
        const y = k < 1 ? (1 - b - k) / (1 - k) : 0;
        const cmykColors = [
          { val: c, color: "cyan", angle: 15 },
          { val: m, color: "magenta", angle: 75 },
          { val: y, color: "yellow", angle: 0 },
          { val: k, color: "black", angle: 45 }
        ];
        for (const { val, color, angle: a } of cmykColors) {
          const radius = val * dotSize / 2;
          if (radius > 0.3) {
            const da = a * Math.PI / 180;
            const dcx = cx + Math.cos(da) * dotSize * 0.1;
            const dcy = cy + Math.sin(da) * dotSize * 0.1;
            output.ctx.beginPath();
            output.ctx.arc(dcx, dcy, radius, 0, Math.PI * 2);
            output.ctx.fillStyle = color;
            output.ctx.globalCompositeOperation = "multiply";
            output.ctx.fill();
            output.ctx.globalCompositeOperation = "source-over";
          }
        }
      }
    }
  }
  return output;
}
function ditherRenderer(input, params) {
  const method = params.method ?? "ordered";
  const levels = Math.max(2, Math.min(256, params.levels ?? 4));
  const matrixSize = params.matrix_size ?? 4;
  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const imageData = input.ctx.getImageData(0, 0, width, height);
  const data = new Float32Array(imageData.data.length);
  for (let i = 0; i < imageData.data.length; i++) {
    data[i] = imageData.data[i];
  }
  const bayer2 = [
    [0, 2],
    [3, 1]
  ];
  const bayer4 = [
    [0, 8, 2, 10],
    [12, 4, 14, 6],
    [3, 11, 1, 9],
    [15, 7, 13, 5]
  ];
  const bayer8 = [
    [0, 32, 8, 40, 2, 34, 10, 42],
    [48, 16, 56, 24, 50, 18, 58, 26],
    [12, 44, 4, 36, 14, 46, 6, 38],
    [60, 28, 52, 20, 62, 30, 54, 22],
    [3, 35, 11, 43, 1, 33, 9, 41],
    [51, 19, 59, 27, 49, 17, 57, 25],
    [15, 47, 7, 39, 13, 45, 5, 37],
    [63, 31, 55, 23, 61, 29, 53, 21]
  ];
  const matrix = matrixSize === 2 ? bayer2 : matrixSize === 8 ? bayer8 : bayer4;
  const matrixMax = matrixSize * matrixSize;
  const quantize = (val) => {
    const step = 255 / (levels - 1);
    return Math.round(val / step) * step;
  };
  if (method === "ordered") {
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const idx = (y * width + x) * 4;
        const threshold = (matrix[y % matrix.length][x % matrix[0].length] / matrixMax - 0.5) * (256 / levels);
        for (let c = 0; c < 3; c++) {
          data[idx + c] = quantize(
            Math.max(0, Math.min(255, data[idx + c] + threshold))
          );
        }
      }
    }
  } else if (method === "floyd_steinberg") {
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const idx = (y * width + x) * 4;
        for (let c = 0; c < 3; c++) {
          const oldVal = data[idx + c];
          const newVal = quantize(oldVal);
          data[idx + c] = newVal;
          const error = oldVal - newVal;
          if (x + 1 < width) {
            data[(y * width + x + 1) * 4 + c] += error * 7 / 16;
          }
          if (y + 1 < height) {
            if (x > 0) {
              data[((y + 1) * width + x - 1) * 4 + c] += error * 3 / 16;
            }
            data[((y + 1) * width + x) * 4 + c] += error * 5 / 16;
            if (x + 1 < width) {
              data[((y + 1) * width + x + 1) * 4 + c] += error * 1 / 16;
            }
          }
        }
      }
    }
  } else if (method === "atkinson") {
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const idx = (y * width + x) * 4;
        for (let c = 0; c < 3; c++) {
          const oldVal = data[idx + c];
          const newVal = quantize(oldVal);
          data[idx + c] = newVal;
          const error = (oldVal - newVal) / 8;
          const offsets = [
            [1, 0],
            [2, 0],
            [-1, 1],
            [0, 1],
            [1, 1],
            [0, 2]
          ];
          for (const [dx, dy] of offsets) {
            const nx = x + dx;
            const ny = y + dy;
            if (nx >= 0 && nx < width && ny < height) {
              data[(ny * width + nx) * 4 + c] += error;
            }
          }
        }
      }
    }
  }
  for (let i = 0; i < data.length; i++) {
    imageData.data[i] = Math.max(0, Math.min(255, Math.round(data[i])));
  }
  output.ctx.putImageData(imageData, 0, 0);
  return output;
}
function rippleRenderer(input, params, frame) {
  const amplitude = params.amplitude ?? 10;
  const wavelength = params.wavelength ?? 50;
  let phase = params.phase ?? 0;
  const centerX = (params.center_x ?? 50) / 100;
  const centerY = (params.center_y ?? 50) / 100;
  const decay = params.decay ?? 0.5;
  if (frame !== void 0 && params.animate !== false) {
    phase = (phase + frame * 5) % 360;
  }
  const phaseRad = phase * Math.PI / 180;
  if (amplitude === 0) return input;
  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const outputData = output.ctx.createImageData(width, height);
  const srcData = inputData.data;
  const dstData = outputData.data;
  const cx = centerX * width;
  const cy = centerY * height;
  const maxDist = Math.sqrt(width * width + height * height) / 2;
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const dx = x - cx;
      const dy = y - cy;
      const dist = Math.sqrt(dx * dx + dy * dy);
      const decayFactor = decay > 0 ? Math.exp(-dist / maxDist * decay * 5) : 1;
      const wave = Math.sin(dist / wavelength * Math.PI * 2 + phaseRad) * amplitude * decayFactor;
      const angle = Math.atan2(dy, dx);
      const srcX = Math.round(x + Math.cos(angle) * wave);
      const srcY = Math.round(y + Math.sin(angle) * wave);
      const sx = Math.max(0, Math.min(width - 1, srcX));
      const sy = Math.max(0, Math.min(height - 1, srcY));
      const srcIdx = (sy * width + sx) * 4;
      const dstIdx = (y * width + x) * 4;
      dstData[dstIdx] = srcData[srcIdx];
      dstData[dstIdx + 1] = srcData[srcIdx + 1];
      dstData[dstIdx + 2] = srcData[srcIdx + 2];
      dstData[dstIdx + 3] = srcData[srcIdx + 3];
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function embossRenderer(input, params) {
  const direction = (params.direction ?? 135) * Math.PI / 180;
  const height = Math.max(1, params.height ?? 3);
  const amount = params.amount ?? 100;
  const output = createMatchingCanvas(input.canvas);
  const { width, height: h } = input.canvas;
  const inputData = input.ctx.getImageData(0, 0, width, h);
  const outputData = output.ctx.createImageData(width, h);
  const src = inputData.data;
  const dst = outputData.data;
  const dx = Math.round(Math.cos(direction) * height);
  const dy = Math.round(Math.sin(direction) * height);
  const factor = amount / 100;
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < width; x++) {
      const idx = (y * width + x) * 4;
      const x1 = Math.max(0, Math.min(width - 1, x - dx));
      const y1 = Math.max(0, Math.min(h - 1, y - dy));
      const x2 = Math.max(0, Math.min(width - 1, x + dx));
      const y2 = Math.max(0, Math.min(h - 1, y + dy));
      const idx1 = (y1 * width + x1) * 4;
      const idx2 = (y2 * width + x2) * 4;
      for (let c = 0; c < 3; c++) {
        const diff = (src[idx1 + c] - src[idx2 + c]) * factor;
        dst[idx + c] = Math.max(0, Math.min(255, 128 + diff));
      }
      dst[idx + 3] = src[idx + 3];
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function findEdgesRenderer(input, params) {
  const invert = params.invert ?? false;
  const blend = (params.blend_with_original ?? 0) / 100;
  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const outputData = output.ctx.createImageData(width, height);
  const src = inputData.data;
  const dst = outputData.data;
  const sobelX = [-1, 0, 1, -2, 0, 2, -1, 0, 1];
  const sobelY = [-1, -2, -1, 0, 0, 0, 1, 2, 1];
  for (let y = 1; y < height - 1; y++) {
    for (let x = 1; x < width - 1; x++) {
      let gxR = 0, gyR = 0;
      let gxG = 0, gyG = 0;
      let gxB = 0, gyB = 0;
      for (let ky = -1; ky <= 1; ky++) {
        for (let kx = -1; kx <= 1; kx++) {
          const idx2 = ((y + ky) * width + (x + kx)) * 4;
          const ki = (ky + 1) * 3 + (kx + 1);
          gxR += src[idx2] * sobelX[ki];
          gyR += src[idx2] * sobelY[ki];
          gxG += src[idx2 + 1] * sobelX[ki];
          gyG += src[idx2 + 1] * sobelY[ki];
          gxB += src[idx2 + 2] * sobelX[ki];
          gyB += src[idx2 + 2] * sobelY[ki];
        }
      }
      const idx = (y * width + x) * 4;
      let magR = Math.sqrt(gxR * gxR + gyR * gyR);
      let magG = Math.sqrt(gxG * gxG + gyG * gyG);
      let magB = Math.sqrt(gxB * gxB + gyB * gyB);
      if (invert) {
        magR = 255 - magR;
        magG = 255 - magG;
        magB = 255 - magB;
      }
      dst[idx] = Math.min(255, magR * (1 - blend) + src[idx] * blend);
      dst[idx + 1] = Math.min(255, magG * (1 - blend) + src[idx + 1] * blend);
      dst[idx + 2] = Math.min(255, magB * (1 - blend) + src[idx + 2] * blend);
      dst[idx + 3] = src[idx + 3];
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
function mosaicRenderer(input, params) {
  const hBlocks = Math.max(2, params.horizontal_blocks ?? 10);
  const vBlocks = Math.max(2, params.vertical_blocks ?? 10);
  const sharp = params.sharp_corners ?? true;
  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const src = inputData.data;
  const blockW = width / hBlocks;
  const blockH = height / vBlocks;
  output.ctx.imageSmoothingEnabled = !sharp;
  for (let by = 0; by < vBlocks; by++) {
    for (let bx = 0; bx < hBlocks; bx++) {
      const x1 = Math.floor(bx * blockW);
      const y1 = Math.floor(by * blockH);
      const x2 = Math.floor((bx + 1) * blockW);
      const y2 = Math.floor((by + 1) * blockH);
      let totalR = 0, totalG = 0, totalB = 0, count = 0;
      for (let y = y1; y < y2 && y < height; y++) {
        for (let x = x1; x < x2 && x < width; x++) {
          const idx = (y * width + x) * 4;
          totalR += src[idx];
          totalG += src[idx + 1];
          totalB += src[idx + 2];
          count++;
        }
      }
      if (count > 0) {
        output.ctx.fillStyle = `rgb(${Math.round(totalR / count)}, ${Math.round(totalG / count)}, ${Math.round(totalB / count)})`;
        output.ctx.fillRect(x1, y1, x2 - x1, y2 - y1);
      }
    }
  }
  return output;
}
function registerStylizeEffects() {
  registerEffectRenderer("pixel-sort", pixelSortRenderer);
  registerEffectRenderer("glitch", glitchRenderer);
  registerEffectRenderer("vhs", vhsRenderer);
  registerEffectRenderer("rgb-split", rgbSplitRenderer);
  registerEffectRenderer("scanlines", scanlinesRenderer);
  registerEffectRenderer("halftone", halftoneRenderer);
  registerEffectRenderer("dither", ditherRenderer);
  registerEffectRenderer("ripple", rippleRenderer);
  registerEffectRenderer("emboss", embossRenderer);
  registerEffectRenderer("find-edges", findEdgesRenderer);
  registerEffectRenderer("mosaic", mosaicRenderer);
}

class TimeEffectFrameBuffer {
  buffer = [];
  maxFrames = 64;
  // Max stored frames
  layerId = "";
  /**
   * Set the layer this buffer is associated with
   */
  setLayer(layerId) {
    if (this.layerId !== layerId) {
      this.clear();
      this.layerId = layerId;
    }
  }
  /**
   * Store a frame in the buffer.
   * Uses frame number for timestamp instead of Date.now() for determinism.
   */
  store(frame, canvas) {
    const ctx = canvas.getContext("2d");
    if (!ctx) return;
    const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
    this.buffer = this.buffer.filter((e) => e.frame !== frame);
    this.buffer.push({
      imageData,
      frame,
      storedAtFrame: frame
      // Frame-based timestamp for determinism
    });
    while (this.buffer.length > this.maxFrames) {
      this.buffer.shift();
    }
  }
  /**
   * Get a frame from the buffer
   * Returns null if frame not found
   */
  get(frame) {
    const entry = this.buffer.find((e) => e.frame === frame);
    return entry ? entry.imageData : null;
  }
  /**
   * Get the closest frame to the target
   */
  getClosest(targetFrame) {
    if (this.buffer.length === 0) return null;
    let closest = this.buffer[0];
    let minDist = Math.abs(closest.frame - targetFrame);
    for (const entry of this.buffer) {
      const dist = Math.abs(entry.frame - targetFrame);
      if (dist < minDist) {
        minDist = dist;
        closest = entry;
      }
    }
    return { imageData: closest.imageData, frame: closest.frame };
  }
  /**
   * Get multiple frames for echo effect
   * Returns frames at specified time offsets
   */
  getEchoFrames(currentFrame, echoTimeFrames, numEchoes) {
    const results = [];
    for (let i = 1; i <= numEchoes; i++) {
      const targetFrame = Math.round(currentFrame + echoTimeFrames * i);
      const entry = this.getClosest(targetFrame);
      if (entry) {
        results.push({ ...entry, echoIndex: i });
      }
    }
    return results;
  }
  /**
   * Clear the buffer
   */
  clear() {
    this.buffer = [];
  }
  /**
   * Remove old entries based on frame distance.
   * Uses frame-based cleanup instead of wall-clock time for determinism.
   */
  cleanup(currentFrame) {
    const maxFrameDistance = this.maxFrames * 2;
    this.buffer = this.buffer.filter(
      (e) => Math.abs(currentFrame - e.storedAtFrame) < maxFrameDistance
    );
  }
  /**
   * Get buffer statistics
   */
  getStats() {
    if (this.buffer.length === 0) {
      return { frames: 0, oldestFrame: -1, newestFrame: -1 };
    }
    const frames = this.buffer.map((e) => e.frame);
    return {
      frames: this.buffer.length,
      oldestFrame: Math.min(...frames),
      newestFrame: Math.max(...frames)
    };
  }
}
const frameBuffers = /* @__PURE__ */ new Map();
function getFrameBuffer(layerId) {
  let buffer = frameBuffers.get(layerId);
  if (!buffer) {
    buffer = new TimeEffectFrameBuffer();
    buffer.setLayer(layerId);
    frameBuffers.set(layerId, buffer);
  }
  return buffer;
}
function echoRenderer(input, params) {
  const frame = params._frame ?? 0;
  const fps = Number.isFinite(params._fps) && params._fps > 0 ? params._fps : 16;
  const rawEchoTime = params.echo_time ?? -1 / fps;
  const echoTime = Number.isFinite(rawEchoTime) ? rawEchoTime : -1 / fps;
  const rawNumEchoes = params.number_of_echoes ?? 8;
  const numEchoes = Number.isFinite(rawNumEchoes) ? Math.max(1, Math.min(50, rawNumEchoes)) : 8;
  const rawIntensity = params.starting_intensity ?? 1;
  const startingIntensity = Number.isFinite(rawIntensity) ? Math.max(0, Math.min(1, rawIntensity)) : 1;
  const rawDecay = params.decay ?? 0.5;
  const decay = Number.isFinite(rawDecay) ? Math.max(0, Math.min(1, rawDecay)) : 0.5;
  const operator = params.echo_operator ?? "add";
  const layerId = params._layerId ?? "default";
  const echoTimeFrames = echoTime * fps;
  const buffer = getFrameBuffer(layerId);
  buffer.store(frame, input.canvas);
  if (numEchoes === 0 || startingIntensity === 0) {
    return input;
  }
  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  if (operator === "composite_back") {
    output.ctx.clearRect(0, 0, width, height);
  } else {
    output.ctx.drawImage(input.canvas, 0, 0);
  }
  const echoFrames = buffer.getEchoFrames(frame, echoTimeFrames, numEchoes);
  const intensities = [];
  for (let i = 0; i < numEchoes; i++) {
    intensities.push(startingIntensity * (1 - decay) ** i);
  }
  for (const echoData of echoFrames) {
    const intensity = intensities[echoData.echoIndex - 1] ?? 0;
    if (intensity <= 1e-3) continue;
    const tempCanvas = document.createElement("canvas");
    tempCanvas.width = width;
    tempCanvas.height = height;
    const tempCtx = tempCanvas.getContext("2d");
    tempCtx.putImageData(echoData.imageData, 0, 0);
    switch (operator) {
      case "add":
        output.ctx.globalCompositeOperation = "lighter";
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;
      case "screen":
        output.ctx.globalCompositeOperation = "screen";
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;
      case "maximum":
        output.ctx.globalCompositeOperation = "lighten";
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;
      case "minimum":
        output.ctx.globalCompositeOperation = "darken";
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;
      case "composite_back":
        output.ctx.globalCompositeOperation = "destination-over";
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;
      case "composite_front":
        output.ctx.globalCompositeOperation = "source-over";
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;
      default:
        output.ctx.globalCompositeOperation = "source-over";
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;
    }
  }
  output.ctx.globalCompositeOperation = "source-over";
  output.ctx.globalAlpha = 1;
  if (operator === "composite_back") {
    output.ctx.drawImage(input.canvas, 0, 0);
  }
  return output;
}
function posterizeTimeRenderer(input, params) {
  const rawTargetFps = params.frame_rate ?? 12;
  const targetFps = Number.isFinite(rawTargetFps) ? Math.max(1, Math.min(60, rawTargetFps)) : 12;
  const frame = params._frame ?? 0;
  const fps = Number.isFinite(params._fps) && params._fps > 0 ? params._fps : 16;
  const layerId = params._layerId ?? "default";
  const frameRatio = fps / targetFps;
  const posterizedFrame = Math.floor(frame / frameRatio) * frameRatio;
  const buffer = getFrameBuffer(layerId);
  buffer.store(frame, input.canvas);
  if (Math.abs(frame - posterizedFrame) < 0.5) {
    return input;
  }
  const heldFrame = buffer.getClosest(posterizedFrame);
  if (heldFrame) {
    const output = createMatchingCanvas(input.canvas);
    output.ctx.putImageData(heldFrame.imageData, 0, 0);
    return output;
  }
  return input;
}
function generateTimeDisplacementMap(width, height, mapType, scale) {
  const map = new Float32Array(width * height);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = y * width + x;
      let value = 0;
      switch (mapType) {
        case "gradient-h":
          value = x / width;
          break;
        case "gradient-v":
          value = y / height;
          break;
        case "radial": {
          const cx = width / 2;
          const cy = height / 2;
          const dist = Math.sqrt((x - cx) ** 2 + (y - cy) ** 2);
          const maxDist = Math.sqrt(cx ** 2 + cy ** 2);
          value = dist / maxDist;
          break;
        }
        case "sine-h":
          value = 0.5 + 0.5 * Math.sin(x / width * Math.PI * 2 * scale);
          break;
        case "sine-v":
          value = 0.5 + 0.5 * Math.sin(y / height * Math.PI * 2 * scale);
          break;
        case "diagonal":
          value = (x / width + y / height) / 2;
          break;
        case "center-out": {
          const cx2 = width / 2;
          const cy2 = height / 2;
          const dist2 = Math.sqrt((x - cx2) ** 2 + (y - cy2) ** 2);
          const maxDist2 = Math.sqrt(cx2 ** 2 + cy2 ** 2);
          value = 1 - dist2 / maxDist2;
          break;
        }
        default:
          value = 0.5;
      }
      map[i] = value;
    }
  }
  return map;
}
function timeDisplacementRenderer(input, params) {
  const rawMaxDisplacement = params.max_displacement ?? 10;
  const maxDisplacement = Number.isFinite(rawMaxDisplacement) ? rawMaxDisplacement : 10;
  const mapType = params.map_type ?? "gradient-h";
  const rawMapScale = params.map_scale ?? 1;
  const mapScale = Number.isFinite(rawMapScale) ? rawMapScale : 1;
  const rawBias = params.time_offset_bias ?? 0;
  const bias = Number.isFinite(rawBias) ? rawBias : 0;
  const frame = params._frame ?? 0;
  const layerId = params._layerId ?? "default";
  if (maxDisplacement === 0) {
    return input;
  }
  const { width, height } = input.canvas;
  const buffer = getFrameBuffer(layerId);
  buffer.store(frame, input.canvas);
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const dispMap = generateTimeDisplacementMap(width, height, mapType, mapScale);
  const output = createMatchingCanvas(input.canvas);
  const outputData = output.ctx.createImageData(width, height);
  const dst = outputData.data;
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = y * width + x;
      const pixelIdx = i * 4;
      const dispValue = dispMap[i];
      const biasedValue = dispValue + bias;
      const frameOffset = Math.round((biasedValue - 0.5) * 2 * maxDisplacement);
      const targetFrame = frame + frameOffset;
      const frameData = buffer.get(targetFrame);
      if (frameData) {
        dst[pixelIdx] = frameData.data[pixelIdx];
        dst[pixelIdx + 1] = frameData.data[pixelIdx + 1];
        dst[pixelIdx + 2] = frameData.data[pixelIdx + 2];
        dst[pixelIdx + 3] = frameData.data[pixelIdx + 3];
      } else {
        dst[pixelIdx] = inputData.data[pixelIdx];
        dst[pixelIdx + 1] = inputData.data[pixelIdx + 1];
        dst[pixelIdx + 2] = inputData.data[pixelIdx + 2];
        dst[pixelIdx + 3] = inputData.data[pixelIdx + 3];
      }
    }
  }
  output.ctx.putImageData(outputData, 0, 0);
  return output;
}
const frozenFrames = /* @__PURE__ */ new Map();
function freezeFrameRenderer(input, params) {
  const freezeAtFrame = Math.max(0, Math.round(params.freeze_at_frame ?? 0));
  const frame = params._frame ?? 0;
  const layerId = params._layerId ?? "default";
  const cacheKey = `${layerId}_freeze`;
  const buffer = getFrameBuffer(layerId);
  buffer.store(frame, input.canvas);
  const cached = frozenFrames.get(cacheKey);
  if (cached && cached.frame === freezeAtFrame) {
    const output = createMatchingCanvas(input.canvas);
    output.ctx.putImageData(cached.imageData, 0, 0);
    return output;
  }
  if (frame === freezeAtFrame) {
    const { width, height } = input.canvas;
    const imageData = input.ctx.getImageData(0, 0, width, height);
    frozenFrames.set(cacheKey, { frame: freezeAtFrame, imageData });
    return input;
  }
  const frozenImageData = buffer.get(freezeAtFrame);
  if (frozenImageData) {
    frozenFrames.set(cacheKey, {
      frame: freezeAtFrame,
      imageData: frozenImageData
    });
    const output = createMatchingCanvas(input.canvas);
    output.ctx.putImageData(frozenImageData, 0, 0);
    return output;
  }
  return input;
}
function registerTimeEffects() {
  registerEffectRenderer("echo", echoRenderer);
  registerEffectRenderer("posterize-time", posterizeTimeRenderer);
  registerEffectRenderer("freeze-frame", freezeFrameRenderer);
  registerEffectRenderer("time-displacement", timeDisplacementRenderer);
}

function initializeEffects() {
  registerBlurEffects();
  registerColorEffects();
  registerDistortEffects();
  registerGenerateEffects();
  registerTimeEffects();
  registerStylizeEffects();
  registerAudioVisualizerEffects();
  registerExpressionControlRenderers();
  registerCinematicBloomEffects();
  registerMeshDeformEffect();
}

let appInstance = null;
let effectsInitialized = false;
let sesInitialized = false;
let sesInitPromise = null;
let bridgeHandler = null;
let cleanupInterval = null;
const CLEANUP_INTERVAL_MS = 6e4;
async function initializeSecuritySandbox() {
  if (sesInitialized) return;
  if (!sesInitPromise) {
    sesInitPromise = (async () => {
      try {
        await initializeSES();
        sesInitialized = true;
      } catch (error) {
        sesInitialized = true;
        console.error(
          "[Security] Expression security initialization error:",
          error
        );
      }
    })();
  }
  await sesInitPromise;
}
function initializeEffectsOnce() {
  if (effectsInitialized) return;
  initializeEffects();
  effectsInitialized = true;
}
function setupBridge() {
  if (bridgeHandler) return;
  bridgeHandler = (e) => {
    window.dispatchEvent(
      new CustomEvent("lattice:load-project-inputs", { detail: e.detail })
    );
  };
  window.addEventListener("lattice:inputs-ready", bridgeHandler);
}
function teardownBridge() {
  if (!bridgeHandler) return;
  window.removeEventListener("lattice:inputs-ready", bridgeHandler);
  bridgeHandler = null;
}
async function mountApp(container) {
  if (appInstance) {
    unmountApp();
  }
  let el = null;
  if (typeof container === "string") {
    el = document.getElementById(container) || document.querySelector(container);
  } else if (container instanceof HTMLElement) {
    el = container;
  }
  if (!el) {
    console.error("[Lattice] mountApp failed: container not found");
    return null;
  }
  await initializeSecuritySandbox();
  initializeEffectsOnce();
  const app = createApp(_sfc_main);
  app.use(createPinia());
  app.mount(el);
  appInstance = app;
  setupBridge();
  if (!cleanupInterval) {
    cleanupInterval = setInterval(cleanupEffectResources, CLEANUP_INTERVAL_MS);
  }
  return app;
}
function unmountApp() {
  if (!appInstance) return;
  try {
    teardownBridge();
    appInstance.unmount();
    if (cleanupInterval) {
      clearInterval(cleanupInterval);
      cleanupInterval = null;
    }
    cleanupEffectResources();
  } catch (error) {
    console.error("[Lattice] unmount failed:", error);
  } finally {
    appInstance = null;
  }
}
async function sendToComfyUI(matte, preview) {
  const bridge = window.LatticeCompositor;
  if (!bridge?.sendOutput) {
    console.warn("[Lattice] sendToComfyUI called before backend bridge ready");
    return false;
  }
  return bridge.sendOutput(matte, preview);
}

export { mountApp, sendToComfyUI, unmountApp };
