/**
 * GLSL Shader Engine
 *
 * Provides GPU-accelerated image processing using WebGL shaders.
 * Shadertoy-compatible uniform system for easy shader authoring.
 *
 * Acknowledgement: Inspired by Jovi/Amorano's Jovi_GLSL
 * https://github.com/Amorano/Jovi_GLSL
 *
 * Features:
 * - Dynamic shader compilation
 * - Shadertoy-compatible uniforms (iResolution, iTime, iFrame, etc.)
 * - Edge handling modes (clamp, wrap, mirror)
 * - Custom shader support
 * - 10x+ speedup over CPU processing
 */

// ============================================================================
// TYPES
// ============================================================================

export interface ShaderUniforms {
  // Shadertoy-compatible uniforms
  iResolution: [number, number, number]; // width, height, pixelAspectRatio
  iTime: number; // Shader playback time (seconds)
  iTimeDelta: number; // Time since last frame
  iFrame: number; // Frame number
  iMouse: [number, number, number, number]; // xy = position, zw = click position
  iDate: [number, number, number, number]; // year, month, day, seconds
  iSampleRate: number; // Audio sample rate (44100)

  // Custom uniforms
  [key: string]: number | number[] | boolean | WebGLTexture;
}

export interface ShaderCompileResult {
  success: boolean;
  program: WebGLProgram | null;
  error?: string;
  errorLine?: number;
}

export type EdgeMode = "clamp" | "wrap" | "mirror";

export interface GLSLEngineOptions {
  preserveDrawingBuffer?: boolean;
  alpha?: boolean;
  premultipliedAlpha?: boolean;
}

// ============================================================================
// SHADER TEMPLATES
// ============================================================================

const DEFAULT_VERTEX_SHADER = `
attribute vec2 a_position;
attribute vec2 a_texCoord;
varying vec2 v_texCoord;
varying vec2 fragCoord;
uniform vec3 iResolution;

void main() {
  gl_Position = vec4(a_position, 0.0, 1.0);
  v_texCoord = a_texCoord;
  fragCoord = a_texCoord * iResolution.xy;
}
`;

const SHADER_HEADER = `
precision highp float;

// Shadertoy-compatible uniforms
uniform vec3 iResolution;      // viewport resolution (pixels)
uniform float iTime;           // shader playback time (seconds)
uniform float iTimeDelta;      // render time (seconds)
uniform int iFrame;            // frame number
uniform vec4 iMouse;           // mouse pixel coords
uniform vec4 iDate;            // year, month, day, time in seconds
uniform float iSampleRate;     // sound sample rate
uniform sampler2D iChannel0;   // input texture

// Texture coordinate from vertex shader
varying vec2 v_texCoord;
varying vec2 fragCoord;
`;

const SHADER_FOOTER = `
void main() {
  vec4 fragColor;
  mainImage(fragColor, fragCoord);
  gl_FragColor = fragColor;
}
`;

// ============================================================================
// BUILT-IN SHADER FUNCTIONS
// ============================================================================

export const GLSL_LIBRARY = `
// ============================================================================
// MATH UTILITIES
// ============================================================================

#define PI 3.14159265359
#define TAU 6.28318530718
#define E 2.71828182846

float map(float value, float min1, float max1, float min2, float max2) {
  return min2 + (value - min1) * (max2 - min2) / (max1 - min1);
}

float saturate(float x) {
  return clamp(x, 0.0, 1.0);
}

vec3 saturate3(vec3 x) {
  return clamp(x, 0.0, 1.0);
}

// ============================================================================
// NOISE FUNCTIONS
// ============================================================================

// Hash function for noise
float hash(float n) {
  return fract(sin(n) * 43758.5453123);
}

float hash2(vec2 p) {
  return fract(sin(dot(p, vec2(12.9898, 78.233))) * 43758.5453);
}

vec2 hash22(vec2 p) {
  p = vec2(dot(p, vec2(127.1, 311.7)), dot(p, vec2(269.5, 183.3)));
  return -1.0 + 2.0 * fract(sin(p) * 43758.5453123);
}

// Value noise
float noise(vec2 p) {
  vec2 i = floor(p);
  vec2 f = fract(p);
  f = f * f * (3.0 - 2.0 * f); // Smoothstep

  float a = hash2(i);
  float b = hash2(i + vec2(1.0, 0.0));
  float c = hash2(i + vec2(0.0, 1.0));
  float d = hash2(i + vec2(1.0, 1.0));

  return mix(mix(a, b, f.x), mix(c, d, f.x), f.y);
}

// Simplex noise 2D
vec3 mod289(vec3 x) { return x - floor(x * (1.0 / 289.0)) * 289.0; }
vec2 mod289_2(vec2 x) { return x - floor(x * (1.0 / 289.0)) * 289.0; }
vec3 permute(vec3 x) { return mod289(((x * 34.0) + 1.0) * x); }

float snoise(vec2 v) {
  const vec4 C = vec4(0.211324865405187, 0.366025403784439, -0.577350269189626, 0.024390243902439);
  vec2 i = floor(v + dot(v, C.yy));
  vec2 x0 = v - i + dot(i, C.xx);
  vec2 i1 = (x0.x > x0.y) ? vec2(1.0, 0.0) : vec2(0.0, 1.0);
  vec4 x12 = x0.xyxy + C.xxzz;
  x12.xy -= i1;
  i = mod289_2(i);
  vec3 p = permute(permute(i.y + vec3(0.0, i1.y, 1.0)) + i.x + vec3(0.0, i1.x, 1.0));
  vec3 m = max(0.5 - vec3(dot(x0, x0), dot(x12.xy, x12.xy), dot(x12.zw, x12.zw)), 0.0);
  m = m * m;
  m = m * m;
  vec3 x = 2.0 * fract(p * C.www) - 1.0;
  vec3 h = abs(x) - 0.5;
  vec3 ox = floor(x + 0.5);
  vec3 a0 = x - ox;
  m *= 1.79284291400159 - 0.85373472095314 * (a0 * a0 + h * h);
  vec3 g;
  g.x = a0.x * x0.x + h.x * x0.y;
  g.yz = a0.yz * x12.xz + h.yz * x12.yw;
  return 130.0 * dot(m, g);
}

// Fractal Brownian Motion
float fbm(vec2 p, int octaves) {
  float value = 0.0;
  float amplitude = 0.5;
  float frequency = 1.0;
  for (int i = 0; i < 8; i++) {
    if (i >= octaves) break;
    value += amplitude * snoise(p * frequency);
    frequency *= 2.0;
    amplitude *= 0.5;
  }
  return value;
}

// ============================================================================
// COLOR SPACE CONVERSIONS
// ============================================================================

// RGB to HSV
vec3 rgb2hsv(vec3 c) {
  vec4 K = vec4(0.0, -1.0 / 3.0, 2.0 / 3.0, -1.0);
  vec4 p = mix(vec4(c.bg, K.wz), vec4(c.gb, K.xy), step(c.b, c.g));
  vec4 q = mix(vec4(p.xyw, c.r), vec4(c.r, p.yzx), step(p.x, c.r));
  float d = q.x - min(q.w, q.y);
  float e = 1.0e-10;
  return vec3(abs(q.z + (q.w - q.y) / (6.0 * d + e)), d / (q.x + e), q.x);
}

// HSV to RGB
vec3 hsv2rgb(vec3 c) {
  vec4 K = vec4(1.0, 2.0 / 3.0, 1.0 / 3.0, 3.0);
  vec3 p = abs(fract(c.xxx + K.xyz) * 6.0 - K.www);
  return c.z * mix(K.xxx, clamp(p - K.xxx, 0.0, 1.0), c.y);
}

// RGB to HSL
vec3 rgb2hsl(vec3 c) {
  float maxC = max(c.r, max(c.g, c.b));
  float minC = min(c.r, min(c.g, c.b));
  float l = (maxC + minC) * 0.5;
  if (maxC == minC) return vec3(0.0, 0.0, l);
  float d = maxC - minC;
  float s = l > 0.5 ? d / (2.0 - maxC - minC) : d / (maxC + minC);
  float h;
  if (maxC == c.r) h = (c.g - c.b) / d + (c.g < c.b ? 6.0 : 0.0);
  else if (maxC == c.g) h = (c.b - c.r) / d + 2.0;
  else h = (c.r - c.g) / d + 4.0;
  return vec3(h / 6.0, s, l);
}

// HSL to RGB
float hue2rgb(float p, float q, float t) {
  if (t < 0.0) t += 1.0;
  if (t > 1.0) t -= 1.0;
  if (t < 1.0 / 6.0) return p + (q - p) * 6.0 * t;
  if (t < 1.0 / 2.0) return q;
  if (t < 2.0 / 3.0) return p + (q - p) * (2.0 / 3.0 - t) * 6.0;
  return p;
}

vec3 hsl2rgb(vec3 c) {
  if (c.y == 0.0) return vec3(c.z);
  float q = c.z < 0.5 ? c.z * (1.0 + c.y) : c.z + c.y - c.z * c.y;
  float p = 2.0 * c.z - q;
  return vec3(
    hue2rgb(p, q, c.x + 1.0 / 3.0),
    hue2rgb(p, q, c.x),
    hue2rgb(p, q, c.x - 1.0 / 3.0)
  );
}

// Luminance
float luminance(vec3 c) {
  return dot(c, vec3(0.299, 0.587, 0.114));
}

// ============================================================================
// TEXTURE SAMPLING WITH EDGE MODES
// ============================================================================

vec4 sampleClamp(sampler2D tex, vec2 uv) {
  return texture2D(tex, clamp(uv, 0.0, 1.0));
}

vec4 sampleWrap(sampler2D tex, vec2 uv) {
  return texture2D(tex, fract(uv));
}

vec4 sampleMirror(sampler2D tex, vec2 uv) {
  vec2 m = mod(uv, 2.0);
  m = mix(m, 2.0 - m, step(1.0, m));
  return texture2D(tex, m);
}

// ============================================================================
// BLUR FUNCTIONS
// ============================================================================

vec4 blur(sampler2D tex, vec2 uv, vec2 resolution, float radius) {
  vec4 color = vec4(0.0);
  float total = 0.0;
  vec2 texelSize = 1.0 / resolution;

  for (float x = -4.0; x <= 4.0; x += 1.0) {
    for (float y = -4.0; y <= 4.0; y += 1.0) {
      float weight = exp(-(x*x + y*y) / (2.0 * radius * radius));
      color += texture2D(tex, uv + vec2(x, y) * texelSize * radius) * weight;
      total += weight;
    }
  }

  return color / total;
}

vec4 directionalBlur(sampler2D tex, vec2 uv, vec2 direction, float strength) {
  vec4 color = vec4(0.0);
  for (float i = -4.0; i <= 4.0; i += 1.0) {
    float weight = exp(-abs(i) * 0.5);
    color += texture2D(tex, uv + direction * i * strength) * weight;
  }
  return color / 9.0;
}

// ============================================================================
// DISTORTION FUNCTIONS
// ============================================================================

vec2 barrel(vec2 uv, float amount) {
  vec2 cc = uv - 0.5;
  float dist = dot(cc, cc);
  return uv + cc * dist * amount;
}

vec2 pincushion(vec2 uv, float amount) {
  return barrel(uv, -amount);
}

vec2 swirl(vec2 uv, vec2 center, float angle, float radius) {
  vec2 tc = uv - center;
  float dist = length(tc);
  float percent = (radius - dist) / radius;
  if (percent > 0.0) {
    float theta = percent * percent * angle;
    float s = sin(theta);
    float c = cos(theta);
    tc = vec2(tc.x * c - tc.y * s, tc.x * s + tc.y * c);
  }
  return center + tc;
}

// ============================================================================
// SHAPE FUNCTIONS
// ============================================================================

float circle(vec2 uv, vec2 center, float radius) {
  return smoothstep(radius, radius - 0.01, length(uv - center));
}

float rectangle(vec2 uv, vec2 center, vec2 size) {
  vec2 d = abs(uv - center) - size;
  return 1.0 - smoothstep(0.0, 0.01, max(d.x, d.y));
}

float roundedRect(vec2 uv, vec2 center, vec2 size, float radius) {
  vec2 d = abs(uv - center) - size + radius;
  return 1.0 - smoothstep(0.0, 0.01, min(max(d.x, d.y), 0.0) + length(max(d, 0.0)) - radius);
}

float line(vec2 uv, vec2 a, vec2 b, float thickness) {
  vec2 pa = uv - a, ba = b - a;
  float h = clamp(dot(pa, ba) / dot(ba, ba), 0.0, 1.0);
  return smoothstep(thickness, thickness - 0.01, length(pa - ba * h));
}

// ============================================================================
// GRADIENT FUNCTIONS
// ============================================================================

vec3 linearGradient(vec2 uv, vec2 start, vec2 end, vec3 colorA, vec3 colorB) {
  vec2 dir = normalize(end - start);
  float t = dot(uv - start, dir) / length(end - start);
  return mix(colorA, colorB, clamp(t, 0.0, 1.0));
}

vec3 radialGradient(vec2 uv, vec2 center, float radius, vec3 colorA, vec3 colorB) {
  float t = length(uv - center) / radius;
  return mix(colorA, colorB, clamp(t, 0.0, 1.0));
}

vec3 angularGradient(vec2 uv, vec2 center, vec3 colorA, vec3 colorB) {
  float angle = atan(uv.y - center.y, uv.x - center.x);
  float t = (angle + PI) / TAU;
  return mix(colorA, colorB, t);
}
`;

// ============================================================================
// GLSL ENGINE CLASS
// ============================================================================

export class GLSLEngine {
  private gl: WebGLRenderingContext | null = null;
  private canvas: HTMLCanvasElement | null = null;
  private program: WebGLProgram | null = null;
  private positionBuffer: WebGLBuffer | null = null;
  private texCoordBuffer: WebGLBuffer | null = null;
  private inputTexture: WebGLTexture | null = null;
  private framebuffer: WebGLFramebuffer | null = null;
  private outputTexture: WebGLTexture | null = null;

  private currentWidth = 0;
  private currentHeight = 0;
  private _isAvailable: boolean | null = null;

  private uniformLocations: Map<string, WebGLUniformLocation> = new Map();
  private currentShaderSource: string = "";

  constructor(private options: GLSLEngineOptions = {}) {}

  /**
   * Check if WebGL is available
   */
  isAvailable(): boolean {
    if (this._isAvailable !== null) {
      return this._isAvailable;
    }

    try {
      const testCanvas = document.createElement("canvas");
      testCanvas.width = 1;
      testCanvas.height = 1;
      const gl =
        testCanvas.getContext("webgl") ||
        testCanvas.getContext("experimental-webgl");
      this._isAvailable = gl !== null;
    } catch {
      this._isAvailable = false;
    }

    return this._isAvailable;
  }

  /**
   * Initialize the WebGL context
   */
  private init(width: number, height: number): boolean {
    if (!this.isAvailable()) return false;

    // Create or resize canvas
    if (!this.canvas) {
      this.canvas = document.createElement("canvas");
    }

    if (this.currentWidth !== width || this.currentHeight !== height) {
      this.canvas.width = width;
      this.canvas.height = height;
      this.currentWidth = width;
      this.currentHeight = height;

      // Recreate textures on resize
      this.outputTexture = null;
    }

    // Get WebGL context
    if (!this.gl) {
      this.gl = this.canvas.getContext("webgl", {
        alpha: this.options.alpha ?? true,
        premultipliedAlpha: this.options.premultipliedAlpha ?? false,
        preserveDrawingBuffer: this.options.preserveDrawingBuffer ?? true,
      }) as WebGLRenderingContext | null;

      if (!this.gl) return false;

      // Create position buffer
      this.positionBuffer = this.gl.createBuffer();
      this.gl.bindBuffer(this.gl.ARRAY_BUFFER, this.positionBuffer);
      this.gl.bufferData(
        this.gl.ARRAY_BUFFER,
        new Float32Array([-1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1]),
        this.gl.STATIC_DRAW,
      );

      // Create texture coordinate buffer
      this.texCoordBuffer = this.gl.createBuffer();
      this.gl.bindBuffer(this.gl.ARRAY_BUFFER, this.texCoordBuffer);
      this.gl.bufferData(
        this.gl.ARRAY_BUFFER,
        new Float32Array([0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1]),
        this.gl.STATIC_DRAW,
      );

      // Create framebuffer
      this.framebuffer = this.gl.createFramebuffer();
    }

    // Create output texture if needed
    if (!this.outputTexture) {
      this.outputTexture = this.gl.createTexture();
      this.gl.bindTexture(this.gl.TEXTURE_2D, this.outputTexture);
      this.gl.texImage2D(
        this.gl.TEXTURE_2D,
        0,
        this.gl.RGBA,
        width,
        height,
        0,
        this.gl.RGBA,
        this.gl.UNSIGNED_BYTE,
        null,
      );
      this.gl.texParameteri(
        this.gl.TEXTURE_2D,
        this.gl.TEXTURE_MIN_FILTER,
        this.gl.LINEAR,
      );
      this.gl.texParameteri(
        this.gl.TEXTURE_2D,
        this.gl.TEXTURE_MAG_FILTER,
        this.gl.LINEAR,
      );
      this.gl.texParameteri(
        this.gl.TEXTURE_2D,
        this.gl.TEXTURE_WRAP_S,
        this.gl.CLAMP_TO_EDGE,
      );
      this.gl.texParameteri(
        this.gl.TEXTURE_2D,
        this.gl.TEXTURE_WRAP_T,
        this.gl.CLAMP_TO_EDGE,
      );
    }

    return true;
  }

  /**
   * Compile a shader from source
   */
  compileShader(
    fragmentSource: string,
    includeLibrary: boolean = true,
  ): ShaderCompileResult {
    if (!this.init(1, 1)) {
      return { success: false, program: null, error: "WebGL not available" };
    }

    const gl = this.gl!;

    // Build full fragment shader source
    let fullSource = SHADER_HEADER;
    if (includeLibrary) {
      fullSource += GLSL_LIBRARY;
    }
    fullSource += fragmentSource;
    fullSource += SHADER_FOOTER;

    // Compile vertex shader
    const vertexShader = gl.createShader(gl.VERTEX_SHADER)!;
    gl.shaderSource(vertexShader, DEFAULT_VERTEX_SHADER);
    gl.compileShader(vertexShader);

    if (!gl.getShaderParameter(vertexShader, gl.COMPILE_STATUS)) {
      const error =
        gl.getShaderInfoLog(vertexShader) || "Unknown vertex shader error";
      gl.deleteShader(vertexShader);
      return {
        success: false,
        program: null,
        error: `Vertex shader: ${error}`,
      };
    }

    // Compile fragment shader
    const fragmentShader = gl.createShader(gl.FRAGMENT_SHADER)!;
    gl.shaderSource(fragmentShader, fullSource);
    gl.compileShader(fragmentShader);

    if (!gl.getShaderParameter(fragmentShader, gl.COMPILE_STATUS)) {
      const error =
        gl.getShaderInfoLog(fragmentShader) || "Unknown fragment shader error";
      gl.deleteShader(vertexShader);
      gl.deleteShader(fragmentShader);

      // Try to extract line number from error
      const lineMatch = error.match(/ERROR: \d+:(\d+)/);
      const errorLine = lineMatch ? parseInt(lineMatch[1], 10) : undefined;

      return { success: false, program: null, error, errorLine };
    }

    // Create program
    const program = gl.createProgram()!;
    gl.attachShader(program, vertexShader);
    gl.attachShader(program, fragmentShader);
    gl.linkProgram(program);

    // Clean up shaders (they're linked to program now)
    gl.deleteShader(vertexShader);
    gl.deleteShader(fragmentShader);

    if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
      const error =
        gl.getProgramInfoLog(program) || "Unknown program link error";
      gl.deleteProgram(program);
      return { success: false, program: null, error: `Program link: ${error}` };
    }

    // Cache uniform locations
    this.uniformLocations.clear();
    this.program = program;
    this.currentShaderSource = fragmentSource;

    return { success: true, program };
  }

  /**
   * Set a shader to use (compiles if source changed)
   */
  setShader(
    fragmentSource: string,
    includeLibrary: boolean = true,
  ): ShaderCompileResult {
    if (this.currentShaderSource === fragmentSource && this.program) {
      return { success: true, program: this.program };
    }

    return this.compileShader(fragmentSource, includeLibrary);
  }

  /**
   * Get or cache uniform location
   */
  private getUniformLocation(name: string): WebGLUniformLocation | null {
    if (!this.gl || !this.program) return null;

    if (this.uniformLocations.has(name)) {
      return this.uniformLocations.get(name)!;
    }

    const location = this.gl.getUniformLocation(this.program, name);
    if (location) {
      this.uniformLocations.set(name, location);
    }
    return location;
  }

  /**
   * Set uniforms on the current shader
   */
  setUniforms(uniforms: Partial<ShaderUniforms>): void {
    if (!this.gl || !this.program) return;

    const gl = this.gl;
    gl.useProgram(this.program);

    for (const [name, value] of Object.entries(uniforms)) {
      const location = this.getUniformLocation(name);
      if (!location) continue;

      if (typeof value === "number") {
        gl.uniform1f(location, value);
      } else if (typeof value === "boolean") {
        gl.uniform1i(location, value ? 1 : 0);
      } else if (Array.isArray(value)) {
        switch (value.length) {
          case 2:
            gl.uniform2f(location, value[0], value[1]);
            break;
          case 3:
            gl.uniform3f(location, value[0], value[1], value[2]);
            break;
          case 4:
            gl.uniform4f(location, value[0], value[1], value[2], value[3]);
            break;
        }
      }
    }
  }

  /**
   * Run the current shader on an input image
   */
  render(
    input: HTMLCanvasElement | ImageData,
    uniforms: Partial<ShaderUniforms> = {},
  ): HTMLCanvasElement | null {
    const width =
      input instanceof HTMLCanvasElement ? input.width : input.width;
    const height =
      input instanceof HTMLCanvasElement ? input.height : input.height;

    if (!this.init(width, height) || !this.program) {
      return null;
    }

    const gl = this.gl!;

    // Set viewport
    gl.viewport(0, 0, width, height);

    // Use program
    gl.useProgram(this.program);

    // Set up attributes
    const positionLoc = gl.getAttribLocation(this.program, "a_position");
    const texCoordLoc = gl.getAttribLocation(this.program, "a_texCoord");

    gl.bindBuffer(gl.ARRAY_BUFFER, this.positionBuffer);
    gl.enableVertexAttribArray(positionLoc);
    gl.vertexAttribPointer(positionLoc, 2, gl.FLOAT, false, 0, 0);

    gl.bindBuffer(gl.ARRAY_BUFFER, this.texCoordBuffer);
    gl.enableVertexAttribArray(texCoordLoc);
    gl.vertexAttribPointer(texCoordLoc, 2, gl.FLOAT, false, 0, 0);

    // Upload input texture
    if (!this.inputTexture) {
      this.inputTexture = gl.createTexture();
    }
    gl.activeTexture(gl.TEXTURE0);
    gl.bindTexture(gl.TEXTURE_2D, this.inputTexture);

    if (input instanceof HTMLCanvasElement) {
      gl.texImage2D(
        gl.TEXTURE_2D,
        0,
        gl.RGBA,
        gl.RGBA,
        gl.UNSIGNED_BYTE,
        input,
      );
    } else {
      gl.texImage2D(
        gl.TEXTURE_2D,
        0,
        gl.RGBA,
        width,
        height,
        0,
        gl.RGBA,
        gl.UNSIGNED_BYTE,
        new Uint8Array(input.data.buffer),
      );
    }

    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);

    // Set default uniforms
    const defaultUniforms: Partial<ShaderUniforms> = {
      iResolution: [width, height, 1],
      iTime: 0,
      iTimeDelta: 1 / 60,
      iFrame: 0,
      iMouse: [0, 0, 0, 0],
      iDate: [2025, 1, 1, 0],
      iSampleRate: 44100,
      ...uniforms,
    };

    this.setUniforms(defaultUniforms);

    // Set iChannel0 uniform
    const channel0Loc = this.getUniformLocation("iChannel0");
    if (channel0Loc) {
      gl.uniform1i(channel0Loc, 0);
    }

    // Render to framebuffer
    gl.bindFramebuffer(gl.FRAMEBUFFER, this.framebuffer);
    gl.framebufferTexture2D(
      gl.FRAMEBUFFER,
      gl.COLOR_ATTACHMENT0,
      gl.TEXTURE_2D,
      this.outputTexture,
      0,
    );

    // Clear and draw
    gl.clearColor(0, 0, 0, 0);
    gl.clear(gl.COLOR_BUFFER_BIT);
    gl.drawArrays(gl.TRIANGLES, 0, 6);

    // Read back result
    const pixels = new Uint8Array(width * height * 4);
    gl.readPixels(0, 0, width, height, gl.RGBA, gl.UNSIGNED_BYTE, pixels);

    // Unbind framebuffer
    gl.bindFramebuffer(gl.FRAMEBUFFER, null);

    // Copy to output canvas (flip Y)
    const outputCanvas = document.createElement("canvas");
    outputCanvas.width = width;
    outputCanvas.height = height;
    const ctx = outputCanvas.getContext("2d")!;
    const imageData = ctx.createImageData(width, height);

    // WebGL has Y-flipped compared to canvas
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
   * Dispose of WebGL resources
   */
  dispose(): void {
    if (this.gl) {
      if (this.program) this.gl.deleteProgram(this.program);
      if (this.inputTexture) this.gl.deleteTexture(this.inputTexture);
      if (this.outputTexture) this.gl.deleteTexture(this.outputTexture);
      if (this.positionBuffer) this.gl.deleteBuffer(this.positionBuffer);
      if (this.texCoordBuffer) this.gl.deleteBuffer(this.texCoordBuffer);
      if (this.framebuffer) this.gl.deleteFramebuffer(this.framebuffer);
    }

    this.gl = null;
    this.canvas = null;
    this.program = null;
    this.uniformLocations.clear();
    this._isAvailable = null;
  }
}

// Singleton instance
let glslEngineInstance: GLSLEngine | null = null;

/**
 * Get the singleton GLSL engine instance
 */
export function getGLSLEngine(): GLSLEngine {
  if (!glslEngineInstance) {
    glslEngineInstance = new GLSLEngine();
  }
  return glslEngineInstance;
}

/**
 * Dispose of the singleton GLSL engine
 */
export function disposeGLSLEngine(): void {
  if (glslEngineInstance) {
    glslEngineInstance.dispose();
    glslEngineInstance = null;
  }
}

export default GLSLEngine;
