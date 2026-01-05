/**
 * ShaderEffects.ts - Pre-built GLSL shader effects library
 *
 * Provides ready-to-use shader effects that leverage the GLSLEngine.
 * Based on Jovi_GLSL patterns with Lattice-specific enhancements.
 */

import { getGLSLEngine, type ShaderUniforms } from "./GLSLEngine";

// =============================================================================
// SHADER EFFECT DEFINITIONS
// =============================================================================

export interface ShaderEffectDefinition {
  name: string;
  category:
    | "blur"
    | "distort"
    | "color"
    | "generate"
    | "stylize"
    | "transition";
  description: string;
  fragmentShader: string;
  uniforms: Record<
    string,
    {
      type: string;
      default: number | number[];
      min?: number;
      max?: number;
      step?: number;
    }
  >;
}

// =============================================================================
// BLUR EFFECTS
// =============================================================================

export const BLUR_EFFECTS: Record<string, ShaderEffectDefinition> = {
  "glsl-gaussian-blur": {
    name: "GLSL Gaussian Blur",
    category: "blur",
    description: "GPU-accelerated Gaussian blur with adjustable radius",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform float u_radius;
      uniform vec2 u_direction;

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        vec4 color = vec4(0.0);
        float total = 0.0;

        float radius = u_radius;
        vec2 dir = u_direction / iResolution.xy;

        for (float i = -20.0; i <= 20.0; i += 1.0) {
          if (abs(i) > radius) continue;
          float weight = exp(-i * i / (2.0 * radius * radius));
          color += texture2D(iChannel0, uv + dir * i) * weight;
          total += weight;
        }

        gl_FragColor = color / total;
      }
    `,
    uniforms: {
      u_radius: { type: "float", default: 5, min: 0, max: 50, step: 0.5 },
      u_direction: { type: "vec2", default: [1, 0] },
    },
  },

  "glsl-directional-blur": {
    name: "GLSL Directional Blur",
    category: "blur",
    description: "Motion blur in a specified direction",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform float u_strength;
      uniform float u_angle;
      uniform int u_samples;

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        float rad = u_angle * 3.14159265 / 180.0;
        vec2 dir = vec2(cos(rad), sin(rad)) * u_strength / iResolution.xy;

        vec4 color = vec4(0.0);
        float samples = float(u_samples);

        for (int i = 0; i < 32; i++) {
          if (i >= u_samples) break;
          float t = float(i) / samples - 0.5;
          color += texture2D(iChannel0, uv + dir * t);
        }

        gl_FragColor = color / samples;
      }
    `,
    uniforms: {
      u_strength: { type: "float", default: 10, min: 0, max: 100, step: 1 },
      u_angle: { type: "float", default: 0, min: 0, max: 360, step: 1 },
      u_samples: { type: "int", default: 16, min: 4, max: 32, step: 1 },
    },
  },

  "glsl-radial-blur": {
    name: "GLSL Radial Blur",
    category: "blur",
    description: "Zoom or spin blur from a center point",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform vec2 u_center;
      uniform float u_strength;
      uniform int u_samples;
      uniform int u_mode; // 0 = zoom, 1 = spin

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        vec2 center = u_center / iResolution.xy;
        vec2 delta = uv - center;
        float dist = length(delta);

        vec4 color = vec4(0.0);
        float samples = float(u_samples);

        for (int i = 0; i < 32; i++) {
          if (i >= u_samples) break;
          float t = float(i) / samples;
          vec2 offset;

          if (u_mode == 0) {
            // Zoom blur
            offset = delta * t * u_strength * 0.01;
          } else {
            // Spin blur
            float angle = t * u_strength * 0.01;
            float c = cos(angle);
            float s = sin(angle);
            offset = vec2(
              delta.x * c - delta.y * s,
              delta.x * s + delta.y * c
            ) - delta;
          }

          color += texture2D(iChannel0, uv - offset);
        }

        gl_FragColor = color / samples;
      }
    `,
    uniforms: {
      u_center: { type: "vec2", default: [0.5, 0.5] },
      u_strength: { type: "float", default: 10, min: 0, max: 100, step: 1 },
      u_samples: { type: "int", default: 16, min: 4, max: 32, step: 1 },
      u_mode: { type: "int", default: 0, min: 0, max: 1, step: 1 },
    },
  },
};

// =============================================================================
// DISTORTION EFFECTS
// =============================================================================

export const DISTORT_EFFECTS: Record<string, ShaderEffectDefinition> = {
  "glsl-wave": {
    name: "GLSL Wave Distortion",
    category: "distort",
    description: "Animated wave distortion effect",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform float iTime;
      uniform float u_amplitude;
      uniform float u_frequency;
      uniform float u_speed;
      uniform int u_direction; // 0 = horizontal, 1 = vertical, 2 = both

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        float time = iTime * u_speed;

        vec2 offset = vec2(0.0);

        if (u_direction == 0 || u_direction == 2) {
          offset.x = sin(uv.y * u_frequency + time) * u_amplitude / iResolution.x;
        }
        if (u_direction == 1 || u_direction == 2) {
          offset.y = sin(uv.x * u_frequency + time) * u_amplitude / iResolution.y;
        }

        gl_FragColor = texture2D(iChannel0, uv + offset);
      }
    `,
    uniforms: {
      u_amplitude: { type: "float", default: 10, min: 0, max: 100, step: 1 },
      u_frequency: { type: "float", default: 10, min: 0.1, max: 50, step: 0.1 },
      u_speed: { type: "float", default: 1, min: 0, max: 10, step: 0.1 },
      u_direction: { type: "int", default: 0, min: 0, max: 2, step: 1 },
    },
  },

  "glsl-bulge": {
    name: "GLSL Bulge",
    category: "distort",
    description: "Spherical bulge/pinch distortion",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform vec2 u_center;
      uniform float u_radius;
      uniform float u_strength;

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        vec2 center = u_center;

        vec2 delta = uv - center;
        float dist = length(delta);
        float radius = u_radius;

        if (dist < radius) {
          float percent = dist / radius;
          float bulge = pow(percent, u_strength);
          delta *= bulge;
        }

        gl_FragColor = texture2D(iChannel0, center + delta);
      }
    `,
    uniforms: {
      u_center: { type: "vec2", default: [0.5, 0.5] },
      u_radius: { type: "float", default: 0.3, min: 0, max: 1, step: 0.01 },
      u_strength: { type: "float", default: 0.5, min: 0.1, max: 3, step: 0.1 },
    },
  },

  "glsl-twirl": {
    name: "GLSL Twirl",
    category: "distort",
    description: "Spiral twirl distortion",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform vec2 u_center;
      uniform float u_radius;
      uniform float u_angle;

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        vec2 center = u_center;

        vec2 delta = uv - center;
        float dist = length(delta);

        if (dist < u_radius) {
          float percent = (u_radius - dist) / u_radius;
          float theta = percent * percent * u_angle;
          float c = cos(theta);
          float s = sin(theta);
          delta = vec2(
            delta.x * c - delta.y * s,
            delta.x * s + delta.y * c
          );
        }

        gl_FragColor = texture2D(iChannel0, center + delta);
      }
    `,
    uniforms: {
      u_center: { type: "vec2", default: [0.5, 0.5] },
      u_radius: { type: "float", default: 0.4, min: 0, max: 1, step: 0.01 },
      u_angle: {
        type: "float",
        default: 3.14,
        min: -12.56,
        max: 12.56,
        step: 0.1,
      },
    },
  },

  "glsl-displacement": {
    name: "GLSL Displacement Map",
    category: "distort",
    description: "Displace pixels based on a second image",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform sampler2D iChannel1;
      uniform vec2 iResolution;
      uniform float u_scaleX;
      uniform float u_scaleY;
      uniform int u_useAlpha;

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        vec4 dispMap = texture2D(iChannel1, uv);

        float dispX = (dispMap.r - 0.5) * 2.0;
        float dispY = (dispMap.g - 0.5) * 2.0;

        if (u_useAlpha == 1) {
          dispX *= dispMap.a;
          dispY *= dispMap.a;
        }

        vec2 offset = vec2(
          dispX * u_scaleX / iResolution.x,
          dispY * u_scaleY / iResolution.y
        );

        gl_FragColor = texture2D(iChannel0, uv + offset);
      }
    `,
    uniforms: {
      u_scaleX: { type: "float", default: 50, min: 0, max: 500, step: 1 },
      u_scaleY: { type: "float", default: 50, min: 0, max: 500, step: 1 },
      u_useAlpha: { type: "int", default: 0, min: 0, max: 1, step: 1 },
    },
  },

  "glsl-turbulence": {
    name: "GLSL Turbulence Distort",
    category: "distort",
    description: "Noise-based turbulent distortion",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform float iTime;
      uniform float u_amount;
      uniform float u_scale;
      uniform float u_speed;
      uniform int u_octaves;

      // Simplex noise function
      vec3 mod289(vec3 x) { return x - floor(x * (1.0 / 289.0)) * 289.0; }
      vec2 mod289(vec2 x) { return x - floor(x * (1.0 / 289.0)) * 289.0; }
      vec3 permute(vec3 x) { return mod289(((x*34.0)+1.0)*x); }

      float snoise(vec2 v) {
        const vec4 C = vec4(0.211324865405187, 0.366025403784439, -0.577350269189626, 0.024390243902439);
        vec2 i  = floor(v + dot(v, C.yy));
        vec2 x0 = v -   i + dot(i, C.xx);
        vec2 i1;
        i1 = (x0.x > x0.y) ? vec2(1.0, 0.0) : vec2(0.0, 1.0);
        vec4 x12 = x0.xyxy + C.xxzz;
        x12.xy -= i1;
        i = mod289(i);
        vec3 p = permute(permute(i.y + vec3(0.0, i1.y, 1.0)) + i.x + vec3(0.0, i1.x, 1.0));
        vec3 m = max(0.5 - vec3(dot(x0,x0), dot(x12.xy,x12.xy), dot(x12.zw,x12.zw)), 0.0);
        m = m*m; m = m*m;
        vec3 x = 2.0 * fract(p * C.www) - 1.0;
        vec3 h = abs(x) - 0.5;
        vec3 ox = floor(x + 0.5);
        vec3 a0 = x - ox;
        m *= 1.79284291400159 - 0.85373472095314 * (a0*a0 + h*h);
        vec3 g;
        g.x  = a0.x  * x0.x  + h.x  * x0.y;
        g.yz = a0.yz * x12.xz + h.yz * x12.yw;
        return 130.0 * dot(m, g);
      }

      float turbulence(vec2 p, int octaves) {
        float value = 0.0;
        float amplitude = 1.0;
        float frequency = 1.0;
        for (int i = 0; i < 8; i++) {
          if (i >= octaves) break;
          value += amplitude * abs(snoise(p * frequency));
          amplitude *= 0.5;
          frequency *= 2.0;
        }
        return value;
      }

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        float time = iTime * u_speed;

        vec2 noiseCoord = uv * u_scale + time;
        float noiseX = turbulence(noiseCoord, u_octaves);
        float noiseY = turbulence(noiseCoord + vec2(100.0), u_octaves);

        vec2 offset = vec2(noiseX - 0.5, noiseY - 0.5) * u_amount / iResolution.xy;

        gl_FragColor = texture2D(iChannel0, uv + offset);
      }
    `,
    uniforms: {
      u_amount: { type: "float", default: 20, min: 0, max: 200, step: 1 },
      u_scale: { type: "float", default: 3, min: 0.1, max: 20, step: 0.1 },
      u_speed: { type: "float", default: 1, min: 0, max: 5, step: 0.1 },
      u_octaves: { type: "int", default: 4, min: 1, max: 8, step: 1 },
    },
  },
};

// =============================================================================
// COLOR EFFECTS
// =============================================================================

export const COLOR_EFFECTS: Record<string, ShaderEffectDefinition> = {
  "glsl-chromatic-aberration": {
    name: "GLSL Chromatic Aberration",
    category: "color",
    description: "RGB channel separation effect",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform float u_amount;
      uniform float u_angle;
      uniform int u_mode; // 0 = radial, 1 = directional

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        vec2 center = vec2(0.5);

        vec2 offset;
        if (u_mode == 0) {
          // Radial
          offset = (uv - center) * u_amount * 0.01;
        } else {
          // Directional
          float rad = u_angle * 3.14159265 / 180.0;
          offset = vec2(cos(rad), sin(rad)) * u_amount * 0.01;
        }

        float r = texture2D(iChannel0, uv + offset).r;
        float g = texture2D(iChannel0, uv).g;
        float b = texture2D(iChannel0, uv - offset).b;
        float a = texture2D(iChannel0, uv).a;

        gl_FragColor = vec4(r, g, b, a);
      }
    `,
    uniforms: {
      u_amount: { type: "float", default: 5, min: 0, max: 50, step: 0.5 },
      u_angle: { type: "float", default: 0, min: 0, max: 360, step: 1 },
      u_mode: { type: "int", default: 0, min: 0, max: 1, step: 1 },
    },
  },

  "glsl-color-grading": {
    name: "GLSL Color Grading",
    category: "color",
    description: "Lift/Gamma/Gain color grading",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform vec3 u_lift;
      uniform vec3 u_gamma;
      uniform vec3 u_gain;
      uniform float u_saturation;

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        vec4 color = texture2D(iChannel0, uv);

        // Lift (shadows)
        color.rgb = color.rgb + u_lift * (1.0 - color.rgb);

        // Gamma (midtones)
        color.rgb = pow(color.rgb, 1.0 / u_gamma);

        // Gain (highlights)
        color.rgb = color.rgb * u_gain;

        // Saturation
        float luma = dot(color.rgb, vec3(0.299, 0.587, 0.114));
        color.rgb = mix(vec3(luma), color.rgb, u_saturation);

        gl_FragColor = clamp(color, 0.0, 1.0);
      }
    `,
    uniforms: {
      u_lift: { type: "vec3", default: [0, 0, 0] },
      u_gamma: { type: "vec3", default: [1, 1, 1] },
      u_gain: { type: "vec3", default: [1, 1, 1] },
      u_saturation: { type: "float", default: 1, min: 0, max: 3, step: 0.1 },
    },
  },

  "glsl-lut": {
    name: "GLSL LUT Application",
    category: "color",
    description: "Apply color lookup table",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform sampler2D iChannel1; // LUT texture
      uniform vec2 iResolution;
      uniform float u_intensity;
      uniform float u_lutSize;

      vec4 applyLUT(vec4 color, sampler2D lut, float size) {
        float blueIndex = color.b * (size - 1.0);
        float row = floor(blueIndex / size);
        float col = mod(blueIndex, size);

        vec2 lutCoord = vec2(
          (col + 0.5 + color.r * (size - 1.0)) / (size * size),
          (row + 0.5 + color.g * (size - 1.0)) / size
        );

        return texture2D(lut, lutCoord);
      }

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        vec4 original = texture2D(iChannel0, uv);
        vec4 graded = applyLUT(original, iChannel1, u_lutSize);

        gl_FragColor = mix(original, graded, u_intensity);
      }
    `,
    uniforms: {
      u_intensity: { type: "float", default: 1, min: 0, max: 1, step: 0.01 },
      u_lutSize: { type: "float", default: 32, min: 8, max: 64, step: 1 },
    },
  },

  "glsl-vignette": {
    name: "GLSL Vignette",
    category: "color",
    description: "Darkened edges vignette effect",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform float u_amount;
      uniform float u_softness;
      uniform float u_roundness;
      uniform vec2 u_center;

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        vec4 color = texture2D(iChannel0, uv);

        vec2 center = u_center;
        vec2 dist = (uv - center) * vec2(iResolution.x / iResolution.y, 1.0);

        float vignette;
        if (u_roundness < 1.0) {
          // Elliptical
          float d = pow(abs(dist.x), 2.0 / u_roundness) + pow(abs(dist.y), 2.0 / u_roundness);
          vignette = pow(d, u_roundness * 0.5);
        } else {
          // Circular
          vignette = length(dist);
        }

        vignette = smoothstep(u_amount, u_amount + u_softness, vignette);

        gl_FragColor = vec4(color.rgb * (1.0 - vignette), color.a);
      }
    `,
    uniforms: {
      u_amount: { type: "float", default: 0.5, min: 0, max: 2, step: 0.01 },
      u_softness: { type: "float", default: 0.5, min: 0, max: 1, step: 0.01 },
      u_roundness: { type: "float", default: 1, min: 0.1, max: 2, step: 0.1 },
      u_center: { type: "vec2", default: [0.5, 0.5] },
    },
  },
};

// =============================================================================
// GENERATE EFFECTS
// =============================================================================

export const GENERATE_EFFECTS: Record<string, ShaderEffectDefinition> = {
  "glsl-noise": {
    name: "GLSL Fractal Noise",
    category: "generate",
    description: "Animated fractal noise generator",
    fragmentShader: `
      precision highp float;
      uniform vec2 iResolution;
      uniform float iTime;
      uniform float u_scale;
      uniform float u_speed;
      uniform int u_octaves;
      uniform float u_persistence;
      uniform int u_type; // 0 = value, 1 = perlin, 2 = simplex
      uniform vec3 u_color1;
      uniform vec3 u_color2;

      // Hash functions
      float hash(vec2 p) {
        return fract(sin(dot(p, vec2(127.1, 311.7))) * 43758.5453123);
      }

      float noise(vec2 p) {
        vec2 i = floor(p);
        vec2 f = fract(p);
        f = f * f * (3.0 - 2.0 * f);

        return mix(
          mix(hash(i), hash(i + vec2(1.0, 0.0)), f.x),
          mix(hash(i + vec2(0.0, 1.0)), hash(i + vec2(1.0, 1.0)), f.x),
          f.y
        );
      }

      float fbm(vec2 p, int octaves, float persistence) {
        float value = 0.0;
        float amplitude = 1.0;
        float frequency = 1.0;
        float total = 0.0;

        for (int i = 0; i < 8; i++) {
          if (i >= octaves) break;
          value += amplitude * noise(p * frequency);
          total += amplitude;
          amplitude *= persistence;
          frequency *= 2.0;
        }

        return value / total;
      }

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        float time = iTime * u_speed;

        float n = fbm(uv * u_scale + time, u_octaves, u_persistence);

        vec3 color = mix(u_color1, u_color2, n);

        gl_FragColor = vec4(color, 1.0);
      }
    `,
    uniforms: {
      u_scale: { type: "float", default: 4, min: 0.1, max: 20, step: 0.1 },
      u_speed: { type: "float", default: 0.5, min: 0, max: 5, step: 0.1 },
      u_octaves: { type: "int", default: 4, min: 1, max: 8, step: 1 },
      u_persistence: {
        type: "float",
        default: 0.5,
        min: 0.1,
        max: 1,
        step: 0.05,
      },
      u_type: { type: "int", default: 0, min: 0, max: 2, step: 1 },
      u_color1: { type: "vec3", default: [0, 0, 0] },
      u_color2: { type: "vec3", default: [1, 1, 1] },
    },
  },

  "glsl-gradient": {
    name: "GLSL Gradient",
    category: "generate",
    description: "Multi-point gradient generator",
    fragmentShader: `
      precision highp float;
      uniform vec2 iResolution;
      uniform vec2 u_start;
      uniform vec2 u_end;
      uniform vec3 u_color1;
      uniform vec3 u_color2;
      uniform vec3 u_color3;
      uniform int u_type; // 0 = linear, 1 = radial
      uniform int u_colorCount; // 2 or 3

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;

        float t;
        if (u_type == 0) {
          // Linear gradient
          vec2 dir = u_end - u_start;
          t = dot(uv - u_start, dir) / dot(dir, dir);
        } else {
          // Radial gradient
          t = length(uv - u_start) / length(u_end - u_start);
        }

        t = clamp(t, 0.0, 1.0);

        vec3 color;
        if (u_colorCount == 2) {
          color = mix(u_color1, u_color2, t);
        } else {
          if (t < 0.5) {
            color = mix(u_color1, u_color3, t * 2.0);
          } else {
            color = mix(u_color3, u_color2, (t - 0.5) * 2.0);
          }
        }

        gl_FragColor = vec4(color, 1.0);
      }
    `,
    uniforms: {
      u_start: { type: "vec2", default: [0, 0] },
      u_end: { type: "vec2", default: [1, 1] },
      u_color1: { type: "vec3", default: [0, 0, 0] },
      u_color2: { type: "vec3", default: [1, 1, 1] },
      u_color3: { type: "vec3", default: [0.5, 0.5, 0.5] },
      u_type: { type: "int", default: 0, min: 0, max: 1, step: 1 },
      u_colorCount: { type: "int", default: 2, min: 2, max: 3, step: 1 },
    },
  },
};

// =============================================================================
// STYLIZE EFFECTS
// =============================================================================

export const STYLIZE_EFFECTS: Record<string, ShaderEffectDefinition> = {
  "glsl-edge-detect": {
    name: "GLSL Edge Detection",
    category: "stylize",
    description: "Sobel edge detection",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform float u_threshold;
      uniform int u_colorMode; // 0 = grayscale, 1 = colored

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        vec2 pixel = 1.0 / iResolution.xy;

        // Sobel kernels
        float gx = 0.0;
        float gy = 0.0;

        // Sample 3x3 neighborhood
        for (int y = -1; y <= 1; y++) {
          for (int x = -1; x <= 1; x++) {
            vec2 offset = vec2(float(x), float(y)) * pixel;
            float sample = dot(texture2D(iChannel0, uv + offset).rgb, vec3(0.299, 0.587, 0.114));

            // Sobel X kernel: -1 0 1, -2 0 2, -1 0 1
            float wx = float(x) * (y == 0 ? 2.0 : 1.0);
            gx += sample * wx;

            // Sobel Y kernel: -1 -2 -1, 0 0 0, 1 2 1
            float wy = float(y) * (x == 0 ? 2.0 : 1.0);
            gy += sample * wy;
          }
        }

        float edge = sqrt(gx * gx + gy * gy);
        edge = step(u_threshold, edge);

        if (u_colorMode == 1) {
          vec4 color = texture2D(iChannel0, uv);
          gl_FragColor = vec4(color.rgb * edge, color.a);
        } else {
          gl_FragColor = vec4(vec3(edge), 1.0);
        }
      }
    `,
    uniforms: {
      u_threshold: { type: "float", default: 0.1, min: 0, max: 1, step: 0.01 },
      u_colorMode: { type: "int", default: 0, min: 0, max: 1, step: 1 },
    },
  },

  "glsl-posterize": {
    name: "GLSL Posterize",
    category: "stylize",
    description: "Reduce color levels",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform float u_levels;

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        vec4 color = texture2D(iChannel0, uv);

        float levels = max(2.0, u_levels);
        color.rgb = floor(color.rgb * levels) / (levels - 1.0);

        gl_FragColor = color;
      }
    `,
    uniforms: {
      u_levels: { type: "float", default: 8, min: 2, max: 32, step: 1 },
    },
  },

  "glsl-pixelate": {
    name: "GLSL Pixelate",
    category: "stylize",
    description: "Pixel mosaic effect",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform float u_pixelSize;

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;

        float size = max(1.0, u_pixelSize);
        vec2 pixelUV = floor(uv * iResolution.xy / size) * size / iResolution.xy;

        gl_FragColor = texture2D(iChannel0, pixelUV);
      }
    `,
    uniforms: {
      u_pixelSize: { type: "float", default: 8, min: 1, max: 64, step: 1 },
    },
  },

  "glsl-halftone": {
    name: "GLSL Halftone",
    category: "stylize",
    description: "Print-style halftone dots",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform float u_dotSize;
      uniform float u_angle;
      uniform int u_colorMode; // 0 = BW, 1 = CMYK

      float halftone(vec2 uv, float angle, float size) {
        float rad = angle * 3.14159265 / 180.0;
        mat2 rot = mat2(cos(rad), -sin(rad), sin(rad), cos(rad));
        vec2 rotUV = rot * uv;

        vec2 nearest = floor(rotUV / size + 0.5) * size;
        float dist = length(rotUV - nearest);

        return dist;
      }

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        vec4 color = texture2D(iChannel0, uv);

        if (u_colorMode == 0) {
          // Black and white
          float luma = dot(color.rgb, vec3(0.299, 0.587, 0.114));
          float dot = halftone(gl_FragCoord.xy, u_angle, u_dotSize);
          float threshold = luma * u_dotSize * 0.5;
          gl_FragColor = vec4(vec3(step(dot, threshold)), color.a);
        } else {
          // CMYK halftone
          float c = 1.0 - color.r;
          float m = 1.0 - color.g;
          float y = 1.0 - color.b;
          float k = min(c, min(m, y));

          float dotC = halftone(gl_FragCoord.xy, u_angle + 15.0, u_dotSize);
          float dotM = halftone(gl_FragCoord.xy, u_angle + 75.0, u_dotSize);
          float dotY = halftone(gl_FragCoord.xy, u_angle, u_dotSize);
          float dotK = halftone(gl_FragCoord.xy, u_angle + 45.0, u_dotSize);

          float threshold = u_dotSize * 0.5;
          c = step(dotC, c * threshold);
          m = step(dotM, m * threshold);
          y = step(dotY, y * threshold);
          k = step(dotK, k * threshold);

          vec3 result = vec3(1.0) - vec3(c, m, y) - k;
          gl_FragColor = vec4(result, color.a);
        }
      }
    `,
    uniforms: {
      u_dotSize: { type: "float", default: 4, min: 2, max: 32, step: 1 },
      u_angle: { type: "float", default: 45, min: 0, max: 90, step: 1 },
      u_colorMode: { type: "int", default: 0, min: 0, max: 1, step: 1 },
    },
  },

  "glsl-glitch": {
    name: "GLSL Glitch",
    category: "stylize",
    description: "Digital glitch/corruption effect",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform vec2 iResolution;
      uniform float iTime;
      uniform float u_intensity;
      uniform float u_speed;
      uniform float u_blockSize;

      float rand(vec2 co) {
        return fract(sin(dot(co.xy, vec2(12.9898, 78.233))) * 43758.5453);
      }

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;
        float time = floor(iTime * u_speed * 10.0);

        // Block-based displacement
        vec2 block = floor(uv * u_blockSize) / u_blockSize;
        float noise = rand(block + time);

        vec2 offset = vec2(0.0);
        if (noise > 1.0 - u_intensity * 0.1) {
          offset.x = (rand(block + time + 1.0) - 0.5) * u_intensity * 0.1;
        }

        // Color channel separation
        vec4 color;
        if (rand(vec2(time)) > 0.95) {
          color.r = texture2D(iChannel0, uv + offset + vec2(0.01, 0.0)).r;
          color.g = texture2D(iChannel0, uv + offset).g;
          color.b = texture2D(iChannel0, uv + offset - vec2(0.01, 0.0)).b;
          color.a = texture2D(iChannel0, uv + offset).a;
        } else {
          color = texture2D(iChannel0, uv + offset);
        }

        // Scan lines
        float scanline = sin(uv.y * iResolution.y * 0.5) * 0.02 * u_intensity;
        color.rgb -= scanline;

        gl_FragColor = color;
      }
    `,
    uniforms: {
      u_intensity: { type: "float", default: 0.5, min: 0, max: 1, step: 0.01 },
      u_speed: { type: "float", default: 1, min: 0.1, max: 5, step: 0.1 },
      u_blockSize: { type: "float", default: 20, min: 5, max: 100, step: 1 },
    },
  },
};

// =============================================================================
// TRANSITION EFFECTS
// =============================================================================

export const TRANSITION_EFFECTS: Record<string, ShaderEffectDefinition> = {
  "glsl-dissolve": {
    name: "GLSL Dissolve",
    category: "transition",
    description: "Noise-based dissolve transition",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform sampler2D iChannel1;
      uniform vec2 iResolution;
      uniform float u_progress;
      uniform float u_softness;
      uniform float u_noiseScale;

      float hash(vec2 p) {
        return fract(sin(dot(p, vec2(127.1, 311.7))) * 43758.5453123);
      }

      float noise(vec2 p) {
        vec2 i = floor(p);
        vec2 f = fract(p);
        f = f * f * (3.0 - 2.0 * f);
        return mix(
          mix(hash(i), hash(i + vec2(1.0, 0.0)), f.x),
          mix(hash(i + vec2(0.0, 1.0)), hash(i + vec2(1.0, 1.0)), f.x),
          f.y
        );
      }

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;

        vec4 from = texture2D(iChannel0, uv);
        vec4 to = texture2D(iChannel1, uv);

        float n = noise(uv * u_noiseScale);
        float threshold = u_progress;
        float edge = smoothstep(threshold - u_softness, threshold + u_softness, n);

        gl_FragColor = mix(from, to, edge);
      }
    `,
    uniforms: {
      u_progress: { type: "float", default: 0, min: 0, max: 1, step: 0.01 },
      u_softness: { type: "float", default: 0.1, min: 0, max: 0.5, step: 0.01 },
      u_noiseScale: { type: "float", default: 10, min: 1, max: 50, step: 1 },
    },
  },

  "glsl-wipe": {
    name: "GLSL Directional Wipe",
    category: "transition",
    description: "Wipe transition with direction",
    fragmentShader: `
      precision highp float;
      uniform sampler2D iChannel0;
      uniform sampler2D iChannel1;
      uniform vec2 iResolution;
      uniform float u_progress;
      uniform float u_softness;
      uniform float u_angle;

      void main() {
        vec2 uv = gl_FragCoord.xy / iResolution.xy;

        vec4 from = texture2D(iChannel0, uv);
        vec4 to = texture2D(iChannel1, uv);

        float rad = u_angle * 3.14159265 / 180.0;
        vec2 dir = vec2(cos(rad), sin(rad));

        float d = dot(uv - 0.5, dir) + 0.5;
        float edge = smoothstep(u_progress - u_softness, u_progress + u_softness, d);

        gl_FragColor = mix(from, to, edge);
      }
    `,
    uniforms: {
      u_progress: { type: "float", default: 0, min: 0, max: 1, step: 0.01 },
      u_softness: {
        type: "float",
        default: 0.05,
        min: 0,
        max: 0.5,
        step: 0.01,
      },
      u_angle: { type: "float", default: 0, min: 0, max: 360, step: 1 },
    },
  },
};

// =============================================================================
// COMBINED EFFECTS REGISTRY
// =============================================================================

export const ALL_SHADER_EFFECTS: Record<string, ShaderEffectDefinition> = {
  ...BLUR_EFFECTS,
  ...DISTORT_EFFECTS,
  ...COLOR_EFFECTS,
  ...GENERATE_EFFECTS,
  ...STYLIZE_EFFECTS,
  ...TRANSITION_EFFECTS,
};

// =============================================================================
// SHADER EFFECT PROCESSOR
// =============================================================================

export class ShaderEffectProcessor {
  private engine: ReturnType<typeof getGLSLEngine>;

  constructor() {
    this.engine = getGLSLEngine();
  }

  /**
   * Set the active effect
   */
  setEffect(effectKey: string): boolean {
    const effect = ALL_SHADER_EFFECTS[effectKey];
    if (!effect) {
      console.warn(`Unknown shader effect: ${effectKey}`);
      return false;
    }

    const result = this.engine.setShader(effect.fragmentShader);
    if (result.success) {
      this.currentEffect = effectKey;
    }
    return result.success;
  }

  /**
   * Render the current effect
   */
  render(
    input: HTMLCanvasElement | ImageData,
    uniforms: Partial<ShaderUniforms> = {},
  ): HTMLCanvasElement | null {
    return this.engine.render(input, uniforms);
  }

  /**
   * Get effect definition
   */
  getEffectDefinition(effectKey: string): ShaderEffectDefinition | undefined {
    return ALL_SHADER_EFFECTS[effectKey];
  }

  /**
   * Get all effects by category
   */
  getEffectsByCategory(
    category: ShaderEffectDefinition["category"],
  ): Record<string, ShaderEffectDefinition> {
    return Object.fromEntries(
      Object.entries(ALL_SHADER_EFFECTS).filter(
        ([_, def]) => def.category === category,
      ),
    );
  }

  /**
   * List all available effects
   */
  listEffects(): { key: string; name: string; category: string }[] {
    return Object.entries(ALL_SHADER_EFFECTS).map(([key, def]) => ({
      key,
      name: def.name,
      category: def.category,
    }));
  }

  /**
   * Dispose resources
   */
  dispose(): void {
    this.engine.dispose();
    this.currentEffect = null;
  }
}

// =============================================================================
// SINGLETON EXPORT
// =============================================================================

let processorInstance: ShaderEffectProcessor | null = null;

export function getShaderEffectProcessor(): ShaderEffectProcessor {
  if (!processorInstance) {
    processorInstance = new ShaderEffectProcessor();
  }
  return processorInstance;
}

export function disposeShaderEffectProcessor(): void {
  if (processorInstance) {
    processorInstance.dispose();
    processorInstance = null;
  }
}
