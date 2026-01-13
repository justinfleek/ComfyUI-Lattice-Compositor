/**
 * Colormap Shader Utility
 *
 * Extracted from LatticeEngine.ts - provides colormap shader materials
 * for depth visualization overlays.
 *
 * Supports viridis, plasma, and grayscale colormaps.
 */

import * as THREE from "three";

export interface ColormapSettings {
  colormap: "viridis" | "plasma" | "grayscale";
  opacity: number;
}

const COLORMAP_VERTEX_SHADER = `
  varying vec2 vUv;
  void main() {
    vUv = uv;
    gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
  }
`;

const COLORMAP_FRAGMENT_SHADER = `
  uniform sampler2D depthMap;
  uniform float opacity;
  uniform int colormap;
  varying vec2 vUv;

  vec3 viridis(float t) {
    const vec3 c0 = vec3(0.267, 0.004, 0.329);
    const vec3 c1 = vec3(0.282, 0.140, 0.458);
    const vec3 c2 = vec3(0.253, 0.265, 0.529);
    const vec3 c3 = vec3(0.191, 0.407, 0.556);
    const vec3 c4 = vec3(0.127, 0.566, 0.551);
    const vec3 c5 = vec3(0.208, 0.718, 0.472);
    const vec3 c6 = vec3(0.565, 0.843, 0.262);
    const vec3 c7 = vec3(0.993, 0.906, 0.144);

    t = clamp(t, 0.0, 1.0);
    float i = t * 7.0;
    int idx = int(floor(i));
    float f = fract(i);

    if (idx < 1) return mix(c0, c1, f);
    if (idx < 2) return mix(c1, c2, f);
    if (idx < 3) return mix(c2, c3, f);
    if (idx < 4) return mix(c3, c4, f);
    if (idx < 5) return mix(c4, c5, f);
    if (idx < 6) return mix(c5, c6, f);
    return mix(c6, c7, f);
  }

  vec3 plasma(float t) {
    const vec3 c0 = vec3(0.050, 0.030, 0.528);
    const vec3 c1 = vec3(0.327, 0.012, 0.615);
    const vec3 c2 = vec3(0.534, 0.054, 0.553);
    const vec3 c3 = vec3(0.716, 0.215, 0.475);
    const vec3 c4 = vec3(0.863, 0.395, 0.362);
    const vec3 c5 = vec3(0.958, 0.590, 0.233);
    const vec3 c6 = vec3(0.995, 0.812, 0.166);
    const vec3 c7 = vec3(0.940, 0.975, 0.131);

    t = clamp(t, 0.0, 1.0);
    float i = t * 7.0;
    int idx = int(floor(i));
    float f = fract(i);

    if (idx < 1) return mix(c0, c1, f);
    if (idx < 2) return mix(c1, c2, f);
    if (idx < 3) return mix(c2, c3, f);
    if (idx < 4) return mix(c3, c4, f);
    if (idx < 5) return mix(c4, c5, f);
    if (idx < 6) return mix(c5, c6, f);
    return mix(c6, c7, f);
  }

  void main() {
    float depth = texture2D(depthMap, vUv).r;
    vec3 color;

    if (colormap == 0) {
      color = viridis(depth);
    } else if (colormap == 1) {
      color = plasma(depth);
    } else {
      color = vec3(depth);
    }

    gl_FragColor = vec4(color, opacity);
  }
`;

/**
 * Get colormap index from name
 */
export function getColormapIndex(colormap: string): number {
  return colormap === "viridis" ? 0 : colormap === "plasma" ? 1 : 2;
}

/**
 * Create a colormap shader material for depth visualization
 * @param texture - Depth texture to visualize
 * @param settings - Colormap and opacity settings
 */
export function createColormapMaterial(
  texture: THREE.Texture,
  settings: ColormapSettings,
): THREE.ShaderMaterial {
  return new THREE.ShaderMaterial({
    uniforms: {
      depthMap: { value: texture },
      opacity: { value: settings.opacity },
      colormap: { value: getColormapIndex(settings.colormap) },
    },
    vertexShader: COLORMAP_VERTEX_SHADER,
    fragmentShader: COLORMAP_FRAGMENT_SHADER,
    transparent: true,
    depthWrite: false,
  });
}

/**
 * Update colormap uniform on an existing material
 */
export function updateColormapUniform(
  material: THREE.ShaderMaterial,
  colormap: "viridis" | "plasma" | "grayscale",
): void {
  material.uniforms.colormap.value = getColormapIndex(colormap);
}

/**
 * Update opacity uniform on an existing material
 */
export function updateOpacityUniform(
  material: THREE.ShaderMaterial,
  opacity: number,
): void {
  material.uniforms.opacity.value = opacity;
}
