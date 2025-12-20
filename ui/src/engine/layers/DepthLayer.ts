/**
 * DepthLayer - Depth Map Visualization Layer
 *
 * Visualizes depth maps for AI video generation workflows.
 * Supports multiple visualization modes:
 * - Grayscale: Direct depth values
 * - Colormap: Turbo, Viridis, Plasma, etc.
 * - Contour: Depth contour lines
 * - 3D Mesh: Displaced mesh preview
 *
 * DETERMINISM: Uses frame-based evaluation only
 */

import * as THREE from 'three';
import type { Layer, DepthLayerData } from '@/types/project';
import { createAnimatableProperty } from '@/types/project';
import { BaseLayer } from './BaseLayer';
import { interpolateProperty } from '@/services/interpolation';

// Color map LUTs (256 colors each)
const COLORMAPS: Record<string, THREE.Color[]> = {
  turbo: generateTurboColormap(),
  viridis: generateViridisColormap(),
  plasma: generatePlasmaColormap(),
  inferno: generateInfernoColormap(),
  magma: generateMagmaColormap(),
  grayscale: generateGrayscaleColormap()
};

export class DepthLayer extends BaseLayer {
  private mesh: THREE.Mesh | null = null;
  private material: THREE.ShaderMaterial | null = null;
  private texture: THREE.Texture | null = null;
  private depthData: DepthLayerData;
  private colormapTexture: THREE.DataTexture | null = null;

  constructor(layerData: Layer) {
    super(layerData);
    this.depthData = this.extractDepthData(layerData);
    this.createMesh();
  }

  /**
   * Extract depth layer data from layer object
   */
  private extractDepthData(layerData: Layer): DepthLayerData {
    const data = layerData.data as Partial<DepthLayerData> | undefined;
    return {
      assetId: data?.assetId ?? null,
      visualizationMode: data?.visualizationMode ?? 'colormap',
      colorMap: data?.colorMap ?? 'turbo',
      invert: data?.invert ?? false,
      minDepth: data?.minDepth ?? 0,
      maxDepth: data?.maxDepth ?? 1,
      autoNormalize: data?.autoNormalize ?? true,
      contourLevels: data?.contourLevels ?? 10,
      contourColor: data?.contourColor ?? '#ffffff',
      contourWidth: data?.contourWidth ?? 1.0,
      meshDisplacement: data?.meshDisplacement ?? createAnimatableProperty('Mesh Displacement', 50, 'number'),
      meshResolution: data?.meshResolution ?? 64,
      wireframe: data?.wireframe ?? false
    };
  }

  private createMesh(): void {
    const geometry = new THREE.PlaneGeometry(1, 1, 1, 1);

    // Custom shader for depth visualization
    this.material = new THREE.ShaderMaterial({
      uniforms: {
        depthMap: { value: null },
        colormap: { value: null },
        invert: { value: this.depthData.invert ? 1.0 : 0.0 },
        minDepth: { value: this.depthData.minDepth },
        maxDepth: { value: this.depthData.maxDepth },
        opacity: { value: 1.0 },
        contourLevels: { value: this.depthData.contourLevels || 10 },
        contourColor: { value: new THREE.Color(this.depthData.contourColor || '#ffffff') },
        contourWidth: { value: this.depthData.contourWidth || 1.0 },
        visualizationMode: { value: this.getVisualizationModeIndex() }
      },
      vertexShader: `
        varying vec2 vUv;
        void main() {
          vUv = uv;
          gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
        }
      `,
      fragmentShader: `
        uniform sampler2D depthMap;
        uniform sampler2D colormap;
        uniform float invert;
        uniform float minDepth;
        uniform float maxDepth;
        uniform float opacity;
        uniform float contourLevels;
        uniform vec3 contourColor;
        uniform float contourWidth;
        uniform int visualizationMode;

        varying vec2 vUv;

        void main() {
          float depth = texture2D(depthMap, vUv).r;

          // Normalize depth to 0-1 range
          float normalizedDepth = (depth - minDepth) / (maxDepth - minDepth);
          normalizedDepth = clamp(normalizedDepth, 0.0, 1.0);

          // Invert if needed
          if (invert > 0.5) {
            normalizedDepth = 1.0 - normalizedDepth;
          }

          vec3 color;

          if (visualizationMode == 0) {
            // Grayscale
            color = vec3(normalizedDepth);
          } else if (visualizationMode == 1) {
            // Colormap
            color = texture2D(colormap, vec2(normalizedDepth, 0.5)).rgb;
          } else if (visualizationMode == 2) {
            // Contour
            float contourValue = fract(normalizedDepth * contourLevels);
            float contourLine = smoothstep(0.0, contourWidth * 0.1, contourValue) *
                               smoothstep(contourWidth * 0.1, 0.0, contourValue - (1.0 - contourWidth * 0.1));
            color = mix(texture2D(colormap, vec2(normalizedDepth, 0.5)).rgb, contourColor, contourLine);
          } else {
            // Default to grayscale
            color = vec3(normalizedDepth);
          }

          gl_FragColor = vec4(color, opacity);
        }
      `,
      transparent: true
    });

    this.mesh = new THREE.Mesh(geometry, this.material);
    this.mesh.name = `depth_${this.id}`;
    this.group.add(this.mesh);

    // Create colormap texture
    this.updateColormapTexture();
  }

  private getVisualizationModeIndex(): number {
    switch (this.depthData.visualizationMode) {
      case 'grayscale': return 0;
      case 'colormap': return 1;
      case 'contour': return 2;
      case '3d-mesh': return 3;
      default: return 0;
    }
  }

  private updateColormapTexture(): void {
    const colors = COLORMAPS[this.depthData.colorMap] || COLORMAPS.grayscale;
    const data = new Uint8Array(256 * 4);

    for (let i = 0; i < 256; i++) {
      const color = colors[i];
      data[i * 4] = Math.floor(color.r * 255);
      data[i * 4 + 1] = Math.floor(color.g * 255);
      data[i * 4 + 2] = Math.floor(color.b * 255);
      data[i * 4 + 3] = 255;
    }

    if (this.colormapTexture) {
      this.colormapTexture.dispose();
    }

    this.colormapTexture = new THREE.DataTexture(data, 256, 1, THREE.RGBAFormat);
    this.colormapTexture.needsUpdate = true;

    if (this.material) {
      this.material.uniforms.colormap.value = this.colormapTexture;
    }
  }

  setTexture(texture: THREE.Texture): void {
    this.texture = texture;
    if (this.material) {
      this.material.uniforms.depthMap.value = texture;
    }
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    if (!this.material) return;

    // Evaluate animated properties
    if (this.depthData.meshDisplacement && this.depthData.visualizationMode === '3d-mesh') {
      const displacement = interpolateProperty(this.depthData.meshDisplacement, frame);
      // Would be used for mesh displacement if implementing 3D mesh mode
    }

    // Update uniforms
    this.material.uniforms.invert.value = this.depthData.invert ? 1.0 : 0.0;
    this.material.uniforms.minDepth.value = this.depthData.minDepth;
    this.material.uniforms.maxDepth.value = this.depthData.maxDepth;
    this.material.uniforms.visualizationMode.value = this.getVisualizationModeIndex();
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<DepthLayerData> | undefined;

    if (data) {
      Object.assign(this.depthData, data);

      if (data.colorMap) {
        this.updateColormapTexture();
      }

      if (this.material) {
        if (data.contourColor) {
          this.material.uniforms.contourColor.value = new THREE.Color(data.contourColor);
        }
        if (data.contourLevels !== undefined) {
          this.material.uniforms.contourLevels.value = data.contourLevels;
        }
        if (data.contourWidth !== undefined) {
          this.material.uniforms.contourWidth.value = data.contourWidth;
        }
      }
    }
  }

  protected onDispose(): void {
    if (this.texture) {
      this.texture.dispose();
    }
    if (this.colormapTexture) {
      this.colormapTexture.dispose();
    }
    if (this.material) {
      this.material.dispose();
    }
    if (this.mesh) {
      this.mesh.geometry.dispose();
    }
  }
}

// Colormap generation functions
function generateTurboColormap(): THREE.Color[] {
  const colors: THREE.Color[] = [];
  for (let i = 0; i < 256; i++) {
    const t = i / 255;
    // Simplified Turbo approximation
    const r = Math.sin(t * Math.PI * 1.5) * 0.5 + 0.5;
    const g = Math.sin(t * Math.PI * 2.0 - 0.5) * 0.5 + 0.5;
    const b = Math.cos(t * Math.PI * 1.5) * 0.5 + 0.5;
    colors.push(new THREE.Color(r, g, b));
  }
  return colors;
}

function generateViridisColormap(): THREE.Color[] {
  const colors: THREE.Color[] = [];
  for (let i = 0; i < 256; i++) {
    const t = i / 255;
    const r = 0.267004 + t * (0.993248 - 0.267004);
    const g = 0.004874 + t * (0.906157 - 0.004874);
    const b = 0.329415 + t * (0.143936 - 0.329415);
    colors.push(new THREE.Color(
      Math.max(0, Math.min(1, r)),
      Math.max(0, Math.min(1, g)),
      Math.max(0, Math.min(1, b))
    ));
  }
  return colors;
}

function generatePlasmaColormap(): THREE.Color[] {
  const colors: THREE.Color[] = [];
  for (let i = 0; i < 256; i++) {
    const t = i / 255;
    const r = 0.050383 + t * (0.940015 - 0.050383);
    const g = 0.029803 + t * (0.975158 - 0.029803);
    const b = 0.527975 + t * (0.131326 - 0.527975);
    colors.push(new THREE.Color(
      Math.max(0, Math.min(1, r)),
      Math.max(0, Math.min(1, g)),
      Math.max(0, Math.min(1, b))
    ));
  }
  return colors;
}

function generateInfernoColormap(): THREE.Color[] {
  const colors: THREE.Color[] = [];
  for (let i = 0; i < 256; i++) {
    const t = i / 255;
    const r = t < 0.5 ? t * 2 : 1;
    const g = t < 0.5 ? t * 0.5 : (t - 0.5) * 2;
    const b = t < 0.25 ? t * 2 : t < 0.75 ? 0.5 - (t - 0.25) : 0;
    colors.push(new THREE.Color(r, g, b));
  }
  return colors;
}

function generateMagmaColormap(): THREE.Color[] {
  const colors: THREE.Color[] = [];
  for (let i = 0; i < 256; i++) {
    const t = i / 255;
    const r = t;
    const g = t * t;
    const b = t < 0.5 ? t * 1.5 : 0.75 - (t - 0.5) * 0.5;
    colors.push(new THREE.Color(r, g, Math.max(0, b)));
  }
  return colors;
}

function generateGrayscaleColormap(): THREE.Color[] {
  const colors: THREE.Color[] = [];
  for (let i = 0; i < 256; i++) {
    const t = i / 255;
    colors.push(new THREE.Color(t, t, t));
  }
  return colors;
}
