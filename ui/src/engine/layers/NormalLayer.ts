/**
 * NormalLayer - Normal Map Visualization Layer
 *
 * Visualizes normal maps for AI video generation workflows.
 * Supports multiple visualization modes:
 * - RGB: Direct normal values as colors
 * - Hemisphere: Hemisphere colorization
 * - Arrows: Normal direction arrows
 * - Lit: Fake lighting preview
 *
 * DETERMINISM: Uses frame-based evaluation only
 */

import * as THREE from "three";
import type { Layer, NormalLayerData } from "@/types/project";
import { BaseLayer } from "./BaseLayer";

export class NormalLayer extends BaseLayer {
  private mesh: THREE.Mesh | null = null;
  private material: THREE.ShaderMaterial | null = null;
  private texture: THREE.Texture | null = null;
  private normalData: NormalLayerData;

  constructor(layerData: Layer) {
    super(layerData);
    this.normalData = this.extractNormalData(layerData);
    this.createMesh();
  }

  /**
   * Extract normal layer data from layer object
   */
  private extractNormalData(layerData: Layer): NormalLayerData {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
    const data = layerData.data as Partial<NormalLayerData> | undefined;
    const assetId = (data !== null && data !== undefined && typeof data === "object" && "assetId" in data) ? data.assetId : null;
    const visualizationMode = (data !== null && data !== undefined && typeof data === "object" && "visualizationMode" in data && typeof data.visualizationMode === "string" && data.visualizationMode.length > 0) ? data.visualizationMode : "rgb";
    const format = (data !== null && data !== undefined && typeof data === "object" && "format" in data && typeof data.format === "string" && data.format.length > 0) ? data.format : "opengl";
    const flipX = (data !== null && data !== undefined && typeof data === "object" && "flipX" in data && typeof data.flipX === "boolean") ? data.flipX : false;
    const flipY = (data !== null && data !== undefined && typeof data === "object" && "flipY" in data && typeof data.flipY === "boolean") ? data.flipY : false;
    const flipZ = (data !== null && data !== undefined && typeof data === "object" && "flipZ" in data && typeof data.flipZ === "boolean") ? data.flipZ : false;
    const arrowDensity = (data !== null && data !== undefined && typeof data === "object" && "arrowDensity" in data && typeof data.arrowDensity === "number" && Number.isFinite(data.arrowDensity) && data.arrowDensity > 0) ? data.arrowDensity : 16;
    const arrowScale = (data !== null && data !== undefined && typeof data === "object" && "arrowScale" in data && typeof data.arrowScale === "number" && Number.isFinite(data.arrowScale) && data.arrowScale > 0) ? data.arrowScale : 1;
    const arrowColor = (data !== null && data !== undefined && typeof data === "object" && "arrowColor" in data && typeof data.arrowColor === "string" && data.arrowColor.length > 0) ? data.arrowColor : "#00ff00";
    const lightDirection = (data !== null && data !== undefined && typeof data === "object" && "lightDirection" in data && typeof data.lightDirection === "object" && data.lightDirection !== null) ? data.lightDirection : { x: 0.5, y: 0.5, z: 1.0 };
    const lightIntensity = (data !== null && data !== undefined && typeof data === "object" && "lightIntensity" in data && typeof data.lightIntensity === "number" && Number.isFinite(data.lightIntensity) && data.lightIntensity >= 0) ? data.lightIntensity : 1.0;
    const ambientIntensity = (data !== null && data !== undefined && typeof data === "object" && "ambientIntensity" in data && typeof data.ambientIntensity === "number" && Number.isFinite(data.ambientIntensity) && data.ambientIntensity >= 0) ? data.ambientIntensity : 0.2;
    return {
      assetId,
      visualizationMode,
      format,
      flipX,
      flipY,
      flipZ,
      arrowDensity,
      arrowScale,
      arrowColor,
      lightDirection,
      lightIntensity,
      ambientIntensity,
    };
  }

  private createMesh(): void {
    const geometry = new THREE.PlaneGeometry(1, 1, 1, 1);

    this.material = new THREE.ShaderMaterial({
      uniforms: {
        normalMap: { value: null },
        flipX: { value: this.normalData.flipX ? -1.0 : 1.0 },
        flipY: { value: this.normalData.flipY ? -1.0 : 1.0 },
        flipZ: { value: this.normalData.flipZ ? -1.0 : 1.0 },
        lightDirection: {
          value: new THREE.Vector3(
            // Validate light direction (NaN would corrupt lighting calculations after normalize())
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
            (() => {
              const lightDir = (this.normalData != null && typeof this.normalData === "object" && "lightDirection" in this.normalData && this.normalData.lightDirection != null && typeof this.normalData.lightDirection === "object") ? this.normalData.lightDirection : undefined;
              const lightDirX = (lightDir != null && typeof lightDir === "object" && "x" in lightDir && typeof lightDir.x === "number") ? lightDir.x : undefined;
              return Number.isFinite(lightDirX) ? lightDirX : 0.5;
            })(),
            (() => {
              const lightDir = (this.normalData != null && typeof this.normalData === "object" && "lightDirection" in this.normalData && this.normalData.lightDirection != null && typeof this.normalData.lightDirection === "object") ? this.normalData.lightDirection : undefined;
              const lightDirY = (lightDir != null && typeof lightDir === "object" && "y" in lightDir && typeof lightDir.y === "number") ? lightDir.y : undefined;
              return Number.isFinite(lightDirY) ? lightDirY : 0.5;
            })(),
            (() => {
              const lightDir = (this.normalData != null && typeof this.normalData === "object" && "lightDirection" in this.normalData && this.normalData.lightDirection != null && typeof this.normalData.lightDirection === "object") ? this.normalData.lightDirection : undefined;
              const lightDirZ = (lightDir != null && typeof lightDir === "object" && "z" in lightDir && typeof lightDir.z === "number") ? lightDir.z : undefined;
              return Number.isFinite(lightDirZ) ? lightDirZ : 1.0;
            })(),
          ).normalize(),
        },
        lightIntensity: {
          value: Number.isFinite(this.normalData.lightIntensity)
            ? this.normalData.lightIntensity
            : 1.0,
        },
        ambientIntensity: {
          value: Number.isFinite(this.normalData.ambientIntensity)
            ? this.normalData.ambientIntensity
            : 0.2,
        },
        opacity: { value: 1.0 },
        visualizationMode: { value: this.getVisualizationModeIndex() },
        isDirectX: { value: this.normalData.format === "directx" ? 1.0 : 0.0 },
      },
      vertexShader: `
        varying vec2 vUv;
        void main() {
          vUv = uv;
          gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
        }
      `,
      fragmentShader: `
        uniform sampler2D normalMap;
        uniform float flipX;
        uniform float flipY;
        uniform float flipZ;
        uniform vec3 lightDirection;
        uniform float lightIntensity;
        uniform float ambientIntensity;
        uniform float opacity;
        uniform int visualizationMode;
        uniform float isDirectX;

        varying vec2 vUv;

        void main() {
          vec3 normal = texture2D(normalMap, vUv).rgb * 2.0 - 1.0;

          // Apply flips
          normal.x *= flipX;
          normal.y *= flipY;
          normal.z *= flipZ;

          // Convert DirectX normals to OpenGL if needed
          if (isDirectX > 0.5) {
            normal.y = -normal.y;
          }

          normal = normalize(normal);

          vec3 color;

          if (visualizationMode == 0) {
            // RGB - direct normal visualization
            color = normal * 0.5 + 0.5;
          } else if (visualizationMode == 1) {
            // Hemisphere - hemisphere colorization
            color = vec3(
              normal.x * 0.5 + 0.5,
              normal.y * 0.5 + 0.5,
              max(0.0, normal.z)
            );
          } else if (visualizationMode == 3) {
            // Lit - fake lighting preview
            float diffuse = max(0.0, dot(normal, lightDirection));
            color = vec3(ambientIntensity + diffuse * lightIntensity);
          } else {
            // Default to RGB
            color = normal * 0.5 + 0.5;
          }

          gl_FragColor = vec4(color, opacity);
        }
      `,
      transparent: true,
    });

    this.mesh = new THREE.Mesh(geometry, this.material);
    this.mesh.name = `normal_${this.id}`;
    this.group.add(this.mesh);
  }

  private getVisualizationModeIndex(): number {
    switch (this.normalData.visualizationMode) {
      case "rgb":
        return 0;
      case "hemisphere":
        return 1;
      case "lit":
        return 3;
      default:
        return 0;
    }
  }

  setTexture(texture: THREE.Texture): void {
    this.texture = texture;
    if (this.material) {
      this.material.uniforms.normalMap.value = texture;
    }
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(_frame: number): void {
    if (!this.material) return;

    // Update uniforms from data
    this.material.uniforms.flipX.value = this.normalData.flipX ? -1.0 : 1.0;
    this.material.uniforms.flipY.value = this.normalData.flipY ? -1.0 : 1.0;
    this.material.uniforms.flipZ.value = this.normalData.flipZ ? -1.0 : 1.0;
    this.material.uniforms.visualizationMode.value =
      this.getVisualizationModeIndex();
    this.material.uniforms.isDirectX.value =
      this.normalData.format === "directx" ? 1.0 : 0.0;

    if (this.normalData.lightDirection) {
      // Validate light direction values (NaN would corrupt normalize() result)
      const lx = Number.isFinite(this.normalData.lightDirection.x)
        ? this.normalData.lightDirection.x
        : 0.5;
      const ly = Number.isFinite(this.normalData.lightDirection.y)
        ? this.normalData.lightDirection.y
        : 0.5;
      const lz = Number.isFinite(this.normalData.lightDirection.z)
        ? this.normalData.lightDirection.z
        : 1.0;
      this.material.uniforms.lightDirection.value.set(lx, ly, lz).normalize();
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<NormalLayerData> | undefined;

    if (data) {
      Object.assign(this.normalData, data);
    }
  }

  protected onDispose(): void {
    if (this.texture) {
      this.texture.dispose();
    }
    if (this.material) {
      this.material.dispose();
    }
    if (this.mesh) {
      this.mesh.geometry.dispose();
    }
  }
}
