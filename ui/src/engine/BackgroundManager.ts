/**
 * Background Manager
 *
 * Extracted from LatticeEngine.ts - handles background images and
 * depth map overlay visualization.
 *
 * Features:
 * - Background image display
 * - Depth map overlay with colormap shaders (viridis, plasma, grayscale)
 * - Opacity and visibility controls
 */

import * as THREE from "three";
import type { SceneManager } from "./core/SceneManager";
import {
  createColormapMaterial,
  updateColormapUniform,
  updateOpacityUniform,
} from "./utils/colormapShader";

export type ColormapType = "viridis" | "plasma" | "grayscale";

export interface DepthMapSettings {
  colormap: ColormapType;
  opacity: number;
  visible: boolean;
}

export class BackgroundManager {
  private backgroundImage: THREE.Mesh | null = null;
  private depthMapMesh: THREE.Mesh | null = null;
  private depthMapSettings: DepthMapSettings = {
    colormap: "viridis",
    opacity: 0.5,
    visible: false,
  };

  constructor(private readonly scene: SceneManager) {}

  /**
   * Set a background image for the composition
   * @param image - HTMLImageElement to use as background
   */
  setBackgroundImage(image: HTMLImageElement): void {
    // Remove existing background
    if (this.backgroundImage) {
      this.scene.removeFromComposition(this.backgroundImage);
      this.backgroundImage.geometry.dispose();
      (this.backgroundImage.material as THREE.Material).dispose();
    }

    // Create texture from image
    const texture = new THREE.Texture(image);
    texture.needsUpdate = true;
    texture.colorSpace = THREE.SRGBColorSpace;

    // Create plane geometry matching image dimensions
    const geometry = new THREE.PlaneGeometry(image.width, image.height);
    const material = new THREE.MeshBasicMaterial({
      map: texture,
      transparent: true,
      depthWrite: false,
    });

    this.backgroundImage = new THREE.Mesh(geometry, material);
    this.backgroundImage.position.set(image.width / 2, image.height / 2, -1000);
    this.backgroundImage.userData.isBackground = true;

    this.scene.addToComposition(this.backgroundImage);
  }

  /**
   * Set the depth map overlay
   * @param image - HTMLImageElement containing depth data
   * @param options - Display options
   */
  setDepthMap(
    image: HTMLImageElement,
    options: { colormap?: ColormapType; opacity?: number; visible?: boolean },
  ): void {
    this.depthMapSettings = {
      colormap: options.colormap ?? this.depthMapSettings.colormap,
      opacity: options.opacity ?? this.depthMapSettings.opacity,
      visible: options.visible ?? this.depthMapSettings.visible,
    };

    // Remove existing depth map mesh
    if (this.depthMapMesh) {
      this.scene.removeFromComposition(this.depthMapMesh);
      this.depthMapMesh.geometry.dispose();
      (this.depthMapMesh.material as THREE.Material).dispose();
    }

    // Create texture from image
    const texture = new THREE.Texture(image);
    texture.needsUpdate = true;

    // Create colormap shader material
    const material = createColormapMaterial(texture, this.depthMapSettings);

    const geometry = new THREE.PlaneGeometry(image.width, image.height);
    this.depthMapMesh = new THREE.Mesh(geometry, material);
    this.depthMapMesh.position.set(image.width / 2, image.height / 2, -999);
    this.depthMapMesh.visible = this.depthMapSettings.visible;
    this.depthMapMesh.userData.isDepthOverlay = true;

    this.scene.addToComposition(this.depthMapMesh);
  }

  /**
   * Set depth overlay visibility
   */
  setDepthOverlayVisible(visible: boolean): void {
    this.depthMapSettings.visible = visible;
    if (this.depthMapMesh) {
      this.depthMapMesh.visible = visible;
    }
  }

  /**
   * Set depth colormap
   */
  setDepthColormap(colormap: ColormapType): void {
    this.depthMapSettings.colormap = colormap;
    if (this.depthMapMesh) {
      const material = this.depthMapMesh.material as THREE.ShaderMaterial;
      updateColormapUniform(material, colormap);
    }
  }

  /**
   * Set depth overlay opacity
   */
  setDepthOpacity(opacity: number): void {
    this.depthMapSettings.opacity = opacity;
    if (this.depthMapMesh) {
      const material = this.depthMapMesh.material as THREE.ShaderMaterial;
      updateOpacityUniform(material, opacity);
    }
  }

  /**
   * Get current depth map settings
   */
  getDepthMapSettings(): DepthMapSettings {
    return { ...this.depthMapSettings };
  }

  /**
   * Check if background image exists
   */
  hasBackgroundImage(): boolean {
    return this.backgroundImage !== null;
  }

  /**
   * Check if depth map exists
   */
  hasDepthMap(): boolean {
    return this.depthMapMesh !== null;
  }

  /**
   * Dispose all resources
   */
  dispose(): void {
    if (this.backgroundImage) {
      this.scene.removeFromComposition(this.backgroundImage);
      this.backgroundImage.geometry.dispose();
      (this.backgroundImage.material as THREE.Material).dispose();
      this.backgroundImage = null;
    }

    if (this.depthMapMesh) {
      this.scene.removeFromComposition(this.depthMapMesh);
      this.depthMapMesh.geometry.dispose();
      (this.depthMapMesh.material as THREE.Material).dispose();
      this.depthMapMesh = null;
    }
  }
}
