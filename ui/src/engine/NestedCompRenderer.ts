/**
 * Nested Composition Renderer
 *
 * Extracted from LatticeEngine.ts - handles render-to-texture for
 * nested compositions (precomps/NestedComps).
 *
 * Manages:
 * - Per-composition scene and layer manager caches
 * - Frame-level texture caching
 * - Resource cleanup
 */

import * as THREE from "three";
import type { Layer } from "@/types/project";
import { engineLogger } from "@/utils/logger";
import { LayerManager } from "./core/LayerManager";
import type { RenderPipeline } from "./core/RenderPipeline";
import type { ResourceManager } from "./core/ResourceManager";
import { SceneManager } from "./core/SceneManager";
import type { LayerAudioReactiveGetter } from "./LatticeEngine";

export interface CompositionSettings {
  width: number;
  height: number;
  fps: number;
}

export class NestedCompRenderer {
  /** Cache of layer managers for nested compositions */
  private layerManagers: Map<string, LayerManager> = new Map();

  /** Cache of scenes for nested compositions */
  private scenes: Map<string, SceneManager> = new Map();

  /** Cache of last rendered frame per composition (for texture caching) */
  private lastRenderedFrame: Map<string, number> = new Map();

  constructor(
    private readonly resources: ResourceManager,
    private readonly renderer: RenderPipeline,
    private readonly mainCamera: THREE.PerspectiveCamera,
  ) {}

  /**
   * Render a composition to a texture
   * Used by NestedCompLayer to render nested compositions
   *
   * @param compositionId - The composition ID to render
   * @param layers - The layers in that composition
   * @param settings - Composition settings (width, height, fps)
   * @param frame - The frame to render
   * @param audioReactiveGetter - Optional audio reactive callback
   * @returns The rendered texture, or null if rendering fails
   */
  renderToTexture(
    compositionId: string,
    layers: Layer[],
    settings: CompositionSettings,
    frame: number,
    audioReactiveGetter: LayerAudioReactiveGetter | null = null,
  ): THREE.Texture | null {
    try {
      // Check if we already rendered this frame (texture caching)
      const lastFrame = this.lastRenderedFrame.get(compositionId);
      const target = this.renderer.getNestedCompRenderTarget(
        compositionId,
        settings.width,
        settings.height,
      );

      // If same frame, return cached texture
      if (lastFrame === frame) {
        return target.texture;
      }

      // Get or create scene for this composition
      let scene = this.scenes.get(compositionId);
      if (!scene) {
        scene = new SceneManager(null);
        scene.setCompositionSize(settings.width, settings.height);
        this.scenes.set(compositionId, scene);
      }

      // Get or create layer manager for this composition
      let layerManager = this.layerManagers.get(compositionId);
      if (!layerManager) {
        layerManager = new LayerManager(scene, this.resources);
        layerManager.setRenderer(this.renderer.getWebGLRenderer());
        layerManager.setCompositionFPS(settings.fps);
        layerManager.setCamera(this.mainCamera);
        this.layerManagers.set(compositionId, layerManager);
      }

      // Sync layers - add new, update existing, remove deleted
      const currentLayerIds = new Set(layerManager.getLayerIds());
      const targetLayerIds = new Set(layers.map((l) => l.id));

      // Remove layers that are no longer in the composition
      for (const id of currentLayerIds) {
        if (!targetLayerIds.has(id)) {
          layerManager.remove(id);
        }
      }

      // Add or update layers
      for (const layerData of layers) {
        if (currentLayerIds.has(layerData.id)) {
          layerManager.update(layerData.id, layerData);
        } else {
          layerManager.create(layerData);
        }
      }

      // Evaluate layers at the given frame
      layerManager.evaluateFrame(frame, audioReactiveGetter);

      // Create a camera for this composition size
      const orthoCamera = new THREE.OrthographicCamera(
        -settings.width / 2,
        settings.width / 2,
        settings.height / 2,
        -settings.height / 2,
        0.1,
        10000,
      );
      orthoCamera.position.set(0, 0, 1000);
      orthoCamera.lookAt(0, 0, 0);

      // Render to texture
      const texture = this.renderer.renderSceneToTexture(
        scene.scene,
        orthoCamera,
        target,
      );

      // Cache the frame number
      this.lastRenderedFrame.set(compositionId, frame);

      return texture;
    } catch (error) {
      engineLogger.error(
        "Failed to render composition to texture:",
        compositionId,
        error,
      );
      return null;
    }
  }

  /**
   * Clear cache for a specific composition
   * Call when a composition is deleted or significantly changed
   */
  clearCache(compositionId: string): void {
    const layerManager = this.layerManagers.get(compositionId);
    if (layerManager) {
      layerManager.dispose();
      this.layerManagers.delete(compositionId);
    }

    const scene = this.scenes.get(compositionId);
    if (scene) {
      scene.dispose();
      this.scenes.delete(compositionId);
    }

    this.lastRenderedFrame.delete(compositionId);
    this.renderer.disposeNestedCompTarget(compositionId);
  }

  /**
   * Clear all cached compositions
   */
  clearAllCaches(): void {
    for (const [id] of this.layerManagers) {
      this.clearCache(id);
    }
    this.renderer.disposeAllNestedCompTargets();
  }

  /**
   * Dispose all resources
   */
  dispose(): void {
    this.clearAllCaches();
  }
}
