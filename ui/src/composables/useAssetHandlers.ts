/**
 * Asset Handlers Composable
 *
 * Handles asset panel event callbacks for the WorkspaceLayout.
 * Extracted from WorkspaceLayout.vue to reduce file size and improve maintainability.
 */

import type { Ref } from "vue";
import { useAssetStore } from "@/stores/assetStore";
import { useCompositorStore } from "@/stores/compositorStore";

export interface AssetHandlersOptions {
  // Template ref to component that exposes getEngine() - can be ThreeCanvas or CenterViewport
  canvasRef: Ref<any>;
}

export function useAssetHandlers(options: AssetHandlersOptions) {
  // Cast to any because Pinia store actions are spread from external modules
  const store = useCompositorStore() as any;
  const assetStore = useAssetStore();

  const { canvasRef } = options;

  /**
   * Create layers from imported SVG paths
   */
  function onCreateLayersFromSvg(svgId: string) {
    const storedSvg = assetStore.svgDocuments.get(svgId);
    if (!storedSvg) return;

    // Create a model layer for each path in the SVG
    storedSvg.document.paths.forEach((path: any, index: number) => {
      const config = storedSvg.layerConfigs[index];

      // Create a 3D model layer
      // Note: This would ideally create a proper ModelLayer with the extruded geometry
      // For now, we'll create a shape layer with the path data
      const layer = store.createShapeLayer();
      store.renameLayer(layer.id, `${storedSvg.name}_${path.id}`);

      // Store the SVG path reference in the layer data
      store.updateLayerData(layer.id, {
        svgDocumentId: svgId,
        svgPathId: path.id,
        svgPathIndex: index,
        extrusionConfig: config,
        // Set Z position based on layer depth
        transform: {
          ...layer.transform,
          position: {
            ...layer.transform.position,
            value: {
              ...layer.transform.position.value,
              z: config?.depth || 0,
            },
          },
        },
      });
    });

    console.log(
      `[Lattice] Created ${storedSvg.document.paths.length} layers from SVG: ${storedSvg.name}`,
    );
  }

  /**
   * Configure a particle emitter to use a mesh shape
   */
  function onUseMeshAsEmitter(meshId: string) {
    const emitterConfig = assetStore.getMeshEmitterConfig(meshId);
    if (!emitterConfig) return;

    // Get the selected layer if it's a particle layer
    const selectedLayerIds = store.selectedLayerIds;
    if (selectedLayerIds.length === 0) {
      console.warn("[Lattice] No layer selected for mesh emitter");
      return;
    }

    const layer = store.layers.find((l: any) => l.id === selectedLayerIds[0]);
    if (!layer || layer.type !== "particle") {
      console.warn("[Lattice] Selected layer is not a particle layer");
      return;
    }

    // Update the particle layer's emitter config with mesh vertices
    store.updateLayerData(layer.id, {
      emitter: {
        ...(layer.data as any).emitter,
        shape: "mesh",
        meshVertices: emitterConfig.meshVertices,
        meshNormals: emitterConfig.meshNormals,
      },
    });

    console.log(`[Lattice] Set mesh emitter for layer: ${layer.name}`);
  }

  /**
   * Update environment settings in the engine
   */
  function onEnvironmentUpdate(settings: any) {
    if (!canvasRef.value) return;
    const engine = canvasRef.value.getEngine?.();
    if (!engine) return;

    engine.setEnvironmentConfig(settings);
  }

  /**
   * Load environment map into the engine
   */
  async function onEnvironmentLoad(settings: any) {
    if (!canvasRef.value) return;
    const engine = canvasRef.value.getEngine?.();
    if (!engine) return;

    if (settings.url) {
      try {
        await engine.loadEnvironmentMap(settings.url, {
          intensity: settings.intensity,
          rotation: settings.rotation,
          backgroundBlur: settings.backgroundBlur,
          useAsBackground: settings.useAsBackground,
        });
        console.log("[Lattice] Environment map loaded");
      } catch (error) {
        console.error("[Lattice] Failed to load environment map:", error);
      }
    }
  }

  /**
   * Clear environment map from the engine
   */
  function onEnvironmentClear() {
    if (!canvasRef.value) return;
    const engine = canvasRef.value.getEngine?.();
    if (!engine) return;

    engine.setEnvironmentEnabled(false);
  }

  return {
    onCreateLayersFromSvg,
    onUseMeshAsEmitter,
    onEnvironmentUpdate,
    onEnvironmentLoad,
    onEnvironmentClear,
  };
}
