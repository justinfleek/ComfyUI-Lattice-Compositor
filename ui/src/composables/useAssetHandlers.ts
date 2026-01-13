/**
 * Asset Handlers Composable
 *
 * Handles asset panel event callbacks for the WorkspaceLayout.
 * Extracted from WorkspaceLayout.vue to reduce file size and improve maintainability.
 */

import type { Ref } from "vue";
import { useAssetStore } from "@/stores/assetStore";
import { useCompositorStore } from "@/stores/compositorStore";
import { useLayerStore } from "@/stores/layerStore";
import { useSelectionStore } from "@/stores/selectionStore";
import { isLayerOfType } from "@/types/project";
import type { ParticleLayerData } from "@/types/particles";

export interface AssetHandlersOptions {
  canvasRef: Ref<{ getEngine?: () => LatticeEngine | undefined } | null>;
}

interface LatticeEngine {
  setEnvironmentConfig(settings: unknown): void;
  loadEnvironmentMap(url: string, options: EnvironmentMapOptions): Promise<void>;
  setEnvironmentEnabled(enabled: boolean): void;
}

interface EnvironmentMapOptions {
  intensity?: number;
  rotation?: number;
  backgroundBlur?: number;
  useAsBackground?: boolean;
}

export function useAssetHandlers(options: AssetHandlersOptions) {
  const compositorStore = useCompositorStore();
  const layerStore = useLayerStore();
  const assetStore = useAssetStore();
  const selectionStore = useSelectionStore();

  const { canvasRef } = options;

  /**
   * Create layers from imported SVG paths
   */
  function onCreateLayersFromSvg(svgId: string): void {
    const storedSvg = assetStore.svgDocuments.get(svgId);
    if (!storedSvg) return;

    storedSvg.document.paths.forEach((path: { id: string }, index: number) => {
      const config = storedSvg.layerConfigs[index];

      const layer = layerStore.createShapeLayer(compositorStore);
      layerStore.renameLayer(compositorStore, layer.id, `${storedSvg.name}_${path.id}`);

      layerStore.updateLayerData(compositorStore, layer.id, {
        svgDocumentId: svgId,
        svgPathId: path.id,
        svgPathIndex: index,
        extrusionConfig: config,
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
   * Configure a particle emitter to use a mesh shape.
   * Works with 'particles' type layers (new particle system).
   */
  function onUseMeshAsEmitter(meshId: string): void {
    const emitterConfig = assetStore.getMeshEmitterConfig(meshId);
    if (!emitterConfig) return;

    const selectedLayerIds = selectionStore.selectedLayerIds;
    if (selectedLayerIds.length === 0) {
      console.warn("[Lattice] No layer selected for mesh emitter");
      return;
    }

    const layer = compositorStore.layers.find((l) => l.id === selectedLayerIds[0]);
    if (!layer) {
      console.warn("[Lattice] Selected layer not found");
      return;
    }

    // Use type guard for particles layer (new particle system)
    if (!isLayerOfType(layer, "particles")) {
      console.warn("[Lattice] Selected layer is not a particles layer");
      return;
    }

    // Now TypeScript knows layer.data is ParticleLayerData
    const particleData: ParticleLayerData = layer.data;
    const existingEmitters = particleData.emitters || [];

    // Update first emitter with mesh shape, or create new one
    const updatedEmitters = existingEmitters.length > 0
      ? existingEmitters.map((emitter, i) =>
          i === 0
            ? {
                ...emitter,
                shape: "mesh" as const,
                meshVertices: emitterConfig.meshVertices,
                meshNormals: emitterConfig.meshNormals,
              }
            : emitter
        )
      : [
          {
            shape: "mesh" as const,
            meshVertices: emitterConfig.meshVertices,
            meshNormals: emitterConfig.meshNormals,
          },
        ];

    layerStore.updateLayerData(compositorStore, layer.id, {
      emitters: updatedEmitters,
    });

    console.log(`[Lattice] Set mesh emitter for layer: ${layer.name}`);
  }

  /**
   * Update environment settings in the engine
   */
  function onEnvironmentUpdate(settings: unknown): void {
    const engine = canvasRef.value?.getEngine?.();
    if (!engine) return;
    engine.setEnvironmentConfig(settings);
  }

  /**
   * Load environment map into the engine
   */
  async function onEnvironmentLoad(settings: EnvironmentMapOptions & { url?: string }): Promise<void> {
    const engine = canvasRef.value?.getEngine?.();
    if (!engine || !settings.url) return;

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

  /**
   * Clear environment map from the engine
   */
  function onEnvironmentClear(): void {
    const engine = canvasRef.value?.getEngine?.();
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
