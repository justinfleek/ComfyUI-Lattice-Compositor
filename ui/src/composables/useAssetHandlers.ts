/**
 * Asset Handlers Composable
 *
 * Handles asset panel event callbacks for the WorkspaceLayout.
 * Extracted from WorkspaceLayout.vue to reduce file size and improve maintainability.
 */

import type { Ref } from "vue";
import { useAssetStore } from "@/stores/assetStore";
import { useLayerStore } from "@/stores/layerStore";
import { useProjectStore } from "@/stores/projectStore";
import { useSelectionStore } from "@/stores/selectionStore";
import { isLayerOfType } from "@/types/project";
import type { ParticleLayerData } from "@/types/particles";
import { isObject } from "@/utils/typeGuards";

// Type for CenterViewport exposed properties (matches defineExpose in CenterViewport.vue)
// Vue's defineExpose exposes refs/computeds directly - threeCanvasRef is a Ref, engine is a ComputedRef
export interface CenterViewportExposed {
  threeCanvasRef?: import("vue").Ref<InstanceType<typeof import("@/components/canvas/ThreeCanvas.vue").default> | null>;
  getEngine?: () => LatticeEngine | undefined;
  engine?: import("vue").ComputedRef<LatticeEngine | null>;
}

export interface AssetHandlersOptions {
  canvasRef: Ref<InstanceType<typeof import("@/components/layout/CenterViewport.vue").default> | null>;
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
  const projectStore = useProjectStore();
  const layerStore = useLayerStore();
  const assetStore = useAssetStore();
  const selectionStore = useSelectionStore();

  const { canvasRef } = options;
  
  // Helper to safely access getEngine from exposed properties
  // Vue exposes functions directly via defineExpose - use runtime property check with type guards
  function getEngine(): LatticeEngine | undefined {
    const viewport = canvasRef.value;
    if (!viewport || !isObject(viewport)) return undefined;
    // Runtime check: Vue exposes getEngine as a function
    // Use property access with runtime check - TypeScript can't know about exposed properties
    const getEngineProp = viewport.getEngine;
    if (typeof getEngineProp === "function") {
      const engine = getEngineProp();
      // Type guard: verify it's the expected engine type
      if (engine && isObject(engine)) {
        return engine as LatticeEngine;
      }
    }
    return undefined;
  }

  /**
   * Create layers from imported SVG paths
   */
  function onCreateLayersFromSvg(svgId: string): void {
    const storedSvg = assetStore.svgDocuments.get(svgId);
    if (!storedSvg) return;

    storedSvg.document.paths.forEach((path: { id: string }, index: number) => {
      const config = storedSvg.layerConfigs[index];

      // Create CompositorStoreAccess helper for layerStore.createShapeLayer which still requires it
      // TODO: Phase 5 - Remove CompositorStoreAccess parameter from createShapeLayer
      const compositorStoreAccess = {
        project: {
          composition: {
            width: projectStore.project.composition.width,
            height: projectStore.project.composition.height,
          },
          meta: projectStore.project.meta,
        },
        getActiveComp: () => projectStore.getActiveComp(),
        getActiveCompLayers: () => projectStore.getActiveCompLayers(),
        pushHistory: () => projectStore.pushHistory(),
      };

      const layer = layerStore.createShapeLayer(compositorStoreAccess);
      layerStore.renameLayer(layer.id, `${storedSvg.name}_${path.id}`);

      layerStore.updateLayerData(layer.id, {
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

    const layers = projectStore.getActiveCompLayers();
    const layer = layers.find((l) => l.id === selectedLayerIds[0]);
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

    layerStore.updateLayerData(layer.id, {
      emitters: updatedEmitters,
    });

    console.log(`[Lattice] Set mesh emitter for layer: ${layer.name}`);
  }

  /**
   * Update environment settings in the engine
   */
  function onEnvironmentUpdate(settings: unknown): void {
    const engine = getEngine();
    if (!engine) return;
    engine.setEnvironmentConfig(settings);
  }

  /**
   * Load environment map into the engine
   */
  async function onEnvironmentLoad(settings: EnvironmentMapOptions & { url?: string }): Promise<void> {
    const engine = getEngine();
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
    const engine = getEngine();
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
