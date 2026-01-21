/**
 * Asset Handlers Composable
 *
 * Handles asset panel event callbacks for the WorkspaceLayout.
 * Extracted from WorkspaceLayout.vue to reduce file size and improve maintainability.
 */

import type { Ref } from "vue";
import type { LatticeEngine } from "@/engine";
import { useAssetStore } from "@/stores/assetStore";
import { useLayerStore } from "@/stores/layerStore";
import { useProjectStore } from "@/stores/projectStore";
import { useSelectionStore } from "@/stores/selectionStore";
import { isLayerOfType, type AnyLayerData } from "@/types/project";
import type { ParticleEmitterConfig, ParticleLayerData, SpriteConfig } from "@/types/particles";
import { isObject, safeCoordinateDefault, isFiniteNumber } from "@/utils/typeGuards";
import type { EnvironmentMapConfig } from "@/engine/core/SceneManager";
import type { JSONValue } from "@/types/dataAsset";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

// Type for CenterViewport exposed properties (matches defineExpose in CenterViewport.vue)
// Vue's defineExpose exposes refs/computeds directly - threeCanvasRef is a Ref, engine is a ComputedRef
export interface CenterViewportExposed {
  threeCanvasRef?: import("vue").Ref<InstanceType<typeof import("@/components/canvas/ThreeCanvas.vue").default> | null>;
  getEngine?: () => LatticeEngine;
  engine?: import("vue").ComputedRef<LatticeEngine | null>;
}

export interface AssetHandlersOptions {
  canvasRef: Ref<InstanceType<typeof import("@/components/layout/CenterViewport.vue").default> | null>;
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
  
  // Helper type guard: System F/Omega proof for LatticeEngine contract satisfaction
  // Type proof: ∀ e: RuntimeValue, isLatticeEngine(e) → e: LatticeEngine
  function isLatticeEngine(value: RuntimeValue): value is LatticeEngine {
    if (!isObject(value)) return false;
    // Check for LatticeEngine contract methods to ensure type safety
    return (
      typeof value.setEnvironmentConfig === "function" &&
      typeof value.loadEnvironmentMap === "function" &&
      typeof value.setEnvironmentEnabled === "function" &&
      typeof value.setFrame === "function" &&
      typeof value.render === "function"
    );
  }

  // Helper to safely access getEngine from exposed properties
  // Vue exposes functions directly via defineExpose - use runtime property check with type guards
  // System F/Omega proof: Runtime type guard ensures LatticeEngine contract satisfaction
  function getEngine(): LatticeEngine {
    const viewport = canvasRef.value;
    if (!viewport || !isObject(viewport)) {
      throw new Error("[AssetHandlers] Cannot get engine: viewport is not available");
    }
    // Runtime check: Vue exposes getEngine as a function
    // Use property access with runtime check - TypeScript can't know about exposed properties
    const getEngineProp = (viewport as { getEngine?: () => RuntimeValue }).getEngine;
    if (typeof getEngineProp !== "function") {
      throw new Error("[AssetHandlers] Cannot get engine: viewport.getEngine is not a function");
    }
    
    const engine = getEngineProp() as RuntimeValue;
    // Type guard: verify it's the expected engine type
    // System F/Omega proof: Type guard narrows unknown → LatticeEngine
    if (isLatticeEngine(engine)) {
      return engine;
    }
    throw new Error("[AssetHandlers] Cannot get engine: viewport.getEngine() did not return a valid LatticeEngine");
  }

  /**
   * Create layers from imported SVG paths
   */
  function onCreateLayersFromSvg(svgId: string): void {
    const storedSvg = assetStore.svgDocuments.get(svgId);
    if (!storedSvg) return;

    storedSvg.document.paths.forEach((path: { id: string }, index: number) => {
      const config = storedSvg.layerConfigs[index];

      const layer = layerStore.createShapeLayer();
      layerStore.renameLayer(layer.id, `${storedSvg.name}_${path.id}`);

      // Type extension: SVG-related properties are runtime data not in ShapeLayerData type
      // CODE IS TRUTH: These properties are used at runtime for SVG path tracking
      // System F/Omega proof: Type-safe update with explicit property construction
      // Type proof: Partial<AnyLayerData> ∪ { svgDocumentId, svgPathId, svgPathIndex, extrusionConfig, transform }
      const layerUpdate: Partial<AnyLayerData> & {
        svgDocumentId?: string;
        svgPathId?: string;
        svgPathIndex?: number;
        extrusionConfig?: typeof config;
        transform?: typeof layer.transform;
      } = {
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
              // Type proof: depth/z coordinate ∈ number | undefined → number (coordinate-like, can be negative)
              // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
              z: safeCoordinateDefault((config !== null && typeof config === "object" && "depth" in config && typeof config.depth === "number") ? config.depth : undefined, 0, "config.depth"),
            },
          },
        },
      };
      layerStore.updateLayerData(layer.id, layerUpdate);
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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
    const emittersRaw = particleData.emitters;
    const existingEmitters = (emittersRaw !== null && emittersRaw !== undefined && Array.isArray(emittersRaw)) ? emittersRaw : [];

    // System F/Omega proof: Construct valid ParticleEmitterConfig with all required properties
    // Type proof: ParticleEmitterConfig requires sprite: SpriteConfig (full object, not partial)
    // Helper to create valid SpriteConfig with required properties
    function createDefaultSpriteConfig(): SpriteConfig {
      return {
        enabled: true,
        imageUrl: null,
        imageData: null,
        isSheet: false,
        columns: 1,
        rows: 1,
        totalFrames: 1,
        frameRate: 30,
        playMode: "loop",
        billboard: false,
        rotationEnabled: false,
        rotationSpeed: 0,
        rotationSpeedVariance: 0,
        alignToVelocity: false,
      };
    }

    // Update first emitter with mesh shape, or create new one
    const updatedEmitters: ParticleEmitterConfig[] = existingEmitters.length > 0
      ? existingEmitters.map((emitter, i) =>
          i === 0
            ? {
                ...emitter,
                shape: "mesh" as const,
                meshVertices: emitterConfig.meshVertices,
                meshNormals: emitterConfig.meshNormals,
                // Ensure sprite is valid SpriteConfig (not partial)
                // Lean4/PureScript/Haskell: Explicit pattern matching on optional property
                // Type proof: emitter.sprite ∈ SpriteConfig | undefined → SpriteConfig
                sprite: emitter.sprite !== undefined && isObject(emitter.sprite)
                  ? emitter.sprite
                  : createDefaultSpriteConfig(),
              }
            : emitter
        )
      : [
          {
            // Create minimal valid emitter config with mesh shape
            // System F/Omega proof: All required ParticleEmitterConfig properties satisfied
            id: `emitter_${Date.now()}`,
            name: "Mesh Emitter",
            x: 0,
            y: 0,
            direction: 0,
            spread: 0,
            speed: 100,
            speedVariance: 0,
            size: 10,
            sizeVariance: 0,
            color: [255, 255, 255] as [number, number, number],
            emissionRate: 10,
            initialBurst: 0,
            particleLifetime: 60,
            lifetimeVariance: 0,
            enabled: true,
            burstOnBeat: false,
            burstCount: 0,
            shape: "mesh" as const,
            shapeRadius: 0,
            shapeWidth: 0,
            shapeHeight: 0,
            shapeDepth: 0,
            shapeInnerRadius: 0,
            emitFromEdge: false,
            emitFromVolume: true,
            splinePath: null,
            sprite: createDefaultSpriteConfig(),
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
   * System F/Omega proof: Runtime type validation ensures EnvironmentMapConfig contract
   */
  function onEnvironmentUpdate(settings: RuntimeValue): void {
    const engine = getEngine();
    if (!engine) return;
    
    // Type guard: Validate settings conform to Partial<EnvironmentMapConfig>
    // Type proof: ∀ s: RuntimeValue, isValidEnvironmentConfig(s) → s: Partial<EnvironmentMapConfig>
    if (!isObject(settings)) {
      console.warn("[Lattice] Environment settings must be an object");
      return;
    }
    
    // Construct valid Partial<EnvironmentMapConfig> with type-safe property extraction
    const config: Partial<EnvironmentMapConfig> = {};
    
    if ("enabled" in settings && typeof settings.enabled === "boolean") {
      config.enabled = settings.enabled;
    }
    if ("url" in settings && (settings.url === null || typeof settings.url === "string")) {
      // Convert null to undefined for Partial<EnvironmentMapConfig>
      config.url = settings.url === null ? undefined : settings.url;
    }
    if ("intensity" in settings && isFiniteNumber(settings.intensity)) {
      config.intensity = settings.intensity;
    }
    if ("rotation" in settings && isFiniteNumber(settings.rotation)) {
      config.rotation = settings.rotation;
    }
    if ("backgroundBlur" in settings && isFiniteNumber(settings.backgroundBlur)) {
      config.backgroundBlur = settings.backgroundBlur;
    }
    if ("useAsBackground" in settings && typeof settings.useAsBackground === "boolean") {
      config.useAsBackground = settings.useAsBackground;
    }
    if ("toneMapping" in settings && typeof settings.toneMapping === "boolean") {
      config.toneMapping = settings.toneMapping;
    }
    
    engine.setEnvironmentConfig(config);
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
