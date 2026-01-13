/**
 * Specialized Layer Operations
 *
 * Text layer creation and source replacement operations.
 * Extracted from layerStore.ts during Phase 1B modularization.
 *
 * @see docs/graphs/layerActions.md
 */

import type {
  CameraLayerData,
  ImageLayerData,
  Layer,
  NestedCompData,
  SplineData,
  VideoData,
} from "@/types/project";
import { createAnimatableProperty, isLayerOfType, createDefaultTransform } from "@/types/project";
import type { Camera3D } from "@/types/camera";
import { createDefaultCamera } from "@/types/camera";
import { storeLogger } from "@/utils/logger";
import { markLayerDirty } from "@/services/layerEvaluationCache";
import { createLayer } from "./crud";
import { selectLayer } from "./hierarchy";
import type { CompositorStoreAccess, LayerSourceReplacement } from "./types";

// ============================================================================
// TEXT LAYER CREATION
// ============================================================================

/**
 * Create a text layer with AE-compatible properties
 * @param compositorStore - The compositor store instance
 * @param text - Initial text content
 * @returns The created text layer
 */
export function createTextLayer(
  compositorStore: CompositorStoreAccess,
  text: string = "Text",
): Layer {
  const layer = createLayer(compositorStore, "text", text.substring(0, 20));

  // Set up text data with full AE parity
  const textData = {
    text,
    fontFamily: "Arial",
    fontSize: 72,
    fontWeight: "400" as const,
    fontStyle: "normal" as const,
    fill: "#ffffff",
    stroke: "",
    strokeWidth: 0,
    // Character Properties (AE Animator defaults)
    tracking: 0,
    lineSpacing: 0,
    lineAnchor: 0,
    characterOffset: 0,
    characterValue: 0,
    blur: { x: 0, y: 0 },
    // Paragraph (legacy aliases)
    letterSpacing: 0,
    lineHeight: 1.2,
    textAlign: "left" as const,
    // Path Options (Full AE Parity)
    pathLayerId: null,
    pathReversed: false,
    pathPerpendicularToPath: true,
    pathForceAlignment: false,
    pathFirstMargin: 0,
    pathLastMargin: 0,
    pathOffset: 0,
    pathAlign: "left" as const,
    // More Options (AE Advanced)
    anchorPointGrouping: "character" as const,
    groupingAlignment: { x: 0, y: 0 },
    fillAndStroke: "fill-over-stroke" as const,
    interCharacterBlending: "normal" as const,
    // 3D Text
    perCharacter3D: false,
  };

  layer.data = textData;

  // Text Properties for timeline
  layer.properties.push(
    createAnimatableProperty("Font Size", 72, "number", "Text"),
  );
  layer.properties.push(
    createAnimatableProperty("Fill Color", "#ffffff", "color", "Text"),
  );
  layer.properties.push(
    createAnimatableProperty("Stroke Color", "#000000", "color", "Text"),
  );
  layer.properties.push(
    createAnimatableProperty("Stroke Width", 0, "number", "Text"),
  );
  // Path Options
  layer.properties.push(
    createAnimatableProperty("Path Offset", 0, "number", "Path Options"),
  );
  layer.properties.push(
    createAnimatableProperty("First Margin", 0, "number", "Path Options"),
  );
  layer.properties.push(
    createAnimatableProperty("Last Margin", 0, "number", "Path Options"),
  );
  // More Options
  layer.properties.push(
    createAnimatableProperty(
      "Grouping Alignment",
      { x: 0, y: 0 },
      "position",
      "More Options",
    ),
  );
  // Advanced / Animators
  layer.properties.push(
    createAnimatableProperty("Tracking", 0, "number", "Advanced"),
  );
  layer.properties.push(
    createAnimatableProperty("Line Spacing", 0, "number", "Advanced"),
  );
  layer.properties.push(
    createAnimatableProperty("Character Offset", 0, "number", "Advanced"),
  );
  layer.properties.push(
    createAnimatableProperty("Character Value", 0, "number", "Advanced"),
  );
  layer.properties.push(
    createAnimatableProperty("Blur", { x: 0, y: 0 }, "position", "Advanced"),
  );

  return layer;
}

// ============================================================================
// SOURCE REPLACEMENT
// ============================================================================

/**
 * Replace a layer's source with a new asset or composition
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID to update
 * @param newSource - The new source data
 */
export function replaceLayerSource(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  newSource: LayerSourceReplacement,
): void {
  const layer = compositorStore
    .getActiveCompLayers()
    .find((l: Layer) => l.id === layerId);
  if (!layer) return;

  // Use assetId if provided, otherwise use id as assetId
  const assetId = newSource.assetId || newSource.id || null;

  // Determine source update based on layer type and new source type
  if (
    isLayerOfType(layer, "image") &&
    newSource.type === "asset" &&
    assetId
  ) {
    // Replace image source - preserve existing data, update assetId
    layer.data.assetId = assetId;
    layer.name = newSource.name || layer.name;
  } else if (
    isLayerOfType(layer, "video") &&
    newSource.type === "asset" &&
    assetId
  ) {
    // Replace video source - preserve existing data, update assetId
    layer.data.assetId = assetId;
    layer.name = newSource.name || layer.name;
  } else if (
    layer.type === "solid" &&
    newSource.type === "asset" &&
    assetId
  ) {
    // Convert solid to image layer (source replacement changes type)
    (layer as Layer).type = "image";
    const imageData: ImageLayerData = { assetId, fit: "none" };
    layer.data = imageData;
    layer.name = newSource.name || layer.name;
  } else if (
    isLayerOfType(layer, "nestedComp") &&
    newSource.type === "composition" &&
    newSource.id
  ) {
    // Replace nested comp source - preserve existing data, update compositionId
    layer.data.compositionId = newSource.id;
    layer.name = newSource.name || layer.name;
  } else if (newSource.type === "composition" && newSource.id) {
    // Convert any layer to nested comp
    (layer as Layer).type = "nestedComp";
    const nestedCompData: NestedCompData = {
      compositionId: newSource.id,
      speedMapEnabled: false,
      flattenTransform: false,
      overrideFrameRate: false,
    };
    layer.data = nestedCompData;
    layer.name = newSource.name || layer.name;
  } else if (newSource.type === "asset" && assetId) {
    // Generic asset replacement - determine new type from asset or file extension
    const path = newSource.path || "";
    const ext = path.split(".").pop()?.toLowerCase() || "";
    const imageExts = ["png", "jpg", "jpeg", "gif", "webp", "svg"];
    const videoExts = ["mp4", "webm", "mov", "avi"];

    if (imageExts.includes(ext)) {
      (layer as Layer).type = "image";
      const imageData: ImageLayerData = { assetId, fit: "none" };
      layer.data = imageData;
    } else if (videoExts.includes(ext)) {
      (layer as Layer).type = "video";
      const videoData: VideoData = {
        assetId,
        loop: true,
        pingPong: false,
        startTime: 0,
        speed: 1,
        speedMapEnabled: false,
        frameBlending: "none",
        audioEnabled: true,
        audioLevel: 100,
        posterFrame: 0,
      };
      layer.data = videoData;
    }
    layer.name = newSource.name || layer.name;
  }

  markLayerDirty(layerId);
  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory();
  storeLogger.info(`Replaced layer source: ${layer.name}`);
}

// ============================================================================
// SPLINE LAYER CREATION
// ============================================================================

/**
 * Create a spline layer with proper data structure
 * @param compositorStore - The compositor store instance
 * @returns The created spline layer
 */
export function createSplineLayer(compositorStore: CompositorStoreAccess): Layer {
  const layer = createLayer(compositorStore, "spline");

  const splineData: SplineData = {
    pathData: "",
    controlPoints: [],
    closed: false,
    stroke: "#00ff00",
    strokeWidth: 2,
    fill: "",
  };

  layer.data = splineData;

  return layer;
}

// ============================================================================
// SHAPE LAYER CREATION
// ============================================================================

/**
 * Create a shape layer
 * @param compositorStore - The compositor store instance
 * @param name - Layer name
 * @returns The created shape layer
 */
export function createShapeLayer(
  compositorStore: CompositorStoreAccess,
  name: string = "Shape Layer",
): Layer {
  return createLayer(compositorStore, "shape", name);
}

// ============================================================================
// CAMERA LAYER CREATION (delegates to cameraStore)
// ============================================================================

/**
 * Create a camera layer
 * NOTE: Camera layer creation requires camera store access (cameras Map, activeCameraId).
 * This function creates both the camera object and the layer, managing camera state.
 *
 * @param compositorStore - The compositor store instance (must have camera store access)
 * @param name - Optional camera name
 * @returns The created camera layer
 */
export function createCameraLayer(
  compositorStore: CompositorStoreAccess & {
    cameras: Map<string, Camera3D>;
    activeCameraId: string | null;
    selectLayer: (layerId: string) => void;
  },
  name?: string,
): Layer {
  const comp = compositorStore.getActiveComp();
  const layers = compositorStore.getActiveCompLayers();

  const cameraId = `camera_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
  const cameraName = name || `Camera ${compositorStore.cameras.size + 1}`;

  // Create the camera object
  const camera = createDefaultCamera(
    cameraId,
    comp?.settings.width || 1024,
    comp?.settings.height || 1024,
  );
  camera.name = cameraName;

  // Add to cameras map
  compositorStore.cameras.set(cameraId, camera);

  // If this is the first camera, make it active
  if (!compositorStore.activeCameraId) {
    compositorStore.activeCameraId = cameraId;
  }

  // Create the layer using generic createLayer
  const layer = createLayer(compositorStore, "camera", cameraName);
  
  // Update layer data with camera-specific info
  layer.data = {
    cameraId,
    isActiveCamera: !compositorStore.activeCameraId || compositorStore.activeCameraId === cameraId,
  } as CameraLayerData;
  
  layer.threeD = true; // Camera layers are always 3D

  // Auto-select the new camera layer
  selectLayer(compositorStore, layer.id);

  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory();

  return layer;
}

// ============================================================================
// VIDEO LAYER CREATION (delegates to videoActions)
// ============================================================================

/**
 * Create a video layer from a file
 * NOTE: Video layer creation requires video metadata extraction and asset management.
 * This function delegates to videoActions.createVideoLayer() which handles the complex
 * video import workflow (metadata extraction, fps handling, composition resizing).
 *
 * @param compositorStore - The compositor store instance (must have video store access)
 * @param file - Video file to import
 * @param autoResizeComposition - Whether to auto-resize composition to match video
 * @returns Promise resolving to video import result
 */
export async function createVideoLayer(
  compositorStore: CompositorStoreAccess & {
    assets: Record<string, any>;
  },
  file: File,
  autoResizeComposition: boolean = true,
): Promise<{ status: string; layer?: Layer; error?: string; [key: string]: any }> {
  // Import videoStore to delegate video import logic
  const { useVideoStore } = await import("@/stores/videoStore");
  const videoStore = useVideoStore();
  
  // Delegate to videoStore which handles metadata extraction and asset creation
  return videoStore.createVideoLayer(compositorStore as any, file, autoResizeComposition);
}

// ============================================================================
// NESTED COMP LAYER CREATION
// ============================================================================

/**
 * Create a nested comp layer referencing another composition
 * @param compositorStore - The compositor store instance
 * @param compositionId - ID of the composition to reference
 * @param name - Optional layer name (defaults to "Nested Comp")
 * @returns The created nested comp layer
 */
export function createNestedCompLayer(
  compositorStore: CompositorStoreAccess,
  compositionId: string,
  name?: string,
): Layer {
  const layer = createLayer(compositorStore, "nestedComp", name || "Nested Comp");

  const nestedCompData: NestedCompData = {
    compositionId,
    // Speed map (new naming)
    speedMapEnabled: false,
    speedMap: undefined,
    // Backwards compatibility
    timeRemapEnabled: false,
    timeRemap: undefined,
    flattenTransform: false,
    overrideFrameRate: false,
    frameRate: undefined,
  };

  layer.data = nestedCompData;
  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory();

  return layer;
}

// ============================================================================
// NESTED COMP LAYER UPDATE
// ============================================================================

/**
 * Update nested comp layer data
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the nested comp layer to update
 * @param updates - Partial nested comp data updates
 */
export function updateNestedCompLayerData(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  updates: Partial<NestedCompData>,
): void {
  const layer = compositorStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "nestedComp") return;

  const data = layer.data as NestedCompData;
  Object.assign(data, updates);
  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory(); // Fixed: was missing in original implementation
}
