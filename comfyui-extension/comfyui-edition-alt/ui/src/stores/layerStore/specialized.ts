/**
 * Specialized Layer Operations
 *
 * Text layer creation and source replacement operations.
 * Extracted from layerStore.ts during Phase 1B modularization.
 *
 * @see docs/graphs/layerActions.md
 */

import type {
  AssetReference,
  CameraLayerData,
  ImageLayerData,
  Layer,
  NestedCompData,
  SplineData,
  VideoData,
} from "@/types/project";
import type { VideoImportResult } from "@/stores/videoStore";
import { createAnimatableProperty, isLayerOfType, createDefaultTransform } from "@/types/project";
import type { Camera3D } from "@/types/camera";
import { createDefaultCamera } from "@/types/camera";
import { storeLogger } from "@/utils/logger";
import { markLayerDirty } from "@/services/layerEvaluationCache";
import { createLayer } from "./crud";
import { selectLayer } from "./hierarchy";
import { useProjectStore } from "../projectStore";
import { useCameraStore } from "../cameraStore";
import { useSelectionStore } from "../selectionStore";
import { useLayerStore } from "./index";
import { useCompositionStore } from "../compositionStore";
import type { LayerSourceReplacement, TimeStretchOptions } from "./types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                 // text // layer // creation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Create a text layer with AE-compatible properties
 * @param compositorStore - The compositor store instance
 * @param text - Initial text content
 * @returns The created text layer
 */
export function createTextLayer(
  text: string = "Text",
): Layer {
  const layer = createLayer("text", text.substring(0, 20));

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
    pathLayerId: "",
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

// ════════════════════════════════════════════════════════════════════════════
//                                                     // source // replacement
// ════════════════════════════════════════════════════════════════════════════

/**
 * Replace a layer's source with a new asset or composition
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID to update
 * @param newSource - The new source data
 */
export function replaceLayerSource(
  layerId: string,
  newSource: LayerSourceReplacement,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore
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
    const imageData: ImageLayerData = {
        assetId,
        source: "",
        fit: "none",
        cropEnabled: false,
        cropRect: { x: 0, y: 0, width: 0, height: 0 },
        sourceType: "file",
        segmentationMaskId: "",
      };
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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const pathParts = path.split(".");
    const lastPart = (pathParts != null && Array.isArray(pathParts) && pathParts.length > 0) ? pathParts[pathParts.length - 1] : undefined;
    const ext = (lastPart != null && typeof lastPart === "string" && typeof lastPart.toLowerCase === "function") ? lastPart.toLowerCase() : "";
    const imageExts = ["png", "jpg", "jpeg", "gif", "webp", "svg"];
    const videoExts = ["mp4", "webm", "mov", "avi"];

    if (imageExts.includes(ext)) {
      (layer as Layer).type = "image";
      const imageData: ImageLayerData = {
        assetId,
        source: "",
        fit: "none",
        cropEnabled: false,
        cropRect: { x: 0, y: 0, width: 0, height: 0 },
        sourceType: "file",
        segmentationMaskId: "",
      };
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
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
  storeLogger.info(`Replaced layer source: ${layer.name}`);
}

// ════════════════════════════════════════════════════════════════════════════
//                                               // spline // layer // creation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Create a spline layer with proper data structure
 * @param compositorStore - The compositor store instance
 * @returns The created spline layer
 */
export function createSplineLayer(): Layer {
  const layer = createLayer("spline");

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

// ════════════════════════════════════════════════════════════════════════════
//                                                // shape // layer // creation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Create a shape layer
 * @param compositorStore - The compositor store instance
 * @param name - Layer name
 * @returns The created shape layer
 */
export function createShapeLayer(
  name: string = "Shape Layer",
): Layer {
  return createLayer("shape", name);
}

// ════════════════════════════════════════════════════════════════════════════
//                                               // camera // layer // creation
// ════════════════════════════════════════════════════════════════════════════

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
  name?: string,
): Layer {
  const projectStore = useProjectStore();
  const cameraStore = useCameraStore();
  const comp = projectStore.getActiveComp();

  const cameraId = `camera_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
  const cameraName = name || `Camera ${cameraStore.cameras.size + 1}`;

  // Create the camera object
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const compSettings = (comp != null && typeof comp === "object" && "settings" in comp && comp.settings != null && typeof comp.settings === "object") ? comp.settings : undefined;
  const compWidth = (compSettings != null && typeof compSettings === "object" && "width" in compSettings && typeof compSettings.width === "number") ? compSettings.width : undefined;
  const compHeight = (compSettings != null && typeof compSettings === "object" && "height" in compSettings && typeof compSettings.height === "number") ? compSettings.height : undefined;
  const camera = createDefaultCamera(
    cameraId,
    compWidth != null ? compWidth : 1024,
    compHeight != null ? compHeight : 1024,
  );
  camera.name = cameraName;

  // Add to cameras map
  cameraStore.cameras.set(cameraId, camera);

  // If this is the first camera, make it active
  if (!cameraStore.activeCameraId) {
    cameraStore.setActiveCamera(cameraId);
  }

  // Create the layer using generic createLayer
  const layer = createLayer("camera", cameraName);
  
  // Update layer data with camera-specific info
  layer.data = {
    cameraId,
    isActiveCamera: !cameraStore.activeCameraId || cameraStore.activeCameraId === cameraId,
  } as CameraLayerData;
  
  layer.threeD = true; // Camera layers are always 3D

  // Auto-select the new camera layer
  selectLayer(layer.id);

  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();

  return layer;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                // video // layer // creation
// ════════════════════════════════════════════════════════════════════════════

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
  file: File,
  autoResizeComposition: boolean = true,
): Promise<VideoImportResult> {
  const { useVideoStore } = await import("@/stores/videoStore");
  const videoStore = useVideoStore();
  
  return videoStore.createVideoLayer(file, autoResizeComposition);
}

// ════════════════════════════════════════════════════════════════════════════
//                                       // nested // comp // layer // creation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Create a nested comp layer referencing another composition
 * @param compositorStore - The compositor store instance
 * @param compositionId - ID of the composition to reference
 * @param name - Optional layer name (defaults to "Nested Comp")
 * @returns The created nested comp layer
 */
export function createNestedCompLayer(
  compositionId: string,
  name?: string,
): Layer {
  const projectStore = useProjectStore();
  const layer = createLayer("nestedComp", name || "Nested Comp");

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
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();

  return layer;
}

// ════════════════════════════════════════════════════════════════════════════
//                                         // nested // comp // layer // update
// ════════════════════════════════════════════════════════════════════════════

/**
 * Update nested comp layer data
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the nested comp layer to update
 * @param updates - Partial nested comp data updates
 */
export function updateNestedCompLayerData(
  layerId: string,
  updates: Partial<NestedCompData>,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "nestedComp") return;

  const data = layer.data as NestedCompData;
  Object.assign(data, updates);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory(); // Fixed: was missing in original implementation
}
