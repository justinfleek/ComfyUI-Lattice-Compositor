/**
 * Specialized Layer Operations
 *
 * Text layer creation and source replacement operations.
 * Extracted from layerStore.ts during Phase 1B modularization.
 *
 * @see docs/graphs/layerActions.md
 */

import type {
  ImageLayerData,
  Layer,
  NestedCompData,
  SplineData,
  VideoData,
} from "@/types/project";
import { createAnimatableProperty, isLayerOfType } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { markLayerDirty } from "@/services/layerEvaluationCache";
import { createLayer } from "./crud";
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
