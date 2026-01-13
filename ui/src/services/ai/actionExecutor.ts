/**
 * AI Action Executor
 *
 * Maps LLM tool calls to actual compositor store actions.
 * This is the bridge between AI intent and store mutations.
 */

import {
  type CameraShakeConfig,
  createRackFocus,
  generateRackFocusKeyframes,
  type RackFocusConfig,
} from "@/services/cameraEnhancements";
import {
  createTrajectoryFromPreset,
  generateTrajectoryKeyframes,
  type TrajectoryType,
} from "@/services/cameraTrajectory";
import { getLayerDecompositionService } from "@/services/layerDecomposition";
import {
  autoGroupPoints,
  filterSmallPaths,
  getVectorizeService,
  normalizeControlPoints,
} from "@/services/vectorize";
import { useEffectStore } from "@/stores/effectStore";
import { useCompositorStore } from "@/stores/compositorStore";
import { useLayerStore } from "@/stores/layerStore";
import { useKeyframeStore, findPropertyByPath } from "@/stores/keyframeStore";
import { usePlaybackStore } from "@/stores/playbackStore";
import { useSelectionStore } from "@/stores/selectionStore";
import { useAnimationStore } from "@/stores/animationStore";
import type {
  CameraLayerData,
  ControlPoint,
  ImageLayerData,
  InterpolationType,
  Layer,
  LayerType,
  ParticleLayerData,
  SplineData,
  TextData,
} from "@/types/project";
import { isLayerOfType } from "@/types/project";
import type { ToolCall } from "./toolDefinitions";

// ============================================================================
// TYPES
// ============================================================================

export interface ExecutionContext {
  store: ReturnType<typeof useCompositorStore>;
  layerStore?: ReturnType<typeof useLayerStore>;
  playbackStore: ReturnType<typeof usePlaybackStore>;
  selectionStore: ReturnType<typeof useSelectionStore>;
  animationStore?: ReturnType<typeof useAnimationStore>;
}

/**
 * Ensure a layer has data, initializing it if needed.
 * This is type-safe because camera layers always have CameraLayerData.
 */
function ensureCameraLayerData(layer: Layer): CameraLayerData {
  if (!layer.data) {
    // Initialize minimal camera data structure
    layer.data = {
      cameraId: null,
      isActiveCamera: false,
    };
  }
  return layer.data as CameraLayerData;
}

// ============================================================================
// MAIN EXECUTOR
// ============================================================================

/**
 * Execute a tool call from the AI agent
 * Returns the result of the action for the AI to verify
 */
export async function executeToolCall(toolCall: ToolCall): Promise<any> {
  const store = useCompositorStore();
  const layerStore = useLayerStore();
  const animationStore = useAnimationStore();
  const playbackStore = usePlaybackStore();
  const selectionStore = useSelectionStore();

  const context: ExecutionContext = { store, playbackStore, selectionStore, layerStore, animationStore };
  const { name, arguments: args } = toolCall;

  // Route to appropriate handler
  switch (name) {
    // Layer Management
    case "createLayer":
      return executeCreateLayer(context, args);
    case "deleteLayer":
      return executeDeleteLayer(context, args);
    case "duplicateLayer":
      return executeDuplicateLayer(context, args);
    case "renameLayer":
      return executeRenameLayer(context, args);
    case "setLayerParent":
      return executeSetLayerParent(context, args);
    case "reorderLayers":
      return executeReorderLayers(context, args);

    // Property Modification
    case "setLayerProperty":
      return executeSetLayerProperty(context, args);
    case "setLayerTransform":
      return executeSetLayerTransform(context, args);

    // Keyframe Animation
    case "addKeyframe":
      return executeAddKeyframe(context, args);
    case "removeKeyframe":
      return executeRemoveKeyframe(context, args);
    case "setKeyframeEasing":
      return executeSetKeyframeEasing(context, args);
    case "scaleKeyframeTiming":
      return executeScaleKeyframeTiming(context, args);

    // Expressions
    case "setExpression":
      return executeSetExpression(context, args);
    case "removeExpression":
      return executeRemoveExpression(context, args);

    // Effects
    case "addEffect":
      return executeAddEffect(context, args);
    case "updateEffect":
      return executeUpdateEffect(context, args);
    case "removeEffect":
      return executeRemoveEffect(context, args);

    // Particle System
    case "configureParticles":
      return executeConfigureParticles(context, args);

    // Camera System
    case "applyCameraTrajectory":
      return executeApplyCameraTrajectory(context, args);
    case "addCameraShake":
      return executeAddCameraShake(context, args);
    case "applyRackFocus":
      return executeApplyRackFocus(context, args);
    case "setCameraPathFollowing":
      return executeSetCameraPathFollowing(context, args);
    case "setCameraAutoFocus":
      return executeSetCameraAutoFocus(context, args);

    // Text
    case "setTextContent":
      return executeSetTextContent(context, args);
    case "setTextPath":
      return executeSetTextPath(context, args);

    // Spline
    case "setSplinePoints":
      return executeSetSplinePoints(context, args);

    // Speed Map (formerly Time Remapping)
    case "setSpeedMap":
      return executeSetSpeedMap(context, args);
    case "setTimeRemap": // Legacy - redirects to setSpeedMap
      return executeSetSpeedMap(context, args);

    // Playback
    case "setCurrentFrame":
      return executeSetCurrentFrame(context, args);
    case "playPreview":
      return executePlayPreview(context, args);

    // AI Image Processing
    case "decomposeImage":
      return executeDecomposeImage(context, args);
    case "vectorizeImage":
      return executeVectorizeImage(context, args);

    // Utility
    case "getLayerInfo":
      return executeGetLayerInfo(context, args);
    case "findLayers":
      return executeFindLayers(context, args);
    case "getProjectState":
      return executeGetProjectState(context, args);

    default:
      throw new Error(`Unknown tool: ${name}`);
  }
}

// ============================================================================
// LAYER MANAGEMENT HANDLERS
// ============================================================================

/**
 * Validate required arguments exist and have correct types
 */
function validateArgs(
  args: Record<string, any>,
  schema: Record<string, { type: string; required?: boolean }>,
): { valid: boolean; error?: string } {
  for (const [key, spec] of Object.entries(schema)) {
    const value = args[key];

    // Check required fields
    if (spec.required && (value === undefined || value === null)) {
      return { valid: false, error: `Missing required argument: ${key}` };
    }

    // Skip type check if value is undefined and not required
    if (value === undefined || value === null) continue;

    // Type validation
    const actualType = Array.isArray(value) ? "array" : typeof value;
    if (spec.type === "array" && !Array.isArray(value)) {
      return { valid: false, error: `Argument ${key} must be an array` };
    } else if (
      spec.type !== "array" &&
      spec.type !== "any" &&
      actualType !== spec.type
    ) {
      return {
        valid: false,
        error: `Argument ${key} must be ${spec.type}, got ${actualType}`,
      };
    }
  }
  return { valid: true };
}

function executeCreateLayer(
  context: ExecutionContext,
  args: Record<string, any>,
): { layerId: string; message: string } {
  const { store, layerStore } = context;
  if (!layerStore) {
    const layerStoreInstance = useLayerStore();
    return executeCreateLayer({ ...context, layerStore: layerStoreInstance }, args);
  }

  // Validate arguments
  const validation = validateArgs(args, {
    type: { type: "string", required: true },
    name: { type: "string", required: false },
    properties: { type: "object", required: false },
    position: { type: "object", required: false },
    inPoint: { type: "number", required: false },
    outPoint: { type: "number", required: false },
  });
  if (!validation.valid) {
    throw new Error(validation.error);
  }

  const { type, name, properties, position, inPoint, outPoint } = args;

  // Complete mapping of all 24 layer types
  const typeMap: Record<string, LayerType> = {
    // Core layer types
    solid: "solid",
    text: "text",
    shape: "shape",
    spline: "spline",
    path: "path",
    image: "image",
    video: "video",
    audio: "audio",

    // 3D layers
    camera: "camera",
    light: "light",
    model: "model",
    pointcloud: "pointcloud",

    // Particle systems (both names supported)
    particle: "particle",
    particles: "particles",

    // Special layers
    control: "control",
    null: "null", // Legacy, maps to control
    group: "group",
    nested: "nestedComp",
    nestedComp: "nestedComp",
    matte: "matte",

    // AI/Generated layers
    depth: "depth",
    normal: "normal",
    generated: "generated",
    depthflow: "depthflow",

    // Effect layers
    effectLayer: "effectLayer",
    adjustment: "adjustment", // @deprecated alias for effectLayer
    "effect-layer": "effectLayer", // kebab-case alias
  };

  const internalType = typeMap[type] || type;
  const layer = layerStore.createLayer(
    store,
    internalType as LayerType,
    name,
  );

  // Apply initial properties
  if (position) {
    layer.transform.position.value = position;
  }
  if (inPoint !== undefined) {
    layer.inPoint = inPoint;
  }
  if (outPoint !== undefined) {
    layer.outPoint = outPoint;
  }
  if (properties) {
    Object.assign(layer.data || {}, properties);
  }

  return {
    layerId: layer.id,
    message: `Created ${type} layer "${layer.name}" with ID ${layer.id}`,
  };
}

function executeDeleteLayer(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store, layerStore } = context;
  if (!layerStore) {
    const layerStoreInstance = useLayerStore();
    return executeDeleteLayer({ ...context, layerStore: layerStoreInstance }, args);
  }
  const { layerId } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  const layerName = layer.name;
  layerStore.deleteLayer(store, layerId);

  return {
    success: true,
    message: `Deleted layer "${layerName}"`,
  };
}

function executeDuplicateLayer(
  context: ExecutionContext,
  args: Record<string, any>,
): { layerId: string | null; message: string } {
  const { store, layerStore } = context;
  if (!layerStore) {
    const layerStoreInstance = useLayerStore();
    return executeDuplicateLayer({ ...context, layerStore: layerStoreInstance }, args);
  }
  const { layerId, newName } = args;

  const duplicate = layerStore.duplicateLayer(store, layerId);
  if (!duplicate) {
    return { layerId: null, message: `Failed to duplicate layer ${layerId}` };
  }

  if (newName) {
    duplicate.name = newName;
  }

  return {
    layerId: duplicate.id,
    message: `Duplicated layer as "${duplicate.name}" with ID ${duplicate.id}`,
  };
}

function executeRenameLayer(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, name } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  const oldName = layer.name;
  layer.name = name;

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: `Renamed layer from "${oldName}" to "${name}"`,
  };
}

function executeSetLayerParent(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store, layerStore } = context;
  if (!layerStore) {
    const layerStoreInstance = useLayerStore();
    return executeSetLayerParent({ ...context, layerStore: layerStoreInstance }, args);
  }
  const { layerId, parentId } = args;

  layerStore.setLayerParent(store, layerId, parentId || null);

  return {
    success: true,
    message: parentId
      ? `Set parent of layer ${layerId} to ${parentId}`
      : `Removed parent from layer ${layerId}`,
  };
}

function executeReorderLayers(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store, layerStore } = context;
  if (!layerStore) {
    const layerStoreInstance = useLayerStore();
    return executeReorderLayers({ ...context, layerStore: layerStoreInstance }, args);
  }
  const { layerId, newIndex } = args;

  layerStore.moveLayer(store, layerId, newIndex);

  return {
    success: true,
    message: `Moved layer ${layerId} to index ${newIndex}`,
  };
}

// ============================================================================
// PROPERTY MODIFICATION HANDLERS
// ============================================================================

function executeSetLayerProperty(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, propertyPath, value } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  // Handle different property paths
  const parts = propertyPath.split(".");

  if (parts[0] === "data" && layer.data) {
    // Layer-specific data (e.g., data.text, data.color)
    setNestedProperty(layer.data, parts.slice(1), value);
  } else if (parts[0] === "transform") {
    // Transform properties - use type-safe property access
    const transformKey = parts[1] as keyof typeof layer.transform;
    const prop = layer.transform[transformKey];
    if (prop && typeof prop === "object" && "value" in prop) {
      (prop as { value: unknown }).value = value;
    }
  } else if (propertyPath === "opacity") {
    layer.opacity.value = value;
  } else if (propertyPath === "visible") {
    layer.visible = value;
  } else if (propertyPath === "locked") {
    layer.locked = value;
  } else if (propertyPath === "inPoint") {
    layer.inPoint = value;
  } else if (propertyPath === "outPoint") {
    layer.outPoint = value;
  } else {
    // Try to find in layer.data
    if (layer.data) {
      setNestedProperty(layer.data, parts, value);
    }
  }

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: `Set ${propertyPath} to ${JSON.stringify(value)}`,
  };
}

function executeSetLayerTransform(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, position, scale, rotation, opacity, anchorPoint } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  const changes: string[] = [];

  if (position !== undefined) {
    layer.transform.position.value = position;
    changes.push("position");
  }
  if (scale !== undefined) {
    layer.transform.scale.value = scale;
    changes.push("scale");
  }
  if (rotation !== undefined) {
    layer.transform.rotation.value = rotation;
    changes.push("rotation");
  }
  if (opacity !== undefined) {
    layer.opacity.value = opacity;
    changes.push("opacity");
  }
  if (anchorPoint !== undefined) {
    // Use origin (new name) with fallback to anchorPoint
    const originProp = layer.transform.origin || layer.transform.anchorPoint;
    if (originProp) {
      originProp.value = anchorPoint;
    }
    changes.push("origin");
  }

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: `Updated transform: ${changes.join(", ")}`,
  };
}

// ============================================================================
// KEYFRAME ANIMATION HANDLERS
// ============================================================================

function executeAddKeyframe(
  context: ExecutionContext,
  args: Record<string, any>,
): { keyframeId: string | null; message: string } {
  const { store } = context;
  const { layerId, propertyPath, frame, value, interpolation } = args;

  const keyframe = useKeyframeStore().addKeyframe(
    store,
    layerId,
    propertyPath,
    value,
    frame,
  );

  if (!keyframe) {
    return {
      keyframeId: null,
      message: `Failed to add keyframe at frame ${frame}`,
    };
  }

  // Set interpolation if specified
  if (interpolation && keyframe) {
    useKeyframeStore().setKeyframeInterpolation(
      store,
      layerId,
      propertyPath,
      keyframe.id,
      interpolation as InterpolationType,
    );
  }

  return {
    keyframeId: keyframe.id,
    message: `Added keyframe at frame ${frame} for ${propertyPath}`,
  };
}

function executeRemoveKeyframe(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, propertyPath, frame } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  // Find keyframe at frame
  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    return { success: false, message: `Property ${propertyPath} not found` };
  }

  const keyframe = property.keyframes.find((k) => k.frame === frame);
  if (!keyframe) {
    return { success: false, message: `No keyframe at frame ${frame}` };
  }

  useKeyframeStore().removeKeyframe(store, layerId, propertyPath, keyframe.id);

  return {
    success: true,
    message: `Removed keyframe at frame ${frame} from ${propertyPath}`,
  };
}

function executeSetKeyframeEasing(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, propertyPath, frame, interpolation } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    return { success: false, message: `Property ${propertyPath} not found` };
  }

  const keyframe = property.keyframes.find((k) => k.frame === frame);
  if (!keyframe) {
    return { success: false, message: `No keyframe at frame ${frame}` };
  }

  useKeyframeStore().setKeyframeInterpolation(
    store,
    layerId,
    propertyPath,
    keyframe.id,
    interpolation as InterpolationType,
  );

  return {
    success: true,
    message: `Set interpolation to ${interpolation} at frame ${frame}`,
  };
}

function executeScaleKeyframeTiming(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, scaleFactor, propertyPath } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  // Get all properties to scale
  const propertiesToScale: string[] = propertyPath
    ? [propertyPath]
    : ["position", "scale", "rotation", "opacity", "anchorPoint"];

  let scaledCount = 0;

  for (const propPath of propertiesToScale) {
    const property = findPropertyByPath(layer, propPath);
    if (property?.keyframes && property.keyframes.length > 0) {
      // Scale each keyframe's frame number
      for (const kf of property.keyframes) {
        kf.frame = Math.round(kf.frame * scaleFactor);
      }
      // Re-sort keyframes
      property.keyframes.sort((a, b) => a.frame - b.frame);
      scaledCount += property.keyframes.length;
    }
  }

  // Record modification and save to undo history (only if changes were made)
  if (scaledCount > 0) {
    store.project.meta.modified = new Date().toISOString();
    store.pushHistory();
  }

  return {
    success: true,
    message: `Scaled ${scaledCount} keyframes by factor ${scaleFactor}`,
  };
}

// ============================================================================
// EXPRESSION HANDLERS
// ============================================================================

function executeSetExpression(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, propertyPath, expressionType, params } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    return { success: false, message: `Property ${propertyPath} not found` };
  }

  // Set expression on property
  property.expression = {
    enabled: true,
    type: "preset" as const,
    name: expressionType,
    params: params || {},
  };

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: `Applied ${expressionType} expression to ${propertyPath}`,
  };
}

function executeRemoveExpression(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, propertyPath } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    return { success: false, message: `Property ${propertyPath} not found` };
  }

  property.expression = undefined;

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: `Removed expression from ${propertyPath}`,
  };
}

// ============================================================================
// EFFECT HANDLERS
// ============================================================================

function executeAddEffect(
  context: ExecutionContext,
  args: Record<string, any>,
): { effectId: string | null; message: string } {
  const { store } = context;
  const { layerId, effectType, params } = args;

  const effectStore = useEffectStore();
  effectStore.addEffectToLayer(store, layerId, effectType);

  // Get the newly added effect (last in array)
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  const effect = layer?.effects?.[layer.effects.length - 1];

  if (!effect) {
    return { effectId: null, message: `Failed to add effect ${effectType}` };
  }

  // Apply initial parameters
  if (params) {
    for (const [key, value] of Object.entries(params)) {
      effectStore.updateEffectParameter(
        store,
        layerId,
        effect.id,
        key,
        value,
      );
    }
  }

  return {
    effectId: effect.id,
    message: `Added ${effectType} effect to layer`,
  };
}

function executeUpdateEffect(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, effectId, params } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer?.effects) {
    return {
      success: false,
      message: `Layer ${layerId} not found or has no effects`,
    };
  }

  const effect = layer.effects.find((e) => e.id === effectId);
  if (!effect) {
    return { success: false, message: `Effect ${effectId} not found` };
  }

  const effectStore = useEffectStore();
  for (const [key, value] of Object.entries(params)) {
    effectStore.updateEffectParameter(store, layerId, effectId, key, value);
  }

  return {
    success: true,
    message: `Updated ${Object.keys(params).length} effect parameters`,
  };
}

function executeRemoveEffect(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, effectId } = args;

  const effectStore = useEffectStore();
  effectStore.removeEffectFromLayer(store, layerId, effectId);

  return {
    success: true,
    message: `Removed effect ${effectId}`,
  };
}

// ============================================================================
// PARTICLE SYSTEM HANDLERS
// ============================================================================

function executeConfigureParticles(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, emitter, particles, physics } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "particles") {
    return { success: false, message: `Particle layer ${layerId} not found` };
  }

  if (!isLayerOfType(layer, "particles")) {
    return { success: false, message: `Layer ${layerId} is not a particles layer` };
  }

  const particleData = layer.data as ParticleLayerData;

  // Update emitter configuration
  if (emitter && particleData.emitters?.[0]) {
    Object.assign(particleData.emitters[0], emitter);
  }

  // Update particle settings
  if (particles && particleData.emitters?.[0]) {
    Object.assign(particleData.emitters[0], particles);
  }

  // Update physics
  if (physics && particleData.systemConfig) {
    if (physics.gravity) {
      particleData.systemConfig.gravity = physics.gravity.y || 0;
    }
    if (physics.wind) {
      // Default to zero if wind components are undefined
      const windX = physics.wind.x ?? 0;
      const windY = physics.wind.y ?? 0;
      particleData.systemConfig.windStrength = Math.sqrt(
        windX ** 2 + windY ** 2,
      );
      particleData.systemConfig.windDirection =
        Math.atan2(windY, windX) * (180 / Math.PI);
    }
    if (physics.turbulence) {
      // Map to system config if applicable
    }
  }

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: `Configured particle system`,
  };
}

// ============================================================================
// CAMERA SYSTEM HANDLERS
// ============================================================================

function executeApplyCameraTrajectory(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; keyframeCount: number; message: string } {
  const { store } = context;
  const {
    cameraLayerId,
    trajectoryType,
    startFrame = 0,
    duration,
    amplitude,
    loops,
    easing,
    center,
  } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === cameraLayerId);
  if (!layer || layer.type !== "camera") {
    return {
      success: false,
      keyframeCount: 0,
      message: `Camera layer ${cameraLayerId} not found`,
    };
  }

  const comp = store.getActiveComp();
  const compSettings = comp?.settings || {
    width: 1920,
    height: 1080,
    frameCount: 81,
  };

  // Build trajectory configuration
  const trajectoryConfig = createTrajectoryFromPreset(
    trajectoryType as TrajectoryType,
    {
      duration: duration ?? compSettings.frameCount,
      amplitude: amplitude ?? undefined,
      loops: loops ?? undefined,
      easing: easing ?? undefined,
      center: center ?? {
        x: compSettings.width / 2,
        y: compSettings.height / 2,
        z: 0,
      },
    },
  );

  // Generate keyframes
  const keyframes = generateTrajectoryKeyframes(
    trajectoryConfig,
    startFrame,
    5,
  );

  // Apply keyframes to layer's camera data
  const cameraData = ensureCameraLayerData(layer);

  // Initialize or update camera settings
  if (!cameraData.camera) {
    cameraData.camera = {
      type: "two-node",
      position: {
        x: compSettings.width / 2,
        y: compSettings.height / 2,
        z: -1500,
      },
      pointOfInterest: {
        x: compSettings.width / 2,
        y: compSettings.height / 2,
        z: 0,
      },
      zoom: 1778,
      depthOfField: false,
      focusDistance: 1500,
      aperture: 2.8,
      blurLevel: 100,
      xRotation: 0,
      yRotation: 0,
      zRotation: 0,
    };
  }

  // Store trajectory keyframes in camera data (filter and map to required format)
  cameraData.trajectoryKeyframes = {
    position: keyframes.position
      .filter((kf) => kf.position !== undefined)
      .map((kf) => ({ frame: kf.frame, position: kf.position! })),
    pointOfInterest: keyframes.pointOfInterest
      .filter((kf) => kf.pointOfInterest !== undefined)
      .map((kf) => ({ frame: kf.frame, pointOfInterest: kf.pointOfInterest! })),
    zoom: keyframes.zoom
      ?.filter((kf) => kf.zoom !== undefined)
      .map((kf) => ({ frame: kf.frame, zoom: kf.zoom! })),
  };

  // Also create standard layer keyframes for position
  for (const kf of keyframes.position) {
    if (kf.position) {
      useKeyframeStore().addKeyframe(
        store,
        cameraLayerId,
        "cameraPosition",
        kf.position,
        kf.frame,
      );
    }
  }

  const totalKeyframes =
    keyframes.position.length +
    keyframes.pointOfInterest.length +
    (keyframes.zoom?.length || 0);

  return {
    success: true,
    keyframeCount: totalKeyframes,
    message: `Applied ${trajectoryType} trajectory with ${totalKeyframes} keyframes`,
  };
}

function executeAddCameraShake(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const {
    cameraLayerId,
    shakeType,
    intensity,
    frequency,
    startFrame = 0,
    duration,
    decay,
    rotationEnabled,
    seed,
  } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === cameraLayerId);
  if (!layer || layer.type !== "camera") {
    return {
      success: false,
      message: `Camera layer ${cameraLayerId} not found`,
    };
  }

  const comp = store.getActiveComp();
  const compDuration = comp?.settings.frameCount || 81;

  // Build shake config
  const shakeConfig: Partial<CameraShakeConfig> = {
    type: shakeType,
    intensity: intensity,
    frequency: frequency,
    decay: decay,
    rotationEnabled: rotationEnabled,
    seed: seed ?? Math.floor(Math.random() * 100000),
  };

  // Store shake configuration in layer data
  const cameraData = ensureCameraLayerData(layer);

  cameraData.shake = {
    enabled: true,
    type: shakeType,
    intensity: shakeConfig.intensity ?? 0.3,
    frequency: shakeConfig.frequency ?? 1.0,
    rotationEnabled: shakeConfig.rotationEnabled ?? true,
    rotationScale: 0.5,
    seed: shakeConfig.seed!,
    decay: shakeConfig.decay ?? 0,
    startFrame,
    duration: duration ?? compDuration,
  };

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: `Added ${shakeType} camera shake (intensity: ${cameraData.shake.intensity}, duration: ${cameraData.shake.duration} frames)`,
  };
}

function executeApplyRackFocus(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; keyframeCount: number; message: string } {
  const { store } = context;
  const {
    cameraLayerId,
    startDistance,
    endDistance,
    startFrame = 0,
    duration = 30,
    easing = "ease-in-out",
    holdStart = 0,
    holdEnd = 0,
  } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === cameraLayerId);
  if (!layer || layer.type !== "camera") {
    return {
      success: false,
      keyframeCount: 0,
      message: `Camera layer ${cameraLayerId} not found`,
    };
  }

  // Create rack focus config
  const rackFocusConfig = createRackFocus(
    startDistance,
    endDistance,
    duration,
    {
      startFrame,
      easing: easing as RackFocusConfig["easing"],
      holdStart,
      holdEnd,
    },
  );

  // Generate focus keyframes
  const focusKeyframes = generateRackFocusKeyframes(rackFocusConfig, 2);

  // Store in layer data
  const cameraData = ensureCameraLayerData(layer);

  // Enable depth of field
  if (cameraData.camera) {
    cameraData.camera.depthOfField = true;
  }

  // Store rack focus config
  cameraData.rackFocus = {
    enabled: true,
    ...rackFocusConfig,
  };

  // Apply focus keyframes to layer
  for (const kf of focusKeyframes) {
    if (kf.focusDistance !== undefined) {
      useKeyframeStore().addKeyframe(
        store,
        cameraLayerId,
        "focusDistance",
        kf.focusDistance,
        kf.frame,
      );
    }
  }

  return {
    success: true,
    keyframeCount: focusKeyframes.length,
    message: `Applied rack focus from ${startDistance}px to ${endDistance}px over ${duration} frames`,
  };
}

function executeSetCameraPathFollowing(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const {
    cameraLayerId,
    splineLayerId,
    lookMode = "tangent",
    lookTarget,
    startOffset = 0,
    speed = 1.0,
    bankAmount = 0,
    smoothing = 0.5,
  } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === cameraLayerId);
  if (!layer || layer.type !== "camera") {
    return {
      success: false,
      message: `Camera layer ${cameraLayerId} not found`,
    };
  }

  // Verify spline layer exists if specified
  if (splineLayerId) {
    const splineLayer = store
      .getActiveCompLayers()
      .find((l) => l.id === splineLayerId);
    if (!splineLayer || splineLayer.type !== "spline") {
      return {
        success: false,
        message: `Spline layer ${splineLayerId} not found`,
      };
    }
  }

  // Store path following config in layer data
  const cameraData = ensureCameraLayerData(layer);

  cameraData.pathFollowingConfig = {
    enabled: !!splineLayerId,
    splineLayerId: splineLayerId || null,
    lookMode: lookMode as "tangent" | "target" | "fixed",
    lookTarget: lookTarget || null,
    startOffset,
    speed,
    bankAmount,
    smoothing,
  };

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: splineLayerId
      ? `Camera now follows spline ${splineLayerId} (mode: ${lookMode})`
      : `Camera path following disabled`,
  };
}

function executeSetCameraAutoFocus(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const {
    cameraLayerId,
    enabled = true,
    mode = "center",
    focusPoint,
    smoothing = 0.8,
  } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === cameraLayerId);
  if (!layer || layer.type !== "camera") {
    return {
      success: false,
      message: `Camera layer ${cameraLayerId} not found`,
    };
  }

  // Store autofocus config in layer data
  const cameraData = ensureCameraLayerData(layer);

  // Enable depth of field if enabling autofocus
  if (enabled && cameraData.camera) {
    cameraData.camera.depthOfField = true;
  }

  // Map mode - 'face' mode from cameraEnhancements falls back to 'center' for our type
  const mappedMode =
    mode === "face"
      ? "center"
      : (mode as CameraLayerData["autoFocus"] extends { mode: infer M }
          ? M
          : never);

  cameraData.autoFocus = {
    enabled,
    mode: mappedMode as "center" | "point" | "nearest" | "farthest",
    focusPoint: focusPoint || { x: 0.5, y: 0.5 },
    smoothing,
    threshold: 10,
    sampleRadius: 0.1,
  };

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: enabled
      ? `Enabled ${mode} autofocus (smoothing: ${smoothing})`
      : `Disabled autofocus`,
  };
}

// ============================================================================
// TEXT HANDLERS
// ============================================================================

function executeSetTextContent(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, text, fontSize, fontFamily, fontWeight, color, alignment } =
    args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "text") {
    return { success: false, message: `Text layer ${layerId} not found` };
  }

  if (!isLayerOfType(layer, "text")) {
    return { success: false, message: `Layer ${layerId} is not a text layer` };
  }

  const textData = layer.data as TextData;

  if (text !== undefined) textData.text = text;
  if (fontSize !== undefined) textData.fontSize = fontSize;
  if (fontFamily !== undefined) textData.fontFamily = fontFamily;
  if (fontWeight !== undefined) textData.fontWeight = String(fontWeight);
  if (color !== undefined) {
    textData.fill = `rgba(${color.r}, ${color.g}, ${color.b}, ${color.a ?? 1})`;
  }
  if (alignment !== undefined) textData.textAlign = alignment;

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: `Updated text content`,
  };
}

function executeSetTextPath(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { textLayerId, splineLayerId, startOffset } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === textLayerId);
  if (!layer || layer.type !== "text") {
    return { success: false, message: `Text layer ${textLayerId} not found` };
  }

  if (!isLayerOfType(layer, "text")) {
    return { success: false, message: `Layer ${textLayerId} is not a text layer` };
  }

  const textData = layer.data as TextData;
  textData.pathLayerId = splineLayerId || null;
  if (startOffset !== undefined) {
    textData.pathOffset = startOffset;
  }

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: splineLayerId
      ? `Attached text to path ${splineLayerId}`
      : `Detached text from path`,
  };
}

// ============================================================================
// SPLINE HANDLERS
// ============================================================================

function executeSetSplinePoints(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, points, closed } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline") {
    return { success: false, message: `Spline layer ${layerId} not found` };
  }

  if (!isLayerOfType(layer, "spline")) {
    return { success: false, message: `Layer ${layerId} is not a spline layer` };
  }

  const splineData = layer.data as SplineData;

  // Convert points to control points format
  splineData.controlPoints = points.map((p: { x: number; y: number; handleIn?: { x: number; y: number } | null; handleOut?: { x: number; y: number } | null }, index: number) => ({
    id: `cp_${Date.now()}_${index}`,
    x: p.x,
    y: p.y,
    handleIn: p.handleIn || null,
    handleOut: p.handleOut || null,
    type: p.handleIn || p.handleOut ? "smooth" : "corner",
  }));

  if (closed !== undefined) {
    splineData.closed = closed;
  }

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: `Set ${points.length} control points on spline`,
  };
}

// ============================================================================
// SPEED MAP HANDLERS (formerly Time Remapping)
// ============================================================================

function executeSetSpeedMap(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, enabled, keyframes } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  // Speed map stored in layer data (with backwards compatibility)
  // Speed maps apply to video/nested comp layers - if no data exists, just modify existing
  if (layer.data) {
    const speedMapData = {
      enabled: enabled !== false,
      keyframes: keyframes || [],
    };
    // Use Object.assign for dynamic property assignment on existing data
    Object.assign(layer.data, { speedMap: speedMapData, timeRemap: speedMapData });
  }

  // Record modification and save to undo history
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return {
    success: true,
    message: enabled ? `Enabled speed map` : `Disabled speed map`,
  };
}

/** @deprecated Use executeSetSpeedMap instead */
function _executeSetTimeRemap(
  context: ExecutionContext,
  args: Record<string, any>,
): { success: boolean; message: string } {
  return executeSetSpeedMap(context, args);
}

// ============================================================================
// PLAYBACK HANDLERS
// ============================================================================

function executeSetCurrentFrame(
  context: ExecutionContext,
  args: Record<string, any>,
): { frame: number; message: string } {
  const { store, playbackStore, animationStore } = context;
  const { frame } = args;

  const comp = store.getActiveComp();
  const frameCount = comp?.settings.frameCount || 81;
  const clampedFrame = Math.max(0, Math.min(frame, frameCount - 1));

  const animStore = animationStore || useAnimationStore();
  animStore.setFrame(store, clampedFrame);

  return {
    frame: clampedFrame,
    message: `Jumped to frame ${clampedFrame}`,
  };
}

function executePlayPreview(
  context: ExecutionContext,
  args: Record<string, any>,
): { playing: boolean; message: string } {
  const { store, playbackStore, animationStore } = context;
  const { play } = args;

  if (play) {
    const comp = store.getActiveComp();
    if (comp) {
      const animStore = animationStore || useAnimationStore();
      playbackStore.play(
        comp.settings.fps,
        comp.settings.frameCount,
        comp.currentFrame,
        (frame) => animStore.setFrame(store, frame),
      );
    }
  } else {
    playbackStore.stop();
  }

  return {
    playing: play,
    message: play ? `Started playback` : `Stopped playback`,
  };
}

// ============================================================================
// AI IMAGE PROCESSING HANDLERS
// ============================================================================

async function executeDecomposeImage(
  context: ExecutionContext,
  args: Record<string, any>,
): Promise<{ layerIds: string[]; message: string }> {
  const { store } = context;
  const { sourceLayerId, numLayers = 4 } = args;

  // Find the source layer
  const sourceLayer = store
    .getActiveCompLayers()
    .find((l) => l.id === sourceLayerId);
  if (!sourceLayer) {
    throw new Error(`Source layer ${sourceLayerId} not found`);
  }

  if (sourceLayer.type !== "image") {
    throw new Error(`Layer ${sourceLayerId} is not an image layer`);
  }

  // Get the source image URL
  if (!isLayerOfType(sourceLayer, "image")) {
    throw new Error(`Source layer is not an image layer`);
  }
  const imageData = sourceLayer.data as ImageLayerData;
  const sourceUrl = imageData?.assetId;
  if (!sourceUrl) {
    throw new Error(`Source layer has no image source`);
  }

  // Convert to data URL if needed
  let imageDataUrl: string;
  if (sourceUrl.startsWith("data:")) {
    imageDataUrl = sourceUrl;
  } else {
    // Load image and convert to data URL
    imageDataUrl = await new Promise((resolve, reject) => {
      const img = new Image();
      img.crossOrigin = "anonymous";
      img.onload = () => {
        const canvas = document.createElement("canvas");
        canvas.width = img.naturalWidth;
        canvas.height = img.naturalHeight;
        const ctx = canvas.getContext("2d")!;
        ctx.drawImage(img, 0, 0);
        resolve(canvas.toDataURL("image/png"));
      };
      img.onerror = () => reject(new Error("Failed to load source image"));
      img.src = sourceUrl;
    });
  }

  // Run decomposition
  const service = getLayerDecompositionService();
  const decomposedLayers = await service.decomposeWithAutoSetup(
    imageDataUrl,
    { numLayers },
    (stage, message) => {
      console.log(`[AI Decompose] ${stage}: ${message}`);
    },
  );

  // Create layers from result (reverse order so Background is at bottom)
  const layerStoreInstance = useLayerStore();
  const createdLayerIds: string[] = [];
  for (let i = decomposedLayers.length - 1; i >= 0; i--) {
    const decomposed = decomposedLayers[i];
    const layer = layerStoreInstance.createLayer(store, "image", decomposed.label);
    if (layer.data && isLayerOfType(layer, "image")) {
      // Store decomposed image - ImageLayerData uses assetId, but we can store temp data
      Object.assign(layer.data, { assetId: decomposed.image });
    }
    createdLayerIds.push(layer.id);
  }

  store.pushHistory();

  return {
    layerIds: createdLayerIds,
    message: `Decomposed image into ${decomposedLayers.length} layers: ${decomposedLayers.map((l) => l.label).join(", ")}`,
  };
}

async function executeVectorizeImage(
  context: ExecutionContext,
  args: Record<string, any>,
): Promise<{ layerIds: string[]; message: string }> {
  const { store } = context;
  const {
    sourceLayerId,
    mode = "trace",
    separateLayers = true,
    groupByPath = true,
    autoGroupByRegion = false,
    enableAnimation = true,
    traceOptions = {},
  } = args;

  // Find the source layer
  const sourceLayer = store
    .getActiveCompLayers()
    .find((l) => l.id === sourceLayerId);
  if (!sourceLayer) {
    throw new Error(`Source layer ${sourceLayerId} not found`);
  }

  if (
    sourceLayer.type !== "image" &&
    sourceLayer.type !== "video" &&
    sourceLayer.type !== "solid"
  ) {
    throw new Error(
      `Layer ${sourceLayerId} must be an image, video, or solid layer`,
    );
  }

  // Get the source image URL from layer data
  // Support image, video, and solid layers with different data structures
  const layerData = sourceLayer.data;
  let imageDataUrl: string;

  if (isLayerOfType(sourceLayer, "image") && sourceLayer.data?.assetId) {
    const asset = store.project?.assets[sourceLayer.data.assetId];
    if (!asset?.data) throw new Error("Asset data not found");
    imageDataUrl = asset.data;
  } else if (layerData && "assetId" in layerData && layerData.assetId) {
    const asset = store.project?.assets[layerData.assetId as string];
    if (!asset?.data) throw new Error("Asset data not found");
    imageDataUrl = asset.data;
  } else {
    throw new Error("Source layer has no image source");
  }

  // Convert to data URL if it's a regular URL
  if (!imageDataUrl.startsWith("data:")) {
    imageDataUrl = await new Promise((resolve, reject) => {
      const img = new Image();
      img.crossOrigin = "anonymous";
      img.onload = () => {
        const canvas = document.createElement("canvas");
        canvas.width = img.naturalWidth;
        canvas.height = img.naturalHeight;
        const ctx = canvas.getContext("2d")!;
        ctx.drawImage(img, 0, 0);
        resolve(canvas.toDataURL("image/png"));
      };
      img.onerror = () => reject(new Error("Failed to load source image"));
      img.src = imageDataUrl;
    });
  }

  // Run vectorization
  const vectorizeService = getVectorizeService();
  const result = await vectorizeService.vectorize(
    imageDataUrl,
    {
      mode: mode as "trace" | "ai",
      traceOptions: {
        colorMode: traceOptions.colorMode || "color",
        filterSpeckle: traceOptions.filterSpeckle ?? 4,
        cornerThreshold: traceOptions.cornerThreshold ?? 60,
        colorPrecision: traceOptions.colorPrecision ?? 6,
        layerDifference: traceOptions.layerDifference ?? 16,
      },
    },
    (stage, message) => {
      console.log(`[AI Vectorize] ${stage}: ${message}`);
    },
  );

  // Filter small paths and normalize control points
  let paths = filterSmallPaths(result.paths, 2);
  paths = normalizeControlPoints(paths, {
    groupByPath: groupByPath,
    prefix: "vec",
  });

  const createdLayerIds: string[] = [];

  if (separateLayers) {
    // Create a separate spline layer for each path
    for (let i = 0; i < paths.length; i++) {
      const path = paths[i];

      // Auto-group by region if requested
      let controlPoints = path.controlPoints;
      if (autoGroupByRegion) {
        controlPoints = autoGroupPoints(controlPoints, { method: "quadrant" });
      }

      // Create the spline layer
      const layerStoreInstance = useLayerStore();
      const layer = layerStoreInstance.createSplineLayer(store);
      layerStoreInstance.renameLayer(store, layer.id, `Vector Path ${i + 1}`);

      // Update with control points
      if (layer.data) {
        Object.assign(layer.data, {
          controlPoints,
          closed: path.closed,
          stroke: path.stroke || "#00ff00",
          strokeWidth: 2,
          fill: path.fill || "",
          animated: enableAnimation,
        });
      }

      createdLayerIds.push(layer.id);
    }
  } else {
    // Create a single layer with all paths merged
    const allPoints: ControlPoint[] = [];
    let pointIdx = 0;

    for (let pathIdx = 0; pathIdx < paths.length; pathIdx++) {
      const path = paths[pathIdx];
      for (const cp of path.controlPoints) {
        allPoints.push({
          ...cp,
          id: `vec_${pointIdx++}`,
          group: `path_${pathIdx}`,
        });
      }
    }

    // Auto-group by region if requested (overrides path grouping)
    let controlPoints = allPoints;
    if (autoGroupByRegion) {
      controlPoints = autoGroupPoints(allPoints, { method: "quadrant" });
    }

    const layerStore = useLayerStore();
    const layer = layerStore.createSplineLayer(store);
    layerStore.renameLayer(store, layer.id, "Vectorized Paths");

    if (layer.data) {
      Object.assign(layer.data, {
        controlPoints,
        closed: false,
        stroke: "#00ff00",
        strokeWidth: 2,
        fill: "",
        animated: enableAnimation,
      });
    }

    createdLayerIds.push(layer.id);
  }

  store.pushHistory();

  return {
    layerIds: createdLayerIds,
    message: `Vectorized image into ${createdLayerIds.length} spline layer(s) with ${result.pathCount} paths`,
  };
}

// ============================================================================
// UTILITY HANDLERS
// ============================================================================

function executeGetLayerInfo(
  context: ExecutionContext,
  args: Record<string, any>,
): { layer: Record<string, any> | null; message: string } {
  const { store } = context;
  const { layerId } = args;

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    return { layer: null, message: `Layer ${layerId} not found` };
  }

  // Return a summary of the layer
  return {
    layer: {
      id: layer.id,
      name: layer.name,
      type: layer.type,
      visible: layer.visible,
      locked: layer.locked,
      inPoint: layer.inPoint,
      outPoint: layer.outPoint,
      transform: {
        position: layer.transform.position,
        scale: layer.transform.scale,
        rotation: layer.transform.rotation,
        origin: layer.transform.origin,
        // @deprecated alias for backwards compatibility
        anchorPoint: layer.transform.origin || layer.transform.anchorPoint,
      },
      opacity: layer.opacity,
      effects: layer.effects?.map((e) => ({
        id: e.id,
        effectKey: e.effectKey,
        name: e.name,
        enabled: e.enabled,
      })),
    },
    message: `Layer info for "${layer.name}"`,
  };
}

function executeFindLayers(
  context: ExecutionContext,
  args: Record<string, any>,
): {
  layers: Array<{ id: string; name: string; type: string }>;
  message: string;
} {
  const { store } = context;
  const { name, type } = args;

  let layers = store.getActiveCompLayers();

  if (name) {
    const lowerName = name.toLowerCase();
    layers = layers.filter((l) => l.name.toLowerCase().includes(lowerName));
  }

  if (type) {
    layers = layers.filter((l) => l.type === type);
  }

  return {
    layers: layers.map((l) => ({
      id: l.id,
      name: l.name,
      type: l.type,
    })),
    message: `Found ${layers.length} layer(s)`,
  };
}

function executeGetProjectState(
  context: ExecutionContext,
  _args: Record<string, any>,
): { state: any; message: string } {
  const { store } = context;
  const comp = store.getActiveComp();

  return {
    state: {
      composition: comp
        ? {
            id: comp.id,
            name: comp.name,
            width: comp.settings.width,
            height: comp.settings.height,
            frameCount: comp.settings.frameCount,
            fps: comp.settings.fps,
            currentFrame: comp.currentFrame,
          }
        : null,
      layerCount: store.getActiveCompLayers().length,
      layers: store.getActiveCompLayers().map((l) => ({
        id: l.id,
        name: l.name,
        type: l.type,
        visible: l.visible,
      })),
    },
    message: `Project state summary`,
  };
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/**
 * Set a nested property value using dot notation path
 */
function setNestedProperty(obj: any, path: string[], value: any): void {
  let current = obj;
  for (let i = 0; i < path.length - 1; i++) {
    if (!(path[i] in current)) {
      current[path[i]] = {};
    }
    current = current[path[i]];
  }
  current[path[path.length - 1]] = value;
}
