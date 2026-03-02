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
import { useEffectStore, type EffectStoreAccess } from "@/stores/effectStore";
import { useLayerStore } from "@/stores/layerStore";
import { useKeyframeStore, findPropertyByPath } from "@/stores/keyframeStore";
import { generateKeyframeId } from "@/utils/uuid5";
import { usePlaybackStore } from "@/stores/playbackStore";
import { useSelectionStore } from "@/stores/selectionStore";
import { useAnimationStore, type AnimationStoreAccess } from "@/stores/animationStore";
import { useProjectStore } from "@/stores/projectStore";
import type { Vec2, Vec3 } from "@/types/transform";
import { isFiniteNumber, assertDefined, safeCoordinateDefault, safeNonNegativeDefault, safePositiveDefault, isRecordLike } from "@/utils/typeGuards";
import type {
  AnimatableProperty,
  CameraLayerData,
  ControlPoint,
  ImageLayerData,
  InterpolationType,
  Layer,
  LayerType,
  ParticleLayerData,
  PropertyValue,
  SplineData,
  TextData,
} from "@/types/project";
import { isLayerOfType } from "@/types/project";
import type { ToolCall } from "./toolDefinitions";
import type { JSONValue } from "@/types/dataAsset";
import { createLogger } from "@/utils/logger";
import { agentSandbox } from "./security/agentSandbox";
import type { LatticeProject } from "@/types/project";

const logger = createLogger("ActionExecutor");
import type {
  CreateLayerArgs,
  DeleteLayerArgs,
  DuplicateLayerArgs,
  RenameLayerArgs,
  SetLayerParentArgs,
  ReorderLayersArgs,
  SetLayerPropertyArgs,
  SetLayerTransformArgs,
  AddKeyframeArgs,
  RemoveKeyframeArgs,
  SetKeyframeEasingArgs,
  ScaleKeyframeTimingArgs,
  SetExpressionArgs,
  RemoveExpressionArgs,
  AddEffectArgs,
  UpdateEffectArgs,
  RemoveEffectArgs,
  ConfigureParticlesArgs,
  ApplyCameraTrajectoryArgs,
  AddCameraShakeArgs,
  ApplyRackFocusArgs,
  SetCameraPathFollowingArgs,
  SetCameraAutoFocusArgs,
  SetTextContentArgs,
  SetTextPathArgs,
  SetSplinePointsArgs,
  SetSpeedMapArgs,
  SetCurrentFrameArgs,
  PlayPreviewArgs,
  DecomposeImageArgs,
  VectorizeImageArgs,
  GetLayerInfoArgs,
  FindLayersArgs,
  GetProjectStateArgs,
  GenerateTextContentArgs,
  GenerateSocialMediaPostArgs,
  GenerateAdCopyArgs,
  GenerateImageArgs,
  GenerateVideoArgs,
  ToolArgumentsFor,
} from "./toolArgumentTypes";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // sandbox // helpers
// ════════════════════════════════════════════════════════════════════════════

/**
 * Helper to update project state (sandbox or main store)
 * Note: Store actions already call pushHistory() - this only handles sandbox mode
 */
function updateProjectState(context: ExecutionContext): void {
  if (context.sandboxId) {
    const sandbox = agentSandbox.getSandbox(context.sandboxId);
    if (sandbox) {
      // Update sandbox state with current project state
      sandbox.currentState = structuredClone(context.projectStore.project) as LatticeProject;
      sandbox.currentState.meta.modified = new Date().toISOString();
      agentSandbox.updateSandboxState(context.sandboxId, sandbox.currentState);
    }
  }
  // Note: pushHistory() is NOT called here - store actions already handle history
  // Adding it here would create duplicate history entries and break undo/redo
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

export interface ExecutionContext {
  projectStore: ReturnType<typeof useProjectStore>;
  layerStore: ReturnType<typeof useLayerStore>;
  playbackStore: ReturnType<typeof usePlaybackStore>;
  selectionStore: ReturnType<typeof useSelectionStore>;
  animationStore: ReturnType<typeof useAnimationStore>;
  /** Sandbox ID if executing in sandbox mode */
  sandboxId?: string;
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

// ════════════════════════════════════════════════════════════════════════════
//                                                          // main // executor
// ════════════════════════════════════════════════════════════════════════════

/**
 * Execute a tool call from the AI agent
 * Returns the result of the action for the AI to verify
 *
 * @param toolCall - The tool call to execute
 * @param options - Execution options
 * @param options.sandboxId - If provided, execute in sandbox mode (updates sandbox state instead of main store)
 */
export async function executeToolCall(
  toolCall: ToolCall,
  options?: { sandboxId?: string },
): Promise<
  | { layerId: string; message: string }
  | { success: boolean; message: string }
  | { layerId: string | null; message: string }
  | { keyframeId: string | null; message: string }
  | { effectId: string | null; message: string }
  | { success: boolean; keyframeCount: number; message: string }
  | { frame: number; message: string }
  | { playing: boolean; message: string }
  | { layerIds: string[]; message: string }
  | { layer: Record<string, string | number | boolean | { x: number; y: number } | Array<{ id: string; effectKey: string; name: string; enabled: boolean }> | null> | null; message: string }
  | { layers: Array<{ id: string; name: string; type: string }>; message: string }
  | { state: Record<string, { id: string; name: string; width: number; height: number; frameCount: number; fps: number; currentFrame: number } | null | number | Array<{ id: string; name: string; type: string; visible: boolean }>>; message: string }
> {
  try {
    const sandboxId = options?.sandboxId;
    const projectStore = useProjectStore();
    const layerStore = useLayerStore();
    const animationStore = useAnimationStore();
    const playbackStore = usePlaybackStore();
    const selectionStore = useSelectionStore();

    //                                                                  // security
    let sandboxProjectState: LatticeProject | null = null;
    if (sandboxId) {
      const sandbox = agentSandbox.getSandbox(sandboxId);
      if (!sandbox) {
        throw new Error(`[ActionExecutor] Sandbox "${sandboxId}" not found`);
      }
      sandboxProjectState = sandbox.currentState;
    }

    const context: ExecutionContext = {
      projectStore,
      playbackStore,
      selectionStore,
      layerStore,
      animationStore,
      sandboxId,
    };
    
    // ToolCall is a discriminated union - TypeScript narrows the type based on name
    // The args are spread directly on toolCall (not nested under 'arguments')
    const { name } = toolCall;

    // Route to appropriate handler with type-safe narrowing
    // TypeScript knows the correct argument type for each case
    // State-modifying actions call updateProjectState to enable undo/redo
    // Result type matches the function's return type union - handlers return various shapes
    let result: Awaited<ReturnType<typeof executeToolCall>>;
    let isStateMutating = true; // Most actions mutate state

    switch (name) {
    // Layer Management
    case "createLayer":
      result = executeCreateLayer(context, toolCall);
      break;
    case "deleteLayer":
      result = executeDeleteLayer(context, toolCall);
      break;
    case "duplicateLayer":
      result = executeDuplicateLayer(context, toolCall);
      break;
    case "renameLayer":
      result = executeRenameLayer(context, toolCall);
      break;
    case "setLayerParent":
      result = executeSetLayerParent(context, toolCall);
      break;
    case "reorderLayers":
      result = executeReorderLayers(context, toolCall);
      break;

    // Property Modification
    case "setLayerProperty":
      result = executeSetLayerProperty(context, toolCall);
      break;
    case "setLayerTransform":
      result = executeSetLayerTransform(context, toolCall);
      break;

    // Keyframe Animation
    case "addKeyframe":
      result = executeAddKeyframe(context, toolCall);
      break;
    case "removeKeyframe":
      result = executeRemoveKeyframe(context, toolCall);
      break;
    case "setKeyframeEasing":
      result = executeSetKeyframeEasing(context, toolCall);
      break;
    case "scaleKeyframeTiming":
      result = executeScaleKeyframeTiming(context, toolCall);
      break;

    // Expressions
    case "setExpression":
      result = executeSetExpression(context, toolCall);
      break;
    case "removeExpression":
      result = executeRemoveExpression(context, toolCall);
      break;

    // Effects
    case "addEffect":
      result = executeAddEffect(context, toolCall);
      break;
    case "updateEffect":
      result = executeUpdateEffect(context, toolCall);
      break;
    case "removeEffect":
      result = executeRemoveEffect(context, toolCall);
      break;

    // Particle System
    case "configureParticles":
      result = executeConfigureParticles(context, toolCall);
      break;

    // Camera System
    case "applyCameraTrajectory":
      result = executeApplyCameraTrajectory(context, toolCall);
      break;
    case "addCameraShake":
      result = executeAddCameraShake(context, toolCall);
      break;
    case "applyRackFocus":
      result = executeApplyRackFocus(context, toolCall);
      break;
    case "setCameraPathFollowing":
      result = executeSetCameraPathFollowing(context, toolCall);
      break;
    case "setCameraAutoFocus":
      result = executeSetCameraAutoFocus(context, toolCall);
      break;

    // Text
    case "setTextContent":
      result = executeSetTextContent(context, toolCall);
      break;
    case "setTextPath":
      result = executeSetTextPath(context, toolCall);
      break;

    // Spline
    case "setSplinePoints":
      result = executeSetSplinePoints(context, toolCall);
      break;

    // Speed Map (formerly Time Remapping)
    case "setSpeedMap":
      result = executeSetSpeedMap(context, toolCall);
      break;
    case "setTimeRemap": // Legacy - redirects to setSpeedMap
      result = executeSetSpeedMap(context, toolCall);
      break;

    // Playback (non-state-mutating - doesn't affect undo history)
    case "setCurrentFrame":
      result = executeSetCurrentFrame(context, toolCall);
      isStateMutating = false;
      break;
    case "playPreview":
      result = executePlayPreview(context, toolCall);
      isStateMutating = false;
      break;

    //                                                                   // ai // i
    case "decomposeImage":
      result = await executeDecomposeImage(context, toolCall);
      break;
    case "vectorizeImage":
      result = await executeVectorizeImage(context, toolCall);
      break;

    // Utility (read-only - doesn't affect undo history)
    case "getLayerInfo":
      result = executeGetLayerInfo(context, toolCall);
      isStateMutating = false;
      break;
    case "findLayers":
      result = executeFindLayers(context, toolCall);
      isStateMutating = false;
      break;
    case "getProjectState":
      result = executeGetProjectState(context, toolCall);
      isStateMutating = false;
      break;

    //                                                              // compass // c
    case "generateTextContent":
      result = await executeGenerateTextContent(context, toolCall);
      break;
    case "generateSocialMediaPost":
      result = await executeGenerateSocialMediaPost(context, toolCall);
      break;
    case "generateAdCopy":
      result = await executeGenerateAdCopy(context, toolCall);
      break;
    case "generateImage":
      result = await executeGenerateImage(context, toolCall);
      break;
    case "generateVideo":
      result = await executeGenerateVideo(context, toolCall);
      break;

    default:
      throw new Error(`[ActionExecutor] Unknown tool: "${name}". Tool name is not recognized.`);
    }

    // Push history for state-mutating actions to enable undo/redo
    if (isStateMutating) {
      updateProjectState(context);
    }

    return result;
  } catch (error) {
    // Convert thrown errors to success: false format for AI agent compatibility
    // Errors are now explicit and debuggable before being converted
    const errorMessage = error instanceof Error ? error.message : String(error);
    return { success: false, message: errorMessage };
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                           // layer // management // handlers
// ════════════════════════════════════════════════════════════════════════════

/**
 * Validated tool argument value - can be string, number, boolean, object, or array
 * This represents the validated structure after schema checking
 * Uses JSONValue for type safety (no circular reference)
 */
type ValidatedToolArgValue = JSONValue;

/**
 * Validate required arguments exist and have correct types
 * Throws explicit errors for invalid arguments
 */
function validateArgs(
  args: Record<string, ValidatedToolArgValue>,
  schema: Record<string, { type: string; required?: boolean }>,
): void {
  for (const [key, spec] of Object.entries(schema)) {
    const value = args[key];

    // Check required fields
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    // Pattern match: Check if value is missing (null or not a valid type)
    // Note: Arrays ARE objects in JavaScript, so we must check Array.isArray separately
    const valueIsMissing = value === null || (typeof value !== "string" && typeof value !== "number" && typeof value !== "boolean" && (typeof value !== "object" || value === null || Array.isArray(value)));
    if (spec.required && valueIsMissing) {
      throw new Error(`[ActionExecutor] Missing required argument: "${key}". Required argument is missing or has invalid type.`);
    }

    // Skip type check if value is missing and not required
    if (valueIsMissing) continue;

    // Type validation
    const actualType = Array.isArray(value) ? "array" : typeof value;
    if (spec.type === "array" && !Array.isArray(value)) {
      throw new Error(`[ActionExecutor] Argument "${key}" must be an array, got ${actualType}. Provide an array value for this argument.`);
    } else if (
      spec.type !== "array" &&
      spec.type !== "any" &&
      actualType !== spec.type
    ) {
      throw new Error(`[ActionExecutor] Argument "${key}" must be ${spec.type}, got ${actualType}. Provide a ${spec.type} value for this argument.`);
    }
  }
}

function executeCreateLayer(
  context: ExecutionContext,
  args: CreateLayerArgs,
): { layerId: string; message: string } {
  const { layerStore } = context;

  // Validate arguments
  // Type guard: Ensure args is a record-like object
  if (typeof args !== "object" || args === null || Array.isArray(args)) {
    throw new Error(`[ActionExecutor] Invalid arguments: expected object, got ${typeof args}. Arguments must be a plain object.`);
  }
  // Type assertion: After type guard, args is a plain object suitable for validation
  // CreateLayerArgs properties are all JSONValue-compatible
  // Convert to Record<string, ValidatedToolArgValue> for validation
  const argsRecord: Record<string, ValidatedToolArgValue> = {};
  for (const [key, value] of Object.entries(args)) {
    // Runtime type check: Ensure value is JSONValue
    if (
      typeof value === "string" ||
      typeof value === "number" ||
      typeof value === "boolean" ||
      value === null ||
      Array.isArray(value) ||
      (typeof value === "object" && value !== null)
    ) {
      argsRecord[key] = value as ValidatedToolArgValue;
    }
  }
  validateArgs(argsRecord, {
    type: { type: "string", required: true },
    name: { type: "string", required: false },
    properties: { type: "object", required: false },
    position: { type: "object", required: false },
    inPoint: { type: "number", required: false },
    outPoint: { type: "number", required: false },
  });

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

    //                                                                        // ai
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
    internalType as LayerType,
    name,
  );

  // Apply initial properties
  if (position) {
    layer.transform.position.value = position;
  }
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  if (typeof inPoint === "number") {
    layer.inPoint = inPoint;
  }
  if (typeof outPoint === "number") {
    layer.outPoint = outPoint;
  }
  if (properties) {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || {}
    const layerData = layer.data;
    const dataObj = (layerData !== null && layerData !== undefined && typeof layerData === "object" && layerData !== null) ? layerData : {};
    Object.assign(dataObj, properties);
  }

  return {
    layerId: layer.id,
    message: `Created ${type} layer "${layer.name}" with ID ${layer.id}`,
  };
}

function executeDeleteLayer(
  context: ExecutionContext,
  args: DeleteLayerArgs,
): { success: boolean; message: string } {
  const { projectStore, layerStore } = context;
  const { layerId } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" not found. Cannot delete non-existent layer.`);
  }

  const layerName = layer.name;
  layerStore.deleteLayer(layerId);

  return {
    success: true,
    message: `Deleted layer "${layerName}"`,
  };
}

function executeDuplicateLayer(
  context: ExecutionContext,
  args: DuplicateLayerArgs,
): { layerId: string | null; message: string } {
  const { layerStore } = context;
  const { layerId, newName } = args;

  const duplicate = layerStore.duplicateLayer(layerId);
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
  args: RenameLayerArgs,
): { success: boolean; message: string } {
  const { projectStore, layerStore } = context;
  const { layerId, name } = args;

  layerStore.renameLayer(layerId, name);
  
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  const oldName = (typeof layer === "object" && layer !== null && "name" in layer && typeof layer.name === "string")
    ? layer.name
    : "Unknown";

  return {
    success: true,
    message: `Renamed layer from "${oldName}" to "${name}"`,
  };
}

function executeSetLayerParent(
  context: ExecutionContext,
  args: SetLayerParentArgs,
): { success: boolean; message: string } {
  const { layerStore } = context;
  const { layerId, parentId } = args;

  layerStore.setLayerParent(layerId, parentId || null);

  return {
    success: true,
    message: parentId
      ? `Set parent of layer ${layerId} to ${parentId}`
      : `Removed parent from layer ${layerId}`,
  };
}

function executeReorderLayers(
  context: ExecutionContext,
  args: ReorderLayersArgs,
): { success: boolean; message: string } {
  const { layerStore } = context;
  const { layerId, newIndex } = args;

  layerStore.moveLayer(layerId, newIndex);

  return {
    success: true,
    message: `Moved layer ${layerId} to index ${newIndex}`,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                      // property // modification // handlers
// ════════════════════════════════════════════════════════════════════════════

function executeSetLayerProperty(
  context: ExecutionContext,
  args: SetLayerPropertyArgs,
): { success: boolean; message: string } {
  const { projectStore, layerStore } = context;
  const { layerId, propertyPath, value } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" not found. Cannot set property "${propertyPath}" on non-existent layer.`);
  }

  // Handle different property paths
  const parts = propertyPath.split(".");

  if (parts[0] === "data" && layer.data) {
    // Layer-specific data (e.g., data.text, data.color)
    // Type guard: Ensure layer.data is a record-like object before setting nested properties
    if (typeof layer.data !== "object" || layer.data === null || Array.isArray(layer.data)) {
      throw new Error(`[ActionExecutor] Cannot set nested property "${propertyPath}": layer.data is not a plain object. Layer type: ${layer.type}.`);
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy type assertions
    // Use type guard to validate structure at runtime
    if (!isRecordLike(layer.data)) {
      throw new Error(`[ActionExecutor] Cannot set nested property "${propertyPath}": layer.data is not a record-like object. Layer type: ${layer.type}.`);
    }
    // Build compatible object by copying properties - validates structure without type assertions
    const layerDataObj: Record<string, PropertyValue | JSONValue | undefined> = {};
    for (const key in layer.data) {
      if (Object.prototype.hasOwnProperty.call(layer.data, key)) {
        const propValue = layer.data[key];
        if (
          propValue === null ||
          typeof propValue === "string" ||
          typeof propValue === "number" ||
          typeof propValue === "boolean" ||
          Array.isArray(propValue) ||
          (typeof propValue === "object" && propValue !== null)
        ) {
          layerDataObj[key] = propValue as PropertyValue | JSONValue | undefined;
        }
      }
    }
    setNestedProperty(layerDataObj, parts.slice(1), value as JSONValue);
    // Copy back to layer.data (we've validated it's a plain object)
    Object.assign(layer.data, layerDataObj);
  } else if (parts[0] === "transform") {
    // Transform properties - use type-safe property access
    const transformKey = parts[1] as keyof typeof layer.transform;
    const prop = layer.transform[transformKey];
    if (prop && typeof prop === "object" && "value" in prop) {
      // Type-safe property value assignment
      if (prop && typeof prop === "object" && "value" in prop) {
        // PropertyValue can be any JSONValue
        (prop as { value: PropertyValue }).value = value as PropertyValue;
      }
    }
  } else if (propertyPath === "opacity") {
    // opacity is AnimatableProperty<number>, so value must be number
    if (typeof value === "number") {
      layer.opacity.value = value;
    } else {
      throw new Error(`[ActionExecutor] Invalid opacity value: expected number, got ${typeof value}. Provide a numeric opacity value between 0 and 100.`);
    }
  } else if (propertyPath === "visible") {
    // visible is boolean
    if (typeof value === "boolean") {
      layer.visible = value;
    } else {
      throw new Error(`[ActionExecutor] Invalid visible value: expected boolean, got ${typeof value}. Provide true or false to set layer visibility.`);
    }
  } else if (propertyPath === "locked") {
    // locked is boolean
    if (typeof value === "boolean") {
      layer.locked = value;
    } else {
      throw new Error(`[ActionExecutor] Invalid locked value: expected boolean, got ${typeof value}. Provide true or false to set layer lock state.`);
    }
  } else if (propertyPath === "inPoint") {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    // Pattern match: inPoint ∈ number | undefined
    // To "clear" optional property, delete it rather than assign undefined
    if (value === null) {
      delete layer.inPoint;
    } else if (typeof value === "number") {
      layer.inPoint = value;
    } else {
      throw new Error(`[ActionExecutor] Invalid inPoint value: expected number or null, got ${typeof value}. Provide a frame number or null to clear the in point.`);
    }
  } else if (propertyPath === "outPoint") {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    // Pattern match: outPoint ∈ number | undefined
    // To "clear" optional property, delete it rather than assign undefined
    if (value === null || typeof value !== "number") {
      delete layer.outPoint;
    } else if (typeof value === "number") {
      layer.outPoint = value;
    } else {
      throw new Error(`[ActionExecutor] Invalid outPoint value: expected number or null, got ${typeof value}. Provide a frame number or null to clear the out point.`);
    }
  } else {
    // Try to find in layer.data
    if (layer.data) {
      // Type guard: Ensure layer.data is a record-like object before setting nested properties
      if (typeof layer.data !== "object" || layer.data === null || Array.isArray(layer.data)) {
        throw new Error(`[ActionExecutor] Cannot set nested property "${propertyPath}": layer.data is not a plain object. Layer type: ${layer.type}.`);
      }
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy type assertions
      // Use type guard to validate structure at runtime
      if (!isRecordLike(layer.data)) {
        throw new Error(`[ActionExecutor] Cannot set nested property "${propertyPath}": layer.data is not a record-like object. Layer type: ${layer.type}.`);
      }
      // Build compatible object by copying properties - validates structure without type assertions
      const layerDataObj: { [K in string]: PropertyValue | JSONValue | undefined } = {};
      for (const key in layer.data) {
        if (Object.prototype.hasOwnProperty.call(layer.data, key)) {
          const propValue = layer.data[key];
          if (
            propValue === null ||
            typeof propValue === "string" ||
            typeof propValue === "number" ||
            typeof propValue === "boolean" ||
            Array.isArray(propValue) ||
            (typeof propValue === "object" && propValue !== null)
          ) {
            layerDataObj[key] = propValue as PropertyValue | JSONValue | undefined;
          }
        }
      }
      setNestedProperty(layerDataObj, parts, value as JSONValue);
      // Copy back to layer.data (we've validated it's a plain object)
      Object.assign(layer.data, layerDataObj);
    }
  }

  // Record modification and save to undo history
  // This function modifies layer state directly (not through store actions),
  // so we must call pushHistory() explicitly for undo/redo support
  context.projectStore.pushHistory();
  //                                                                  // security
  updateProjectState(context);

  return {
    success: true,
    message: `Set ${propertyPath} to ${JSON.stringify(value)}`,
  };
}

function executeSetLayerTransform(
  context: ExecutionContext,
  args: SetLayerTransformArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
  const { layerId, position, scale, rotation, opacity, anchorPoint } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" not found. Cannot set transform on non-existent layer.`);
  }

  const changes: string[] = [];

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  if (typeof position === "object" && position !== null) {
    layer.transform.position.value = position;
    changes.push("position");
  }
  if (typeof scale === "object" && scale !== null) {
    layer.transform.scale.value = scale;
    changes.push("scale");
  }
  if (typeof rotation === "number") {
    layer.transform.rotation.value = rotation;
    changes.push("rotation");
  }
  if (typeof opacity === "number") {
    layer.opacity.value = opacity;
    changes.push("opacity");
  }
  if (typeof anchorPoint === "object" && anchorPoint !== null) {
    // Use origin (new name) with fallback to anchorPoint
    const originProp = layer.transform.origin || layer.transform.anchorPoint;
    if (originProp) {
      originProp.value = anchorPoint;
    }
    changes.push("origin");
  }

  // Record modification and save to undo history
  // This function modifies layer state directly (not through store actions),
  // so we must call pushHistory() explicitly for undo/redo support
  context.projectStore.pushHistory();
  //                                                                  // security
  updateProjectState(context);

  return {
    success: true,
    message: `Updated transform: ${changes.join(", ")}`,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                         // keyframe // animation // handlers
// ════════════════════════════════════════════════════════════════════════════

function executeAddKeyframe(
  context: ExecutionContext,
  args: AddKeyframeArgs,
): { keyframeId: string | null; message: string } {
  const keyframeStore = useKeyframeStore();
  const { layerId, propertyPath, frame, value, interpolation } = args;

  const keyframe = keyframeStore.addKeyframe(
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
    keyframeStore.setKeyframeInterpolation(
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
  args: RemoveKeyframeArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
  const keyframeStore = useKeyframeStore();
  const { layerId, propertyPath, frame } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" not found. Cannot remove keyframe from non-existent layer.`);
  }

  // Find keyframe at frame
  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    throw new Error(`[ActionExecutor] Property "${propertyPath}" not found on layer "${layerId}". Check the property path and try again.`);
  }

  const keyframe = property.keyframes.find((k) => k.frame === frame);
  if (!keyframe) {
    throw new Error(`[ActionExecutor] No keyframe found at frame ${frame} for property "${propertyPath}" on layer "${layerId}". Add a keyframe first or check the frame number.`);
  }

  keyframeStore.removeKeyframe(layerId, propertyPath, keyframe.id);

  return {
    success: true,
    message: `Removed keyframe at frame ${frame} from ${propertyPath}`,
  };
}

function executeSetKeyframeEasing(
  context: ExecutionContext,
  args: SetKeyframeEasingArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
  const keyframeStore = useKeyframeStore();
  const { layerId, propertyPath, frame, interpolation } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" not found. Cannot set keyframe easing on non-existent layer.`);
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    throw new Error(`[ActionExecutor] Property "${propertyPath}" not found on layer "${layerId}". Check the property path and try again.`);
  }

  const keyframe = property.keyframes.find((k) => k.frame === frame);
  if (!keyframe) {
    throw new Error(`[ActionExecutor] No keyframe found at frame ${frame} for property "${propertyPath}" on layer "${layerId}". Add a keyframe first or check the frame number.`);
  }

  keyframeStore.setKeyframeInterpolation(
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
  args: ScaleKeyframeTimingArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
  const { layerId, scaleFactor, propertyPath } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" not found. Cannot scale keyframe timing on non-existent layer.`);
  }

  // Get all properties to scale
  const propertiesToScale: string[] = propertyPath
    ? [propertyPath]
    : ["position", "scale", "rotation", "opacity", "anchorPoint"];

  let scaledCount = 0;

  for (const propPath of propertiesToScale) {
    const property = findPropertyByPath(layer, propPath);
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof property === "object" && property !== null && "keyframes" in property && Array.isArray(property.keyframes) && property.keyframes.length > 0) {
      // Scale each keyframe's frame number and regenerate IDs
      for (const kf of property.keyframes) {
        const newFrame = Math.round(kf.frame * scaleFactor);
        // Regenerate keyframe ID based on new frame number for determinism
        // Same layer/property/frame/value should always produce same ID
        const valueStr = typeof kf.value === "object" && kf.value !== null && "x" in kf.value && "y" in kf.value
          ? `${(kf.value as { x: number; y: number }).x},${(kf.value as { x: number; y: number }).y}${"z" in kf.value ? `,${(kf.value as { x: number; y: number; z?: number }).z}` : ""}`
          : String(kf.value);
        kf.id = generateKeyframeId(layerId, propPath, newFrame, valueStr);
        kf.frame = newFrame;
      }
      // Re-sort keyframes
      property.keyframes.sort((a, b) => a.frame - b.frame);
      scaledCount += property.keyframes.length;
    }
  }

  // Record modification and save to undo history (only if changes were made)
  if (scaledCount > 0) {
    projectStore.project.meta.modified = new Date().toISOString();
    //                                                                  // security
  updateProjectState(context);
  }

  return {
    success: true,
    message: `Scaled ${scaledCount} keyframes by factor ${scaleFactor}`,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                    // expression // handlers
// ════════════════════════════════════════════════════════════════════════════

function executeSetExpression(
  context: ExecutionContext,
  args: SetExpressionArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
  const { layerId, propertyPath, expressionType, params } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" not found. Cannot set expression on non-existent layer.`);
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    throw new Error(`[ActionExecutor] Property "${propertyPath}" not found on layer "${layerId}". Check the property path and try again.`);
  }

  // Set expression on property
  property.expression = {
    enabled: true,
    type: "preset" as const,
    name: expressionType,
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || {}
    params: (params !== null && params !== undefined && typeof params === "object" && params !== null) ? params : {},
  };

  // Record modification and save to undo history
  // This function modifies layer state directly (not through store actions),
  // so we must call pushHistory() explicitly for undo/redo support
  context.projectStore.pushHistory();
  //                                                                  // security
  updateProjectState(context);

  return {
    success: true,
    message: `Applied ${expressionType} expression to ${propertyPath}`,
  };
}

function executeRemoveExpression(
  context: ExecutionContext,
  args: RemoveExpressionArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
  const { layerId, propertyPath } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" not found. Cannot remove expression from non-existent layer.`);
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    throw new Error(`[ActionExecutor] Property "${propertyPath}" not found on layer "${layerId}". Check the property path and try again.`);
  }

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  // Pattern match: expression ∈ PropertyExpression | undefined
  // To "clear" optional property, delete it rather than assign undefined
  delete property.expression;

  // Record modification and save to undo history
  // This function modifies layer state directly (not through store actions),
  // so we must call pushHistory() explicitly for undo/redo support
  context.projectStore.pushHistory();
  //                                                                  // security
  updateProjectState(context);

  return {
    success: true,
    message: `Removed expression from ${propertyPath}`,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                        // effect // handlers
// ════════════════════════════════════════════════════════════════════════════

function executeAddEffect(
  context: ExecutionContext,
  args: AddEffectArgs,
): { effectId: string | null; message: string } {
  const { projectStore, animationStore } = context;
  const { layerId, effectType, params } = args;

  const effectStore = useEffectStore();
  const effectStoreAccess: EffectStoreAccess = {
    project: {
      meta: { modified: projectStore.project.meta.modified },
    },
    currentFrame: animationStore.currentFrame,
    getActiveCompLayers: () => projectStore.getActiveCompLayers(),
    getActiveComp: () => projectStore.getActiveComp(),
      pushHistory: () => updateProjectState(context),
  };

  effectStore.addEffectToLayer(effectStoreAccess, layerId, effectType);

  // Get the newly added effect (last in array)
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  const effects = (typeof layer === "object" && layer !== null && "effects" in layer && Array.isArray(layer.effects))
    ? layer.effects
    : [];
  const effect = effects.length > 0 ? effects[effects.length - 1] : null;

  if (!effect) {
    return { effectId: null, message: `Failed to add effect ${effectType}` };
  }

  // Apply initial parameters
  if (params) {
    for (const [key, value] of Object.entries(params)) {
      effectStore.updateEffectParameter(
        effectStoreAccess,
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
  args: UpdateEffectArgs,
): { success: boolean; message: string } {
  const { projectStore, animationStore } = context;
  const { layerId, effectId, params } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  if (typeof layer !== "object" || layer === null || !("effects" in layer) || !Array.isArray(layer.effects)) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" not found or has no effects. Cannot update effect parameters on non-existent layer or layer without effects.`);
  }

  const effect = layer.effects.find((e) => e.id === effectId);
  if (!effect) {
    throw new Error(`[ActionExecutor] Effect "${effectId}" not found on layer "${layerId}". Check the effect ID and try again.`);
  }

  const effectStore = useEffectStore();
  const effectStoreAccess: EffectStoreAccess = {
    project: {
      meta: { modified: projectStore.project.meta.modified },
    },
    currentFrame: animationStore.currentFrame,
    getActiveCompLayers: () => projectStore.getActiveCompLayers(),
    getActiveComp: () => projectStore.getActiveComp(),
      pushHistory: () => updateProjectState(context),
  };

  for (const [key, value] of Object.entries(params)) {
    effectStore.updateEffectParameter(effectStoreAccess, layerId, effectId, key, value);
  }

  return {
    success: true,
    message: `Updated ${Object.keys(params).length} effect parameters`,
  };
}

function executeRemoveEffect(
  context: ExecutionContext,
  args: RemoveEffectArgs,
): { success: boolean; message: string } {
  const { projectStore, animationStore } = context;
  const { layerId, effectId } = args;

  const effectStore = useEffectStore();
  const effectStoreAccess: EffectStoreAccess = {
    project: {
      meta: { modified: projectStore.project.meta.modified },
    },
    currentFrame: animationStore.currentFrame,
    getActiveCompLayers: () => projectStore.getActiveCompLayers(),
    getActiveComp: () => projectStore.getActiveComp(),
      pushHistory: () => updateProjectState(context),
  };

  effectStore.removeEffectFromLayer(effectStoreAccess, layerId, effectId);

  return {
    success: true,
    message: `Removed effect ${effectId}`,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                            // particle // system // handlers
// ════════════════════════════════════════════════════════════════════════════

function executeConfigureParticles(
  context: ExecutionContext,
  args: ConfigureParticlesArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
  const { layerId, emitter, particles, physics } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "particles") {
    throw new Error(`[ActionExecutor] Particle layer "${layerId}" not found. Cannot configure particles on non-existent layer.`);
  }

  if (!isLayerOfType(layer, "particles")) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" is not a particles layer. Only particle layers can be configured with particle settings.`);
  }

  const particleData = layer.data as ParticleLayerData;

  // Update emitter configuration
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  const emitters = Array.isArray(particleData.emitters) && particleData.emitters.length > 0
    ? particleData.emitters
    : [];
  if (emitter && emitters.length > 0) {
    Object.assign(emitters[0], emitter);
  }

  // Update particle settings
  if (particles && emitters.length > 0) {
    Object.assign(particleData.emitters[0], particles);
  }

  // Update physics
  if (physics && particleData.systemConfig) {
    if (physics.gravity) {
      // Type proof: gravity.y ∈ number | undefined → number (coordinate-like, can be negative)
      particleData.systemConfig.gravity = safeCoordinateDefault(physics.gravity.y, 0, "physics.gravity.y");
    }
    if (physics.wind) {
      // Default to zero if wind components are undefined
      // Type proof: x, y ∈ ℝ ∪ {undefined} → x, y ∈ ℝ
      const windXValue = physics.wind.x;
      const windX = isFiniteNumber(windXValue) ? windXValue : 0;
      const windYValue = physics.wind.y;
      const windY = isFiniteNumber(windYValue) ? windYValue : 0;
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
  //                                                                  // security
  updateProjectState(context);

  return {
    success: true,
    message: `Configured particle system`,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                              // camera // system // handlers
// ════════════════════════════════════════════════════════════════════════════

function executeApplyCameraTrajectory(
  context: ExecutionContext,
  args: ApplyCameraTrajectoryArgs,
): { success: boolean; keyframeCount: number; message: string } {
  const { projectStore } = context;
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

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === cameraLayerId);
  if (!layer || layer.type !== "camera") {
    throw new Error(`[ActionExecutor] Camera layer "${cameraLayerId}" not found. Cannot generate trajectory on non-existent camera layer.`);
  }

  const comp = projectStore.getActiveComp();
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  if (comp === null || typeof comp !== "object" || !("settings" in comp) || comp.settings === null || typeof comp.settings !== "object") {
    throw new Error(`[ActionExecutor] No active composition. Cannot generate trajectory without a valid composition.`);
  }
  const compSettings = comp.settings;

  // Build trajectory configuration
  // Type proof: duration ∈ ℕ ∪ {undefined} → ℕ
  const durationValue = duration;
  const trajectoryDuration = isFiniteNumber(durationValue) && Number.isInteger(durationValue) && durationValue >= 0
    ? durationValue
    : compSettings.frameCount;
  // Type proof: amplitude ∈ ℝ ∪ {undefined} → ℝ | undefined
  const amplitudeValue = amplitude;
  const trajectoryAmplitude = isFiniteNumber(amplitudeValue) ? amplitudeValue : undefined;
  // Type proof: loops ∈ ℕ ∪ {undefined} → ℕ | undefined
  const loopsValue = loops;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  const trajectoryLoops = isFiniteNumber(loopsValue) && Number.isInteger(loopsValue) && loopsValue >= 0 ? loopsValue : 0;
  const trajectoryConfig = createTrajectoryFromPreset(
    trajectoryType as TrajectoryType,
    {
      duration: trajectoryDuration,
      amplitude: trajectoryAmplitude,
      loops: trajectoryLoops,
      easing: easing && ["linear", "ease-in", "ease-out", "ease-in-out", "bounce"].includes(easing) 
        ? easing as "linear" | "ease-in" | "ease-out" | "ease-in-out" | "bounce"
        : undefined,
      // Type proof: center ∈ {x, y, z} | undefined → {x, y, z}
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      center: typeof center === "object" && center !== null
        ? center
        : {
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
  // Type proof: After filter, position/pointOfInterest/zoom are guaranteed non-null
  // Type guard: Check if zoom exists before accessing
  const zoomKeyframes = "zoom" in keyframes && Array.isArray(keyframes.zoom)
    ? keyframes.zoom
    : [];
  cameraData.trajectoryKeyframes = {
    position: keyframes.position
      .filter((kf): kf is typeof kf & { position: NonNullable<typeof kf.position> } => typeof kf.position === "object" && kf.position !== null)
      .map((kf) => ({ frame: kf.frame, position: kf.position })),
    pointOfInterest: keyframes.pointOfInterest
      .filter((kf): kf is typeof kf & { pointOfInterest: NonNullable<typeof kf.pointOfInterest> } => typeof kf.pointOfInterest === "object" && kf.pointOfInterest !== null)
      .map((kf) => ({ frame: kf.frame, pointOfInterest: kf.pointOfInterest })),
    zoom: zoomKeyframes
      .filter((kf): kf is typeof kf & { zoom: NonNullable<typeof kf.zoom> } => typeof kf.zoom === "number")
      .map((kf) => ({ frame: kf.frame, zoom: kf.zoom })),
  };

  // Also create standard layer keyframes for position
  const keyframeStore = useKeyframeStore();
  for (const kf of keyframes.position) {
    if (kf.position) {
      keyframeStore.addKeyframe(
        cameraLayerId,
        "cameraPosition",
        kf.position,
        kf.frame,
      );
    }
  }

  // Type proof: zoomKeyframes.length ∈ number (≥ 0, count)
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  // Use the zoomKeyframes already defined above
  const zoomKeyframeCount = safeNonNegativeDefault(zoomKeyframes.length, 0, "zoomKeyframes.length");
  const totalKeyframes =
    keyframes.position.length +
    keyframes.pointOfInterest.length +
    zoomKeyframeCount;

  return {
    success: true,
    keyframeCount: totalKeyframes,
    message: `Applied ${trajectoryType} trajectory with ${totalKeyframes} keyframes`,
  };
}

function executeAddCameraShake(
  context: ExecutionContext,
  args: AddCameraShakeArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
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

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === cameraLayerId);
  if (!layer || layer.type !== "camera") {
    throw new Error(`[ActionExecutor] Camera layer "${cameraLayerId}" not found. Cannot configure camera on non-existent layer.`);
  }

  const comp = projectStore.getActiveComp();
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  if (comp === null || typeof comp !== "object" || !("settings" in comp) || comp.settings === null || typeof comp.settings !== "object" || !("frameCount" in comp.settings) || typeof comp.settings.frameCount !== "number") {
    throw new Error(`[ActionExecutor] No active composition or invalid frame count. Cannot generate camera shake without a valid composition.`);
  }
  const compDuration = comp.settings.frameCount;

  // Build shake config
  // Type proof: seed ∈ ℕ ∪ {undefined} → ℕ
  const seedValue = seed;
  const shakeSeed = isFiniteNumber(seedValue) && Number.isInteger(seedValue) && seedValue >= 0
    ? seedValue
    : Math.floor(Math.random() * 100000);
  const shakeConfig: Partial<CameraShakeConfig> = {
    type: shakeType,
    intensity: intensity,
    frequency: frequency,
    decay: decay,
    rotationEnabled: rotationEnabled,
    seed: shakeSeed,
  };

  // Store shake configuration in layer data
  const cameraData = ensureCameraLayerData(layer);

  // Type proof: intensity, frequency, decay ∈ ℝ ∪ {undefined} → ℝ
  const shakeIntensity = isFiniteNumber(shakeConfig.intensity) ? shakeConfig.intensity : 0.3;
  const shakeFrequency = isFiniteNumber(shakeConfig.frequency) && shakeConfig.frequency > 0 ? shakeConfig.frequency : 1.0;
  const shakeDecay = isFiniteNumber(shakeConfig.decay) && shakeConfig.decay >= 0 ? shakeConfig.decay : 0;
  // Type proof: rotationEnabled ∈ {true, false} ∪ {undefined} → {true, false}
  const shakeRotationEnabled = typeof shakeConfig.rotationEnabled === "boolean" ? shakeConfig.rotationEnabled : true;
  // Type proof: duration ∈ ℕ ∪ {undefined} → ℕ
  const shakeDuration = isFiniteNumber(duration) && Number.isInteger(duration) && duration >= 0 ? duration : compDuration;
  // Type proof: seed is guaranteed non-null because shakeSeed was assigned above
  assertDefined(shakeConfig.seed, "shakeConfig.seed must exist after assignment");
  cameraData.shake = {
    enabled: true,
    type: shakeType,
    intensity: shakeIntensity,
    frequency: shakeFrequency,
    rotationEnabled: shakeRotationEnabled,
    rotationScale: 0.5,
    seed: shakeConfig.seed,
    decay: shakeDecay,
    startFrame,
    duration: shakeDuration,
  };

  // Record modification and save to undo history
  //                                                                  // security
  updateProjectState(context);

  return {
    success: true,
    message: `Added ${shakeType} camera shake (intensity: ${cameraData.shake.intensity}, duration: ${cameraData.shake.duration} frames)`,
  };
}

function executeApplyRackFocus(
  context: ExecutionContext,
  args: ApplyRackFocusArgs,
): { success: boolean; keyframeCount: number; message: string } {
  const { projectStore } = context;
  const keyframeStore = useKeyframeStore();
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

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === cameraLayerId);
  if (!layer || layer.type !== "camera") {
    throw new Error(`[ActionExecutor] Camera layer "${cameraLayerId}" not found. Cannot generate trajectory on non-existent camera layer.`);
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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof kf.focusDistance === "number") {
      keyframeStore.addKeyframe(
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
  args: SetCameraPathFollowingArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
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

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === cameraLayerId);
  if (!layer || layer.type !== "camera") {
    throw new Error(`[ActionExecutor] Camera layer "${cameraLayerId}" not found. Cannot configure camera on non-existent layer.`);
  }

  // Verify spline layer exists if specified
  if (splineLayerId) {
    const splineLayer = projectStore
      .getActiveCompLayers()
      .find((l) => l.id === splineLayerId);
    if (!splineLayer || splineLayer.type !== "spline") {
      throw new Error(`[ActionExecutor] Spline layer "${splineLayerId}" not found. Cannot attach camera to non-existent spline layer.`);
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
  //                                                                  // security
  updateProjectState(context);

  return {
    success: true,
    message: splineLayerId
      ? `Camera now follows spline ${splineLayerId} (mode: ${lookMode})`
      : `Camera path following disabled`,
  };
}

function executeSetCameraAutoFocus(
  context: ExecutionContext,
  args: SetCameraAutoFocusArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
  const {
    cameraLayerId,
    enabled = true,
    mode = "center",
    focusPoint,
    smoothing = 0.8,
  } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === cameraLayerId);
  if (!layer || layer.type !== "camera") {
    throw new Error(`[ActionExecutor] Camera layer "${cameraLayerId}" not found. Cannot configure camera on non-existent layer.`);
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
  //                                                                  // security
  updateProjectState(context);

  return {
    success: true,
    message: enabled
      ? `Enabled ${mode} autofocus (smoothing: ${smoothing})`
      : `Disabled autofocus`,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                          // text // handlers
// ════════════════════════════════════════════════════════════════════════════

function executeSetTextContent(
  context: ExecutionContext,
  args: SetTextContentArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
  const { layerId, text, fontSize, fontFamily, fontWeight, color, alignment } =
    args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "text") {
    throw new Error(`[ActionExecutor] Text layer "${layerId}" not found. Cannot update text on non-existent layer.`);
  }

  if (!isLayerOfType(layer, "text")) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" is not a text layer. Only text layers can have their text content updated.`);
  }

  const textData = layer.data as TextData;

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  if (typeof text === "string") textData.text = text;
  if (typeof fontSize === "number") textData.fontSize = fontSize;
  if (typeof fontFamily === "string") textData.fontFamily = fontFamily;
  if (typeof fontWeight === "number" || typeof fontWeight === "string") textData.fontWeight = String(fontWeight);
  if (typeof color === "object" && color !== null) {
    // Type proof: a ∈ ℝ ∪ {undefined} → a ∈ ℝ
    const alphaValue = color.a;
    const alpha = isFiniteNumber(alphaValue) ? Math.max(0, Math.min(1, alphaValue)) : 1;
    textData.fill = `rgba(${color.r}, ${color.g}, ${color.b}, ${alpha})`;
  }
  if (typeof alignment === "string") {
    // Map "justify" to "left" since TextData.textAlign doesn't support justify
    textData.textAlign = alignment === "justify" ? "left" : alignment;
  }

  // Record modification and save to undo history
  //                                                                  // security
  updateProjectState(context);

  return {
    success: true,
    message: `Updated text content`,
  };
}

function executeSetTextPath(
  context: ExecutionContext,
  args: SetTextPathArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
  const { textLayerId, splineLayerId, startOffset } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === textLayerId);
  if (!layer || layer.type !== "text") {
    throw new Error(`[ActionExecutor] Text layer "${textLayerId}" not found. Cannot set text path on non-existent layer.`);
  }

  if (!isLayerOfType(layer, "text")) {
    throw new Error(`[ActionExecutor] Layer "${textLayerId}" is not a text layer. Only text layers can be attached to paths.`);
  }

  const textData = layer.data as TextData;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null/logical OR
  textData.pathLayerId = (typeof splineLayerId === "string" && splineLayerId.length > 0) ? splineLayerId : "";
  if (typeof startOffset === "number") {
    textData.pathOffset = startOffset;
  }

  // Record modification and save to undo history
  //                                                                  // security
  updateProjectState(context);

  return {
    success: true,
    message: splineLayerId
      ? `Attached text to path ${splineLayerId}`
      : `Detached text from path`,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                        // spline // handlers
// ════════════════════════════════════════════════════════════════════════════

function executeSetSplinePoints(
  context: ExecutionContext,
  args: SetSplinePointsArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
  const { layerId, points, closed } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline") {
    throw new Error(`[ActionExecutor] Spline layer "${layerId}" not found. Cannot set spline points on non-existent layer.`);
  }

  if (!isLayerOfType(layer, "spline")) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" is not a spline layer. Only spline layers can have their control points updated.`);
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

  if (typeof closed === "boolean") {
    splineData.closed = closed;
  }

  // Record modification and save to undo history
  //                                                                  // security
  updateProjectState(context);

  return {
    success: true,
    message: `Set ${points.length} control points on spline`,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                  // speed // map // handlers
// ════════════════════════════════════════════════════════════════════════════

function executeSetSpeedMap(
  context: ExecutionContext,
  args: SetSpeedMapArgs,
): { success: boolean; message: string } {
  const { projectStore } = context;
  const { layerId, enabled, keyframes } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[ActionExecutor] Layer "${layerId}" not found. Cannot set speed map on non-existent layer.`);
  }

  // Speed map stored in layer data (with backwards compatibility)
  // Speed maps apply to video/nested comp layers - if no data exists, just modify existing
  if (layer.data) {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
    const keyframesArray = (keyframes !== null && keyframes !== undefined && Array.isArray(keyframes)) ? keyframes : [];
    const speedMapData = {
      enabled: enabled !== false,
      keyframes: keyframesArray,
    };
    // Use Object.assign for dynamic property assignment on existing data
    Object.assign(layer.data, { speedMap: speedMapData, timeRemap: speedMapData });
  }

  // Record modification and save to undo history
  //                                                                  // security
  updateProjectState(context);

  return {
    success: true,
    message: enabled ? `Enabled speed map` : `Disabled speed map`,
  };
}

/** @deprecated Use executeSetSpeedMap instead */
function _executeSetTimeRemap(
  context: ExecutionContext,
  args: SetSpeedMapArgs,
): { success: boolean; message: string } {
  return executeSetSpeedMap(context, args);
}

// ════════════════════════════════════════════════════════════════════════════
//                                                      // playback // handlers
// ════════════════════════════════════════════════════════════════════════════

function executeSetCurrentFrame(
  context: ExecutionContext,
  args: SetCurrentFrameArgs,
): { frame: number; message: string } {
  const { projectStore, animationStore, playbackStore, layerStore } = context;
  const { frame } = args;

  const comp = projectStore.getActiveComp();
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  if (comp === null || typeof comp !== "object" || !("settings" in comp) || comp.settings === null || typeof comp.settings !== "object" || !("frameCount" in comp.settings) || typeof comp.settings.frameCount !== "number") {
    return { frame: 0, message: "No active composition or invalid frame count" };
  }
  const frameCount = comp.settings.frameCount;
  const clampedFrame = Math.max(0, Math.min(frame, frameCount - 1));

  const animationStoreAccess: AnimationStoreAccess = {
    get isPlaying() {
      return playbackStore.isPlaying;
    },
    getActiveComp: () => projectStore.getActiveComp(),
    get currentFrame() {
      return animationStore.currentFrame;
    },
    get frameCount() {
      const c = projectStore.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      if (c === null || typeof c !== "object" || !("settings" in c) || c.settings === null || typeof c.settings !== "object" || !("frameCount" in c.settings) || typeof c.settings.frameCount !== "number") {
        return 0;
      }
      return safeNonNegativeDefault(c.settings.frameCount, 0, "c.settings.frameCount");
    },
    get fps() {
      const c = projectStore.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      if (c === null || typeof c !== "object" || !("settings" in c) || c.settings === null || typeof c.settings !== "object" || !("fps" in c.settings) || typeof c.settings.fps !== "number") {
        return 16;
      }
      return safePositiveDefault(c.settings.fps, 16, "c.settings.fps");
    },
    getActiveCompLayers: () => projectStore.getActiveCompLayers(),
    getLayerById: (id: string) => layerStore.getLayerById(id),
    project: {
      composition: {
        width: projectStore.getWidth(),
        height: projectStore.getHeight(),
      },
      meta: { modified: projectStore.project.meta.modified },
    },
      pushHistory: () => updateProjectState(context),
  };

  animationStore.setFrame(animationStoreAccess, clampedFrame);

  return {
    frame: clampedFrame,
    message: `Jumped to frame ${clampedFrame}`,
  };
}

function executePlayPreview(
  context: ExecutionContext,
  args: PlayPreviewArgs,
): { playing: boolean; message: string } {
  const { projectStore, playbackStore, animationStore, layerStore } = context;
  const { play } = args;

  const animationStoreAccess: AnimationStoreAccess = {
    get isPlaying() {
      return playbackStore.isPlaying;
    },
    getActiveComp: () => projectStore.getActiveComp(),
    get currentFrame() {
      return animationStore.currentFrame;
    },
    get frameCount() {
      const c = projectStore.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      if (c === null || typeof c !== "object" || !("settings" in c) || c.settings === null || typeof c.settings !== "object" || !("frameCount" in c.settings) || typeof c.settings.frameCount !== "number") {
        return 0;
      }
      return safeNonNegativeDefault(c.settings.frameCount, 0, "c.settings.frameCount");
    },
    get fps() {
      const c = projectStore.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      if (c === null || typeof c !== "object" || !("settings" in c) || c.settings === null || typeof c.settings !== "object" || !("fps" in c.settings) || typeof c.settings.fps !== "number") {
        return 16;
      }
      return safePositiveDefault(c.settings.fps, 16, "c.settings.fps");
    },
    getActiveCompLayers: () => projectStore.getActiveCompLayers(),
    getLayerById: (id: string) => layerStore.getLayerById(id),
    project: {
      composition: {
        width: projectStore.getWidth(),
        height: projectStore.getHeight(),
      },
      meta: { modified: projectStore.project.meta.modified },
    },
      pushHistory: () => updateProjectState(context),
  };

  if (play) {
    const comp = projectStore.getActiveComp();
    if (comp) {
      playbackStore.play(
        comp.settings.fps,
        comp.settings.frameCount,
        animationStore.currentFrame,
        (frame) => animationStore.setFrame(animationStoreAccess, frame),
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

// ════════════════════════════════════════════════════════════════════════════
//                                     // ai // image // processing // handlers
// ════════════════════════════════════════════════════════════════════════════

async function executeDecomposeImage(
  context: ExecutionContext,
  args: DecomposeImageArgs,
): Promise<{ layerIds: string[]; message: string }> {
  const { projectStore, layerStore } = context;
  const { sourceLayerId, numLayers = 4 } = args;

  // Find the source layer
  const sourceLayer = projectStore
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
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  const sourceUrl = (typeof imageData === "object" && imageData !== null && "assetId" in imageData && typeof imageData.assetId === "string")
    ? imageData.assetId
    : "";
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
        // Deterministic: Explicit null check for getContext - "2d" should always succeed but we verify
        const ctx = canvas.getContext("2d");
        if (!ctx) {
          throw new Error("[ActionExecutor] Failed to get 2d context from HTMLCanvasElement");
        }
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
      logger.debug(`[AI Decompose] ${stage}: ${message}`);
    },
  );

  // Create layers from result (reverse order so Background is at bottom)
  const createdLayerIds: string[] = [];
  for (let i = decomposedLayers.length - 1; i >= 0; i--) {
    const decomposed = decomposedLayers[i];
    const layer = layerStore.createLayer("image", decomposed.label);
    if (layer.data && isLayerOfType(layer, "image")) {
      // Store decomposed image - ImageLayerData uses assetId, but we can store temp data
      Object.assign(layer.data, { assetId: decomposed.image });
    }
    createdLayerIds.push(layer.id);
  }

  //                                                                  // security
  updateProjectState(context);

  return {
    layerIds: createdLayerIds,
    message: `Decomposed image into ${decomposedLayers.length} layers: ${decomposedLayers.map((l) => l.label).join(", ")}`,
  };
}

async function executeVectorizeImage(
  context: ExecutionContext,
  args: VectorizeImageArgs,
): Promise<{ layerIds: string[]; message: string }> {
  const { projectStore, layerStore } = context;
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
  const sourceLayer = projectStore
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

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  if (isLayerOfType(sourceLayer, "image") && sourceLayer.data !== null && typeof sourceLayer.data === "object" && "assetId" in sourceLayer.data && typeof sourceLayer.data.assetId === "string") {
    const sourceLayerData = sourceLayer.data.assetId;
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    const project = (typeof projectStore.project === "object" && projectStore.project !== null && "assets" in projectStore.project && typeof projectStore.project.assets === "object" && projectStore.project.assets !== null)
      ? projectStore.project.assets
      : {};
    const asset = (sourceLayerData in project && typeof project[sourceLayerData] === "object" && project[sourceLayerData] !== null)
      ? project[sourceLayerData]
      : null;
    if (asset === null || typeof asset !== "object" || !("data" in asset) || typeof asset.data !== "string") throw new Error("Asset data not found");
    imageDataUrl = asset.data;
  } else if (layerData !== null && typeof layerData === "object" && "assetId" in layerData && typeof layerData.assetId === "string") {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    const assetId = (layerData !== null && typeof layerData === "object" && "assetId" in layerData && typeof layerData.assetId === "string")
      ? layerData.assetId
      : "";
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    const project = (typeof projectStore.project === "object" && projectStore.project !== null && "assets" in projectStore.project && typeof projectStore.project.assets === "object" && projectStore.project.assets !== null)
      ? projectStore.project.assets
      : {};
    const asset = (assetId in project && typeof project[assetId] === "object" && project[assetId] !== null)
      ? project[assetId]
      : null;
    if (asset === null || typeof asset !== "object" || !("data" in asset) || typeof asset.data !== "string") throw new Error("Asset data not found");
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
        // Deterministic: Explicit null check for getContext - "2d" should always succeed but we verify
        const ctx = canvas.getContext("2d");
        if (!ctx) {
          throw new Error("[ActionExecutor] Failed to get 2d context from HTMLCanvasElement");
        }
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
        colorMode: traceOptions.colorMode === "blackAndWhite" || traceOptions.colorMode === "grayscale" 
          ? "binary" 
          : (traceOptions.colorMode || "color"),
        // Type proof: filterSpeckle, cornerThreshold, colorPrecision, layerDifference ∈ ℕ ∪ {undefined} → ℕ
        filterSpeckle: (() => {
          const value = traceOptions.filterSpeckle;
          return isFiniteNumber(value) && Number.isInteger(value) && value >= 0 ? value : 4;
        })(),
        cornerThreshold: (() => {
          const value = traceOptions.cornerThreshold;
          return isFiniteNumber(value) && Number.isInteger(value) && value >= 0 ? value : 60;
        })(),
        colorPrecision: (() => {
          const value = traceOptions.colorPrecision;
          return isFiniteNumber(value) && Number.isInteger(value) && value >= 0 ? value : 6;
        })(),
        layerDifference: (() => {
          const value = traceOptions.layerDifference;
          return isFiniteNumber(value) && Number.isInteger(value) && value >= 0 ? value : 16;
        })(),
      },
    },
    (stage, message) => {
      logger.debug(`[AI Vectorize] ${stage}: ${message}`);
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
      const layer = layerStore.createSplineLayer();
      layerStore.renameLayer(layer.id, `Vector Path ${i + 1}`);

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

    const layer = layerStore.createSplineLayer();
    layerStore.renameLayer(layer.id, "Vectorized Paths");

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

  //                                                                  // security
  updateProjectState(context);

  return {
    layerIds: createdLayerIds,
    message: `Vectorized image into ${createdLayerIds.length} spline layer(s) with ${result.pathCount} paths`,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                       // utility // handlers
// ════════════════════════════════════════════════════════════════════════════

function executeGetLayerInfo(
  context: ExecutionContext,
  args: GetLayerInfoArgs,
): { success: boolean; layer: {
    id: string;
    name: string;
    type: string;
    visible: boolean;
    locked: boolean;
      inPoint: number;
      outPoint: number;
    transform: {
      position: { x: number; y: number; z?: number };
      scale: { x: number; y: number; z?: number };
      rotation: number;
      origin: { x: number; y: number; z?: number };
      anchorPoint?: { x: number; y: number; z?: number };
    };
    opacity: number;
    effects?: Array<{ id: string; effectKey: string; name: string; enabled: boolean }>;
  }; 
  message: string;
} {
  const { projectStore } = context;
  const { layerId } = args;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    // Lean4/PureScript/Haskell: Explicit error - never return null
    throw new Error(`[ActionExecutor] Layer "${layerId}" not found. Cannot get layer info for non-existent layer.`);
  }

  // Return a summary of the layer
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined/null checks
  // Pattern match: inPoint/outPoint ∈ number | undefined → number (explicit default)
  return {
    success: true,
    layer: {
      id: layer.id,
      name: layer.name,
      type: layer.type,
      visible: layer.visible,
      locked: layer.locked,
      inPoint: typeof layer.inPoint === "number" ? layer.inPoint : layer.startFrame,
      outPoint: typeof layer.outPoint === "number" ? layer.outPoint : layer.endFrame,
      transform: {
        position: layer.transform.position.value,
        scale: layer.transform.scale.value,
        rotation: layer.transform.rotation.value,
        origin: layer.transform.origin.value,
        // @deprecated alias for backwards compatibility
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        anchorPoint: layer.transform.origin.value || ((typeof layer.transform.anchorPoint === "object" && layer.transform.anchorPoint !== null && "value" in layer.transform.anchorPoint && typeof layer.transform.anchorPoint.value === "object" && layer.transform.anchorPoint.value !== null)
          ? layer.transform.anchorPoint.value
          : { x: 0, y: 0, z: 0 }),
      },
      opacity: layer.opacity.value,
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      effects: Array.isArray(layer.effects)
        ? layer.effects.map((e) => ({
          id: e.id,
          effectKey: e.effectKey,
          name: e.name,
          enabled: e.enabled,
        }))
        : [],
    },
    message: `Layer info for "${layer.name}"`,
  };
}

function executeFindLayers(
  context: ExecutionContext,
  args: FindLayersArgs,
): {
  layers: Array<{ id: string; name: string; type: string }>;
  message: string;
} {
  const { projectStore } = context;
  const { name, type } = args;

  let layers = projectStore.getActiveCompLayers();

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
  _args: GetProjectStateArgs,
): { state: Record<string, { id: string; name: string; width: number; height: number; frameCount: number; fps: number; currentFrame: number } | null | number | Array<{ id: string; name: string; type: string; visible: boolean }>>; message: string } {
  const { projectStore, animationStore } = context;
  const comp = projectStore.getActiveComp();

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
            currentFrame: animationStore.currentFrame,
          }
        : null,
      layerCount: projectStore.getActiveCompLayers().length,
      layers: projectStore.getActiveCompLayers().map((l) => ({
        id: l.id,
        name: l.name,
        type: l.type,
        visible: l.visible,
      })),
    },
    message: `Project state summary`,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                              // compass // content // generation // handlers
// ════════════════════════════════════════════════════════════════════════════

async function executeGenerateTextContent(
  context: ExecutionContext,
  args: GenerateTextContentArgs,
): Promise<{ success: boolean; message: string; content?: string }> {
  const { contentType, topic, platform, brandVoice, maxTokens } = args;

  try {
    // Call backend text generation API
    const response = await fetch("/lattice/api/content/generate", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        content_type: contentType,
        topic,
        platform,
        brand_voice: brandVoice,
        max_tokens: maxTokens || 2000,
      }),
    });

    if (!response.ok) {
      const error = await response.json().catch(() => ({ message: "Unknown error" }));
      return {
        success: false,
        message: `Text generation failed: ${error.message || "Unknown error"}`,
      };
    }

    const result = await response.json();
    return {
      success: true,
      message: `Generated ${contentType} content`,
      content: result.text,
    };
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : "Unknown error";
    return {
      success: false,
      message: `Text generation error: ${errorMessage}`,
    };
  }
}

async function executeGenerateSocialMediaPost(
  context: ExecutionContext,
  args: GenerateSocialMediaPostArgs,
): Promise<{ success: boolean; message: string; content?: string }> {
  const { platform, topic, style, includeHashtags } = args;

  try {
    const response = await fetch("/lattice/api/content/generate-social", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        platform,
        topic,
        style: style || "numbers",
        include_hashtags: includeHashtags !== false,
      }),
    });

    if (!response.ok) {
      const error = await response.json().catch(() => ({ message: "Unknown error" }));
      return {
        success: false,
        message: `Social media generation failed: ${error.message || "Unknown error"}`,
      };
    }

    const result = await response.json();
    return {
      success: true,
      message: `Generated ${platform} post`,
      content: result.text,
    };
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : "Unknown error";
    return {
      success: false,
      message: `Social media generation error: ${errorMessage}`,
    };
  }
}

async function executeGenerateAdCopy(
  context: ExecutionContext,
  args: GenerateAdCopyArgs,
): Promise<{ success: boolean; message: string; content?: string }> {
  const { platform, product, targetAudience, adType } = args;

  try {
    const response = await fetch("/lattice/api/content/generate-ad", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        platform,
        product,
        target_audience: targetAudience,
        ad_type: adType || "headline",
      }),
    });

    if (!response.ok) {
      const error = await response.json().catch(() => ({ message: "Unknown error" }));
      return {
        success: false,
        message: `Ad copy generation failed: ${error.message || "Unknown error"}`,
      };
    }

    const result = await response.json();
    return {
      success: true,
      message: `Generated ${platform} ad copy`,
      content: result.text,
    };
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : "Unknown error";
    return {
      success: false,
      message: `Ad copy generation error: ${errorMessage}`,
    };
  }
}

async function executeGenerateImage(
  context: ExecutionContext,
  args: GenerateImageArgs,
): Promise<{ success: boolean; message: string; imagePath?: string }> {
  const { contentType, prompt, width, height, style } = args;

  try {
    const response = await fetch("/lattice/api/content/generate-image", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        content_type: contentType,
        prompt,
        width: width || 1024,
        height: height || 1024,
        style,
      }),
    });

    if (!response.ok) {
      const error = await response.json().catch(() => ({ message: "Unknown error" }));
      return {
        success: false,
        message: `Image generation failed: ${error.message || "Unknown error"}`,
      };
    }

    const result = await response.json();
    return {
      success: true,
      message: `Generated ${contentType} image`,
      imagePath: result.image_path,
    };
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : "Unknown error";
    return {
      success: false,
      message: `Image generation error: ${errorMessage}`,
    };
  }
}

async function executeGenerateVideo(
  context: ExecutionContext,
  args: GenerateVideoArgs,
): Promise<{ success: boolean; message: string; videoPath?: string }> {
  const { contentType, prompt, width, height, frameCount, fps, referenceImage } = args;

  try {
    const response = await fetch("/lattice/api/content/generate-video", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        content_type: contentType,
        prompt,
        width: width || 1024,
        height: height || 1024,
        frame_count: frameCount || 81,
        fps: fps || 24,
        reference_image: referenceImage,
      }),
    });

    if (!response.ok) {
      const error = await response.json().catch(() => ({ message: "Unknown error" }));
      return {
        success: false,
        message: `Video generation failed: ${error.message || "Unknown error"}`,
      };
    }

    const result = await response.json();
    return {
      success: true,
      message: `Generated ${contentType} video`,
      videoPath: result.video_path,
    };
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : "Unknown error";
    return {
      success: false,
      message: `Video generation error: ${errorMessage}`,
    };
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                      // utility // functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Set a nested property value using dot notation path
 * Works with layer.data objects which contain JSON-serializable values
 */
function setNestedProperty(obj: { [K in string]: PropertyValue | JSONValue | undefined }, path: string[], value: JSONValue): void {
  let current: { [K in string]: PropertyValue | JSONValue | undefined } = obj;
  for (let i = 0; i < path.length - 1; i++) {
    const key = path[i];
    if (!(key in current) || current[key] === undefined) {
      current[key] = {} as JSONValue;
    }
    const next = current[key];
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (next === null || typeof next !== "object" || Array.isArray(next)) {
      current[key] = {} as JSONValue;
      const nextObj = current[key];
      if (nextObj === undefined || typeof nextObj !== "object" || nextObj === null || Array.isArray(nextObj)) {
        throw new Error(`[ActionExecutor] Cannot set nested property: intermediate path "${key}" is not an object`);
      }
      current = nextObj as { [K in string]: PropertyValue | JSONValue | undefined };
    } else {
      current = next as { [K in string]: PropertyValue | JSONValue | undefined };
    }
  }
  const finalKey = path[path.length - 1];
  current[finalKey] = value;
}
