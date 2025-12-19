/**
 * AI Action Executor
 *
 * Maps LLM tool calls to actual compositor store actions.
 * This is the bridge between AI intent and store mutations.
 */

import { useCompositorStore } from '@/stores/compositorStore';
import { usePlaybackStore } from '@/stores/playbackStore';
import { useSelectionStore } from '@/stores/selectionStore';
import * as layerActions from '@/stores/actions/layerActions';
import * as keyframeActions from '@/stores/actions/keyframeActions';
import * as effectActions from '@/stores/actions/effectActions';
import { getLayerDecompositionService } from '@/services/layerDecomposition';
import type { ToolCall } from './toolDefinitions';
import type { Layer, LayerType, InterpolationType } from '@/types/project';

// ============================================================================
// TYPES
// ============================================================================

export interface ExecutionContext {
  store: ReturnType<typeof useCompositorStore>;
  playbackStore: ReturnType<typeof usePlaybackStore>;
  selectionStore: ReturnType<typeof useSelectionStore>;
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
  const playbackStore = usePlaybackStore();
  const selectionStore = useSelectionStore();

  const context: ExecutionContext = { store, playbackStore, selectionStore };
  const { name, arguments: args } = toolCall;

  // Route to appropriate handler
  switch (name) {
    // Layer Management
    case 'createLayer':
      return executeCreateLayer(context, args);
    case 'deleteLayer':
      return executeDeleteLayer(context, args);
    case 'duplicateLayer':
      return executeDuplicateLayer(context, args);
    case 'renameLayer':
      return executeRenameLayer(context, args);
    case 'setLayerParent':
      return executeSetLayerParent(context, args);
    case 'reorderLayers':
      return executeReorderLayers(context, args);

    // Property Modification
    case 'setLayerProperty':
      return executeSetLayerProperty(context, args);
    case 'setLayerTransform':
      return executeSetLayerTransform(context, args);

    // Keyframe Animation
    case 'addKeyframe':
      return executeAddKeyframe(context, args);
    case 'removeKeyframe':
      return executeRemoveKeyframe(context, args);
    case 'setKeyframeEasing':
      return executeSetKeyframeEasing(context, args);
    case 'scaleKeyframeTiming':
      return executeScaleKeyframeTiming(context, args);

    // Expressions
    case 'setExpression':
      return executeSetExpression(context, args);
    case 'removeExpression':
      return executeRemoveExpression(context, args);

    // Effects
    case 'addEffect':
      return executeAddEffect(context, args);
    case 'updateEffect':
      return executeUpdateEffect(context, args);
    case 'removeEffect':
      return executeRemoveEffect(context, args);

    // Particle System
    case 'configureParticles':
      return executeConfigureParticles(context, args);

    // Text
    case 'setTextContent':
      return executeSetTextContent(context, args);
    case 'setTextPath':
      return executeSetTextPath(context, args);

    // Spline
    case 'setSplinePoints':
      return executeSetSplinePoints(context, args);

    // Time Remapping
    case 'setTimeRemap':
      return executeSetTimeRemap(context, args);

    // Playback
    case 'setCurrentFrame':
      return executeSetCurrentFrame(context, args);
    case 'playPreview':
      return executePlayPreview(context, args);

    // AI Image Processing
    case 'decomposeImage':
      return executeDecomposeImage(context, args);

    // Utility
    case 'getLayerInfo':
      return executeGetLayerInfo(context, args);
    case 'findLayers':
      return executeFindLayers(context, args);
    case 'getProjectState':
      return executeGetProjectState(context, args);

    default:
      throw new Error(`Unknown tool: ${name}`);
  }
}

// ============================================================================
// LAYER MANAGEMENT HANDLERS
// ============================================================================

function executeCreateLayer(
  context: ExecutionContext,
  args: Record<string, any>
): { layerId: string; message: string } {
  const { store } = context;
  const { type, name, properties, position, inPoint, outPoint } = args;

  // Map tool type names to internal types
  const typeMap: Record<string, LayerType> = {
    solid: 'solid',
    text: 'text',
    shape: 'shape',
    spline: 'spline',
    particles: 'particles',
    image: 'image',
    camera: 'camera',
    control: 'null',  // Control layer maps to null type
    nested: 'nestedComp',
  };

  const internalType = typeMap[type] || type;
  const layer = layerActions.createLayer(store, internalType as LayerType, name);

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
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  const layerName = layer.name;
  layerActions.deleteLayer(store, layerId);

  return {
    success: true,
    message: `Deleted layer "${layerName}"`,
  };
}

function executeDuplicateLayer(
  context: ExecutionContext,
  args: Record<string, any>
): { layerId: string | null; message: string } {
  const { store } = context;
  const { layerId, newName } = args;

  const duplicate = layerActions.duplicateLayer(store, layerId);
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
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, name } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  const oldName = layer.name;
  layer.name = name;

  return {
    success: true,
    message: `Renamed layer from "${oldName}" to "${name}"`,
  };
}

function executeSetLayerParent(
  context: ExecutionContext,
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, parentId } = args;

  layerActions.setLayerParent(store, layerId, parentId || null);

  return {
    success: true,
    message: parentId
      ? `Set parent of layer ${layerId} to ${parentId}`
      : `Removed parent from layer ${layerId}`,
  };
}

function executeReorderLayers(
  context: ExecutionContext,
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, newIndex } = args;

  layerActions.moveLayer(store, layerId, newIndex);

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
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, propertyPath, value } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  // Handle different property paths
  const parts = propertyPath.split('.');

  if (parts[0] === 'data' && layer.data) {
    // Layer-specific data (e.g., data.text, data.color)
    setNestedProperty(layer.data, parts.slice(1), value);
  } else if (parts[0] === 'transform') {
    // Transform properties
    const prop = (layer.transform as any)[parts[1]];
    if (prop && 'value' in prop) {
      prop.value = value;
    }
  } else if (propertyPath === 'opacity') {
    layer.opacity.value = value;
  } else if (propertyPath === 'visible') {
    layer.visible = value;
  } else if (propertyPath === 'locked') {
    layer.locked = value;
  } else if (propertyPath === 'inPoint') {
    layer.inPoint = value;
  } else if (propertyPath === 'outPoint') {
    layer.outPoint = value;
  } else {
    // Try to find in layer.data
    if (layer.data) {
      setNestedProperty(layer.data, parts, value);
    }
  }

  return {
    success: true,
    message: `Set ${propertyPath} to ${JSON.stringify(value)}`,
  };
}

function executeSetLayerTransform(
  context: ExecutionContext,
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, position, scale, rotation, opacity, anchorPoint } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  const changes: string[] = [];

  if (position !== undefined) {
    layer.transform.position.value = position;
    changes.push('position');
  }
  if (scale !== undefined) {
    layer.transform.scale.value = scale;
    changes.push('scale');
  }
  if (rotation !== undefined) {
    layer.transform.rotation.value = rotation;
    changes.push('rotation');
  }
  if (opacity !== undefined) {
    layer.opacity.value = opacity;
    changes.push('opacity');
  }
  if (anchorPoint !== undefined) {
    layer.transform.anchorPoint.value = anchorPoint;
    changes.push('anchorPoint');
  }

  return {
    success: true,
    message: `Updated transform: ${changes.join(', ')}`,
  };
}

// ============================================================================
// KEYFRAME ANIMATION HANDLERS
// ============================================================================

function executeAddKeyframe(
  context: ExecutionContext,
  args: Record<string, any>
): { keyframeId: string | null; message: string } {
  const { store } = context;
  const { layerId, propertyPath, frame, value, interpolation } = args;

  const keyframe = keyframeActions.addKeyframe(store, layerId, propertyPath, value, frame);

  if (!keyframe) {
    return { keyframeId: null, message: `Failed to add keyframe at frame ${frame}` };
  }

  // Set interpolation if specified
  if (interpolation && keyframe) {
    keyframeActions.setKeyframeInterpolation(
      store,
      layerId,
      propertyPath,
      keyframe.id,
      interpolation as InterpolationType
    );
  }

  return {
    keyframeId: keyframe.id,
    message: `Added keyframe at frame ${frame} for ${propertyPath}`,
  };
}

function executeRemoveKeyframe(
  context: ExecutionContext,
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, propertyPath, frame } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  // Find keyframe at frame
  const property = keyframeActions.findPropertyByPath(layer, propertyPath);
  if (!property) {
    return { success: false, message: `Property ${propertyPath} not found` };
  }

  const keyframe = property.keyframes.find(k => k.frame === frame);
  if (!keyframe) {
    return { success: false, message: `No keyframe at frame ${frame}` };
  }

  keyframeActions.removeKeyframe(store, layerId, propertyPath, keyframe.id);

  return {
    success: true,
    message: `Removed keyframe at frame ${frame} from ${propertyPath}`,
  };
}

function executeSetKeyframeEasing(
  context: ExecutionContext,
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, propertyPath, frame, interpolation } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  const property = keyframeActions.findPropertyByPath(layer, propertyPath);
  if (!property) {
    return { success: false, message: `Property ${propertyPath} not found` };
  }

  const keyframe = property.keyframes.find(k => k.frame === frame);
  if (!keyframe) {
    return { success: false, message: `No keyframe at frame ${frame}` };
  }

  keyframeActions.setKeyframeInterpolation(
    store,
    layerId,
    propertyPath,
    keyframe.id,
    interpolation as InterpolationType
  );

  return {
    success: true,
    message: `Set interpolation to ${interpolation} at frame ${frame}`,
  };
}

function executeScaleKeyframeTiming(
  context: ExecutionContext,
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, scaleFactor, propertyPath } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  // Get all properties to scale
  const propertiesToScale: string[] = propertyPath
    ? [propertyPath]
    : ['position', 'scale', 'rotation', 'opacity', 'anchorPoint'];

  let scaledCount = 0;

  for (const propPath of propertiesToScale) {
    const property = keyframeActions.findPropertyByPath(layer, propPath);
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
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, propertyPath, expressionType, params } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  const property = keyframeActions.findPropertyByPath(layer, propertyPath);
  if (!property) {
    return { success: false, message: `Property ${propertyPath} not found` };
  }

  // Set expression on property
  property.expression = {
    enabled: true,
    type: 'preset' as const,
    name: expressionType,
    params: params || {},
  };

  return {
    success: true,
    message: `Applied ${expressionType} expression to ${propertyPath}`,
  };
}

function executeRemoveExpression(
  context: ExecutionContext,
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, propertyPath } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  const property = keyframeActions.findPropertyByPath(layer, propertyPath);
  if (!property) {
    return { success: false, message: `Property ${propertyPath} not found` };
  }

  property.expression = undefined;

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
  args: Record<string, any>
): { effectId: string | null; message: string } {
  const { store } = context;
  const { layerId, effectType, params } = args;

  effectActions.addEffectToLayer(store, layerId, effectType);

  // Get the newly added effect (last in array)
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  const effect = layer?.effects?.[layer.effects.length - 1];

  if (!effect) {
    return { effectId: null, message: `Failed to add effect ${effectType}` };
  }

  // Apply initial parameters
  if (params) {
    for (const [key, value] of Object.entries(params)) {
      effectActions.updateEffectParameter(store, layerId, effect.id, key, value);
    }
  }

  return {
    effectId: effect.id,
    message: `Added ${effectType} effect to layer`,
  };
}

function executeUpdateEffect(
  context: ExecutionContext,
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, effectId, params } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer?.effects) {
    return { success: false, message: `Layer ${layerId} not found or has no effects` };
  }

  const effect = layer.effects.find(e => e.id === effectId);
  if (!effect) {
    return { success: false, message: `Effect ${effectId} not found` };
  }

  for (const [key, value] of Object.entries(params)) {
    effectActions.updateEffectParameter(store, layerId, effectId, key, value);
  }

  return {
    success: true,
    message: `Updated ${Object.keys(params).length} effect parameters`,
  };
}

function executeRemoveEffect(
  context: ExecutionContext,
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, effectId } = args;

  effectActions.removeEffectFromLayer(store, layerId, effectId);

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
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, emitter, particles, physics } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'particles') {
    return { success: false, message: `Particle layer ${layerId} not found` };
  }

  if (!layer.data) {
    return { success: false, message: `Particle layer has no data` };
  }

  const particleData = layer.data as any;

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
      particleData.systemConfig.windStrength = Math.sqrt(
        physics.wind.x ** 2 + physics.wind.y ** 2
      );
      particleData.systemConfig.windDirection = Math.atan2(
        physics.wind.y,
        physics.wind.x
      ) * (180 / Math.PI);
    }
    if (physics.turbulence) {
      // Map to system config if applicable
    }
  }

  return {
    success: true,
    message: `Configured particle system`,
  };
}

// ============================================================================
// TEXT HANDLERS
// ============================================================================

function executeSetTextContent(
  context: ExecutionContext,
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, text, fontSize, fontFamily, fontWeight, color, alignment } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'text') {
    return { success: false, message: `Text layer ${layerId} not found` };
  }

  if (!layer.data) {
    return { success: false, message: `Text layer has no data` };
  }

  const textData = layer.data as any;

  if (text !== undefined) textData.text = text;
  if (fontSize !== undefined) textData.fontSize = fontSize;
  if (fontFamily !== undefined) textData.fontFamily = fontFamily;
  if (fontWeight !== undefined) textData.fontWeight = String(fontWeight);
  if (color !== undefined) {
    textData.fill = `rgba(${color.r}, ${color.g}, ${color.b}, ${color.a ?? 1})`;
  }
  if (alignment !== undefined) textData.textAlign = alignment;

  return {
    success: true,
    message: `Updated text content`,
  };
}

function executeSetTextPath(
  context: ExecutionContext,
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { textLayerId, splineLayerId, startOffset } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === textLayerId);
  if (!layer || layer.type !== 'text') {
    return { success: false, message: `Text layer ${textLayerId} not found` };
  }

  if (!layer.data) {
    return { success: false, message: `Text layer has no data` };
  }

  const textData = layer.data as any;
  textData.pathLayerId = splineLayerId || null;
  if (startOffset !== undefined) {
    textData.pathOffset = startOffset;
  }

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
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, points, closed } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline') {
    return { success: false, message: `Spline layer ${layerId} not found` };
  }

  if (!layer.data) {
    return { success: false, message: `Spline layer has no data` };
  }

  const splineData = layer.data as any;

  // Convert points to control points format
  splineData.controlPoints = points.map((p: any, index: number) => ({
    id: `cp_${Date.now()}_${index}`,
    x: p.x,
    y: p.y,
    handleIn: p.handleIn || null,
    handleOut: p.handleOut || null,
    type: p.handleIn || p.handleOut ? 'smooth' : 'corner',
  }));

  if (closed !== undefined) {
    splineData.closed = closed;
  }

  return {
    success: true,
    message: `Set ${points.length} control points on spline`,
  };
}

// ============================================================================
// TIME REMAPPING HANDLERS
// ============================================================================

function executeSetTimeRemap(
  context: ExecutionContext,
  args: Record<string, any>
): { success: boolean; message: string } {
  const { store } = context;
  const { layerId, enabled, keyframes } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    return { success: false, message: `Layer ${layerId} not found` };
  }

  // Time remapping stored in layer data
  if (!layer.data) {
    (layer as any).data = {};
  }

  (layer.data as any).timeRemap = {
    enabled: enabled !== false,
    keyframes: keyframes || [],
  };

  return {
    success: true,
    message: enabled ? `Enabled time remapping` : `Disabled time remapping`,
  };
}

// ============================================================================
// PLAYBACK HANDLERS
// ============================================================================

function executeSetCurrentFrame(
  context: ExecutionContext,
  args: Record<string, any>
): { frame: number; message: string } {
  const { store, playbackStore } = context;
  const { frame } = args;

  const comp = store.getActiveComp();
  const frameCount = comp?.settings.frameCount || 81;
  const clampedFrame = Math.max(0, Math.min(frame, frameCount - 1));

  store.setFrame(clampedFrame);

  return {
    frame: clampedFrame,
    message: `Jumped to frame ${clampedFrame}`,
  };
}

function executePlayPreview(
  context: ExecutionContext,
  args: Record<string, any>
): { playing: boolean; message: string } {
  const { store, playbackStore } = context;
  const { play } = args;

  if (play) {
    const comp = store.getActiveComp();
    if (comp) {
      playbackStore.play(
        comp.settings.fps,
        comp.settings.frameCount,
        comp.currentFrame,
        (frame) => store.setFrame(frame)
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
  args: Record<string, any>
): Promise<{ layerIds: string[]; message: string }> {
  const { store } = context;
  const { sourceLayerId, numLayers = 4 } = args;

  // Find the source layer
  const sourceLayer = store.getActiveCompLayers().find(l => l.id === sourceLayerId);
  if (!sourceLayer) {
    throw new Error(`Source layer ${sourceLayerId} not found`);
  }

  if (sourceLayer.type !== 'image') {
    throw new Error(`Layer ${sourceLayerId} is not an image layer`);
  }

  // Get the source image URL
  const layerData = sourceLayer.data as any;
  const sourceUrl = layerData?.source || layerData?.url || layerData?.assetId;
  if (!sourceUrl) {
    throw new Error(`Source layer has no image source`);
  }

  // Convert to data URL if needed
  let imageDataUrl: string;
  if (sourceUrl.startsWith('data:')) {
    imageDataUrl = sourceUrl;
  } else {
    // Load image and convert to data URL
    imageDataUrl = await new Promise((resolve, reject) => {
      const img = new Image();
      img.crossOrigin = 'anonymous';
      img.onload = () => {
        const canvas = document.createElement('canvas');
        canvas.width = img.naturalWidth;
        canvas.height = img.naturalHeight;
        const ctx = canvas.getContext('2d')!;
        ctx.drawImage(img, 0, 0);
        resolve(canvas.toDataURL('image/png'));
      };
      img.onerror = () => reject(new Error('Failed to load source image'));
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
    }
  );

  // Create layers from result (reverse order so Background is at bottom)
  const createdLayerIds: string[] = [];
  for (let i = decomposedLayers.length - 1; i >= 0; i--) {
    const decomposed = decomposedLayers[i];
    const layer = layerActions.createLayer(store, 'image', decomposed.label);
    if (layer.data) {
      (layer.data as any).source = decomposed.image;
    }
    createdLayerIds.push(layer.id);
  }

  store.pushHistory();

  return {
    layerIds: createdLayerIds,
    message: `Decomposed image into ${decomposedLayers.length} layers: ${decomposedLayers.map(l => l.label).join(', ')}`,
  };
}

// ============================================================================
// UTILITY HANDLERS
// ============================================================================

function executeGetLayerInfo(
  context: ExecutionContext,
  args: Record<string, any>
): { layer: Record<string, any> | null; message: string } {
  const { store } = context;
  const { layerId } = args;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
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
        anchorPoint: layer.transform.anchorPoint,
      },
      opacity: layer.opacity,
      effects: layer.effects?.map(e => ({
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
  args: Record<string, any>
): { layers: Array<{ id: string; name: string; type: string }>; message: string } {
  const { store } = context;
  const { name, type } = args;

  let layers = store.getActiveCompLayers();

  if (name) {
    const lowerName = name.toLowerCase();
    layers = layers.filter(l => l.name.toLowerCase().includes(lowerName));
  }

  if (type) {
    layers = layers.filter(l => l.type === type);
  }

  return {
    layers: layers.map(l => ({
      id: l.id,
      name: l.name,
      type: l.type,
    })),
    message: `Found ${layers.length} layer(s)`,
  };
}

function executeGetProjectState(
  context: ExecutionContext,
  _args: Record<string, any>
): { state: any; message: string } {
  const { store } = context;
  const comp = store.getActiveComp();

  return {
    state: {
      composition: comp ? {
        id: comp.id,
        name: comp.name,
        width: comp.settings.width,
        height: comp.settings.height,
        frameCount: comp.settings.frameCount,
        fps: comp.settings.fps,
        currentFrame: comp.currentFrame,
      } : null,
      layerCount: store.getActiveCompLayers().length,
      layers: store.getActiveCompLayers().map(l => ({
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
