/**
 * Project State Serializer
 *
 * Serializes the current project state into a JSON format that the LLM
 * can understand and use for context when processing instructions.
 *
 * The serialization is optimized to:
 * 1. Include all information needed for the LLM to understand the project
 * 2. Exclude unnecessary details that would waste tokens
 * 3. Format data in a way that's easy for the LLM to parse
 */

import { useCompositorStore } from '@/stores/compositorStore';
import type { Layer, Composition, AnimatableProperty, Keyframe, EffectInstance } from '@/types/project';

// ============================================================================
// TYPES
// ============================================================================

export interface SerializedProjectState {
  composition: SerializedComposition;
  layers: SerializedLayer[];
  selectedLayerIds: string[];
  currentFrame: number;
}

export interface SerializedComposition {
  id: string;
  name: string;
  width: number;
  height: number;
  frameCount: number;
  fps: number;
  duration: number;
}

export interface SerializedLayer {
  id: string;
  name: string;
  type: string;
  visible: boolean;
  locked: boolean;
  startFrame: number;
  endFrame: number;
  /** @deprecated Use 'startFrame' instead */
  inPoint?: number;
  /** @deprecated Use 'endFrame' instead */
  outPoint?: number;
  parentId: string | null;
  transform: SerializedTransform;
  opacity: SerializedAnimatableProperty;
  effects?: SerializedEffect[];
  data?: Record<string, any>;
}

export interface SerializedTransform {
  position: SerializedAnimatableProperty;
  scale: SerializedAnimatableProperty;
  rotation: SerializedAnimatableProperty;
  origin: SerializedAnimatableProperty;
  /** @deprecated Use 'origin' instead */
  anchorPoint?: SerializedAnimatableProperty;
}

export interface SerializedAnimatableProperty {
  value: any;
  animated: boolean;
  keyframeCount?: number;
  keyframes?: SerializedKeyframe[];
}

export interface SerializedKeyframe {
  frame: number;
  value: any;
  interpolation: string;
}

export interface SerializedEffect {
  id: string;
  name: string;
  type: string;
  enabled: boolean;
  parameters: Record<string, any>;
}

// ============================================================================
// MAIN SERIALIZER
// ============================================================================

/**
 * Serialize the current project state for LLM context
 * @param includeKeyframes - Include full keyframe data (increases token count)
 */
export function serializeProjectState(includeKeyframes = true): string {
  const store = useCompositorStore();
  const comp = store.getActiveComp();

  if (!comp) {
    return JSON.stringify({ error: 'No active composition' }, null, 2);
  }

  const state: SerializedProjectState = {
    composition: serializeComposition(comp),
    layers: store.getActiveCompLayers().map(layer =>
      serializeLayer(layer, includeKeyframes)
    ),
    selectedLayerIds: [...store.selectedLayerIds],
    currentFrame: comp.currentFrame,
  };

  return JSON.stringify(state, null, 2);
}

/**
 * Serialize just the layer list (lightweight)
 */
export function serializeLayerList(): string {
  const store = useCompositorStore();

  const layers = store.getActiveCompLayers().map(layer => ({
    id: layer.id,
    name: layer.name,
    type: layer.type,
    visible: layer.visible,
    startFrame: layer.startFrame ?? layer.inPoint ?? 0,
    endFrame: layer.endFrame ?? layer.outPoint ?? 80,
  }));

  return JSON.stringify({ layers }, null, 2);
}

/**
 * Serialize a specific layer with full details
 */
export function serializeLayerDetails(layerId: string): string {
  const store = useCompositorStore();
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);

  if (!layer) {
    return JSON.stringify({ error: `Layer ${layerId} not found` }, null, 2);
  }

  return JSON.stringify(serializeLayer(layer, true), null, 2);
}

// ============================================================================
// SERIALIZATION HELPERS
// ============================================================================

function serializeComposition(comp: Composition): SerializedComposition {
  return {
    id: comp.id,
    name: comp.name,
    width: comp.settings.width,
    height: comp.settings.height,
    frameCount: comp.settings.frameCount,
    fps: comp.settings.fps,
    duration: comp.settings.duration,
  };
}

function serializeLayer(layer: Layer, includeKeyframes: boolean): SerializedLayer {
  const serialized: SerializedLayer = {
    id: layer.id,
    name: layer.name,
    type: layer.type,
    visible: layer.visible,
    locked: layer.locked,
    startFrame: layer.startFrame ?? layer.inPoint ?? 0,
    endFrame: layer.endFrame ?? layer.outPoint ?? 80,
    parentId: layer.parentId,
    transform: {
      position: serializeAnimatableProperty(layer.transform.position, includeKeyframes),
      scale: serializeAnimatableProperty(layer.transform.scale, includeKeyframes),
      rotation: serializeAnimatableProperty(layer.transform.rotation, includeKeyframes),
      // Use origin (new name) with fallback to anchorPoint for backwards compatibility
      origin: serializeAnimatableProperty(layer.transform.origin || layer.transform.anchorPoint!, includeKeyframes),
    },
    opacity: serializeAnimatableProperty(layer.opacity, includeKeyframes),
  };

  // Add effects if present
  if (layer.effects && layer.effects.length > 0) {
    serialized.effects = layer.effects.map(serializeEffect);
  }

  // Add type-specific data (summarized)
  if (layer.data) {
    serialized.data = serializeLayerData(layer.type, layer.data);
  }

  return serialized;
}

function serializeAnimatableProperty(
  prop: AnimatableProperty<any>,
  includeKeyframes: boolean
): SerializedAnimatableProperty {
  const serialized: SerializedAnimatableProperty = {
    value: prop.value,
    animated: prop.animated || false,
  };

  if (prop.keyframes && prop.keyframes.length > 0) {
    serialized.keyframeCount = prop.keyframes.length;

    if (includeKeyframes) {
      serialized.keyframes = prop.keyframes.map(kf => ({
        frame: kf.frame,
        value: kf.value,
        interpolation: kf.interpolation,
      }));
    }
  }

  return serialized;
}

function serializeEffect(effect: EffectInstance): SerializedEffect {
  // Summarize effect parameters (just current values)
  const parameters: Record<string, any> = {};
  for (const [key, param] of Object.entries(effect.parameters)) {
    parameters[key] = param.value;
  }

  return {
    id: effect.id,
    name: effect.name,
    type: effect.effectKey,
    enabled: effect.enabled,
    parameters,
  };
}

function serializeLayerData(type: string, data: any): Record<string, any> {
  // Return a summarized version of layer-specific data
  switch (type) {
    case 'text':
      return {
        text: data.text,
        fontFamily: data.fontFamily,
        fontSize: data.fontSize,
        fill: data.fill,
        textAlign: data.textAlign,
        pathLayerId: data.pathLayerId,
      };

    case 'solid':
      return {
        color: data.color,
        width: data.width,
        height: data.height,
      };

    case 'spline':
      return {
        pointCount: data.controlPoints?.length || 0,
        closed: data.closed,
        stroke: data.stroke,
        strokeWidth: data.strokeWidth,
      };

    case 'particles':
      return {
        emitterCount: data.emitters?.length || 0,
        maxParticles: data.systemConfig?.maxParticles,
        gravity: data.systemConfig?.gravity,
        firstEmitter: data.emitters?.[0] ? {
          x: data.emitters[0].x,
          y: data.emitters[0].y,
          direction: data.emitters[0].direction,
          spread: data.emitters[0].spread,
          speed: data.emitters[0].speed,
          emissionRate: data.emitters[0].emissionRate,
          particleLifetime: data.emitters[0].particleLifetime,
          color: data.emitters[0].color,
        } : null,
      };

    case 'image':
      return {
        assetId: data.assetId,
        fit: data.fit,
      };

    case 'video':
      return {
        assetId: data.assetId,
        loop: data.loop,
        speed: data.speed,
      };

    case 'camera':
      return {
        cameraId: data.cameraId,
        isActiveCamera: data.isActiveCamera,
      };

    case 'shape':
      return {
        shapeCount: data.shapes?.length || 0,
        fill: data.fill,
        stroke: data.stroke,
        strokeWidth: data.strokeWidth,
      };

    case 'nestedComp':
      return {
        compositionId: data.compositionId,
        hasSpeedMap: !!(data.speedMap ?? data.timeRemap),
      };

    case 'depthflow':
      return {
        sourceLayerId: data.sourceLayerId,
        depthLayerId: data.depthLayerId,
        preset: data.config?.preset,
      };

    case 'light':
      return {
        lightType: data.lightType,
        color: data.color,
        intensity: data.intensity,
      };

    default:
      // Return raw data for unknown types (limited to prevent huge output)
      return Object.fromEntries(
        Object.entries(data).slice(0, 10)
      );
  }
}

// ============================================================================
// CHANGE TRACKING (for verification)
// ============================================================================

/**
 * Compare two states and return a summary of changes
 */
export function compareStates(
  before: SerializedProjectState,
  after: SerializedProjectState
): string[] {
  const changes: string[] = [];

  // Check composition changes
  if (before.composition.frameCount !== after.composition.frameCount) {
    changes.push(`Frame count changed: ${before.composition.frameCount} → ${after.composition.frameCount}`);
  }
  if (before.composition.width !== after.composition.width ||
      before.composition.height !== after.composition.height) {
    changes.push(`Composition size changed: ${before.composition.width}x${before.composition.height} → ${after.composition.width}x${after.composition.height}`);
  }

  // Check layer changes
  const beforeIds = new Set(before.layers.map(l => l.id));
  const afterIds = new Set(after.layers.map(l => l.id));

  // New layers
  for (const layer of after.layers) {
    if (!beforeIds.has(layer.id)) {
      changes.push(`Created layer: "${layer.name}" (${layer.type})`);
    }
  }

  // Deleted layers
  for (const layer of before.layers) {
    if (!afterIds.has(layer.id)) {
      changes.push(`Deleted layer: "${layer.name}"`);
    }
  }

  // Modified layers
  for (const afterLayer of after.layers) {
    const beforeLayer = before.layers.find(l => l.id === afterLayer.id);
    if (!beforeLayer) continue;

    // Check visibility
    if (beforeLayer.visible !== afterLayer.visible) {
      changes.push(`Layer "${afterLayer.name}": visibility ${beforeLayer.visible} → ${afterLayer.visible}`);
    }

    // Check transform
    if (JSON.stringify(beforeLayer.transform.position.value) !==
        JSON.stringify(afterLayer.transform.position.value)) {
      changes.push(`Layer "${afterLayer.name}": position changed`);
    }
    if (JSON.stringify(beforeLayer.transform.scale.value) !==
        JSON.stringify(afterLayer.transform.scale.value)) {
      changes.push(`Layer "${afterLayer.name}": scale changed`);
    }
    if (beforeLayer.transform.rotation.value !== afterLayer.transform.rotation.value) {
      changes.push(`Layer "${afterLayer.name}": rotation changed`);
    }
    if (beforeLayer.opacity.value !== afterLayer.opacity.value) {
      changes.push(`Layer "${afterLayer.name}": opacity changed`);
    }

    // Check keyframe counts
    const beforeKfCount = beforeLayer.transform.position.keyframeCount || 0;
    const afterKfCount = afterLayer.transform.position.keyframeCount || 0;
    if (beforeKfCount !== afterKfCount) {
      changes.push(`Layer "${afterLayer.name}": position keyframes ${beforeKfCount} → ${afterKfCount}`);
    }

    // Check effects
    const beforeEffects = beforeLayer.effects?.length || 0;
    const afterEffects = afterLayer.effects?.length || 0;
    if (beforeEffects !== afterEffects) {
      changes.push(`Layer "${afterLayer.name}": effects ${beforeEffects} → ${afterEffects}`);
    }
  }

  return changes;
}

/**
 * Generate a human-readable summary of the current state
 */
export function generateStateSummary(): string {
  const store = useCompositorStore();
  const comp = store.getActiveComp();
  const layers = store.getActiveCompLayers();

  if (!comp) {
    return 'No active composition';
  }

  const lines: string[] = [
    `Composition: ${comp.name} (${comp.settings.width}x${comp.settings.height})`,
    `Duration: ${comp.settings.frameCount} frames at ${comp.settings.fps} fps (${comp.settings.duration.toFixed(2)}s)`,
    `Current Frame: ${comp.currentFrame}`,
    `Layers: ${layers.length}`,
    '',
  ];

  // Group layers by type
  const byType: Record<string, Layer[]> = {};
  for (const layer of layers) {
    if (!byType[layer.type]) byType[layer.type] = [];
    byType[layer.type].push(layer);
  }

  for (const [type, typeLayers] of Object.entries(byType)) {
    lines.push(`${type.toUpperCase()} LAYERS (${typeLayers.length}):`);
    for (const layer of typeLayers) {
      const animatedProps: string[] = [];
      if (layer.transform.position.animated) animatedProps.push('pos');
      if (layer.transform.scale.animated) animatedProps.push('scale');
      if (layer.transform.rotation.animated) animatedProps.push('rot');
      if (layer.opacity.animated) animatedProps.push('opacity');

      const animated = animatedProps.length > 0
        ? ` [animated: ${animatedProps.join(', ')}]`
        : '';
      const effects = layer.effects?.length
        ? ` [${layer.effects.length} effect(s)]`
        : '';

      lines.push(`  - ${layer.name}${animated}${effects}`);
    }
    lines.push('');
  }

  return lines.join('\n');
}
