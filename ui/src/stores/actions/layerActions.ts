/**
 * Layer Actions
 *
 * Layer management including creation, deletion, duplication, clipboard operations,
 * and layer-specific updates (spline, 3D, parenting).
 */

import { toRaw } from 'vue';
import { storeLogger } from '@/utils/logger';
import type {
  Layer,
  AnimatableProperty,
  SplineData,
  ControlPoint,
  AnimatableControlPoint,
  EvaluatedControlPoint,
  ClipboardKeyframe,
  AnyLayerData,
  PropertyValue,
  LayerType,
  ImageLayerData,
  VideoData,
  NestedCompData,
  Keyframe
} from '@/types/project';
import { createDefaultTransform, createAnimatableProperty, controlPointToAnimatable, animatableToControlPoint, isLayerOfType } from '@/types/project';

/**
 * Layer source replacement data for asset/composition swapping
 */
export interface LayerSourceReplacement {
  type: 'asset' | 'composition' | string;
  name: string;
  path?: string;
  id?: string;
  assetId?: string;
  data?: string;  // Base64 data URL for asset data
}
import { useSelectionStore } from '../selectionStore';
import { markLayerDirty, clearLayerCache } from '@/services/layerEvaluationCache';
import { interpolateProperty } from '@/services/interpolation';
import { textToVectorFromUrl, type TextToVectorResult, type CharacterVectorGroup } from '@/services/textToVector';
import type { BezierPath, BezierVertex } from '@/types/shapes';
import { getDefaultLayerData } from './layer/layerDefaults';

// Re-export from sub-modules for backwards compatibility
export * from './layers/layerTimeActions';

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface LayerStore {
  project: {
    composition: { width: number; height: number };
    meta: { modified: string };
  };
  clipboard: {
    layers: Layer[];
    keyframes: ClipboardKeyframe[];
  };
  getActiveComp(): { settings: { width: number; height: number; frameCount: number }; layers: Layer[] } | null;
  getActiveCompLayers(): Layer[];
  pushHistory(): void;
}

// ============================================================================
// LAYER CREATION
// ============================================================================

/**
 * Create a new layer of the specified type
 */
export function createLayer(
  store: LayerStore,
  type: Layer['type'],
  name?: string
): Layer {
  const id = `layer_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

  // Get type-specific data from layer defaults module
  const layerData = getDefaultLayerData(type, {
    width: store.project.composition.width,
    height: store.project.composition.height
  });

  // Initialize audio props for video/audio layers
  let audioProps = undefined;
  if (type === 'video' || type === 'audio') {
    audioProps = {
      level: createAnimatableProperty('Audio Levels', 0, 'number') // 0dB default
    };
  }

  // Initialize layer-specific properties
  let layerProperties: AnimatableProperty<PropertyValue>[] = [];

  // Spline layer properties for timeline
  // Note: Splines don't have Fill (only shapes/text do) - they only have stroke
  if (type === 'spline') {
    const splineData = layerData as unknown as { strokeWidth?: number; strokeOpacity?: number };
    layerProperties = [
      createAnimatableProperty('Stroke Width', splineData?.strokeWidth ?? 2, 'number', 'Stroke'),
      createAnimatableProperty('Stroke Opacity', splineData?.strokeOpacity ?? 100, 'number', 'Stroke'),
      // Line Cap, Line Join, Dashes are stored in layer.data and shown in More Options
      createAnimatableProperty('Trim Start', 0, 'number', 'Trim Paths'),
      createAnimatableProperty('Trim End', 100, 'number', 'Trim Paths'),
      createAnimatableProperty('Trim Offset', 0, 'number', 'Trim Paths'),
      // Note: "Closed" is stored in layer.data.closed as a boolean, not animatable
      // It's displayed in the timeline via the Path Options group in EnhancedLayerTrack
    ];
  }

  const comp = store.getActiveComp();
  const layers = store.getActiveCompLayers();

  // Create transform with position centered in composition
  const compWidth = comp?.settings.width || store.project.composition.width || 1920;
  const compHeight = comp?.settings.height || store.project.composition.height || 1080;
  const centeredTransform = createDefaultTransform();
  // Center the layer in the composition
  centeredTransform.position.value = { x: compWidth / 2, y: compHeight / 2 };

  const layer: Layer = {
    id,
    name: name || `${type.charAt(0).toUpperCase() + type.slice(1)} ${layers.length + 1}`,
    type,
    visible: true,
    locked: false,
    isolate: false,
    threeD: false,
    motionBlur: false,
    // Timing (primary properties)
    startFrame: 0,
    endFrame: (comp?.settings.frameCount || 81) - 1,
    // Backwards compatibility aliases
    inPoint: 0,
    outPoint: (comp?.settings.frameCount || 81) - 1,
    parentId: null,
    blendMode: 'normal',
    opacity: createAnimatableProperty('opacity', 100, 'number'),
    transform: centeredTransform,
    audio: audioProps,
    properties: layerProperties,
    effects: [],
    data: layerData as Layer['data']
  };

  // Camera layers should use createCameraLayer() instead
  if (type === 'camera') {
    storeLogger.warn('Use createCameraLayer() for camera layers');
  }

  console.log('[layerActions] Creating layer:', {
    id: layer.id,
    type: layer.type,
    name: layer.name,
    position: layer.transform?.position?.value,
    data: layer.data,
    layersCountBefore: layers.length
  });

  layers.unshift(layer);

  console.log('[layerActions] Layer added:', {
    layersCountAfter: layers.length,
    allLayerIds: layers.map(l => l.id)
  });

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return layer;
}

/**
 * Create a text layer with proper data structure and AE-compatible properties
 */
export function createTextLayer(store: LayerStore, text: string = 'Text'): Layer {
  const layer = createLayer(store, 'text', text.substring(0, 20));

  // Set up text data with full AE parity
  const textData = {
    text,
    fontFamily: 'Arial',
    fontSize: 72,
    fontWeight: '400' as const,
    fontStyle: 'normal' as const,
    fill: '#ffffff',
    stroke: '',
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
    textAlign: 'left' as const,
    // Path Options (Full AE Parity)
    pathLayerId: null,
    pathReversed: false,
    pathPerpendicularToPath: true,
    pathForceAlignment: false,
    pathFirstMargin: 0,
    pathLastMargin: 0,
    pathOffset: 0,
    pathAlign: 'left' as const,
    // More Options (AE Advanced)
    anchorPointGrouping: 'character' as const,
    groupingAlignment: { x: 0, y: 0 },
    fillAndStroke: 'fill-over-stroke' as const,
    interCharacterBlending: 'normal' as const,
    // 3D Text
    perCharacter3D: false
  };

  layer.data = textData;

  // Text Properties for timeline
  layer.properties.push(createAnimatableProperty('Font Size', 72, 'number', 'Text'));
  layer.properties.push(createAnimatableProperty('Fill Color', '#ffffff', 'color', 'Text'));
  layer.properties.push(createAnimatableProperty('Stroke Color', '#000000', 'color', 'Text'));
  layer.properties.push(createAnimatableProperty('Stroke Width', 0, 'number', 'Text'));
  // Path Options
  layer.properties.push(createAnimatableProperty('Path Offset', 0, 'number', 'Path Options'));
  layer.properties.push(createAnimatableProperty('First Margin', 0, 'number', 'Path Options'));
  layer.properties.push(createAnimatableProperty('Last Margin', 0, 'number', 'Path Options'));
  // More Options
  layer.properties.push(createAnimatableProperty('Grouping Alignment', { x: 0, y: 0 }, 'position', 'More Options'));
  // Advanced / Animators
  layer.properties.push(createAnimatableProperty('Tracking', 0, 'number', 'Advanced'));
  layer.properties.push(createAnimatableProperty('Line Spacing', 0, 'number', 'Advanced'));
  layer.properties.push(createAnimatableProperty('Character Offset', 0, 'number', 'Advanced'));
  layer.properties.push(createAnimatableProperty('Character Value', 0, 'number', 'Advanced'));
  layer.properties.push(createAnimatableProperty('Blur', { x: 0, y: 0 }, 'position', 'Advanced'));

  return layer;
}

/**
 * Create a spline layer with proper data structure
 */
export function createSplineLayer(store: LayerStore): Layer {
  const layer = createLayer(store, 'spline');

  const splineData: SplineData = {
    pathData: '',
    controlPoints: [],
    closed: false,
    stroke: '#00ff00',
    strokeWidth: 2,
    fill: ''
  };

  layer.data = splineData;

  return layer;
}

/**
 * Create a shape layer with proper data structure
 */
export function createShapeLayer(store: LayerStore, name: string = 'Shape Layer'): Layer {
  return createLayer(store, 'shape', name);
}

// ============================================================================
// LAYER DELETION
// ============================================================================

/**
 * Options for deleteLayer to allow dependency injection for testing
 */
export interface DeleteLayerOptions {
  /** Callback to remove layer from selection. If not provided, uses useSelectionStore() */
  onRemoveFromSelection?: (layerId: string) => void;
  /** Skip history push (useful for batch operations) */
  skipHistory?: boolean;
}

/**
 * Delete a layer by ID
 *
 * @param store - The layer store
 * @param layerId - ID of the layer to delete
 * @param options - Optional callbacks for dependency injection (enables testing without Pinia)
 */
export function deleteLayer(
  store: LayerStore,
  layerId: string,
  options?: DeleteLayerOptions
): void {
  const layers = store.getActiveCompLayers();
  const index = layers.findIndex(l => l.id === layerId);
  if (index === -1) return;

  layers.splice(index, 1);

  // BUG-037 FIX: Clean up all stale references to deleted layer
  for (const layer of layers) {
    // Clear parent reference
    if (layer.parentId === layerId) {
      layer.parentId = null;
    }

    // Clear matte reference
    if (layer.matteLayerId === layerId) {
      layer.matteLayerId = undefined;
      layer.matteType = undefined;
    }

    // Clear followPath reference but preserve constraint settings (keyframes, offset, etc.)
    if (layer.followPath?.pathLayerId === layerId) {
      layer.followPath.enabled = false;
      layer.followPath.pathLayerId = '';
    }

    // Clear text layer path reference
    if (layer.type === 'text' && layer.data && (layer.data as any).pathLayerId === layerId) {
      (layer.data as any).pathLayerId = null;
    }
  }

  // Use injected callback if provided, otherwise fall back to Pinia store
  if (options?.onRemoveFromSelection) {
    options.onRemoveFromSelection(layerId);
  } else {
    // Default behavior - requires Pinia context
    useSelectionStore().removeFromSelection(layerId);
  }

  clearLayerCache(layerId); // Clear evaluation cache for deleted layer
  store.project.meta.modified = new Date().toISOString();

  if (!options?.skipHistory) {
    store.pushHistory();
  }
}

// ============================================================================
// LAYER DUPLICATION
// ============================================================================

/**
 * Duplicate a layer
 */
export function duplicateLayer(store: LayerStore, layerId: string): Layer | null {
  const layers = store.getActiveCompLayers();
  const original = layers.find(l => l.id === layerId);
  if (!original) return null;

  // Deep clone the layer - use toRaw to handle Vue reactive proxies
  const duplicate: Layer = structuredClone(toRaw(original));

  // Generate new IDs
  duplicate.id = crypto.randomUUID();
  duplicate.name = original.name + ' Copy';

  // Generate new keyframe IDs to avoid conflicts
  regenerateKeyframeIds(duplicate);

  // Insert after the original
  const index = layers.findIndex(l => l.id === layerId);
  layers.splice(index, 0, duplicate);

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return duplicate;
}

// ============================================================================
// CLIPBOARD OPERATIONS
// ============================================================================

/**
 * Copy selected layers to clipboard
 */
export function copySelectedLayers(store: LayerStore): void {
  const layers = store.getActiveCompLayers();
  const selection = useSelectionStore();
  const selectedLayers = layers.filter(l => selection.selectedLayerIds.includes(l.id));
  if (selectedLayers.length === 0) return;

  // Deep clone layers to clipboard - use toRaw to handle Vue reactive proxies
  store.clipboard.layers = selectedLayers.map(layer => structuredClone(toRaw(layer)));
  storeLogger.debug(`Copied ${store.clipboard.layers.length} layer(s) to clipboard`);
}

/**
 * Paste layers from clipboard
 */
export function pasteLayers(store: LayerStore): Layer[] {
  if (store.clipboard.layers.length === 0) return [];

  const layers = store.getActiveCompLayers();
  const pastedLayers: Layer[] = [];

  for (const clipboardLayer of store.clipboard.layers) {
    // Deep clone from clipboard
    const newLayer: Layer = structuredClone(clipboardLayer);

    // Generate new IDs
    newLayer.id = crypto.randomUUID();
    newLayer.name = clipboardLayer.name + ' Copy';

    // Generate new keyframe IDs
    regenerateKeyframeIds(newLayer);

    // Clear parent reference (may not exist in this comp)
    newLayer.parentId = null;

    layers.unshift(newLayer);
    pastedLayers.push(newLayer);
  }

  // Select pasted layers
  useSelectionStore().selectLayers(pastedLayers.map(l => l.id));

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  storeLogger.debug(`Pasted ${pastedLayers.length} layer(s)`);
  return pastedLayers;
}

/**
 * Cut selected layers (copy + delete)
 */
export function cutSelectedLayers(store: LayerStore): void {
  copySelectedLayers(store);
  const layerIds = [...useSelectionStore().selectedLayerIds];
  for (const id of layerIds) {
    deleteLayer(store, id);
  }
}

// ============================================================================
// LAYER UPDATES
// ============================================================================

/**
 * Update layer properties
 * Note: Locked layers can only have their 'locked' property changed.
 * All other updates are blocked.
 */
export function updateLayer(store: LayerStore, layerId: string, updates: Partial<Layer>): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  // If layer is locked, only allow changing the 'locked' property itself
  if (layer.locked) {
    const updateKeys = Object.keys(updates);
    const onlyChangingLocked = updateKeys.length === 1 && updateKeys[0] === 'locked';
    if (!onlyChangingLocked) {
      storeLogger.warn('Cannot update locked layer:', layerId);
      return;
    }
  }

  Object.assign(layer, updates);
  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Update layer-specific data (e.g., text content, image path, etc.)
 * Note: Cannot update data on locked layers.
 *
 * The dataUpdates parameter accepts both common AnyLayerData properties AND
 * layer-type-specific properties (via Record<string, unknown>). This is necessary
 * because Partial<UnionType> in TypeScript only allows properties common to ALL
 * types in the union, but each layer type has unique properties.
 */
export function updateLayerData(
  store: LayerStore,
  layerId: string,
  dataUpdates: Partial<AnyLayerData> & Record<string, unknown>
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || !layer.data) return;

  // Locked layers cannot have their data updated
  if (layer.locked) {
    storeLogger.warn('Cannot update data on locked layer:', layerId);
    return;
  }

  // Use spread operator with toRaw to ensure plain objects for structuredClone
  layer.data = { ...toRaw(layer.data), ...dataUpdates } as Layer['data'];
  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Replace layer source with a new asset (Alt+drag replacement)
 * Keeps all keyframes, effects, and transforms
 */
export function replaceLayerSource(
  store: LayerStore,
  layerId: string,
  newSource: LayerSourceReplacement
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  // Use assetId if provided, otherwise use id as assetId
  const assetId = newSource.assetId || newSource.id || null;

  // Determine source update based on layer type and new source type
  if (isLayerOfType(layer, 'image') && newSource.type === 'asset' && assetId) {
    // Replace image source - preserve existing data, update assetId
    layer.data.assetId = assetId;
    layer.name = newSource.name || layer.name;
  } else if (isLayerOfType(layer, 'video') && newSource.type === 'asset' && assetId) {
    // Replace video source - preserve existing data, update assetId
    layer.data.assetId = assetId;
    layer.name = newSource.name || layer.name;
  } else if (layer.type === 'solid' && newSource.type === 'asset' && assetId) {
    // Convert solid to image layer (source replacement changes type)
    // Type assertion needed: we're intentionally mutating the layer type
    (layer as Layer).type = 'image';
    const imageData: ImageLayerData = { assetId, fit: 'none' };
    layer.data = imageData;
    layer.name = newSource.name || layer.name;
  } else if (isLayerOfType(layer, 'nestedComp') && newSource.type === 'composition' && newSource.id) {
    // Replace nested comp source - preserve existing data, update compositionId
    layer.data.compositionId = newSource.id;
    layer.name = newSource.name || layer.name;
  } else if (newSource.type === 'composition' && newSource.id) {
    // Convert any layer to nested comp
    // Type assertion needed: we're intentionally mutating the layer type
    (layer as Layer).type = 'nestedComp';
    const nestedCompData: NestedCompData = {
      compositionId: newSource.id,
      speedMapEnabled: false,
      flattenTransform: false,
      overrideFrameRate: false
    };
    layer.data = nestedCompData;
    layer.name = newSource.name || layer.name;
  } else if (newSource.type === 'asset' && assetId) {
    // Generic asset replacement - determine new type from asset or file extension
    const path = newSource.path || '';
    const ext = path.split('.').pop()?.toLowerCase() || '';
    const imageExts = ['png', 'jpg', 'jpeg', 'gif', 'webp', 'svg'];
    const videoExts = ['mp4', 'webm', 'mov', 'avi'];

    if (imageExts.includes(ext)) {
      // Type assertion needed: we're intentionally mutating the layer type
      (layer as Layer).type = 'image';
      const imageData: ImageLayerData = { assetId, fit: 'none' };
      layer.data = imageData;
    } else if (videoExts.includes(ext)) {
      // Type assertion needed: we're intentionally mutating the layer type
      (layer as Layer).type = 'video';
      const videoData: VideoData = {
        assetId,
        loop: true,
        pingPong: false,
        startTime: 0,
        speed: 1,
        speedMapEnabled: false,
        frameBlending: 'none',
        audioEnabled: true,
        audioLevel: 100,
        posterFrame: 0
      };
      layer.data = videoData;
    }
    layer.name = newSource.name || layer.name;
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
  storeLogger.info(`Replaced layer source: ${layer.name}`);
}

/**
 * Reorder layers
 */
export function moveLayer(store: LayerStore, layerId: string, newIndex: number): void {
  // Validate newIndex (NaN coerces to 0 in splice, causing wrong position)
  if (!Number.isInteger(newIndex) || newIndex < 0) {
    storeLogger.warn('moveLayer: Invalid index:', newIndex);
    return;
  }

  const layers = store.getActiveCompLayers();
  const currentIndex = layers.findIndex(l => l.id === layerId);
  if (currentIndex === -1) return;

  // Clamp index to valid range
  const clampedIndex = Math.min(newIndex, layers.length - 1);

  const [layer] = layers.splice(currentIndex, 1);
  layers.splice(clampedIndex, 0, layer);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

// ============================================================================
// 3D LAYER OPERATIONS
// ============================================================================

/**
 * Toggle 3D mode for a layer
 */
export function toggleLayer3D(store: LayerStore, layerId: string): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  layer.threeD = !layer.threeD;

  if (layer.threeD) {
    const t = layer.transform;

    // Force reactivity by replacing the entire value objects
    // Position - always create new object with z
    const pos = t.position.value as { x: number; y: number; z?: number };
    const posZ = 'z' in pos && typeof pos.z === 'number' ? pos.z : 0;
    t.position.value = { x: pos.x, y: pos.y, z: posZ };
    t.position.type = 'vector3';

    // Origin (formerly Anchor Point)
    const originProp = t.origin || t.anchorPoint;
    if (originProp) {
      const orig = originProp.value as { x: number; y: number; z?: number };
      const origZ = 'z' in orig && typeof orig.z === 'number' ? orig.z : 0;
      originProp.value = { x: orig.x, y: orig.y, z: origZ };
      originProp.type = 'vector3';
    }

    // Scale
    const scl = t.scale.value as { x: number; y: number; z?: number };
    const sclZ = 'z' in scl && typeof scl.z === 'number' ? scl.z : 100;
    t.scale.value = { x: scl.x, y: scl.y, z: sclZ };
    t.scale.type = 'vector3';

    // Initialize 3D rotations
    if (!t.orientation) {
      t.orientation = createAnimatableProperty('orientation', { x: 0, y: 0, z: 0 }, 'vector3');
    }
    if (!t.rotationX) {
      t.rotationX = createAnimatableProperty('rotationX', 0, 'number');
    }
    if (!t.rotationY) {
      t.rotationY = createAnimatableProperty('rotationY', 0, 'number');
    }
    if (!t.rotationZ) {
      t.rotationZ = createAnimatableProperty('rotationZ', 0, 'number');
      // Copy existing 2D rotation to Z rotation
      t.rotationZ.value = t.rotation.value;
    }
  } else {
    // Reverting to 2D
    // Map Z rotation back to standard rotation
    if (layer.transform.rotationZ) {
      layer.transform.rotation.value = layer.transform.rotationZ.value;
    }
  }

  store.project.meta.modified = new Date().toISOString();
}

// ============================================================================
// PARENTING
// ============================================================================

/**
 * Set a layer's parent for parenting/hierarchy
 */
export function setLayerParent(store: LayerStore, layerId: string, parentId: string | null): void {
  const layers = store.getActiveCompLayers();
  const layer = layers.find(l => l.id === layerId);
  if (!layer) return;

  // Prevent self-parenting
  if (parentId === layerId) return;

  // Prevent circular parenting (parent can't be a descendant)
  if (parentId) {
    const getDescendants = (id: string): Set<string> => {
      const descendants = new Set<string>();
      const children = layers.filter(l => l.parentId === id);
      for (const child of children) {
        descendants.add(child.id);
        const childDescendants = getDescendants(child.id);
        childDescendants.forEach(d => descendants.add(d));
      }
      return descendants;
    };

    const descendants = getDescendants(layerId);
    if (descendants.has(parentId)) {
      storeLogger.warn('Cannot set parent: would create circular reference');
      return;
    }
  }

  layer.parentId = parentId;
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

// ============================================================================
// SPLINE LAYER OPERATIONS (Re-exported from layer/splineActions.ts)
// ============================================================================

// Re-export all spline operations for backwards compatibility
export {
  type SplineControlPoint,
  addSplineControlPoint,
  insertSplineControlPoint,
  updateSplineControlPoint,
  deleteSplineControlPoint,
  enableSplineAnimation,
  addSplinePointKeyframe,
  addSplinePointPositionKeyframe,
  updateSplinePointWithKeyframe,
  getEvaluatedSplinePoints,
  isSplineAnimated,
  hasSplinePointKeyframes,
  simplifySpline,
  smoothSplineHandles,
} from './layer/splineActions';

// ============================================================================
// SELECTION (delegated to selectionStore)
// ============================================================================

/**
 * Select a layer
 */
export function selectLayer(_store: LayerStore, layerId: string, addToSelection = false): void {
  const selection = useSelectionStore();
  if (addToSelection) {
    selection.addToSelection(layerId);
  } else {
    selection.selectLayer(layerId);
  }
}

/**
 * Deselect a layer
 */
export function deselectLayer(_store: LayerStore, layerId: string): void {
  useSelectionStore().removeFromSelection(layerId);
}

/**
 * Clear all selection
 */
export function clearSelection(_store: LayerStore): void {
  useSelectionStore().clearLayerSelection();
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/**
 * Regenerate all keyframe IDs in a layer to avoid conflicts
 */
function regenerateKeyframeIds(layer: Layer): void {
  // Type for dynamic transform property access
  type TransformProp = AnimatableProperty<PropertyValue> | undefined;

  if (layer.transform) {
    const transformRecord = layer.transform as unknown as Record<string, TransformProp>;
    for (const key of Object.keys(layer.transform)) {
      const prop = transformRecord[key];
      if (prop?.keyframes) {
        prop.keyframes = prop.keyframes.map((kf: Keyframe<PropertyValue>) => ({
          ...kf,
          id: crypto.randomUUID()
        }));
      }
    }
  }
  if (layer.properties) {
    for (const prop of layer.properties) {
      if (prop.keyframes) {
        prop.keyframes = prop.keyframes.map((kf: Keyframe<PropertyValue>) => ({
          ...kf,
          id: crypto.randomUUID()
        }));
      }
    }
  }
}

/**
 * Get a layer by ID
 */
export function getLayerById(store: LayerStore, layerId: string): Layer | null {
  return store.getActiveCompLayers().find(l => l.id === layerId) || null;
}

/**
 * Get all children of a layer
 */
export function getLayerChildren(store: LayerStore, layerId: string): Layer[] {
  return store.getActiveCompLayers().filter(l => l.parentId === layerId);
}

/**
 * Get all descendants of a layer (recursive)
 */
export function getLayerDescendants(store: LayerStore, layerId: string): Layer[] {
  const layers = store.getActiveCompLayers();
  const descendants: Layer[] = [];

  const collectDescendants = (id: string) => {
    const children = layers.filter(l => l.parentId === id);
    for (const child of children) {
      descendants.push(child);
      collectDescendants(child.id);
    }
  };

  collectDescendants(layerId);
  return descendants;
}

// ============================================================================
// TEXT TO SPLINES CONVERSION
// ============================================================================

/**
 * Convert BezierPath vertices to ControlPoint format
 */
function bezierPathToControlPoints(path: BezierPath): ControlPoint[] {
  return path.vertices.map((vertex, index) => {
    // BezierVertex handles are RELATIVE, ControlPoint handles are ABSOLUTE
    const handleIn = (vertex.inHandle.x !== 0 || vertex.inHandle.y !== 0)
      ? {
          x: vertex.point.x + vertex.inHandle.x,
          y: vertex.point.y + vertex.inHandle.y,
        }
      : null;

    const handleOut = (vertex.outHandle.x !== 0 || vertex.outHandle.y !== 0)
      ? {
          x: vertex.point.x + vertex.outHandle.x,
          y: vertex.point.y + vertex.outHandle.y,
        }
      : null;

    return {
      id: `cp_${Date.now()}_${index}_${Math.random().toString(36).slice(2, 6)}`,
      x: vertex.point.x,
      y: vertex.point.y,
      depth: 0,
      handleIn,
      handleOut,
      type: (handleIn || handleOut) ? 'smooth' as const : 'corner' as const,
    };
  });
}

/**
 * Convert SVG d path data to ControlPoints
 * Used as fallback when BezierPath is not available
 */
function pathDataToControlPoints(pathData: string): ControlPoint[] {
  const points: ControlPoint[] = [];
  // Simple SVG path parser for M, L, C, Q, Z commands
  const commands = pathData.match(/[MLCQZ][^MLCQZ]*/gi) || [];

  let currentX = 0;
  let currentY = 0;

  for (const cmd of commands) {
    const type = cmd[0].toUpperCase();
    const args = cmd.slice(1).trim().split(/[\s,]+/).map(parseFloat);

    switch (type) {
      case 'M':
        currentX = args[0];
        currentY = args[1];
        points.push({
          id: `cp_${Date.now()}_${points.length}`,
          x: currentX,
          y: currentY,
          depth: 0,
          handleIn: null,
          handleOut: null,
          type: 'corner',
        });
        break;
      case 'L':
        currentX = args[0];
        currentY = args[1];
        points.push({
          id: `cp_${Date.now()}_${points.length}`,
          x: currentX,
          y: currentY,
          depth: 0,
          handleIn: null,
          handleOut: null,
          type: 'corner',
        });
        break;
      case 'C':
        // Cubic bezier: cp1x, cp1y, cp2x, cp2y, x, y
        const lastPoint = points[points.length - 1];
        if (lastPoint) {
          lastPoint.handleOut = { x: args[0], y: args[1] };
        }
        currentX = args[4];
        currentY = args[5];
        points.push({
          id: `cp_${Date.now()}_${points.length}`,
          x: currentX,
          y: currentY,
          depth: 0,
          handleIn: { x: args[2], y: args[3] },
          handleOut: null,
          type: 'smooth',
        });
        break;
    }
  }

  return points;
}

/**
 * Convert a text layer to one or more spline layers
 *
 * @param store - The layer store
 * @param layerId - ID of the text layer to convert
 * @param options - Conversion options
 * @returns Array of created spline layer IDs, or null on failure
 */
export async function convertTextLayerToSplines(
  store: LayerStore,
  layerId: string,
  options: {
    /** Create separate layer per character */
    perCharacter?: boolean;
    /** Font URL to use (required if font not loaded) */
    fontUrl?: string;
    /** Keep original text layer */
    keepOriginal?: boolean;
    /** Group character layers under a null parent */
    groupCharacters?: boolean;
  } = {}
): Promise<string[] | null> {
  const layer = getLayerById(store, layerId);
  if (!layer || layer.type !== 'text') {
    storeLogger.error('convertTextLayerToSplines: Layer not found or not a text layer');
    return null;
  }

  const textData = layer.data as {
    text: string;
    fontFamily: string;
    fontSize: number;
    fill: string;
    stroke: string;
    strokeWidth: number;
  };

  if (!textData.text) {
    storeLogger.error('convertTextLayerToSplines: No text content');
    return null;
  }

  // Get font URL - use Google Fonts CDN as fallback
  const fontUrl = options.fontUrl ||
    `https://fonts.gstatic.com/s/${textData.fontFamily.toLowerCase().replace(/\s+/g, '')}/v1/regular.woff`;

  try {
    // Convert text to vector paths
    const result = await textToVectorFromUrl(
      textData.text,
      fontUrl,
      textData.fontSize,
      {
        x: layer.transform.position.value.x,
        y: layer.transform.position.value.y,
        kerning: true,
      }
    );

    if (!result.allPaths.length && !result.characters.length) {
      storeLogger.error('convertTextLayerToSplines: No paths generated');
      return null;
    }

    store.pushHistory();

    const createdLayerIds: string[] = [];
    const layers = store.getActiveCompLayers();
    const originalIndex = layers.findIndex(l => l.id === layerId);

    if (options.perCharacter && result.characters.length > 0) {
      // Create parent group layer if requested
      let parentId: string | null = layer.parentId ?? null;

      if (options.groupCharacters) {
        const groupLayer = createLayer(store, 'null', `${layer.name} (Group)`);
        groupLayer.transform = { ...layer.transform };
        parentId = groupLayer.id;
        createdLayerIds.push(groupLayer.id);
      }

      // Create one spline layer per character
      for (let i = 0; i < result.characters.length; i++) {
        const charGroup = result.characters[i];

        // Skip whitespace characters
        if (charGroup.character.trim() === '' || charGroup.paths.length === 0) {
          continue;
        }

        // Combine all paths for this character into one
        const allControlPoints: ControlPoint[] = [];
        for (const path of charGroup.paths) {
          const points = bezierPathToControlPoints(path);
          allControlPoints.push(...points);
        }

        if (allControlPoints.length === 0) continue;

        const charLayerName = `${layer.name} - "${charGroup.character}" [${i}]`;
        const charLayer = createLayer(store, 'spline', charLayerName);

        // Set up spline data
        const splineData: SplineData = {
          pathData: '',
          controlPoints: allControlPoints,
          closed: charGroup.paths[0]?.closed ?? true,
          stroke: textData.stroke || '',
          strokeWidth: textData.strokeWidth || 0,
          fill: textData.fill || '#ffffff',
        };

        charLayer.data = splineData;
        charLayer.parentId = parentId;
        charLayer.inPoint = layer.inPoint;
        charLayer.outPoint = layer.outPoint;

        // Position relative to character bounds
        if (!options.groupCharacters) {
          charLayer.transform = {
            ...createDefaultTransform(),
            position: createAnimatableProperty('Position', {
              x: layer.transform.position.value.x + charGroup.bounds.x,
              y: layer.transform.position.value.y,
            }, 'position'),
          };
        }

        createdLayerIds.push(charLayer.id);
      }
    } else {
      // Create single spline layer with all paths
      const allControlPoints: ControlPoint[] = [];

      for (const path of result.allPaths) {
        const points = bezierPathToControlPoints(path);
        allControlPoints.push(...points);
      }

      if (allControlPoints.length === 0) {
        storeLogger.error('convertTextLayerToSplines: No control points generated');
        return null;
      }

      const splineLayer = createLayer(store, 'spline', `${layer.name} (Spline)`);

      const splineData: SplineData = {
        pathData: '',
        controlPoints: allControlPoints,
        closed: result.allPaths[0]?.closed ?? true,
        stroke: textData.stroke || '',
        strokeWidth: textData.strokeWidth || 0,
        fill: textData.fill || '#ffffff',
      };

      splineLayer.data = splineData;
      splineLayer.transform = { ...layer.transform };
      splineLayer.parentId = layer.parentId;
      splineLayer.inPoint = layer.inPoint;
      splineLayer.outPoint = layer.outPoint;

      createdLayerIds.push(splineLayer.id);
    }

    // Remove original layer if not keeping
    if (!options.keepOriginal) {
      deleteLayer(store, layerId);
    }

    // Select the first created layer
    if (createdLayerIds.length > 0) {
      const selectionStore = useSelectionStore();
      selectionStore.clearLayerSelection();
      selectionStore.selectLayer(createdLayerIds[0]);
    }

    storeLogger.info(`Converted text layer to ${createdLayerIds.length} spline layer(s)`);
    return createdLayerIds;

  } catch (error) {
    storeLogger.error('convertTextLayerToSplines: Failed to convert', error);
    return null;
  }
}

// ============================================================================
// COPY PATH TO POSITION
// ============================================================================

/**
 * Copy a path from a spline layer and paste it as position keyframes on a target layer.
 * This creates a motion path where the layer follows the spline's shape over time.
 *
 * @param store - The layer store
 * @param sourceSplineLayerId - The spline layer to copy the path from
 * @param targetLayerId - The layer to apply position keyframes to
 * @param options - Configuration options
 * @returns Number of keyframes created, or null if failed
 */
export function copyPathToPosition(
  store: LayerStore,
  sourceSplineLayerId: string,
  targetLayerId: string,
  options: {
    /** Use the full composition duration for the motion (default: true) */
    useFullDuration?: boolean;
    /** Start frame for keyframes (if not using full duration) */
    startFrame?: number;
    /** End frame for keyframes (if not using full duration) */
    endFrame?: number;
    /** Number of keyframes to create (default: auto based on path complexity) */
    keyframeCount?: number;
    /** Interpolation type for keyframes (default: 'bezier') */
    interpolation?: 'linear' | 'bezier' | 'hold';
    /** Apply spatial tangents from path handles (default: true) */
    useSpatialTangents?: boolean;
    /** Reverse the path direction (default: false) */
    reversed?: boolean;
  } = {}
): number | null {
  const comp = store.getActiveComp();
  if (!comp) {
    storeLogger.error('copyPathToPosition: No active composition');
    return null;
  }

  // Get source spline layer
  const sourceLayer = comp.layers.find(l => l.id === sourceSplineLayerId);
  if (!sourceLayer || sourceLayer.type !== 'spline' || !sourceLayer.data) {
    storeLogger.error('copyPathToPosition: Source layer not found or not a spline');
    return null;
  }

  // Get target layer
  const targetLayer = comp.layers.find(l => l.id === targetLayerId);
  if (!targetLayer) {
    storeLogger.error('copyPathToPosition: Target layer not found');
    return null;
  }

  const splineData = sourceLayer.data as SplineData;
  const controlPoints = splineData.controlPoints || [];

  if (controlPoints.length < 2) {
    storeLogger.error('copyPathToPosition: Path needs at least 2 control points');
    return null;
  }

  // Configuration
  const useFullDuration = options.useFullDuration ?? true;
  const startFrame = options.startFrame ?? 0;
  const endFrame = options.endFrame ?? (comp.settings.frameCount - 1);
  const interpolation = options.interpolation ?? 'bezier';
  const useSpatialTangents = options.useSpatialTangents ?? true;
  const reversed = options.reversed ?? false;

  // Calculate frame range
  const frameStart = useFullDuration ? 0 : startFrame;
  const frameEnd = useFullDuration ? (comp.settings.frameCount - 1) : endFrame;
  const frameDuration = frameEnd - frameStart;

  // Determine keyframe count based on path complexity or use specified value
  const defaultKeyframeCount = Math.max(
    controlPoints.length,
    Math.ceil(frameDuration / 5) // At least one keyframe every 5 frames
  );
  const keyframeCount = options.keyframeCount ?? defaultKeyframeCount;

  // Sample points along the path
  const sampledPoints = samplePathPoints(controlPoints, keyframeCount, splineData.closed ?? false);
  if (reversed) {
    sampledPoints.reverse();
  }

  // Create keyframes with proper BezierHandle structure
  const keyframes: Array<{
    id: string;
    frame: number;
    value: { x: number; y: number; z: number };
    interpolation: 'linear' | 'bezier' | 'hold';
    inHandle: { frame: number; value: number; enabled: boolean };
    outHandle: { frame: number; value: number; enabled: boolean };
    controlMode: 'symmetric' | 'smooth' | 'corner';
    spatialInTangent?: { x: number; y: number; z: number };
    spatialOutTangent?: { x: number; y: number; z: number };
  }> = [];

  for (let i = 0; i < sampledPoints.length; i++) {
    const t = sampledPoints.length > 1 ? i / (sampledPoints.length - 1) : 0;
    const frame = Math.round(frameStart + t * frameDuration);
    const point = sampledPoints[i];

    // Calculate frame distance to neighboring keyframes for handle influence
    const prevFrame = i > 0 ? keyframes[i - 1]?.frame ?? 0 : 0;
    const nextFrame = i < sampledPoints.length - 1
      ? Math.round(frameStart + ((i + 1) / (sampledPoints.length - 1)) * frameDuration)
      : frameDuration;

    const inInfluence = (frame - prevFrame) * 0.33;
    const outInfluence = (nextFrame - frame) * 0.33;

    const keyframe: typeof keyframes[0] = {
      id: `kf_${Date.now()}_${i}`,
      frame,
      value: { x: point.x, y: point.y, z: point.depth ?? 0 },
      interpolation,
      inHandle: { frame: -inInfluence, value: 0, enabled: true },
      outHandle: { frame: outInfluence, value: 0, enabled: true },
      controlMode: 'smooth'
    };

    // Apply spatial tangents from path handles if available
    if (useSpatialTangents && point.handleIn && point.handleOut) {
      keyframe.spatialInTangent = {
        x: point.handleIn.x - point.x,
        y: point.handleIn.y - point.y,
        z: 0
      };
      keyframe.spatialOutTangent = {
        x: point.handleOut.x - point.x,
        y: point.handleOut.y - point.y,
        z: 0
      };
    }

    keyframes.push(keyframe);
  }

  // Apply keyframes to target layer's position
  store.pushHistory();

  targetLayer.transform.position.animated = true;
  // Type assertion needed: our keyframes match Keyframe<{x,y,z}> structure
  targetLayer.transform.position.keyframes = keyframes as Keyframe<{ x: number; y: number; z: number }>[];

  // Mark layer dirty for re-evaluation
  markLayerDirty(targetLayerId);
  store.project.meta.modified = new Date().toISOString();

  storeLogger.info(`copyPathToPosition: Created ${keyframes.length} position keyframes on layer "${targetLayer.name}"`);
  return keyframes.length;
}

/**
 * Sample points along a path at regular intervals.
 * Uses arc-length parameterization for even spacing.
 */
function samplePathPoints(
  controlPoints: ControlPoint[],
  count: number,
  closed: boolean
): Array<{ x: number; y: number; depth?: number; handleIn?: { x: number; y: number }; handleOut?: { x: number; y: number } }> {
  if (controlPoints.length === 0) return [];
  if (controlPoints.length === 1) {
    return [{ x: controlPoints[0].x, y: controlPoints[0].y, depth: controlPoints[0].depth }];
  }

  // Build path segments
  const segments: Array<{
    p0: { x: number; y: number; depth?: number };
    p1: { x: number; y: number };
    p2: { x: number; y: number };
    p3: { x: number; y: number; depth?: number };
    length: number;
  }> = [];

  let totalLength = 0;

  for (let i = 0; i < controlPoints.length - 1; i++) {
    const curr = controlPoints[i];
    const next = controlPoints[i + 1];

    // Get bezier control points
    const p0 = { x: curr.x, y: curr.y, depth: curr.depth };
    const p3 = { x: next.x, y: next.y, depth: next.depth };

    // Control points (handle out from curr, handle in to next)
    const p1 = curr.handleOut
      ? { x: curr.handleOut.x, y: curr.handleOut.y }
      : { x: curr.x, y: curr.y };
    const p2 = next.handleIn
      ? { x: next.handleIn.x, y: next.handleIn.y }
      : { x: next.x, y: next.y };

    // Approximate segment length
    const length = approximateBezierLength(p0, p1, p2, p3);
    totalLength += length;

    segments.push({ p0, p1, p2, p3, length });
  }

  // Handle closed path
  if (closed && controlPoints.length > 2) {
    const last = controlPoints[controlPoints.length - 1];
    const first = controlPoints[0];

    const p0 = { x: last.x, y: last.y, depth: last.depth };
    const p3 = { x: first.x, y: first.y, depth: first.depth };
    const p1 = last.handleOut
      ? { x: last.handleOut.x, y: last.handleOut.y }
      : { x: last.x, y: last.y };
    const p2 = first.handleIn
      ? { x: first.handleIn.x, y: first.handleIn.y }
      : { x: first.x, y: first.y };

    const length = approximateBezierLength(p0, p1, p2, p3);
    totalLength += length;
    segments.push({ p0, p1, p2, p3, length });
  }

  // Sample along path
  const result: Array<{ x: number; y: number; depth?: number; handleIn?: { x: number; y: number }; handleOut?: { x: number; y: number } }> = [];

  // Guard against division by zero (count must be at least 2)
  if (count < 2) {
    const cp = controlPoints[0];
    return [{ x: cp.x, y: cp.y, depth: cp.depth }];
  }

  const step = totalLength / (count - 1);

  let currentDist = 0;
  let segIndex = 0;
  let segDist = 0;

  for (let i = 0; i < count; i++) {
    const targetDist = i * step;

    // Find the segment containing this distance
    while (segIndex < segments.length - 1 && currentDist + segments[segIndex].length < targetDist) {
      currentDist += segments[segIndex].length;
      segIndex++;
    }

    const seg = segments[segIndex];
    if (!seg) {
      // Past the end, use last point
      const lastCp = controlPoints[controlPoints.length - 1];
      result.push({ x: lastCp.x, y: lastCp.y, depth: lastCp.depth });
      continue;
    }

    // Calculate t within this segment
    segDist = targetDist - currentDist;
    const t = seg.length > 0 ? Math.min(1, segDist / seg.length) : 0;

    // Evaluate cubic bezier
    const point = evaluateCubicBezier(seg.p0, seg.p1, seg.p2, seg.p3, t);

    // Interpolate depth
    const depth = seg.p0.depth !== undefined && seg.p3.depth !== undefined
      ? seg.p0.depth + (seg.p3.depth - seg.p0.depth) * t
      : undefined;

    // Calculate tangent for handles
    const tangent = evaluateCubicBezierDerivative(seg.p0, seg.p1, seg.p2, seg.p3, t);
    const handleScale = 20; // Scale factor for handle length

    result.push({
      x: point.x,
      y: point.y,
      depth,
      handleIn: { x: point.x - tangent.x * handleScale, y: point.y - tangent.y * handleScale },
      handleOut: { x: point.x + tangent.x * handleScale, y: point.y + tangent.y * handleScale }
    });
  }

  return result;
}

/**
 * Approximate the length of a cubic bezier curve using chord length approximation
 */
function approximateBezierLength(
  p0: { x: number; y: number },
  p1: { x: number; y: number },
  p2: { x: number; y: number },
  p3: { x: number; y: number },
  samples: number = 10
): number {
  let length = 0;
  let prev = p0;

  for (let i = 1; i <= samples; i++) {
    const t = i / samples;
    const curr = evaluateCubicBezier(p0, p1, p2, p3, t);
    length += Math.sqrt(
      (curr.x - prev.x) ** 2 + (curr.y - prev.y) ** 2
    );
    prev = curr;
  }

  return length;
}

/**
 * Evaluate a cubic bezier curve at parameter t
 */
function evaluateCubicBezier(
  p0: { x: number; y: number },
  p1: { x: number; y: number },
  p2: { x: number; y: number },
  p3: { x: number; y: number },
  t: number
): { x: number; y: number } {
  const t2 = t * t;
  const t3 = t2 * t;
  const mt = 1 - t;
  const mt2 = mt * mt;
  const mt3 = mt2 * mt;

  return {
    x: mt3 * p0.x + 3 * mt2 * t * p1.x + 3 * mt * t2 * p2.x + t3 * p3.x,
    y: mt3 * p0.y + 3 * mt2 * t * p1.y + 3 * mt * t2 * p2.y + t3 * p3.y
  };
}

/**
 * Evaluate the derivative (tangent) of a cubic bezier curve at parameter t
 */
function evaluateCubicBezierDerivative(
  p0: { x: number; y: number },
  p1: { x: number; y: number },
  p2: { x: number; y: number },
  p3: { x: number; y: number },
  t: number
): { x: number; y: number } {
  const t2 = t * t;
  const mt = 1 - t;
  const mt2 = mt * mt;

  const dx = 3 * mt2 * (p1.x - p0.x) + 6 * mt * t * (p2.x - p1.x) + 3 * t2 * (p3.x - p2.x);
  const dy = 3 * mt2 * (p1.y - p0.y) + 6 * mt * t * (p2.y - p1.y) + 3 * t2 * (p3.y - p2.y);

  // Normalize
  const len = Math.sqrt(dx * dx + dy * dy);
  if (len === 0) return { x: 0, y: 0 };

  return { x: dx / len, y: dy / len };
}

// Time manipulation actions moved to ./layers/layerTimeActions.ts
// Re-exported at top of file for backwards compatibility

// ============================================================================
// SEQUENCE LAYERS
// ============================================================================

export interface SequenceLayersOptions {
  /** Gap between layers in frames (positive = gap, negative = overlap) */
  gapFrames?: number;
  /** Starting frame for the sequence */
  startFrame?: number;
  /** Whether to maintain layer order or reverse */
  reverse?: boolean;
}

/**
 * Sequence selected layers - arrange them one after another.
 * Similar to After Effects "Keyframe Assistant > Sequence Layers"
 *
 * @param store - The layer store
 * @param layerIds - Array of layer IDs to sequence (in order)
 * @param options - Sequence options
 * @returns Number of layers sequenced
 */
export function sequenceLayers(
  store: LayerStore,
  layerIds: string[],
  options: SequenceLayersOptions = {}
): number {
  const {
    gapFrames = 0,
    startFrame = 0,
    reverse = false
  } = options;

  if (layerIds.length < 2) {
    storeLogger.warn('sequenceLayers: need at least 2 layers');
    return 0;
  }

  // Get layers in order
  const layers = layerIds
    .map(id => store.getActiveCompLayers().find(l => l.id === id))
    .filter((l): l is Layer => l !== null && l !== undefined);

  if (layers.length < 2) {
    storeLogger.warn('sequenceLayers: could not find enough layers');
    return 0;
  }

  // Optionally reverse the order
  const orderedLayers = reverse ? [...layers].reverse() : layers;

  // Push history BEFORE changes for undo support
  store.pushHistory();

  let currentFrame = startFrame;

  orderedLayers.forEach((layer, index) => {
    const duration = layer.endFrame - layer.startFrame;

    // Set new start/end frames
    layer.startFrame = currentFrame;
    layer.endFrame = currentFrame + duration;

    // Move to next position
    currentFrame = layer.endFrame + gapFrames;

    markLayerDirty(layer.id);
  });

  store.project.meta.modified = new Date().toISOString();

  storeLogger.info(`sequenceLayers: sequenced ${orderedLayers.length} layers starting at frame ${startFrame}`);
  return orderedLayers.length;
}

// ============================================================================
// EXPONENTIAL SCALE
// ============================================================================

export interface ExponentialScaleOptions {
  /** Starting scale percentage */
  startScale?: number;
  /** Ending scale percentage */
  endScale?: number;
  /** Starting frame */
  startFrame?: number;
  /** Ending frame */
  endFrame?: number;
  /** Number of keyframes to create (more = smoother) */
  keyframeCount?: number;
  /** Whether to apply to X, Y, or both */
  axis?: 'both' | 'x' | 'y';
}

/**
 * Create exponential scale animation on a layer.
 * Uses exponential curve instead of linear for more natural zoom effect.
 *
 * Formula: scale(t) = startScale * (endScale/startScale)^t
 *
 * @param store - The layer store (must have pushHistory)
 * @param layerId - Layer to apply exponential scale to
 * @param options - Scale animation options
 * @returns Number of keyframes created
 */
export function applyExponentialScale(
  store: LayerStore,
  layerId: string,
  options: ExponentialScaleOptions = {}
): number {
  const {
    startScale = 100,
    endScale = 200,
    startFrame = 0,
    endFrame = 30,
    keyframeCount = 10,
    axis = 'both'
  } = options;

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    storeLogger.warn('applyExponentialScale: layer not found');
    return 0;
  }

  // Validate scale values (prevent division by zero)
  if (!Number.isFinite(startScale) || startScale === 0) {
    storeLogger.warn('applyExponentialScale: startScale must be a non-zero finite number');
    return 0;
  }
  if (!Number.isFinite(endScale)) {
    storeLogger.warn('applyExponentialScale: endScale must be a finite number');
    return 0;
  }

  // Push history BEFORE changes for undo support
  store.pushHistory();

  // Clear existing scale keyframes
  layer.transform.scale.keyframes = [];
  layer.transform.scale.animated = true;

  const duration = endFrame - startFrame;
  const ratio = endScale / startScale;

  // Generate keyframes with exponential interpolation
  for (let i = 0; i <= keyframeCount; i++) {
    const t = i / keyframeCount; // 0 to 1
    const frame = Math.round(startFrame + t * duration);

    // Exponential formula: startScale * ratio^t
    const scaleValue = startScale * Math.pow(ratio, t);

    const currentValue = layer.transform.scale.value;
    let newValue: { x: number; y: number; z?: number };

    if (axis === 'x') {
      newValue = { x: scaleValue, y: currentValue.y, z: currentValue.z };
    } else if (axis === 'y') {
      newValue = { x: currentValue.x, y: scaleValue, z: currentValue.z };
    } else {
      newValue = { x: scaleValue, y: scaleValue, z: currentValue.z };
    }

    layer.transform.scale.keyframes.push({
      id: `kf_expscale_${frame}_${Date.now()}_${i}`,
      frame,
      value: newValue,
      interpolation: 'linear', // Linear between exponential samples gives smooth curve
      inHandle: { frame: -2, value: 0, enabled: false },
      outHandle: { frame: 2, value: 0, enabled: false },
      controlMode: 'smooth'
    });
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();

  storeLogger.info(`applyExponentialScale: created ${keyframeCount + 1} keyframes for exponential scale ${startScale}% -> ${endScale}%`);
  return keyframeCount + 1;
}
