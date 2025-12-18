/**
 * Layer Actions
 *
 * Layer management including creation, deletion, duplication, clipboard operations,
 * and layer-specific updates (spline, 3D, parenting).
 */

import { storeLogger } from '@/utils/logger';
import type { Layer, AnimatableProperty } from '@/types/project';
import { createDefaultTransform, createAnimatableProperty } from '@/types/project';
import { useSelectionStore } from '../selectionStore';
import { markLayerDirty, clearLayerCache } from '@/services/layerEvaluationCache';

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
    keyframes: any[];
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
  const id = `layer_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;

  // Initialize type-specific data
  let layerData: any = null;

  switch (type) {
    case 'text':
      layerData = {
        text: 'Text',
        fontFamily: 'Arial',
        fontSize: 72,
        fontWeight: '400',
        fontStyle: 'normal',
        fill: '#ffffff',
        stroke: '',
        strokeWidth: 0,
        tracking: 0,
        letterSpacing: 0,
        lineHeight: 1.2,
        textAlign: 'left',
        pathLayerId: null,
        pathReversed: false,
        pathPerpendicularToPath: true,
        pathForceAlignment: false,
        pathFirstMargin: 0,
        pathLastMargin: 0,
        pathOffset: 0,
        pathAlign: 'left'
      };
      break;

    case 'solid':
      layerData = {
        color: '#808080',
        width: store.project.composition.width,
        height: store.project.composition.height
      };
      break;

    case 'null':
      layerData = {
        size: 40
      };
      break;

    case 'spline':
      layerData = {
        pathData: '',
        controlPoints: [],
        closed: false,
        stroke: '#00ff00',
        strokeWidth: 2,
        fill: ''
      };
      break;

    case 'particles':
      layerData = {
        systemConfig: {
          maxParticles: 1000,
          gravity: 0,
          windStrength: 0,
          windDirection: 0,
          warmupPeriod: 0,
          respectMaskBoundary: false,
          boundaryBehavior: 'kill',
          friction: 0.01
        },
        emitters: [{
          id: 'emitter_1',
          name: 'Emitter 1',
          x: store.project.composition.width / 2,
          y: store.project.composition.height / 2,
          direction: -90,
          spread: 30,
          speed: 5,
          speedVariance: 0.2,
          size: 10,
          sizeVariance: 0.3,
          color: [255, 255, 255],
          emissionRate: 10,
          initialBurst: 0,
          particleLifetime: 60,
          lifetimeVariance: 0.2,
          enabled: true,
          burstOnBeat: false,
          burstCount: 20
        }],
        gravityWells: [],
        vortices: [],
        modulations: [],
        renderOptions: {
          blendMode: 'additive',
          renderTrails: false,
          trailLength: 10,
          trailOpacityFalloff: 0.9,
          particleShape: 'circle',
          glowEnabled: false,
          glowRadius: 5,
          glowIntensity: 0.5,
          motionBlur: false,
          motionBlurStrength: 0.5,
          motionBlurSamples: 4,
          connections: {
            enabled: false,
            maxDistance: 100,
            maxConnections: 3,
            lineWidth: 1,
            lineOpacity: 0.5,
            fadeByDistance: true
          }
        }
      };
      break;

    case 'depthflow':
      layerData = {
        sourceLayerId: null,
        depthLayerId: null,
        config: {
          preset: 'static',
          zoom: 1,
          offsetX: 0,
          offsetY: 0,
          rotation: 0,
          depthScale: 1,
          focusDepth: 0.5,
          dollyZoom: 0,
          orbitRadius: 0,
          orbitSpeed: 1,
          swingAmplitude: 0,
          swingFrequency: 1,
          edgeDilation: 0,
          inpaintEdges: false
        }
      };
      break;

    case 'light':
      layerData = {
        lightType: 'point',
        color: '#ffffff',
        intensity: 100,
        radius: 500,
        falloff: 'none',
        falloffDistance: 500,
        castShadows: false,
        shadowDarkness: 100,
        shadowDiffusion: 0
      };
      break;

    case 'camera':
      // Camera layers are created via createCameraLayer(), but handle here too
      layerData = {
        cameraId: null,
        isActiveCamera: false
      };
      break;

    case 'image':
      layerData = {
        assetId: null,
        fit: 'contain'
      };
      break;

    case 'video':
      layerData = {
        assetId: null,
        loop: false,
        startTime: 0,
        speed: 1.0
      };
      break;

    case 'shape':
      layerData = {
        shapes: [],
        fill: '#ffffff',
        stroke: '#000000',
        strokeWidth: 2
      };
      break;

    case 'precomp':
      layerData = {
        compositionId: null,
        timeRemap: null
      };
      break;

    case 'matte':
      layerData = {
        matteType: 'luminance',
        invert: false,
        threshold: 0.5
      };
      break;
  }

  // Initialize audio props for video/audio layers
  let audioProps = undefined;
  if (type === 'video' || type === 'audio') {
    audioProps = {
      level: createAnimatableProperty('Audio Levels', 0, 'number') // 0dB default
    };
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
    solo: false,
    threeD: false,
    motionBlur: false,
    inPoint: 0,
    outPoint: (comp?.settings.frameCount || 81) - 1,
    parentId: null,
    blendMode: 'normal',
    opacity: createAnimatableProperty('opacity', 100, 'number'),
    transform: centeredTransform,
    audio: audioProps,
    properties: [],
    effects: [],
    data: layerData
  };

  // Camera layers should use createCameraLayer() instead
  if (type === 'camera') {
    storeLogger.warn('Use createCameraLayer() for camera layers');
  }

  layers.unshift(layer);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return layer;
}

// ============================================================================
// LAYER DELETION
// ============================================================================

/**
 * Delete a layer by ID
 */
export function deleteLayer(store: LayerStore, layerId: string): void {
  const layers = store.getActiveCompLayers();
  const index = layers.findIndex(l => l.id === layerId);
  if (index === -1) return;

  layers.splice(index, 1);
  useSelectionStore().removeFromSelection(layerId);
  clearLayerCache(layerId); // Clear evaluation cache for deleted layer
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
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

  // Deep clone the layer
  const duplicate: Layer = structuredClone(original);

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

  // Deep clone layers to clipboard
  store.clipboard.layers = selectedLayers.map(layer => structuredClone(layer));
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
 */
export function updateLayer(store: LayerStore, layerId: string, updates: Partial<Layer>): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  Object.assign(layer, updates);
  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Update layer-specific data (e.g., text content, image path, etc.)
 */
export function updateLayerData(store: LayerStore, layerId: string, dataUpdates: Record<string, any>): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || !layer.data) return;

  Object.assign(layer.data, dataUpdates);
  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Reorder layers
 */
export function moveLayer(store: LayerStore, layerId: string, newIndex: number): void {
  const layers = store.getActiveCompLayers();
  const currentIndex = layers.findIndex(l => l.id === layerId);
  if (currentIndex === -1) return;

  const [layer] = layers.splice(currentIndex, 1);
  layers.splice(newIndex, 0, layer);
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
    const pos = t.position.value;
    t.position.value = { x: pos.x, y: pos.y, z: (pos as any).z ?? 0 };
    t.position.type = 'vector3';

    // Anchor Point
    const anch = t.anchorPoint.value;
    t.anchorPoint.value = { x: anch.x, y: anch.y, z: (anch as any).z ?? 0 };
    t.anchorPoint.type = 'vector3';

    // Scale
    const scl = t.scale.value;
    t.scale.value = { x: scl.x, y: scl.y, z: (scl as any).z ?? 100 };
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
// SPLINE LAYER OPERATIONS
// ============================================================================

export interface SplineControlPoint {
  id: string;
  x: number;
  y: number;
  depth?: number;
  handleIn?: { x: number; y: number } | null;
  handleOut?: { x: number; y: number } | null;
  type: 'corner' | 'smooth' | 'symmetric';
}

/**
 * Add a control point to a spline layer
 */
export function addSplineControlPoint(store: LayerStore, layerId: string, point: SplineControlPoint): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as any;
  if (!splineData.controlPoints) {
    splineData.controlPoints = [];
  }
  splineData.controlPoints.push(point);
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Update a spline control point
 */
export function updateSplineControlPoint(
  store: LayerStore,
  layerId: string,
  pointId: string,
  updates: Partial<SplineControlPoint>
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as any;
  const point = splineData.controlPoints?.find((p: any) => p.id === pointId);
  if (!point) return;

  Object.assign(point, updates);
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Delete a spline control point
 */
export function deleteSplineControlPoint(store: LayerStore, layerId: string, pointId: string): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as any;
  if (!splineData.controlPoints) return;

  const index = splineData.controlPoints.findIndex((p: any) => p.id === pointId);
  if (index >= 0) {
    splineData.controlPoints.splice(index, 1);
    store.project.meta.modified = new Date().toISOString();
  }
}

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
  if (layer.transform) {
    for (const key of Object.keys(layer.transform)) {
      const prop = (layer.transform as any)[key];
      if (prop?.keyframes) {
        prop.keyframes = prop.keyframes.map((kf: any) => ({
          ...kf,
          id: crypto.randomUUID()
        }));
      }
    }
  }
  if (layer.properties) {
    for (const prop of layer.properties) {
      if (prop.keyframes) {
        prop.keyframes = prop.keyframes.map((kf: any) => ({
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
