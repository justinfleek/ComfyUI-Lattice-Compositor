/**
 * Layer Actions
 *
 * Layer management including creation, deletion, duplication, clipboard operations,
 * and layer-specific updates (spline, 3D, parenting).
 */

import { storeLogger } from '@/utils/logger';
import type { Layer, AnimatableProperty, SplineData, ControlPoint, AnimatableControlPoint, EvaluatedControlPoint } from '@/types/project';
import { createDefaultTransform, createAnimatableProperty, controlPointToAnimatable, animatableToControlPoint } from '@/types/project';
import { useSelectionStore } from '../selectionStore';
import { markLayerDirty, clearLayerCache } from '@/services/layerEvaluationCache';
import { interpolateProperty } from '@/services/interpolation';
import { textToVectorFromUrl, type TextToVectorResult, type CharacterVectorGroup } from '@/services/textToVector';
import type { BezierPath, BezierVertex } from '@/types/shapes';

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
        // Stroke options (shown in More Options group)
        lineCap: 'round',    // butt, round, square
        lineJoin: 'round',   // miter, round, bevel
        dashArray: '',       // e.g., "10, 5" for dashed lines
        dashOffset: 0
      };
      break;

    case 'path':
      // Path layer - invisible motion guide for text-on-path, camera paths, etc.
      layerData = {
        pathData: '',
        controlPoints: [],
        closed: false,
        showGuide: true,           // Show dashed guide line in editor
        guideColor: '#00FFFF',     // Cyan guide line
        guideDashPattern: [10, 5]  // [dash, gap]
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
          },
          // Sprite sheet defaults
          spriteEnabled: false,
          spriteImageUrl: '',
          spriteColumns: 1,
          spriteRows: 1,
          spriteAnimate: false,
          spriteFrameRate: 10,
          spriteRandomStart: false
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

    case 'nestedComp':
      layerData = {
        compositionId: null,
        // Speed map (new naming)
        speedMap: null,
        speedMapEnabled: false,
        // Backwards compatibility
        timeRemap: null,
        timeRemapEnabled: false
      };
      break;

    case 'matte':
      layerData = {
        matteType: 'luminance',
        invert: false,
        threshold: 0.5
      };
      break;

    case 'model':
      // 3D Model layer - GLTF, OBJ, FBX, USD
      layerData = {
        assetId: '',
        format: 'gltf' as const,
        scale: createAnimatableProperty('Scale', 1, 'number'),
        uniformScale: true,
        castShadow: true,
        receiveShadow: true,
        frustumCulled: true,
        renderOrder: 0,
        showBoundingBox: false,
        showSkeleton: false,
        envMapIntensity: 1.0
      };
      break;

    case 'pointcloud':
      // Point Cloud layer - PLY, PCD, LAS
      layerData = {
        assetId: '',
        format: 'ply' as const,
        pointCount: 0,
        pointSize: createAnimatableProperty('Point Size', 2, 'number'),
        sizeAttenuation: true,
        minPointSize: 1,
        maxPointSize: 64,
        colorMode: 'rgb' as const,
        uniformColor: '#ffffff',
        renderMode: 'points' as const,
        opacity: createAnimatableProperty('Opacity', 1, 'number'),
        depthTest: true,
        depthWrite: true,
        showBoundingBox: false,
        pointBudget: 1000000
      };
      break;

    case 'control':
      // Control layer (null object replacement) - transform-only parent
      layerData = {
        size: 50,           // Visual size of control icon in editor
        showAxes: true,     // Show axis indicators
        showIcon: true      // Show control layer icon
      };
      break;

    case 'depth':
      // Depth map visualization layer
      layerData = {
        assetId: null,
        visualizationMode: 'colormap' as const,
        colorMap: 'turbo' as const,
        invert: false,
        minDepth: 0,
        maxDepth: 1,
        autoNormalize: true,
        contourLevels: 10,
        contourColor: '#ffffff',
        contourWidth: 1,
        meshDisplacement: createAnimatableProperty('Displacement', 50, 'number'),
        meshResolution: 128,
        wireframe: false
      };
      break;

    case 'normal':
      // Normal map visualization layer
      layerData = {
        assetId: null,
        visualizationMode: 'rgb' as const,
        format: 'opengl' as const,
        flipX: false,
        flipY: false,
        flipZ: false,
        arrowDensity: 20,
        arrowScale: 10,
        arrowColor: '#00ff00',
        lightDirection: { x: 0.5, y: 0.5, z: 1.0 },
        lightIntensity: 1.0,
        ambientIntensity: 0.2
      };
      break;

    case 'audio':
      // Audio-only layer
      layerData = {
        assetId: null,
        level: createAnimatableProperty('Level', 0, 'number'),
        muted: false,
        solo: false,
        pan: createAnimatableProperty('Pan', 0, 'number'),
        startTime: 0,
        loop: false,
        speed: 1.0,
        showWaveform: true,
        waveformColor: '#4a90d9',
        exposeFeatures: true
      };
      break;

    case 'generated':
      // AI-generated content layer
      layerData = {
        generationType: 'depth' as const,
        sourceLayerId: null,
        model: 'depth-anything-v2',
        parameters: {},
        generatedAssetId: null,
        status: 'pending' as const,
        autoRegenerate: false
      };
      break;

    case 'group':
      // Layer group/folder
      layerData = {
        collapsed: false,
        color: null,
        passThrough: true,
        isolate: false
      };
      break;

    case 'particle':
      // Legacy particle layer (backwards compatibility)
      layerData = {
        emitterType: 'point' as const,
        particleCount: 100,
        lifetime: 2.0,
        speed: 50,
        spread: 45,
        gravity: -9.8,
        color: '#ffffff',
        size: 5
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

  // Use spread operator instead of Object.assign for proper Vue reactivity
  layer.data = { ...layer.data, ...dataUpdates };
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

    // Origin (formerly Anchor Point)
    const originProp = t.origin || t.anchorPoint;
    if (originProp) {
      const orig = originProp.value;
      originProp.value = { x: orig.x, y: orig.y, z: (orig as any).z ?? 0 };
      originProp.type = 'vector3';
    }

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
 * Insert a control point at a specific index in a spline layer
 */
export function insertSplineControlPoint(store: LayerStore, layerId: string, point: SplineControlPoint, index: number): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as any;
  if (!splineData.controlPoints) {
    splineData.controlPoints = [];
  }
  // Clamp index to valid range
  const insertIndex = Math.max(0, Math.min(index, splineData.controlPoints.length));
  splineData.controlPoints.splice(insertIndex, 0, point);
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
// SPLINE ANIMATION (Per-Point Keyframing)
// ============================================================================

/**
 * Enable animation mode on a spline layer
 * Converts static controlPoints to animatedControlPoints
 */
export function enableSplineAnimation(store: LayerStore, layerId: string): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as SplineData;

  // Already animated?
  if (splineData.animated && splineData.animatedControlPoints) {
    storeLogger.debug('Spline already in animated mode');
    return;
  }

  // Convert static control points to animatable
  const staticPoints = splineData.controlPoints || [];
  const animatedPoints: AnimatableControlPoint[] = staticPoints.map(cp =>
    controlPointToAnimatable(cp)
  );

  // Update spline data
  splineData.animatedControlPoints = animatedPoints;
  splineData.animated = true;

  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);

  storeLogger.debug('Enabled spline animation with', animatedPoints.length, 'control points');
}

/**
 * Add keyframe to a spline control point property at the specified frame
 * This sets the current value as a keyframe
 *
 * @param pointId - The control point ID
 * @param property - Which property ('x', 'y', 'depth', 'handleIn.x', 'handleIn.y', 'handleOut.x', 'handleOut.y')
 * @param frame - Frame number to add keyframe at
 */
export function addSplinePointKeyframe(
  store: LayerStore,
  layerId: string,
  pointId: string,
  property: 'x' | 'y' | 'depth' | 'handleIn.x' | 'handleIn.y' | 'handleOut.x' | 'handleOut.y',
  frame: number
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as SplineData;

  // Auto-enable animation if needed
  if (!splineData.animated || !splineData.animatedControlPoints) {
    enableSplineAnimation(store, layerId);
  }

  // Find the animated control point
  const point = splineData.animatedControlPoints?.find(p => p.id === pointId);
  if (!point) {
    storeLogger.warn('Control point not found:', pointId);
    return;
  }

  // Get the property to keyframe
  let animatableProp: AnimatableProperty<number> | undefined;

  switch (property) {
    case 'x':
      animatableProp = point.x;
      break;
    case 'y':
      animatableProp = point.y;
      break;
    case 'depth':
      animatableProp = point.depth;
      break;
    case 'handleIn.x':
      animatableProp = point.handleIn?.x;
      break;
    case 'handleIn.y':
      animatableProp = point.handleIn?.y;
      break;
    case 'handleOut.x':
      animatableProp = point.handleOut?.x;
      break;
    case 'handleOut.y':
      animatableProp = point.handleOut?.y;
      break;
  }

  if (!animatableProp) {
    storeLogger.warn('Property not found on control point:', property);
    return;
  }

  // Check if keyframe already exists at this frame
  const existingIdx = animatableProp.keyframes.findIndex(k => k.frame === frame);

  if (existingIdx >= 0) {
    // Update existing keyframe
    animatableProp.keyframes[existingIdx].value = animatableProp.value;
  } else {
    // Add new keyframe
    animatableProp.keyframes.push({
      id: `kf_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
      frame,
      value: animatableProp.value,
      interpolation: 'bezier',
      controlMode: 'smooth',
      inHandle: { frame: -5, value: 0, enabled: true },
      outHandle: { frame: 5, value: 0, enabled: true }
    });

    // Sort keyframes by frame
    animatableProp.keyframes.sort((a, b) => a.frame - b.frame);
  }

  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);

  storeLogger.debug('Added keyframe to control point', pointId, 'property', property, 'at frame', frame);
}

/**
 * Add keyframes to all position properties of a control point at once
 */
export function addSplinePointPositionKeyframe(
  store: LayerStore,
  layerId: string,
  pointId: string,
  frame: number
): void {
  addSplinePointKeyframe(store, layerId, pointId, 'x', frame);
  addSplinePointKeyframe(store, layerId, pointId, 'y', frame);
}

/**
 * Update a spline control point position and optionally add keyframe
 * Used when dragging control points in the editor
 */
export function updateSplinePointWithKeyframe(
  store: LayerStore,
  layerId: string,
  pointId: string,
  x: number,
  y: number,
  frame: number,
  addKeyframe: boolean = false
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as SplineData;

  if (splineData.animated && splineData.animatedControlPoints) {
    // Update animated control point
    const point = splineData.animatedControlPoints.find(p => p.id === pointId);
    if (!point) return;

    point.x.value = x;
    point.y.value = y;

    if (addKeyframe) {
      addSplinePointPositionKeyframe(store, layerId, pointId, frame);
    }

    // Also update the static version for backwards compatibility
    const staticPoint = splineData.controlPoints?.find(p => p.id === pointId);
    if (staticPoint) {
      staticPoint.x = x;
      staticPoint.y = y;
    }
  } else {
    // Update static control point
    const point = splineData.controlPoints?.find(p => p.id === pointId);
    if (!point) return;

    point.x = x;
    point.y = y;
  }

  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
}

/**
 * Get evaluated (interpolated) control points at a specific frame
 */
export function getEvaluatedSplinePoints(
  store: LayerStore,
  layerId: string,
  frame: number
): EvaluatedControlPoint[] {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return [];

  const splineData = layer.data as SplineData;

  // If not animated, return static points as evaluated
  if (!splineData.animated || !splineData.animatedControlPoints) {
    return (splineData.controlPoints || []).map(cp => ({
      id: cp.id,
      x: cp.x,
      y: cp.y,
      depth: cp.depth ?? 0,
      handleIn: cp.handleIn ? { ...cp.handleIn } : null,
      handleOut: cp.handleOut ? { ...cp.handleOut } : null,
      type: cp.type
    }));
  }

  // Evaluate animated control points at frame
  return splineData.animatedControlPoints.map(acp => {
    const x = interpolateProperty(acp.x, frame);
    const y = interpolateProperty(acp.y, frame);
    const depth = acp.depth ? interpolateProperty(acp.depth, frame) : 0;

    let handleIn: { x: number; y: number } | null = null;
    let handleOut: { x: number; y: number } | null = null;

    if (acp.handleIn) {
      handleIn = {
        x: interpolateProperty(acp.handleIn.x, frame),
        y: interpolateProperty(acp.handleIn.y, frame)
      };
    }

    if (acp.handleOut) {
      handleOut = {
        x: interpolateProperty(acp.handleOut.x, frame),
        y: interpolateProperty(acp.handleOut.y, frame)
      };
    }

    return {
      id: acp.id,
      x,
      y,
      depth,
      handleIn,
      handleOut,
      type: animatableToControlPoint(acp).type
    };
  });
}

/**
 * Check if a spline has animation enabled
 */
export function isSplineAnimated(store: LayerStore, layerId: string): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return false;

  const splineData = layer.data as SplineData;
  return !!splineData.animated;
}

/**
 * Check if a control point has any keyframes
 */
export function hasSplinePointKeyframes(store: LayerStore, layerId: string, pointId: string): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return false;

  const splineData = layer.data as SplineData;
  if (!splineData.animated || !splineData.animatedControlPoints) return false;

  const point = splineData.animatedControlPoints.find(p => p.id === pointId);
  if (!point) return false;

  // Check if any property has keyframes
  if (point.x.keyframes.length > 0) return true;
  if (point.y.keyframes.length > 0) return true;
  if (point.depth?.keyframes.length) return true;
  if (point.handleIn?.x.keyframes.length) return true;
  if (point.handleIn?.y.keyframes.length) return true;
  if (point.handleOut?.x.keyframes.length) return true;
  if (point.handleOut?.y.keyframes.length) return true;

  return false;
}

// ============================================================================
// SPLINE SIMPLIFICATION AND SMOOTHING
// ============================================================================

interface Point2D {
  x: number;
  y: number;
}

/**
 * Simplify a spline by reducing control points using Douglas-Peucker algorithm
 * @param tolerance - Distance threshold in pixels (higher = more simplification)
 */
export function simplifySpline(store: LayerStore, layerId: string, tolerance: number): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as SplineData;
  const controlPoints = splineData.controlPoints;
  if (!controlPoints || controlPoints.length <= 2) return;

  // Convert to simple points for Douglas-Peucker
  const points: Point2D[] = controlPoints.map(cp => ({ x: cp.x, y: cp.y }));

  // Apply Douglas-Peucker simplification
  const simplified = douglasPeuckerSimplify(points, tolerance);

  // Map back to original control points (keep ones that survived simplification)
  const newControlPoints: ControlPoint[] = [];
  let simplifiedIdx = 0;

  for (const cp of controlPoints) {
    // Check if this point matches a simplified point
    if (simplifiedIdx < simplified.length) {
      const sp = simplified[simplifiedIdx];
      if (Math.abs(cp.x - sp.x) < 0.01 && Math.abs(cp.y - sp.y) < 0.01) {
        newControlPoints.push(cp);
        simplifiedIdx++;
      }
    }
  }

  // Update spline data
  splineData.controlPoints = newControlPoints;

  // Also update animated control points if present
  if (splineData.animated && splineData.animatedControlPoints) {
    const newAnimatedPoints = splineData.animatedControlPoints.filter(acp =>
      newControlPoints.some(cp => cp.id === acp.id)
    );
    splineData.animatedControlPoints = newAnimatedPoints;
  }

  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);

  storeLogger.debug(`Simplified spline from ${controlPoints.length} to ${newControlPoints.length} points`);
}

/**
 * Douglas-Peucker line simplification algorithm
 */
function douglasPeuckerSimplify(points: Point2D[], tolerance: number): Point2D[] {
  if (points.length <= 2) return [...points];

  // Find point with maximum distance from line between first and last
  let maxDist = 0;
  let maxIndex = 0;

  const start = points[0];
  const end = points[points.length - 1];

  for (let i = 1; i < points.length - 1; i++) {
    const dist = perpendicularDist(points[i], start, end);
    if (dist > maxDist) {
      maxDist = dist;
      maxIndex = i;
    }
  }

  // If max distance exceeds tolerance, recursively simplify
  if (maxDist > tolerance) {
    const left = douglasPeuckerSimplify(points.slice(0, maxIndex + 1), tolerance);
    const right = douglasPeuckerSimplify(points.slice(maxIndex), tolerance);
    return [...left.slice(0, -1), ...right];
  } else {
    return [start, end];
  }
}

/**
 * Calculate perpendicular distance from point to line segment
 */
function perpendicularDist(point: Point2D, lineStart: Point2D, lineEnd: Point2D): number {
  const dx = lineEnd.x - lineStart.x;
  const dy = lineEnd.y - lineStart.y;
  const length = Math.sqrt(dx * dx + dy * dy);

  if (length < 0.0001) {
    return Math.sqrt((point.x - lineStart.x) ** 2 + (point.y - lineStart.y) ** 2);
  }

  // Project point onto line
  const t = ((point.x - lineStart.x) * dx + (point.y - lineStart.y) * dy) / (length * length);
  const closest = {
    x: lineStart.x + t * dx,
    y: lineStart.y + t * dy,
  };

  return Math.sqrt((point.x - closest.x) ** 2 + (point.y - closest.y) ** 2);
}

/**
 * Smooth spline handles to create smoother curves
 * @param amount - Smoothing amount 0-100 (100 = fully smooth bezier handles)
 */
export function smoothSplineHandles(store: LayerStore, layerId: string, amount: number): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as SplineData;
  const controlPoints = splineData.controlPoints;
  if (!controlPoints || controlPoints.length < 2) return;

  const factor = Math.max(0, Math.min(100, amount)) / 100;

  for (let i = 0; i < controlPoints.length; i++) {
    const cp = controlPoints[i];
    const prev = controlPoints[(i - 1 + controlPoints.length) % controlPoints.length];
    const next = controlPoints[(i + 1) % controlPoints.length];

    // Skip first/last point if path is not closed
    if (!splineData.closed && (i === 0 || i === controlPoints.length - 1)) {
      continue;
    }

    // Calculate direction vectors
    const toPrev = { x: prev.x - cp.x, y: prev.y - cp.y };
    const toNext = { x: next.x - cp.x, y: next.y - cp.y };

    // Average direction (tangent)
    const avgDir = { x: toNext.x - toPrev.x, y: toNext.y - toPrev.y };
    const avgLength = Math.sqrt(avgDir.x * avgDir.x + avgDir.y * avgDir.y);

    if (avgLength < 0.01) continue;

    // Normalize
    const normalized = { x: avgDir.x / avgLength, y: avgDir.y / avgLength };

    // Calculate ideal handle length (1/3 of distance to neighbors)
    const distPrev = Math.sqrt(toPrev.x * toPrev.x + toPrev.y * toPrev.y);
    const distNext = Math.sqrt(toNext.x * toNext.x + toNext.y * toNext.y);
    const handleLength = (distPrev + distNext) / 6;

    // Calculate ideal smooth handles
    const idealIn = { x: cp.x - normalized.x * handleLength, y: cp.y - normalized.y * handleLength };
    const idealOut = { x: cp.x + normalized.x * handleLength, y: cp.y + normalized.y * handleLength };

    // Blend current handles toward ideal
    if (cp.handleIn) {
      cp.handleIn = {
        x: cp.handleIn.x + (idealIn.x - cp.handleIn.x) * factor,
        y: cp.handleIn.y + (idealIn.y - cp.handleIn.y) * factor
      };
    } else {
      cp.handleIn = { x: idealIn.x * factor + cp.x * (1 - factor), y: idealIn.y * factor + cp.y * (1 - factor) };
    }

    if (cp.handleOut) {
      cp.handleOut = {
        x: cp.handleOut.x + (idealOut.x - cp.handleOut.x) * factor,
        y: cp.handleOut.y + (idealOut.y - cp.handleOut.y) * factor
      };
    } else {
      cp.handleOut = { x: idealOut.x * factor + cp.x * (1 - factor), y: idealOut.y * factor + cp.y * (1 - factor) };
    }

    // Set point type to smooth
    cp.type = 'smooth';
  }

  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);

  storeLogger.debug(`Smoothed spline handles with amount ${amount}%`);
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
