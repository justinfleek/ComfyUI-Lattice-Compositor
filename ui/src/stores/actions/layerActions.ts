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
import { createDefaultShapeLayerData, createDefaultGroup, createDefaultRectangle, createDefaultFill, createDefaultStroke } from '@/types/shapes';

// ============================================================================
// HELPERS
// ============================================================================

/**
 * Create default T-pose keypoints for COCO 18-point format (normalized 0-1)
 */
function createDefaultTPoseKeypoints(): Array<{ x: number; y: number; confidence: number }> {
  return [
    { x: 0.5, y: 0.1, confidence: 1 },    // 0: nose
    { x: 0.5, y: 0.2, confidence: 1 },    // 1: neck
    { x: 0.35, y: 0.2, confidence: 1 },   // 2: right_shoulder
    { x: 0.2, y: 0.2, confidence: 1 },    // 3: right_elbow
    { x: 0.1, y: 0.2, confidence: 1 },    // 4: right_wrist
    { x: 0.65, y: 0.2, confidence: 1 },   // 5: left_shoulder
    { x: 0.8, y: 0.2, confidence: 1 },    // 6: left_elbow
    { x: 0.9, y: 0.2, confidence: 1 },    // 7: left_wrist
    { x: 0.4, y: 0.45, confidence: 1 },   // 8: right_hip
    { x: 0.4, y: 0.65, confidence: 1 },   // 9: right_knee
    { x: 0.4, y: 0.85, confidence: 1 },   // 10: right_ankle
    { x: 0.6, y: 0.45, confidence: 1 },   // 11: left_hip
    { x: 0.6, y: 0.65, confidence: 1 },   // 12: left_knee
    { x: 0.6, y: 0.85, confidence: 1 },   // 13: left_ankle
    { x: 0.45, y: 0.08, confidence: 1 },  // 14: right_eye
    { x: 0.55, y: 0.08, confidence: 1 },  // 15: left_eye
    { x: 0.4, y: 0.1, confidence: 1 },    // 16: right_ear
    { x: 0.6, y: 0.1, confidence: 1 },    // 17: left_ear
  ];
}

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
        turbulenceFields: [],
        subEmitters: [],
        collision: {
          enabled: false,
          particleCollision: false,
          particleRadius: 5,
          bounciness: 0.8,
          friction: 0.1,
          boundaryEnabled: true,
          boundaryBehavior: 'bounce',
          boundaryPadding: 0
        },
        flocking: {
          enabled: false,
          separationWeight: 50,
          separationRadius: 30,
          alignmentWeight: 50,
          alignmentRadius: 50,
          cohesionWeight: 50,
          cohesionRadius: 50,
          maxSpeed: 10,
          maxForce: 0.5,
          perceptionAngle: 270
        },
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
      // Use proper ShapeLayerData structure with contents array
      // Shape layers contain groups which contain generators (rect, ellipse) + modifiers (fill, stroke)
      layerData = createDefaultShapeLayerData();
      // Add a default group with rectangle + fill + stroke as starter content
      const defaultGroup = createDefaultGroup();
      defaultGroup.name = 'Group 1';
      defaultGroup.contents = [
        createDefaultRectangle(),
        createDefaultFill(),
        createDefaultStroke()
      ];
      layerData.contents = [defaultGroup];
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
        matteType: 'luminance' as const,
        invert: false,
        threshold: 0.5,
        feather: 0,
        expansion: 0,
        sourceLayerId: null,
        previewMode: 'matte' as const
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
        size: 50,
        showAxes: true,
        showIcon: true,
        iconShape: 'crosshair' as const,
        iconColor: '#ffcc00'
      };
      break;

    case 'pose':
      // OpenPose skeleton layer for ControlNet conditioning
      layerData = {
        poses: [{
          id: `pose-${Date.now()}`,
          format: 'coco18' as const,
          keypoints: createDefaultTPoseKeypoints(),
        }],
        format: 'coco18' as const,
        normalized: true,
        boneWidth: 4,
        keypointRadius: 4,
        showKeypoints: true,
        showBones: true,
        showLabels: false,
        useDefaultColors: true,
        customBoneColor: '#FFFFFF',
        customKeypointColor: '#FF0000',
        selectedKeypoint: -1,
        selectedPose: 0,
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

    case 'adjustment':
      // Adjustment/Effect layer - applies effects to layers below
      layerData = {
        color: '#808080',
        effectLayer: true,
        adjustmentLayer: true  // Backwards compatibility
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

  // Initialize layer-specific properties
  let layerProperties: AnimatableProperty<any>[] = [];

  // Spline layer properties for timeline
  // Note: Splines don't have Fill (only shapes/text do) - they only have stroke
  if (type === 'spline') {
    layerProperties = [
      createAnimatableProperty('Stroke Width', layerData?.strokeWidth ?? 2, 'number', 'Stroke'),
      createAnimatableProperty('Stroke Opacity', layerData?.strokeOpacity ?? 100, 'number', 'Stroke'),
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
  store.pushHistory();
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
 * Replace layer source with a new asset (Alt+drag replacement)
 * Keeps all keyframes, effects, and transforms
 */
export function replaceLayerSource(
  store: LayerStore,
  layerId: string,
  newSource: { type: string; name: string; path?: string; id?: string; assetId?: string; data?: any }
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  // Use assetId if provided, otherwise use id as assetId
  const assetId = newSource.assetId || newSource.id || null;

  // Determine source update based on layer type and new source type
  if (layer.type === 'image' && newSource.type === 'asset' && assetId) {
    // Replace image source - preserve existing data, update assetId
    (layer.data as any).assetId = assetId;
    layer.name = newSource.name || layer.name;
  } else if (layer.type === 'video' && newSource.type === 'asset' && assetId) {
    // Replace video source - preserve existing data, update assetId
    (layer.data as any).assetId = assetId;
    layer.name = newSource.name || layer.name;
  } else if (layer.type === 'solid' && newSource.type === 'asset' && assetId) {
    // Convert solid to image layer (source replacement changes type)
    layer.type = 'image' as any;
    layer.data = { assetId, fit: 'none' as const } as any;
    layer.name = newSource.name || layer.name;
  } else if (layer.type === 'nestedComp' && newSource.type === 'composition' && newSource.id) {
    // Replace nested comp source - preserve existing data, update compositionId
    (layer.data as any).compositionId = newSource.id;
    layer.name = newSource.name || layer.name;
  } else if (newSource.type === 'composition' && newSource.id) {
    // Convert any layer to nested comp
    layer.type = 'nestedComp' as any;
    layer.data = { compositionId: newSource.id, speedMapEnabled: false, flattenTransform: false, overrideFrameRate: false } as any;
    layer.name = newSource.name || layer.name;
  } else if (newSource.type === 'asset' && assetId) {
    // Generic asset replacement - determine new type from asset or file extension
    const path = newSource.path || '';
    const ext = path.split('.').pop()?.toLowerCase() || '';
    const imageExts = ['png', 'jpg', 'jpeg', 'gif', 'webp', 'svg'];
    const videoExts = ['mp4', 'webm', 'mov', 'avi'];

    if (imageExts.includes(ext)) {
      layer.type = 'image' as any;
      layer.data = { assetId, fit: 'none' as const } as any;
    } else if (videoExts.includes(ext)) {
      layer.type = 'video' as any;
      layer.data = {
        assetId,
        loop: true,
        pingPong: false,
        startTime: 0,
        speed: 1,
        speedMapEnabled: false,
        frameBlending: 'none' as const,
        audioEnabled: true,
        audioLevel: 100,
        posterFrame: 0
      } as any;
    }
    layer.name = newSource.name || layer.name;
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
  console.log(`[Weyl] Replaced layer source: ${layer.name}`);
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
  // Cast to any to allow assignment - structure is correct but TS doesn't fully match
  // due to optional spatial tangent fields
  targetLayer.transform.position.keyframes = keyframes as any;

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

// ============================================================================
// TIME MANIPULATION ACTIONS
// ============================================================================

export interface TimeStretchOptions {
  stretchFactor: number;           // 100% = normal, 200% = half speed, 50% = double speed
  holdInPlace: 'in-point' | 'current-frame' | 'out-point';
  reverse: boolean;
  newStartFrame: number;
  newEndFrame: number;
  speed: number;                   // Computed speed value (100 / stretchFactor)
}

/**
 * Apply time stretch to a video or nested comp layer
 * Adjusts layer timing based on stretch factor and hold-in-place pivot
 */
export function timeStretchLayer(
  store: LayerStore,
  layerId: string,
  options: TimeStretchOptions
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    storeLogger.warn('Layer not found for time stretch:', layerId);
    return;
  }

  // Only works for video and nested comp layers
  if (layer.type !== 'video' && layer.type !== 'nestedComp') {
    storeLogger.warn('Time stretch only works on video/nestedComp layers');
    return;
  }

  store.pushHistory();

  // Update layer timing
  layer.startFrame = options.newStartFrame;
  layer.endFrame = options.newEndFrame;

  // Update speed in layer data
  if (layer.data) {
    const data = layer.data as any;
    data.speed = options.speed;
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();

  storeLogger.debug(
    `Time stretched layer ${layer.name}: ${options.stretchFactor}% ` +
    `(speed: ${options.speed.toFixed(2)}, hold: ${options.holdInPlace})`
  );
}

/**
 * Reverse layer playback
 * Toggles the speed sign for video/nested comp layers
 */
export function reverseLayer(store: LayerStore, layerId: string): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    storeLogger.warn('Layer not found for reverse:', layerId);
    return;
  }

  if (layer.type !== 'video' && layer.type !== 'nestedComp') {
    storeLogger.warn('Reverse only works on video/nestedComp layers');
    return;
  }

  store.pushHistory();

  if (layer.data) {
    const data = layer.data as any;
    // Negate speed to reverse
    data.speed = -(data.speed ?? 1);
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Reversed layer: ${layer.name}`);
}

/**
 * Create a freeze frame at the current playhead position
 * Uses speedMap with hold keyframes to freeze at a specific source time
 */
export function freezeFrameAtPlayhead(
  store: LayerStore & { currentFrame: number; fps: number },
  layerId: string
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    storeLogger.warn('Layer not found for freeze frame:', layerId);
    return;
  }

  if (layer.type !== 'video' && layer.type !== 'nestedComp') {
    storeLogger.warn('Freeze frame only works on video/nestedComp layers');
    return;
  }

  store.pushHistory();

  const currentFrame = store.currentFrame ?? 0;
  const fps = store.fps ?? 30;
  const sourceTime = currentFrame / fps;

  if (layer.data) {
    const data = layer.data as any;

    // Enable speed map if not already
    data.speedMapEnabled = true;

    // Create or update speed map with freeze frame
    if (!data.speedMap) {
      data.speedMap = createAnimatableProperty('Speed Map', sourceTime, 'number');
    }

    // Clear existing keyframes and add freeze frame keyframes
    data.speedMap.keyframes = [
      {
        id: `kf_freeze_start_${Date.now()}`,
        frame: currentFrame,
        value: sourceTime,
        interpolation: 'hold' as const,
        controlMode: 'linked' as const,
        inHandle: { frame: -5, value: 0, enabled: true },
        outHandle: { frame: 5, value: 0, enabled: true }
      },
      {
        id: `kf_freeze_end_${Date.now() + 1}`,
        frame: (layer.endFrame ?? store.getActiveComp()?.settings.frameCount ?? 81) - 1,
        value: sourceTime,
        interpolation: 'hold' as const,
        controlMode: 'linked' as const,
        inHandle: { frame: -5, value: 0, enabled: true },
        outHandle: { frame: 5, value: 0, enabled: true }
      }
    ];

    data.speedMap.value = sourceTime;
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Created freeze frame on ${layer.name} at frame ${currentFrame}`);
}

/**
 * Split layer at the current playhead position
 * Creates two layers: one ending at playhead, one starting at playhead
 */
export function splitLayerAtPlayhead(
  store: LayerStore & { currentFrame: number },
  layerId: string
): Layer | null {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    storeLogger.warn('Layer not found for split:', layerId);
    return null;
  }

  const currentFrame = store.currentFrame ?? 0;
  const startFrame = layer.startFrame ?? 0;
  const endFrame = layer.endFrame ?? store.getActiveComp()?.settings.frameCount ?? 81;

  // Can't split outside layer bounds
  if (currentFrame <= startFrame || currentFrame >= endFrame) {
    storeLogger.warn('Split point must be within layer bounds');
    return null;
  }

  store.pushHistory();

  // Create new layer as copy of original
  const newLayerId = `layer_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  const newLayer: Layer = {
    ...JSON.parse(JSON.stringify(layer)),
    id: newLayerId,
    name: `${layer.name} (split)`
  };

  // Original layer ends at playhead
  layer.endFrame = currentFrame;

  // New layer starts at playhead
  newLayer.startFrame = currentFrame;
  newLayer.endFrame = endFrame;

  // Adjust source time for video layers
  if ((layer.type === 'video' || layer.type === 'nestedComp') && newLayer.data) {
    const data = newLayer.data as any;
    const fps = 30; // Default FPS
    const originalStartTime = data.startTime ?? 0;
    const speed = data.speed ?? 1;

    // Calculate new source start time based on split point
    const frameOffset = currentFrame - startFrame;
    const timeOffset = (frameOffset / fps) * speed;
    data.startTime = originalStartTime + timeOffset;
  }

  // Add new layer after original
  const layers = store.getActiveCompLayers();
  const originalIndex = layers.findIndex(l => l.id === layerId);
  layers.splice(originalIndex + 1, 0, newLayer);

  markLayerDirty(layerId);
  markLayerDirty(newLayerId);
  store.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Split layer ${layer.name} at frame ${currentFrame}`);

  return newLayer;
}
