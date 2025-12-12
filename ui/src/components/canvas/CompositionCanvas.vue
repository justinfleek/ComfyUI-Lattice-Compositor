<template>
  <div class="composition-canvas" ref="containerRef">
    <canvas ref="canvasRef" />

    <!-- Spline Editor overlay (when pen tool is active) -->
    <SplineEditor
      v-if="activeSplineLayerId || isPenMode"
      :layerId="activeSplineLayerId"
      :canvasWidth="canvasWidth"
      :canvasHeight="canvasHeight"
      :zoom="zoom"
      :viewportTransform="viewportTransformArray"
      :isPenMode="isPenMode"
      @pointAdded="onPointAdded"
      @pathUpdated="onPathUpdated"
      ref="splineEditorRef"
    />

    <!-- Zoom controls -->
    <div class="zoom-controls">
      <button @click="zoomIn" title="Zoom In">+</button>
      <span class="zoom-level">{{ Math.round(zoom * 100) }}%</span>
      <button @click="zoomOut" title="Zoom Out">-</button>
      <button @click="fitToView" title="Fit to View">Fit</button>
    </div>

    <!-- Depth overlay toggle -->
    <div class="overlay-controls" v-if="hasDepthMap">
      <label>
        <input type="checkbox" v-model="showDepthOverlay" />
        Depth Overlay
      </label>
      <select v-model="depthColormap" class="colormap-select">
        <option value="viridis">Viridis</option>
        <option value="plasma">Plasma</option>
        <option value="grayscale">Grayscale</option>
      </select>
      <input
        type="range"
        min="0"
        max="100"
        v-model.number="depthOpacity"
        class="opacity-slider"
      />
    </div>

    <!-- Loading overlay -->
    <div class="loading-overlay" v-if="loading">
      <div class="loading-spinner"></div>
      <span>Loading...</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, onMounted, onUnmounted, watch, computed, nextTick } from 'vue';
import { Canvas, FabricImage, Point, Rect, type FabricObject } from 'fabric';
import { useCompositorStore } from '@/stores/compositorStore';
import { DepthMapImage, type ColormapType } from '@/fabric/DepthMapImage';
import { SplinePath } from '@/fabric/SplinePath';
import { AnimatedText } from '@/fabric/AnimatedText';
import SplineEditor from './SplineEditor.vue';
import type { SplineData, ControlPoint, ParticleLayerData, DepthflowLayerData, TextData } from '@/types/project';
import { ParticleSystem } from '@/services/particleSystem';
import { DepthflowRenderer } from '@/services/depthflow';
import type { PathAnimatorState } from '@/services/audioPathAnimator';

// Store
const store = useCompositorStore();

// Refs
const containerRef = ref<HTMLDivElement | null>(null);
const canvasRef = ref<HTMLCanvasElement | null>(null);
const splineEditorRef = ref<InstanceType<typeof SplineEditor> | null>(null);

// State
const fabricCanvas = ref<Canvas | null>(null);
const sourceImageObj = ref<FabricImage | null>(null);
const depthMapObj = ref<DepthMapImage | null>(null);
const splineObjects = ref<Map<string, SplinePath>>(new Map());
const textObjects = ref<Map<string, AnimatedText>>(new Map());
const compositionBounds = ref<Rect | null>(null);
const loading = ref(false);
const zoom = ref(1);
const showDepthOverlay = ref(true);
const depthColormap = ref<ColormapType>('viridis');
const depthOpacity = ref(50);
const canvasWidth = ref(800);
const canvasHeight = ref(600);

// Particle and Depthflow systems
const particleSystems = ref<Map<string, ParticleSystem>>(new Map());
const depthflowRenderers = ref<Map<string, DepthflowRenderer>>(new Map());
const particleCanvas = ref<HTMLCanvasElement | null>(null);
const particleCtx = ref<CanvasRenderingContext2D | null>(null);
const animationFrameId = ref<number | null>(null);

// Path animation state cache (for text-on-path with audio)
const pathAnimationStates = ref<Map<string, PathAnimatorState>>(new Map());

// Computed
const hasDepthMap = computed(() => store.depthMap !== null);
const isPenMode = computed(() => store.currentTool === 'pen');

// Active spline layer (selected spline or new spline being drawn)
const activeSplineLayerId = computed(() => {
  const selectedLayer = store.selectedLayer;
  if (selectedLayer?.type === 'spline') {
    return selectedLayer.id;
  }
  // If in pen mode but no spline selected, create one
  if (isPenMode.value && store.layers.filter(l => l.type === 'spline').length === 0) {
    return null;
  }
  // Return most recent spline if in pen mode
  if (isPenMode.value) {
    const splines = store.layers.filter(l => l.type === 'spline');
    return splines.length > 0 ? splines[splines.length - 1].id : null;
  }
  return null;
});

// Viewport transform as array for SplineEditor
const viewportTransformArray = computed(() => {
  const vpt = fabricCanvas.value?.viewportTransform;
  return vpt ? Array.from(vpt) : [1, 0, 0, 1, 0, 0];
});

// Initialize Fabric.js canvas
onMounted(() => {
  console.log('[CompositionCanvas] onMounted called');
  console.log('[CompositionCanvas] canvasRef:', canvasRef.value);
  console.log('[CompositionCanvas] containerRef:', containerRef.value);

  if (!canvasRef.value || !containerRef.value) {
    console.error('[CompositionCanvas] Missing refs - canvasRef:', !!canvasRef.value, 'containerRef:', !!containerRef.value);
    return;
  }

  const container = containerRef.value;
  const rect = container.getBoundingClientRect();
  console.log('[CompositionCanvas] Container rect:', rect.width, 'x', rect.height);

  canvasWidth.value = rect.width;
  canvasHeight.value = rect.height;

  fabricCanvas.value = new Canvas(canvasRef.value, {
    width: rect.width,
    height: rect.height,
    backgroundColor: '#1a1a1a',
    selection: true,
    preserveObjectStacking: true
  });

  console.log('[CompositionCanvas] Fabric canvas created:', fabricCanvas.value);
  console.log('[CompositionCanvas] Store dimensions:', store.width, 'x', store.height);

  // Enable zoom/pan
  setupZoomPan();

  // Add composition bounds rectangle (visible frame boundary)
  // Use nextTick to ensure DOM has fully rendered with proper dimensions
  nextTick(() => {
    createCompositionBounds();
  });

  // Handle resize
  const resizeObserver = new ResizeObserver(handleResize);
  resizeObserver.observe(container);

  // Watch for input changes from ComfyUI
  watch(() => store.sourceImage, loadSourceImage, { immediate: true });
  watch(() => store.depthMap, loadDepthMap, { immediate: true });

  // Watch for layer changes to render splines
  watch(() => store.layers, renderSplineLayers, { deep: true, immediate: true });

  // Watch for text layers
  watch(() => store.layers, renderTextLayers, { deep: true, immediate: true });

  // Watch for particle layers
  watch(() => store.layers, syncParticleSystems, { deep: true, immediate: true });

  // Watch for depthflow layers
  watch(() => store.layers, syncDepthflowRenderers, { deep: true, immediate: true });

  // Watch for composition size changes
  watch(() => [store.width, store.height], updateCompositionBounds, { immediate: false });

  // Create particle overlay canvas
  particleCanvas.value = document.createElement('canvas');
  particleCtx.value = particleCanvas.value.getContext('2d');

  // Start render loop
  startRenderLoop();

  console.log('[CompositionCanvas] Initialization complete');
});

onUnmounted(() => {
  // Stop render loop
  if (animationFrameId.value !== null) {
    cancelAnimationFrame(animationFrameId.value);
  }

  // Dispose particle systems
  particleSystems.value.forEach(system => {
    system.reset();
  });
  particleSystems.value.clear();

  // Dispose depthflow renderers
  depthflowRenderers.value.forEach(renderer => {
    renderer.dispose();
  });
  depthflowRenderers.value.clear();

  // Clear text objects
  textObjects.value.clear();

  // Clear spline objects
  splineObjects.value.clear();

  fabricCanvas.value?.dispose();
});

// Setup zoom and pan controls
function setupZoomPan() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;

  // Mouse wheel zoom
  canvas.on('mouse:wheel', (opt) => {
    const delta = opt.e.deltaY;
    let newZoom = canvas.getZoom() * (delta > 0 ? 0.9 : 1.1);
    newZoom = Math.min(Math.max(newZoom, 0.1), 10);

    const point = new Point(opt.e.offsetX, opt.e.offsetY);
    canvas.zoomToPoint(point, newZoom);
    zoom.value = newZoom;

    opt.e.preventDefault();
    opt.e.stopPropagation();
  });

  // Pan with middle mouse button or alt + drag
  let isPanning = false;
  let lastPosX = 0;
  let lastPosY = 0;

  canvas.on('mouse:down', (opt) => {
    const evt = opt.e as MouseEvent;
    if (evt.button === 1 || (evt.button === 0 && evt.altKey)) {
      isPanning = true;
      lastPosX = evt.clientX;
      lastPosY = evt.clientY;
      canvas.selection = false;
    }
  });

  canvas.on('mouse:move', (opt) => {
    if (isPanning) {
      const evt = opt.e as MouseEvent;
      const vpt = canvas.viewportTransform;
      if (vpt) {
        vpt[4] += evt.clientX - lastPosX;
        vpt[5] += evt.clientY - lastPosY;
        canvas.requestRenderAll();
      }
      lastPosX = evt.clientX;
      lastPosY = evt.clientY;
    }
  });

  canvas.on('mouse:up', () => {
    if (isPanning) {
      isPanning = false;
      canvas.selection = true;
    }
  });

  // Object selection
  canvas.on('selection:created', (e) => {
    const selected = e.selected?.[0];
    if (selected && (selected as any).layerId) {
      store.selectLayer((selected as any).layerId);
    }
  });
}

// Create composition bounds rectangle (visible frame boundary)
function createCompositionBounds() {
  const canvas = fabricCanvas.value;
  if (!canvas) {
    console.error('[CompositionCanvas] createCompositionBounds - no canvas');
    return;
  }

  // Use store dimensions or defaults
  const compWidth = store.width || 1920;
  const compHeight = store.height || 1080;

  console.log('[CompositionCanvas] Creating bounds:', compWidth, 'x', compHeight);

  // Remove existing bounds if any
  if (compositionBounds.value) {
    canvas.remove(compositionBounds.value as unknown as FabricObject);
  }

  // Create the bounds rectangle
  compositionBounds.value = new Rect({
    left: 0,
    top: 0,
    width: compWidth,
    height: compHeight,
    fill: '#2a2a2a',  // Dark fill so we can see it
    stroke: '#4a90d9',  // Blue border
    strokeWidth: 2,
    selectable: false,
    evented: false,
    strokeUniform: true,  // Keep stroke width consistent at any zoom
  });

  canvas.add(compositionBounds.value as unknown as FabricObject);
  canvas.sendObjectToBack(compositionBounds.value as unknown as FabricObject);

  console.log('[CompositionCanvas] Bounds added, object count:', canvas.getObjects().length);

  // Center the view on the composition
  centerOnComposition();

  canvas.requestRenderAll();
}

// Update composition bounds when size changes
function updateCompositionBounds() {
  const canvas = fabricCanvas.value;
  if (!canvas || !compositionBounds.value) return;

  const compWidth = store.width || 1920;
  const compHeight = store.height || 1080;

  console.log('[CompositionCanvas] Updating bounds:', compWidth, 'x', compHeight);

  compositionBounds.value.set({
    width: compWidth,
    height: compHeight,
  });

  compositionBounds.value.setCoords();
  centerOnComposition();
  canvas.requestRenderAll();
}

// Center the viewport on the composition
function centerOnComposition() {
  const canvas = fabricCanvas.value;
  const container = containerRef.value;
  if (!canvas || !container) return;

  const compWidth = store.width || 1920;
  const compHeight = store.height || 1080;

  const containerRect = container.getBoundingClientRect();

  // Calculate zoom to fit with padding
  const padding = 60;
  const scaleX = (containerRect.width - padding * 2) / compWidth;
  const scaleY = (containerRect.height - padding * 2) / compHeight;
  const scale = Math.min(scaleX, scaleY, 1);

  // Center the composition
  const vpt = canvas.viewportTransform;
  if (vpt) {
    vpt[0] = scale;
    vpt[3] = scale;
    vpt[4] = (containerRect.width - compWidth * scale) / 2;
    vpt[5] = (containerRect.height - compHeight * scale) / 2;
  }

  zoom.value = scale;

  console.log('[CompositionCanvas] Centered at zoom:', scale);
}

// Handle container resize
function handleResize(entries: ResizeObserverEntry[]) {
  const canvas = fabricCanvas.value;
  if (!canvas) return;

  for (const entry of entries) {
    const { width, height } = entry.contentRect;
    canvas.setDimensions({ width, height });
    canvasWidth.value = width;
    canvasHeight.value = height;
    canvas.requestRenderAll();
  }
}

// Load source image from store
async function loadSourceImage(imageData: string | null) {
  const canvas = fabricCanvas.value;
  if (!canvas || !imageData) return;

  loading.value = true;

  try {
    // Remove existing source image
    if (sourceImageObj.value) {
      canvas.remove(sourceImageObj.value as unknown as FabricObject);
    }

    // Load new image
    const img = await loadImage(imageData);
    sourceImageObj.value = new FabricImage(img, {
      selectable: false,
      evented: false,
      left: 0,
      top: 0
    });

    canvas.add(sourceImageObj.value as unknown as FabricObject);
    canvas.sendObjectToBack(sourceImageObj.value as unknown as FabricObject);

    // Fit to view
    fitToView();
  } catch (err) {
    console.error('[CompositionCanvas] Failed to load source image:', err);
  } finally {
    loading.value = false;
  }
}

// Load depth map from store
async function loadDepthMap(depthData: string | null) {
  const canvas = fabricCanvas.value;
  if (!canvas || !depthData) return;

  try {
    // Remove existing depth map
    if (depthMapObj.value) {
      canvas.remove(depthMapObj.value as unknown as FabricObject);
    }

    // Load depth map with colorization
    depthMapObj.value = await DepthMapImage.fromBase64(depthData, {
      colormap: depthColormap.value,
      opacity: depthOpacity.value / 100,
      visible: showDepthOverlay.value
    });

    depthMapObj.value.set({
      selectable: false,
      evented: false,
      left: 0,
      top: 0
    });

    canvas.add(depthMapObj.value as unknown as FabricObject);

    // Position depth map above source but below other layers
    if (sourceImageObj.value) {
      const sourceIndex = canvas.getObjects().indexOf(sourceImageObj.value as unknown as FabricObject);
      canvas.moveObjectTo(depthMapObj.value as unknown as FabricObject, sourceIndex + 1);
    }

    canvas.requestRenderAll();
  } catch (err) {
    console.error('[CompositionCanvas] Failed to load depth map:', err);
  }
}

// Helper to get the current value from an AnimatableProperty
// For now, just return the base value - keyframe interpolation can be added later
function getAnimatedValue<T>(prop: { value: T; animated?: boolean; keyframes?: any[] } | undefined, defaultValue: T): T {
  if (!prop) return defaultValue;
  // TODO: If prop.animated && prop.keyframes.length > 0, interpolate based on store.currentFrame
  return prop.value ?? defaultValue;
}

// Render spline layers from store
function renderSplineLayers() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;

  const splineLayers = store.layers.filter(l => l.type === 'spline');

  // Update or create spline objects
  for (const layer of splineLayers) {
    const splineData = layer.data as SplineData | null;
    if (!splineData) continue;

    let splineObj = splineObjects.value.get(layer.id);

    // Get transform values from layer.transform (AnimatableProperty structure)
    const position = getAnimatedValue(layer.transform?.position, { x: 0, y: 0 });
    const scale = getAnimatedValue(layer.transform?.scale, { x: 1, y: 1 });
    const rotation = getAnimatedValue(layer.transform?.rotation, 0);
    const opacity = getAnimatedValue(layer.opacity, 1);

    if (!splineObj) {
      // Create new SplinePath
      splineObj = new SplinePath('', {
        stroke: splineData.stroke || '#00ff00',
        strokeWidth: splineData.strokeWidth || 2,
        fill: splineData.fill || '',
        controlPoints: splineData.controlPoints || [],
        selectable: !layer.locked
      });
      (splineObj as any).layerId = layer.id;

      splineObjects.value.set(layer.id, splineObj);
      canvas.add(splineObj as unknown as FabricObject);
    } else {
      // Update existing
      splineObj.controlPoints = splineData.controlPoints || [];
      splineObj.set({
        stroke: splineData.stroke,
        strokeWidth: splineData.strokeWidth,
        fill: splineData.fill
      });
    }

    // Apply transform and visibility (always update these)
    splineObj.set({
      left: position.x,
      top: position.y,
      scaleX: scale.x,
      scaleY: scale.y,
      angle: rotation,
      opacity: opacity,
      visible: layer.visible,
      selectable: !layer.locked
    });

    splineObj.updatePathFromControlPoints();
    splineObj.setCoords();
  }

  // Remove deleted splines
  const layerIds = new Set(splineLayers.map(l => l.id));
  for (const [id, obj] of splineObjects.value) {
    if (!layerIds.has(id)) {
      canvas.remove(obj as unknown as FabricObject);
      splineObjects.value.delete(id);
    }
  }

  canvas.requestRenderAll();
}

// Render text layers from store
function renderTextLayers() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;

  const textLayers = store.layers.filter(l => l.type === 'text');

  // Update or create text objects
  for (const layer of textLayers) {
    const textData = layer.data as TextData | null;
    if (!textData) continue;

    let textObj = textObjects.value.get(layer.id);

    // Get transform values from layer.transform (AnimatableProperty structure)
    const position = getAnimatedValue(layer.transform?.position, { x: 0, y: 0 });
    const scale = getAnimatedValue(layer.transform?.scale, { x: 1, y: 1 });
    const rotation = getAnimatedValue(layer.transform?.rotation, 0);
    const anchor = layer.transform?.anchor ?? { x: 0, y: 0 };
    const opacity = getAnimatedValue(layer.opacity, 1);

    // Default position is center of composition
    const centerX = (store.width || 1920) / 2;
    const centerY = (store.height || 1080) / 2;
    const posX = position.x || centerX;
    const posY = position.y || centerY;

    if (!textObj) {
      // Create new AnimatedText
      textObj = new AnimatedText({
        text: textData.text || 'Text',
        fontFamily: textData.fontFamily || 'Arial',
        fontSize: textData.fontSize || 48,
        fontWeight: textData.fontWeight || '400',
        fill: textData.fill || '#ffffff',
        stroke: textData.stroke || '',
        strokeWidth: textData.strokeWidth || 0,
        letterSpacing: textData.letterSpacing || 0,
        pathLayerId: textData.pathLayerId,
        pathOffset: textData.pathOffset || 0,
        selectable: !layer.locked
      });
      (textObj as any).layerId = layer.id;

      textObjects.value.set(layer.id, textObj);
      canvas.add(textObj as unknown as FabricObject);
    } else {
      // Update existing text object
      if (textData.text !== textObj.textContent) {
        textObj.setText(textData.text || 'Text');
      }

      // Update font if changed
      if (textData.fontFamily !== textObj.fontFamily ||
          textData.fontSize !== textObj.fontSize ||
          textData.fontWeight !== textObj.fontWeight) {
        textObj.setFont(
          textData.fontFamily || 'Arial',
          textData.fontSize || 48,
          textData.fontWeight || '400'
        );
      }

      // Update colors
      if (textData.fill !== textObj.textFill) {
        textObj.setFillColor(textData.fill || '#ffffff');
      }

      if (textData.stroke !== textObj.textStroke ||
          textData.strokeWidth !== textObj.textStrokeWidth) {
        textObj.setStroke(textData.stroke || '', textData.strokeWidth || 0);
      }

      // Update letter spacing
      if (textData.letterSpacing !== textObj.letterSpacing) {
        textObj.setLetterSpacing(textData.letterSpacing || 0);
      }

      // Update path binding
      textObj.pathLayerId = textData.pathLayerId || null;
      textObj.pathOffset = textData.pathOffset || 0;
    }

    // Apply transform and visibility (always update these)
    textObj.set({
      left: posX,
      top: posY,
      originX: 'center',
      originY: 'center',
      scaleX: scale.x,
      scaleY: scale.y,
      angle: rotation,
      opacity: opacity,
      visible: layer.visible,
      selectable: !layer.locked
    });

    textObj.setCoords();
  }

  // Remove deleted text layers
  const layerIds = new Set(textLayers.map(l => l.id));
  for (const [id, obj] of textObjects.value) {
    if (!layerIds.has(id)) {
      canvas.remove(obj as unknown as FabricObject);
      textObjects.value.delete(id);
    }
  }

  canvas.requestRenderAll();
}

// Handle spline editor events
function onPointAdded(_point: ControlPoint) {
  // If no active spline layer, create one
  if (!activeSplineLayerId.value) {
    const newLayer = store.createLayer('spline');
    store.selectLayer(newLayer.id);
  }
}

function onPathUpdated() {
  // Re-render splines when path is updated
  renderSplineLayers();
}

// Watch depth overlay settings
watch(showDepthOverlay, (visible) => {
  if (depthMapObj.value) {
    depthMapObj.value.set('visible', visible);
    fabricCanvas.value?.requestRenderAll();
  }
});

watch(depthColormap, (colormap) => {
  if (depthMapObj.value) {
    depthMapObj.value.setColormap(colormap);
  }
});

watch(depthOpacity, (opacity) => {
  if (depthMapObj.value) {
    depthMapObj.value.set('opacity', opacity / 100);
    fabricCanvas.value?.requestRenderAll();
  }
});

// Helper to load image from data URL or base64
function loadImage(src: string): Promise<HTMLImageElement> {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.crossOrigin = 'anonymous';
    img.onload = () => resolve(img);
    img.onerror = reject;
    img.src = src.startsWith('data:') ? src : `data:image/png;base64,${src}`;
  });
}

// Zoom controls
function zoomIn() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;

  const newZoom = Math.min(canvas.getZoom() * 1.2, 10);
  canvas.setZoom(newZoom);
  zoom.value = newZoom;
}

function zoomOut() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;

  const newZoom = Math.max(canvas.getZoom() * 0.8, 0.1);
  canvas.setZoom(newZoom);
  zoom.value = newZoom;
}

function fitToView() {
  const canvas = fabricCanvas.value;
  const container = containerRef.value;
  if (!canvas || !container || !sourceImageObj.value) return;

  const rect = container.getBoundingClientRect();
  const imgWidth = sourceImageObj.value.width || 1;
  const imgHeight = sourceImageObj.value.height || 1;

  // Calculate zoom to fit with padding
  const padding = 40;
  const scaleX = (rect.width - padding * 2) / imgWidth;
  const scaleY = (rect.height - padding * 2) / imgHeight;
  const scale = Math.min(scaleX, scaleY, 1);

  // Center the image
  const vpt = canvas.viewportTransform;
  if (vpt) {
    vpt[0] = scale;
    vpt[3] = scale;
    vpt[4] = (rect.width - imgWidth * scale) / 2;
    vpt[5] = (rect.height - imgHeight * scale) / 2;
  }

  zoom.value = scale;
  canvas.requestRenderAll();
}

// ============================================================
// PARTICLE SYSTEM FUNCTIONS
// ============================================================

function syncParticleSystems() {
  const particleLayers = store.layers.filter(l => l.type === 'particles');
  const layerIds = new Set(particleLayers.map(l => l.id));

  // Create new systems for new layers
  for (const layer of particleLayers) {
    if (!particleSystems.value.has(layer.id)) {
      const data = layer.data as ParticleLayerData | null;
      if (data) {
        const system = new ParticleSystem(data.systemConfig);

        // Add emitters
        for (const emitter of data.emitters) {
          system.addEmitter(emitter);
        }

        // Add gravity wells
        for (const well of data.gravityWells) {
          system.addGravityWell(well);
        }

        // Add vortices
        for (const vortex of data.vortices) {
          system.addVortex(vortex);
        }

        // Add modulations
        for (const mod of data.modulations) {
          system.addModulation(mod);
        }

        particleSystems.value.set(layer.id, system);
      }
    } else {
      // Update existing system
      const system = particleSystems.value.get(layer.id)!;
      const data = layer.data as ParticleLayerData | null;

      if (data) {
        system.setConfig(data.systemConfig);

        // Sync emitters (simplified - full sync would track individual changes)
        const currentEmitters = system.getEmitters();
        for (const emitter of data.emitters) {
          const existing = currentEmitters.find(e => e.id === emitter.id);
          if (existing) {
            system.updateEmitter(emitter.id, emitter);
          } else {
            system.addEmitter(emitter);
          }
        }
      }
    }
  }

  // Remove systems for deleted layers
  for (const [id] of particleSystems.value) {
    if (!layerIds.has(id)) {
      particleSystems.value.get(id)?.reset();
      particleSystems.value.delete(id);
    }
  }
}

function syncDepthflowRenderers() {
  const depthflowLayers = store.layers.filter(l => l.type === 'depthflow');
  const layerIds = new Set(depthflowLayers.map(l => l.id));

  // Create new renderers for new layers
  for (const layer of depthflowLayers) {
    if (!depthflowRenderers.value.has(layer.id)) {
      const data = layer.data as DepthflowLayerData | null;
      if (data) {
        const renderer = new DepthflowRenderer();
        renderer.setConfig(data.config);
        depthflowRenderers.value.set(layer.id, renderer);
      }
    } else {
      // Update existing renderer config
      const renderer = depthflowRenderers.value.get(layer.id)!;
      const data = layer.data as DepthflowLayerData | null;
      if (data) {
        renderer.setConfig(data.config);
      }
    }
  }

  // Remove renderers for deleted layers
  for (const [id] of depthflowRenderers.value) {
    if (!layerIds.has(id)) {
      depthflowRenderers.value.get(id)?.dispose();
      depthflowRenderers.value.delete(id);
    }
  }
}

function startRenderLoop() {
  const renderFrame = () => {
    // Update path animators with current audio values
    if (store.isPlaying || store.audioAnalysis) {
      updatePathAnimators();
    }

    // Update particle systems during playback
    if (store.isPlaying) {
      updateParticleSystems();
    }

    // Render particles on top of fabric canvas
    renderParticles();

    // Render text-on-path with audio animation
    renderTextOnPathAudio();

    animationFrameId.value = requestAnimationFrame(renderFrame);
  };

  animationFrameId.value = requestAnimationFrame(renderFrame);
}

function updateParticleSystems() {
  // Check for beat/onset to trigger bursts
  const isOnset = store.audioAnalysis?.onsets.includes(store.currentFrame) ?? false;

  // Apply audio reactivity
  particleSystems.value.forEach((system, layerId) => {
    const mappings = store.getActiveMappingsForLayer(layerId);

    for (const mapping of mappings) {
      const featureValue = store.getAudioFeatureAtFrame(mapping.feature);
      const scaledValue = featureValue * mapping.sensitivity;

      // Extract the parameter name from target (e.g., 'particle.emissionRate' -> 'emissionRate')
      const paramParts = mapping.target.split('.');
      const param = paramParts.length > 1 ? paramParts[1] : mapping.target;

      system.setFeatureValue(param, scaledValue, mapping.targetEmitterId);
    }

    // Trigger beat bursts if audio is loaded and we're on an onset
    if (isOnset) {
      system.triggerAllBursts();
    }

    // Step the simulation
    system.step(1);
  });
}

function renderParticles() {
  const canvas = fabricCanvas.value;
  if (!canvas || !particleCanvas.value || !particleCtx.value) return;

  const particleLayers = store.layers.filter(l => l.type === 'particles' && l.visible);
  if (particleLayers.length === 0) return;

  // Resize particle canvas to match fabric canvas
  if (particleCanvas.value.width !== canvas.width || particleCanvas.value.height !== canvas.height) {
    particleCanvas.value.width = canvas.width || 800;
    particleCanvas.value.height = canvas.height || 600;
  }

  const ctx = particleCtx.value;
  ctx.clearRect(0, 0, particleCanvas.value.width, particleCanvas.value.height);

  // Render each particle layer
  for (const layer of particleLayers) {
    const system = particleSystems.value.get(layer.id);
    const data = layer.data as ParticleLayerData | null;

    if (system && data) {
      // Apply viewport transform
      ctx.save();
      const vpt = canvas.viewportTransform;
      if (vpt) {
        ctx.transform(vpt[0], vpt[1], vpt[2], vpt[3], vpt[4], vpt[5]);
      }

      // Render particles
      system.renderToCanvas(
        ctx,
        store.width,
        store.height,
        data.renderOptions
      );

      ctx.restore();
    }
  }

  // Composite particle canvas onto fabric canvas
  const fabricCtx = canvas.getContext();
  if (fabricCtx && particleLayers.length > 0) {
    fabricCtx.drawImage(particleCanvas.value, 0, 0);
  }
}

// Get particle count for a layer (used by properties panel)
function getParticleCount(layerId: string): number {
  const system = particleSystems.value.get(layerId);
  return system?.getParticleCount() ?? 0;
}

// ============================================================
// PATH ANIMATOR FUNCTIONS
// ============================================================

/**
 * Update all path animators with current audio values
 */
function updatePathAnimators() {
  // Call store method to update all animators
  store.updatePathAnimators();

  // Cache the states for rendering
  for (const layer of store.layers) {
    const animator = store.getPathAnimator(layer.id);
    if (animator) {
      const state = animator.getState();
      pathAnimationStates.value.set(layer.id, state);
    }
  }
}

/**
 * Render text layers that are on paths with audio animation
 * This draws motion blur trails when enabled
 */
function renderTextOnPathAudio() {
  const canvas = fabricCanvas.value;
  if (!canvas || !particleCanvas.value || !particleCtx.value) return;

  const textLayers = store.layers.filter(l => l.type === 'text' && l.visible);
  if (textLayers.length === 0) return;

  const ctx = particleCtx.value;

  for (const layer of textLayers) {
    const textData = layer.data as TextData | null;
    if (!textData?.pathLayerId) continue;

    // Check if this layer has an audio path animator
    const animator = store.getPathAnimator(layer.id);
    if (!animator) continue;

    const state = pathAnimationStates.value.get(layer.id);
    if (!state) continue;

    // Get the spline path
    const splineLayer = store.layers.find(l => l.id === textData.pathLayerId);
    if (!splineLayer) continue;

    const splineData = splineLayer.data as SplineData | null;
    if (!splineData?.pathData) continue;

    // Apply viewport transform
    ctx.save();
    const vpt = canvas.viewportTransform;
    if (vpt) {
      ctx.transform(vpt[0], vpt[1], vpt[2], vpt[3], vpt[4], vpt[5]);
    }

    // Draw motion blur trail if enabled
    const config = animator.getConfig();
    // Check for position change (velocity proxy)
    const positionDelta = Math.abs(state.position - state.previousPosition);
    if (config.motionBlur && positionDelta > 0.001) {
      const trail = animator.getMotionBlurTrail(8);

      ctx.lineCap = 'round';
      ctx.lineJoin = 'round';

      for (let i = 0; i < trail.length - 1; i++) {
        const point = trail[i];
        const nextPoint = trail[i + 1];

        // Gradient opacity for trail
        const alpha = point.opacity * config.motionBlurStrength * 0.5;

        ctx.strokeStyle = `rgba(255, 255, 255, ${alpha})`;
        ctx.lineWidth = Math.max(2, (textData.fontSize || 48) * 0.1 * (1 - i / trail.length));

        ctx.beginPath();
        ctx.moveTo(point.x, point.y);
        ctx.lineTo(nextPoint.x, nextPoint.y);
        ctx.stroke();
      }
    }

    // The actual text rendering on path is handled by fabric.js
    // This function just handles the motion blur effect overlay

    ctx.restore();
  }
}

/**
 * Get the audio-animated position for a text layer on a path
 * This is called from text rendering to get the current position
 */
function getTextPathPosition(layerId: string): { x: number; y: number; angle: number } | null {
  const animator = store.getPathAnimator(layerId);
  if (!animator) return null;

  const state = pathAnimationStates.value.get(layerId);
  if (!state) return null;

  // Use animator to get position on path from the normalized position (0-1)
  const pathPos = animator.getPositionOnPath(state.position);

  return {
    x: pathPos.x,
    y: pathPos.y,
    angle: pathPos.angle
  };
}

// Expose canvas for external use
defineExpose({
  fabricCanvas,
  fitToView,
  zoom,
  particleSystems,
  depthflowRenderers,
  textObjects,
  splineObjects,
  getParticleCount,
  getTextPathPosition,
  pathAnimationStates
});
</script>

<style scoped>
.composition-canvas {
  position: relative;
  width: 100%;
  height: 100%;
  overflow: hidden;
  background: #1a1a1a;
}

.composition-canvas canvas {
  display: block;
}

.zoom-controls {
  position: absolute;
  bottom: 12px;
  left: 12px;
  display: flex;
  align-items: center;
  gap: 8px;
  background: rgba(0, 0, 0, 0.7);
  padding: 6px 10px;
  border-radius: 6px;
  font-size: 12px;
  z-index: 10;
}

.zoom-controls button {
  width: 24px;
  height: 24px;
  border: none;
  background: #3a3a3a;
  color: #e0e0e0;
  border-radius: 4px;
  cursor: pointer;
  font-size: 14px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.zoom-controls button:hover {
  background: #4a4a4a;
}

.zoom-level {
  min-width: 40px;
  text-align: center;
  font-variant-numeric: tabular-nums;
}

.overlay-controls {
  position: absolute;
  top: 12px;
  right: 12px;
  display: flex;
  align-items: center;
  gap: 8px;
  background: rgba(0, 0, 0, 0.7);
  padding: 6px 10px;
  border-radius: 6px;
  font-size: 12px;
  z-index: 10;
}

.overlay-controls label {
  display: flex;
  align-items: center;
  gap: 4px;
  cursor: pointer;
}

.colormap-select {
  background: #3a3a3a;
  border: none;
  color: #e0e0e0;
  padding: 2px 6px;
  border-radius: 4px;
  font-size: 12px;
}

.opacity-slider {
  width: 60px;
  height: 4px;
  cursor: pointer;
}

.loading-overlay {
  position: absolute;
  inset: 0;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  background: rgba(0, 0, 0, 0.7);
  color: #e0e0e0;
  gap: 12px;
  z-index: 20;
}

.loading-spinner {
  width: 32px;
  height: 32px;
  border: 3px solid #3a3a3a;
  border-top-color: #4a90d9;
  border-radius: 50%;
  animation: spin 1s linear infinite;
}

@keyframes spin {
  to { transform: rotate(360deg); }
}
</style>
