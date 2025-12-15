<template>
  <div class="composition-canvas" ref="containerRef">
    <canvas ref="canvasRef" />

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
import type { SplineData, ControlPoint, ParticleLayerData, DepthflowLayerData, TextData, AnimatableProperty } from '@/types/project';
import { ParticleSystem } from '@/services/particleSystem';
import { DepthflowRenderer } from '@/services/depthflow';
import type { PathAnimatorState } from '@/services/audioPathAnimator';
import { processEffectStack, hasEnabledEffects } from '@/services/effectProcessor';
import { interpolateProperty } from '@/services/interpolation';

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
const solidObjects = ref<Map<string, Rect>>(new Map());
const nullObjects = ref<Map<string, { h: Rect; v: Rect }>>(new Map());
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

// Effect processing canvases (one per layer that has effects)
const effectCanvases = ref<Map<string, HTMLCanvasElement>>(new Map());

// Grid and guides state
const showGrid = ref(false);
const showGuides = ref(false);

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
  if (!canvasRef.value || !containerRef.value) return;

  const container = containerRef.value;
  const rect = container.getBoundingClientRect();

  canvasWidth.value = rect.width;
  canvasHeight.value = rect.height;

  fabricCanvas.value = new Canvas(canvasRef.value, {
    width: rect.width,
    height: rect.height,
    backgroundColor: '#1a1a1a',
    selection: true,
    preserveObjectStacking: true
  });

  // Enable zoom/pan
  setupZoomPan();

  // Add composition bounds rectangle (visible frame boundary)
  nextTick(() => {
    createCompositionBounds();
  });

  // Handle resize
  const resizeObserver = new ResizeObserver(handleResize);
  resizeObserver.observe(container);

  // Watchers for reactivity
  watch(() => store.sourceImage, loadSourceImage, { immediate: true });
  watch(() => store.depthMap, loadDepthMap, { immediate: true });

  // Render loop watchers
  watch(() => store.layers, () => {
      renderSplineLayers();
      renderSolidLayers();
      renderNullLayers();
      renderTextLayers();  // Renders last, then calls syncLayerZOrder
      syncParticleSystems();
      syncDepthflowRenderers();
  }, { deep: true, immediate: true });

  watch(() => store.currentFrame, () => {
    renderSplineLayers();
    renderSolidLayers();
    renderNullLayers();
    renderTextLayers();  // Renders last, then calls syncLayerZOrder
  });

  watch(() => [store.width, store.height], updateCompositionBounds, { immediate: false });

  // Create particle overlay canvas
  particleCanvas.value = document.createElement('canvas');
  particleCtx.value = particleCanvas.value.getContext('2d');

  // Start render loop
  startRenderLoop();
});

onUnmounted(() => {
  if (animationFrameId.value !== null) {
    cancelAnimationFrame(animationFrameId.value);
  }
  // Cleanup resources
  particleSystems.value.forEach(s => s.reset());
  particleSystems.value.clear();
  depthflowRenderers.value.forEach(r => r.dispose());
  depthflowRenderers.value.clear();
  textObjects.value.clear();
  splineObjects.value.clear();
  solidObjects.value.clear();
  nullObjects.value.clear();
  fabricCanvas.value?.dispose();
});

// Setup zoom/pan
function setupZoomPan() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;

  // Tool state variables (declared before event handlers)
  let isPanning = false;
  let isZooming = false;
  let lastPosX = 0;
  let lastPosY = 0;
  let zoomStartY = 0;
  let zoomStartLevel = 1;

  // Prevent default middle mouse button behavior (auto-scroll)
  const container = containerRef.value;
  if (container) {
    container.addEventListener('mousedown', (e: MouseEvent) => {
      if (e.button === 1) {
        e.preventDefault();
      }
    });
    // Also prevent the auxclick which can trigger on middle mouse
    container.addEventListener('auxclick', (e: MouseEvent) => {
      if (e.button === 1) {
        e.preventDefault();
      }
    });
  }

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

  canvas.on('mouse:down', (opt) => {
    const evt = opt.e as MouseEvent;
    const currentTool = store.currentTool;

    // Middle mouse button (button === 1) or Alt+Left click for panning
    if (evt.button === 1 || currentTool === 'hand' || (evt.button === 0 && evt.altKey)) {
      isPanning = true;
      lastPosX = evt.clientX;
      lastPosY = evt.clientY;
      canvas.selection = false;
      canvas.defaultCursor = 'grabbing';
      canvas.discardActiveObject();
      evt.preventDefault();
      evt.stopPropagation();
      return;
    }

    if (currentTool === 'zoom') {
      if (evt.shiftKey) {
        const newZoom = Math.max(canvas.getZoom() * 0.7, 0.1);
        const point = new Point(evt.offsetX, evt.offsetY);
        canvas.zoomToPoint(point, newZoom);
        zoom.value = newZoom;
      } else {
        isZooming = true;
        zoomStartY = evt.clientY;
        zoomStartLevel = canvas.getZoom();
      }
      return;
    }

    if (currentTool === 'text') {
      const pointer = canvas.getScenePoint(evt);
      const newLayer = store.createLayer('text');
      if (newLayer.transform && newLayer.transform.position) {
        newLayer.transform.position.value = { x: pointer.x, y: pointer.y };
      }
      store.updateLayer(newLayer.id, {
        transform: {
          ...newLayer.transform,
          position: {
            ...newLayer.transform.position,
            value: { x: pointer.x, y: pointer.y }
          }
        }
      });
      store.selectLayer(newLayer.id);
      store.setTool('select');
      renderTextLayers();
      return;
    }
  });

  canvas.on('mouse:move', (opt) => {
    const evt = opt.e as MouseEvent;
    if (isPanning) {
      const vpt = canvas.viewportTransform;
      if (vpt) {
        vpt[4] += evt.clientX - lastPosX;
        vpt[5] += evt.clientY - lastPosY;
        canvas.requestRenderAll();
      }
      lastPosX = evt.clientX;
      lastPosY = evt.clientY;
      evt.preventDefault();
      return;
    }
    if (isZooming) {
      const dy = zoomStartY - evt.clientY;
      const zoomFactor = 1 + dy * 0.01;
      const newZoom = Math.max(0.1, Math.min(10, zoomStartLevel * zoomFactor));
      canvas.setZoom(newZoom);
      zoom.value = newZoom;
      canvas.requestRenderAll();
      return;
    }
    const currentTool = store.currentTool;
    if (currentTool === 'hand') canvas.defaultCursor = 'grab';
    else if (currentTool === 'zoom') canvas.defaultCursor = 'zoom-in';
    else if (currentTool === 'text') canvas.defaultCursor = 'text';
    else if (currentTool === 'pen') canvas.defaultCursor = 'crosshair';
    else canvas.defaultCursor = 'default';
  });

  canvas.on('mouse:up', (opt) => {
    const evt = opt.e as MouseEvent;
    if (isPanning) {
      isPanning = false;
      canvas.selection = true;
      canvas.defaultCursor = store.currentTool === 'hand' ? 'grab' : 'default';
      evt.preventDefault();
    }
    if (isZooming) isZooming = false;
  });

  canvas.on('selection:created', (e) => {
    const selected = e.selected?.[0];
    if (selected && (selected as any).layerId) store.selectLayer((selected as any).layerId);
  });

  canvas.on('selection:updated', (e) => {
    const selected = e.selected?.[0];
    if (selected && (selected as any).layerId) store.selectLayer((selected as any).layerId);
  });

  canvas.on('selection:cleared', () => {
    store.clearSelection();
  });
}

function createCompositionBounds() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;
  const compWidth = store.width || 1920;
  const compHeight = store.height || 1080;

  if (compositionBounds.value) {
    canvas.remove(compositionBounds.value as unknown as FabricObject);
  }

  compositionBounds.value = new Rect({
    left: 0,
    top: 0,
    width: compWidth,
    height: compHeight,
    fill: 'transparent',
    stroke: '#4a90d9',
    strokeWidth: 2,
    selectable: false,
    evented: false,
    strokeUniform: true,
  });

  canvas.add(compositionBounds.value as unknown as FabricObject);
  canvas.sendObjectToBack(compositionBounds.value as unknown as FabricObject);
  centerOnComposition();
  canvas.requestRenderAll();
}

function updateCompositionBounds() {
  const canvas = fabricCanvas.value;
  if (!canvas || !compositionBounds.value) return;
  const compWidth = store.width || 1920;
  const compHeight = store.height || 1080;
  compositionBounds.value.set({ width: compWidth, height: compHeight });
  compositionBounds.value.setCoords();
  centerOnComposition();
  canvas.requestRenderAll();
}

function centerOnComposition() {
  const canvas = fabricCanvas.value;
  const container = containerRef.value;
  if (!canvas || !container) return;
  const compWidth = store.width || 1920;
  const compHeight = store.height || 1080;
  const containerRect = container.getBoundingClientRect();
  const padding = 60;
  const scaleX = (containerRect.width - padding * 2) / compWidth;
  const scaleY = (containerRect.height - padding * 2) / compHeight;
  const scale = Math.min(scaleX, scaleY, 1);
  const vpt = canvas.viewportTransform;
  if (vpt) {
    vpt[0] = scale;
    vpt[3] = scale;
    vpt[4] = (containerRect.width - compWidth * scale) / 2;
    vpt[5] = (containerRect.height - compHeight * scale) / 2;
  }
  zoom.value = scale;
}

function handleResize(entries: ResizeObserverEntry[]) {
  const canvas = fabricCanvas.value;
  if (!canvas || !canvas.lowerCanvasEl) return;
  for (const entry of entries) {
    const { width, height } = entry.contentRect;
    if (width > 0 && height > 0) {
      canvas.setDimensions({ width, height });
      canvasWidth.value = width;
      canvasHeight.value = height;
    }
  }
  canvas.requestRenderAll();
}

async function loadSourceImage(imageData: string | null) {
  const canvas = fabricCanvas.value;
  if (!canvas || !imageData) return;
  loading.value = true;
  try {
    if (sourceImageObj.value) canvas.remove(sourceImageObj.value as unknown as FabricObject);
    const img = await loadImage(imageData);
    sourceImageObj.value = new FabricImage(img, { selectable: false, evented: false, left: 0, top: 0 });
    canvas.add(sourceImageObj.value as unknown as FabricObject);
    canvas.sendObjectToBack(sourceImageObj.value as unknown as FabricObject);
    fitToView();
  } catch (err) {
    console.error('[CompositionCanvas] Failed to load source image:', err);
  } finally {
    loading.value = false;
  }
}

async function loadDepthMap(depthData: string | null) {
  const canvas = fabricCanvas.value;
  if (!canvas || !depthData) return;
  try {
    if (depthMapObj.value) canvas.remove(depthMapObj.value as unknown as FabricObject);
    depthMapObj.value = await DepthMapImage.fromBase64(depthData, {
      colormap: depthColormap.value,
      opacity: depthOpacity.value / 100,
      visible: showDepthOverlay.value
    });
    depthMapObj.value.set({ selectable: false, evented: false, left: 0, top: 0 });
    canvas.add(depthMapObj.value as unknown as FabricObject);
    if (sourceImageObj.value) {
      const sourceIndex = canvas.getObjects().indexOf(sourceImageObj.value as unknown as FabricObject);
      canvas.moveObjectTo(depthMapObj.value as unknown as FabricObject, sourceIndex + 1);
    }
    canvas.requestRenderAll();
  } catch (err) {
    console.error('[CompositionCanvas] Failed to load depth map:', err);
  }
}

/**
 * Helper to get the current animated value from an AnimatableProperty
 * Uses the full interpolation engine with Bezier/Easing support
 */
function getAnimatedValue<T>(prop: AnimatableProperty<T> | undefined, defaultValue: T): T {
  if (!prop) return defaultValue;
  // Use the central interpolation engine (Bezier/Easing support)
  return interpolateProperty(prop, store.currentFrame);
}

function renderSplineLayers() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;
  const splineLayers = store.layers.filter(l => l.type === 'spline');

  for (const layer of splineLayers) {
    const splineData = layer.data as SplineData | null;
    if (!splineData) continue;

    let splineObj = splineObjects.value.get(layer.id);
    const position = getAnimatedValue(layer.transform?.position, { x: 0, y: 0, z: 0 });
    const scale = getAnimatedValue(layer.transform?.scale, { x: 100, y: 100 });
    const rotation = getAnimatedValue(layer.transform?.rotation, 0);
    const opacity = getAnimatedValue(layer.opacity, 100) / 100;

    if (!splineObj) {
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
      splineObj.controlPoints = splineData.controlPoints || [];
      splineObj.set({
        stroke: splineData.stroke,
        strokeWidth: splineData.strokeWidth,
        fill: splineData.fill
      });
    }

    splineObj.set({
      left: position.x,
      top: position.y,
      scaleX: scale.x / 100,  // Convert from percentage (100 = 100%) to multiplier (1.0)
      scaleY: scale.y / 100,
      angle: rotation,
      opacity: opacity,
      visible: layer.visible,
      selectable: !layer.locked
    });

    splineObj.updatePathFromControlPoints();
    splineObj.setCoords();
  }

  const layerIds = new Set(splineLayers.map(l => l.id));
  for (const [id, obj] of splineObjects.value) {
    if (!layerIds.has(id)) {
      canvas.remove(obj as unknown as FabricObject);
      splineObjects.value.delete(id);
    }
  }
  canvas.requestRenderAll();
}

function renderSolidLayers() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;
  const solidLayers = store.layers.filter(l => l.type === 'solid');
  if (!solidObjects.value) solidObjects.value = new Map();

  for (const layer of solidLayers) {
    let solidObj = solidObjects.value.get(layer.id);
    const position = getAnimatedValue(layer.transform?.position, { x: 0, y: 0, z: 0 });
    const scale = getAnimatedValue(layer.transform?.scale, { x: 100, y: 100 });
    const rotation = getAnimatedValue(layer.transform?.rotation, 0);
    const opacity = getAnimatedValue(layer.opacity, 100) / 100;
    const solidData = layer.data as { color?: string } | null;
    const color = solidData?.color || '#808080';
    const width = store.width || 1920;
    const height = store.height || 1080;

    if (!solidObj) {
      solidObj = new Rect({
        left: position.x,
        top: position.y,
        width: width,
        height: height,
        fill: color,
        selectable: !layer.locked,
        evented: !layer.locked
      });
      (solidObj as any).layerId = layer.id;
      solidObjects.value.set(layer.id, solidObj);
      canvas.add(solidObj as unknown as FabricObject);
    } else {
      solidObj.set({ fill: color, width: width, height: height });
    }

    solidObj.set({
      left: position.x,
      top: position.y,
      scaleX: scale.x / 100,  // Convert from percentage (100 = 100%) to multiplier (1.0)
      scaleY: scale.y / 100,
      angle: rotation,
      opacity: opacity,
      visible: layer.visible,
      selectable: !layer.locked
    });
    solidObj.setCoords();
  }

  const layerIds = new Set(solidLayers.map(l => l.id));
  for (const [id, obj] of solidObjects.value) {
    if (!layerIds.has(id)) {
      canvas.remove(obj as unknown as FabricObject);
      solidObjects.value.delete(id);
    }
  }
  canvas.requestRenderAll();
}

function renderNullLayers() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;
  const nullLayers = store.layers.filter(l => l.type === 'null');
  if (!nullObjects.value) nullObjects.value = new Map();

  for (const layer of nullLayers) {
    let nullGroup = nullObjects.value.get(layer.id);
    const position = getAnimatedValue(layer.transform?.position, { x: 0, y: 0, z: 0 });
    const scale = getAnimatedValue(layer.transform?.scale, { x: 100, y: 100 });
    const rotation = getAnimatedValue(layer.transform?.rotation, 0);
    const opacity = getAnimatedValue(layer.opacity, 100) / 100;
    const centerX = (store.width || 1920) / 2;
    const centerY = (store.height || 1080) / 2;
    const posX = (position.x !== undefined && position.x !== null) ? position.x : centerX;
    const posY = (position.y !== undefined && position.y !== null) ? position.y : centerY;
    const crosshairSize = 40;

    if (!nullGroup) {
      const horizontalLine = new Rect({
        left: posX - crosshairSize / 2,
        top: posY - 1,
        width: crosshairSize,
        height: 2,
        fill: '#ff9900',
        selectable: false,
        evented: false
      });
      const verticalLine = new Rect({
        left: posX - 1,
        top: posY - crosshairSize / 2,
        width: 2,
        height: crosshairSize,
        fill: '#ff9900',
        selectable: false,
        evented: false
      });
      (horizontalLine as any).layerId = layer.id;
      (verticalLine as any).layerId = layer.id;
      nullObjects.value.set(layer.id, { h: horizontalLine, v: verticalLine });
      canvas.add(horizontalLine as unknown as FabricObject);
      canvas.add(verticalLine as unknown as FabricObject);
      nullGroup = { h: horizontalLine, v: verticalLine };
    }

    // Convert scale from percentage (100 = 100%) to multiplier
    const scaleMultX = scale.x / 100;
    const scaleMultY = scale.y / 100;

    nullGroup.h.set({
      left: posX - (crosshairSize * scaleMultX) / 2,
      top: posY - 1,
      width: crosshairSize * scaleMultX,
      scaleX: 1,
      scaleY: scaleMultY,
      angle: rotation,
      opacity: opacity,
      visible: layer.visible
    });

    nullGroup.v.set({
      left: posX - 1,
      top: posY - (crosshairSize * scaleMultY) / 2,
      width: 2,
      height: crosshairSize * scaleMultY,
      scaleX: scaleMultX,
      scaleY: 1,
      angle: rotation,
      opacity: opacity,
      visible: layer.visible
    });

    nullGroup.h.setCoords();
    nullGroup.v.setCoords();
  }

  const layerIds = new Set(nullLayers.map(l => l.id));
  for (const [id, obj] of nullObjects.value) {
    if (!layerIds.has(id)) {
      canvas.remove(obj.h as unknown as FabricObject);
      canvas.remove(obj.v as unknown as FabricObject);
      nullObjects.value.delete(id);
    }
  }
  canvas.requestRenderAll();
}

function renderTextLayers() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;
  const textLayers = store.layers.filter(l => l.type === 'text');

  for (const layer of textLayers) {
    const textData = layer.data as TextData | null;
    if (!textData) continue;

    let textObj = textObjects.value.get(layer.id);
    const position = getAnimatedValue(layer.transform?.position, { x: 0, y: 0, z: 0 });
    const anchorPoint = getAnimatedValue(layer.transform?.anchorPoint, { x: 0, y: 0, z: 0 });
    const scale = getAnimatedValue(layer.transform?.scale, { x: 100, y: 100, z: 100 });  // Default 100%
    const opacity = getAnimatedValue(layer.opacity, 100) / 100;

    // Get rotation - use rotationZ for 3D layers, rotation for 2D
    let rotation = 0;
    let rotationX = 0;
    let rotationY = 0;
    if (layer.threeD) {
      rotationX = getAnimatedValue(layer.transform?.rotationX, 0);
      rotationY = getAnimatedValue(layer.transform?.rotationY, 0);
      rotation = getAnimatedValue(layer.transform?.rotationZ, 0);
    } else {
      rotation = getAnimatedValue(layer.transform?.rotation, 0);
    }
    const centerX = (store.width || 1920) / 2;
    const centerY = (store.height || 1080) / 2;

    // Position is layer position; anchor point offsets the object's origin
    const posX = (position.x !== undefined && position.x !== null) ? position.x : centerX;
    const posY = (position.y !== undefined && position.y !== null) ? position.y : centerY;

    if (!textObj) {
      textObj = new AnimatedText({
        text: textData.text || 'Text',
        fontFamily: textData.fontFamily || 'Arial',
        fontSize: textData.fontSize || 72,
        fontWeight: textData.fontWeight || '400',
        fontStyle: textData.fontStyle || 'normal',
        fill: textData.fill || '#ffffff',
        stroke: textData.stroke || '',
        strokeWidth: textData.strokeWidth || 0,
        letterSpacing: textData.letterSpacing || 0,
        textAlign: textData.textAlign || 'left',
        pathLayerId: textData.pathLayerId,
        pathOffset: textData.pathOffset || 0,
        selectable: !layer.locked
      });
      (textObj as any).layerId = layer.id;
      textObjects.value.set(layer.id, textObj);
      canvas.add(textObj as unknown as FabricObject);
      textObj.setText(textObj.textContent);
      canvas.bringObjectToFront(textObj as unknown as FabricObject);
    } else {
      // Update text content
      if (textData.text !== textObj.textContent) textObj.setText(textData.text || 'Text');

      // Update font properties - check all font-related properties
      const fontChanged = textData.fontFamily !== textObj.fontFamily ||
                          textData.fontSize !== textObj.fontSize ||
                          textData.fontWeight !== textObj.fontWeight ||
                          textData.fontStyle !== textObj.fontStyle;
      if (fontChanged) {
        textObj.setFont(
          textData.fontFamily || 'Arial',
          textData.fontSize || 72,
          textData.fontWeight || '400',
          textData.fontStyle || 'normal'
        );
      }

      // Update colors
      if (textData.fill !== textObj.textFill) textObj.setFillColor(textData.fill || '#ffffff');
      if (textData.stroke !== textObj.textStroke || textData.strokeWidth !== textObj.textStrokeWidth) {
        textObj.setStroke(textData.stroke || '', textData.strokeWidth || 0);
      }

      // Update spacing and alignment
      if (textData.letterSpacing !== textObj.letterSpacing) textObj.setLetterSpacing(textData.letterSpacing || 0);
      if (textData.textAlign !== textObj.textAlign) textObj.setTextAlign(textData.textAlign || 'left');

      textObj.pathLayerId = textData.pathLayerId || null;
      textObj.pathOffset = textData.pathOffset || 0;
    }

    // Convert scale from percentage (100 = 100%) to multiplier (1.0)
    let scaleX = scale.x / 100;
    let scaleY = scale.y / 100;

    // Apply 3D effects for 3D layers
    if (layer.threeD) {
      // Z Position: Perspective scaling - closer objects (higher Z) appear larger
      // Using a simple linear perspective with Z=0 at normal size
      // Positive Z = closer = larger, Negative Z = further = smaller
      const perspectiveDistance = 1000; // Virtual camera distance
      const zPos = position.z || 0;
      const perspectiveFactor = perspectiveDistance / (perspectiveDistance - zPos);
      scaleX *= perspectiveFactor;
      scaleY *= perspectiveFactor;

      // X Rotation: Simulates tilting forward/backward by compressing Y scale
      // cos(angle) gives the foreshortening factor
      if (rotationX !== 0) {
        const radX = rotationX * Math.PI / 180;
        scaleY *= Math.cos(radX);
      }

      // Y Rotation: Simulates turning left/right by compressing X scale
      if (rotationY !== 0) {
        const radY = rotationY * Math.PI / 180;
        scaleX *= Math.cos(radY);
      }
    }

    textObj.set({
      left: posX,
      top: posY,
      originX: 'center',
      originY: 'center',
      scaleX: scaleX,
      scaleY: scaleY,
      angle: rotation,
      opacity: opacity,
      visible: layer.visible,
      selectable: !layer.locked
    });

    // Apply anchor point as an offset to the object's position
    // Anchor point is relative to the object's bounding box
    if (anchorPoint.x !== 0 || anchorPoint.y !== 0) {
      const offsetX = anchorPoint.x * scaleX;
      const offsetY = anchorPoint.y * scaleY;
      // Rotate the offset by the object's angle
      const rad = rotation * Math.PI / 180;
      const rotatedOffsetX = offsetX * Math.cos(rad) - offsetY * Math.sin(rad);
      const rotatedOffsetY = offsetX * Math.sin(rad) + offsetY * Math.cos(rad);
      textObj.set({
        left: posX - rotatedOffsetX,
        top: posY - rotatedOffsetY
      });
    }

    textObj.setCoords();
  }

  const layerIds = new Set(textLayers.map(l => l.id));
  for (const [id, obj] of textObjects.value) {
    if (!layerIds.has(id)) {
      canvas.remove(obj as unknown as FabricObject);
      textObjects.value.delete(id);
    }
  }
  canvas.requestRenderAll();

  // After rendering all layers, sync Z-order
  syncLayerZOrder();
}

/**
 * Synchronize Fabric.js object stacking order based on layer Z position.
 * Higher Z = closer to camera = rendered on top.
 * This ensures 3D layers render in the correct depth order.
 */
function syncLayerZOrder() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;

  // Collect all layer objects with their Z positions
  type LayerZInfo = { layerId: string; zPos: number; obj: FabricObject };
  const layerZInfos: LayerZInfo[] = [];

  // Helper to get Z position from layer
  const getLayerZ = (layer: any): number => {
    if (!layer.threeD) return 0;
    const pos = layer.transform?.position?.value;
    return pos?.z ?? 0;
  };

  // Collect from all object maps
  for (const layer of store.layers) {
    const z = getLayerZ(layer);

    // Text objects
    const textObj = textObjects.value.get(layer.id);
    if (textObj) {
      layerZInfos.push({ layerId: layer.id, zPos: z, obj: textObj as unknown as FabricObject });
    }

    // Spline objects
    const splineObj = splineObjects.value.get(layer.id);
    if (splineObj) {
      layerZInfos.push({ layerId: layer.id, zPos: z, obj: splineObj as unknown as FabricObject });
    }

    // Solid objects
    const solidObj = solidObjects.value.get(layer.id);
    if (solidObj) {
      layerZInfos.push({ layerId: layer.id, zPos: z, obj: solidObj as unknown as FabricObject });
    }

    // Null objects (both horizontal and vertical lines)
    const nullObj = nullObjects.value.get(layer.id);
    if (nullObj) {
      layerZInfos.push({ layerId: layer.id, zPos: z, obj: nullObj.h as unknown as FabricObject });
      layerZInfos.push({ layerId: layer.id, zPos: z, obj: nullObj.v as unknown as FabricObject });
    }
  }

  // Sort by Z position (ascending = furthest first, so they render behind)
  // Lower Z = further from camera = render first (behind)
  // Higher Z = closer to camera = render last (on top)
  layerZInfos.sort((a, b) => a.zPos - b.zPos);

  // Reorder objects in canvas
  // moveTo uses index where 0 is bottom (behind everything)
  layerZInfos.forEach((info, index) => {
    // Skip the composition bounds rect (always at bottom)
    const baseIndex = compositionBounds.value ? 1 : 0;
    canvas.moveTo(info.obj, baseIndex + index);
  });
}

// Event handlers for SplineEditor
function onPointAdded(_point: ControlPoint) {
  if (!activeSplineLayerId.value) {
    const newLayer = store.createLayer('spline');
    store.selectLayer(newLayer.id);
  }
}

function onPathUpdated() {
  renderSplineLayers();
}

// Watch depth settings
watch(showDepthOverlay, (visible) => {
  if (depthMapObj.value) {
    depthMapObj.value.set('visible', visible);
    fabricCanvas.value?.requestRenderAll();
  }
});
watch(depthColormap, (colormap) => {
  if (depthMapObj.value) depthMapObj.value.setColormap(colormap);
});
watch(depthOpacity, (opacity) => {
  if (depthMapObj.value) {
    depthMapObj.value.set('opacity', opacity / 100);
    fabricCanvas.value?.requestRenderAll();
  }
});

function loadImage(src: string): Promise<HTMLImageElement> {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.crossOrigin = 'anonymous';
    img.onload = () => resolve(img);
    img.onerror = reject;
    img.src = src.startsWith('data:') ? src : `data:image/png;base64,${src}`;
  });
}

// Zoom helpers
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

function setZoomFromSelect(event: Event) {
  const canvas = fabricCanvas.value;
  if (!canvas) return;
  const select = event.target as HTMLSelectElement;
  const newZoom = parseInt(select.value, 10) / 100;
  canvas.setZoom(newZoom);
  zoom.value = newZoom;
  canvas.requestRenderAll();
}

function fitToView() {
  const canvas = fabricCanvas.value;
  const container = containerRef.value;
  if (!canvas || !container || !sourceImageObj.value) return;
  const rect = container.getBoundingClientRect();
  const imgWidth = sourceImageObj.value.width || 1;
  const imgHeight = sourceImageObj.value.height || 1;
  const padding = 40;
  const scaleX = (rect.width - padding * 2) / imgWidth;
  const scaleY = (rect.height - padding * 2) / imgHeight;
  const scale = Math.min(scaleX, scaleY, 1);
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

// Particle System Sync
function syncParticleSystems() {
  const particleLayers = store.layers.filter(l => l.type === 'particles');
  const layerIds = new Set(particleLayers.map(l => l.id));

  for (const layer of particleLayers) {
    if (!particleSystems.value.has(layer.id)) {
      const data = layer.data as ParticleLayerData | null;
      if (data) {
        const system = new ParticleSystem(data.systemConfig);
        data.emitters.forEach(e => system.addEmitter(e));
        data.gravityWells.forEach(w => system.addGravityWell(w));
        data.vortices.forEach(v => system.addVortex(v));
        data.modulations.forEach(m => system.addModulation(m));
        particleSystems.value.set(layer.id, system);
      }
    } else {
      const system = particleSystems.value.get(layer.id)!;
      const data = layer.data as ParticleLayerData | null;
      if (data) {
        system.setConfig(data.systemConfig);
        const currentEmitters = system.getEmitters();
        for (const emitter of data.emitters) {
          const existing = currentEmitters.find(e => e.id === emitter.id);
          if (existing) system.updateEmitter(emitter.id, emitter);
          else system.addEmitter(emitter);
        }
      }
    }
  }

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

  for (const layer of depthflowLayers) {
    if (!depthflowRenderers.value.has(layer.id)) {
      const data = layer.data as DepthflowLayerData | null;
      if (data) {
        const renderer = new DepthflowRenderer();
        renderer.setConfig(data.config);
        depthflowRenderers.value.set(layer.id, renderer);
      }
    } else {
      const renderer = depthflowRenderers.value.get(layer.id)!;
      const data = layer.data as DepthflowLayerData | null;
      if (data) renderer.setConfig(data.config);
    }
  }

  for (const [id] of depthflowRenderers.value) {
    if (!layerIds.has(id)) {
      depthflowRenderers.value.get(id)?.dispose();
      depthflowRenderers.value.delete(id);
    }
  }
}

function startRenderLoop() {
  const renderFrame = () => {
    if (store.isPlaying || store.audioAnalysis) updatePathAnimators();
    if (store.isPlaying) updateParticleSystems();
    applyLayerEffects();
    renderParticles();
    renderTextOnPathAudio();
    animationFrameId.value = requestAnimationFrame(renderFrame);
  };
  animationFrameId.value = requestAnimationFrame(renderFrame);
}

function updateParticleSystems() {
  const isOnset = store.audioAnalysis?.onsets.includes(store.currentFrame) ?? false;
  particleSystems.value.forEach((system, layerId) => {
    const mappings = store.getActiveMappingsForLayer(layerId);
    for (const mapping of mappings) {
      const featureValue = store.getAudioFeatureAtFrame(mapping.feature);
      const scaledValue = featureValue * mapping.sensitivity;
      const paramParts = mapping.target.split('.');
      const param = paramParts.length > 1 ? paramParts[1] : mapping.target;
      system.setFeatureValue(param, scaledValue, mapping.targetEmitterId);
    }
    if (isOnset) system.triggerAllBursts();
    system.step(1);
  });
}

function renderParticles() {
  const canvas = fabricCanvas.value;
  if (!canvas || !particleCanvas.value || !particleCtx.value) return;
  const particleLayers = store.layers.filter(l => l.type === 'particles' && l.visible);
  if (particleLayers.length === 0) return;

  if (particleCanvas.value.width !== canvas.width || particleCanvas.value.height !== canvas.height) {
    particleCanvas.value.width = canvas.width || 800;
    particleCanvas.value.height = canvas.height || 600;
  }

  const ctx = particleCtx.value;
  ctx.clearRect(0, 0, particleCanvas.value.width, particleCanvas.value.height);

  for (const layer of particleLayers) {
    const system = particleSystems.value.get(layer.id);
    const data = layer.data as ParticleLayerData | null;
    if (system && data) {
      ctx.save();
      const vpt = canvas.viewportTransform;
      if (vpt) ctx.transform(vpt[0], vpt[1], vpt[2], vpt[3], vpt[4], vpt[5]);
      system.renderToCanvas(ctx, store.width, store.height, data.renderOptions);
      ctx.restore();
    }
  }

  const fabricCtx = canvas.getContext();
  if (fabricCtx && particleLayers.length > 0) {
    fabricCtx.drawImage(particleCanvas.value, 0, 0);
  }
}

function getParticleCount(layerId: string): number {
  const system = particleSystems.value.get(layerId);
  return system?.getParticleCount() ?? 0;
}

// Path Animator functions
function updatePathAnimators() {
  store.updatePathAnimators();
  for (const layer of store.layers) {
    const animator = store.getPathAnimator(layer.id);
    if (animator) {
      pathAnimationStates.value.set(layer.id, animator.getState());
    }
  }
}

function renderTextOnPathAudio() {
  const canvas = fabricCanvas.value;
  if (!canvas || !particleCanvas.value || !particleCtx.value) return;
  const textLayers = store.layers.filter(l => l.type === 'text' && l.visible);
  if (textLayers.length === 0) return;

  const ctx = particleCtx.value;
  for (const layer of textLayers) {
    const textData = layer.data as TextData | null;
    if (!textData?.pathLayerId) continue;
    const animator = store.getPathAnimator(layer.id);
    if (!animator) continue;
    const state = pathAnimationStates.value.get(layer.id);
    if (!state) continue;
    const splineLayer = store.layers.find(l => l.id === textData.pathLayerId);
    if (!splineLayer) continue;
    const splineData = splineLayer.data as SplineData | null;
    if (!splineData?.pathData) continue;

    ctx.save();
    const vpt = canvas.viewportTransform;
    if (vpt) ctx.transform(vpt[0], vpt[1], vpt[2], vpt[3], vpt[4], vpt[5]);

    const config = animator.getConfig();
    const positionDelta = Math.abs(state.position - state.previousPosition);
    if (config.motionBlur && positionDelta > 0.001) {
      const trail = animator.getMotionBlurTrail(8);
      ctx.lineCap = 'round';
      ctx.lineJoin = 'round';
      for (let i = 0; i < trail.length - 1; i++) {
        const point = trail[i];
        const nextPoint = trail[i + 1];
        const alpha = point.opacity * config.motionBlurStrength * 0.5;
        ctx.strokeStyle = `rgba(255, 255, 255, ${alpha})`;
        ctx.lineWidth = Math.max(2, (textData.fontSize || 48) * 0.1 * (1 - i / trail.length));
        ctx.beginPath();
        ctx.moveTo(point.x, point.y);
        ctx.lineTo(nextPoint.x, nextPoint.y);
        ctx.stroke();
      }
    }
    ctx.restore();
  }
}

function getTextPathPosition(layerId: string): { x: number; y: number; angle: number } | null {
  const animator = store.getPathAnimator(layerId);
  if (!animator) return null;
  const state = pathAnimationStates.value.get(layerId);
  if (!state) return null;
  const pathPos = animator.getPositionOnPath(state.position);
  return { x: pathPos.x, y: pathPos.y, angle: pathPos.angle };
}

function applyLayerEffects() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;
  const currentFrame = store.currentFrame;

  for (const layer of store.layers) {
    if (!layer.visible || !layer.effects || !hasEnabledEffects(layer.effects)) continue;
    let fabricObj: FabricObject | null = null;
    if (layer.type === 'spline') fabricObj = splineObjects.value.get(layer.id) as unknown as FabricObject;
    else if (layer.type === 'text') fabricObj = textObjects.value.get(layer.id) as unknown as FabricObject;

    if (!fabricObj) continue;
    const objectCanvas = renderObjectToCanvas(fabricObj);
    if (!objectCanvas) continue;
    const result = processEffectStack(layer.effects, objectCanvas, currentFrame);
    effectCanvases.value.set(layer.id, result.canvas);
    applyEffectResultToObject(fabricObj, result.canvas);
  }
}

function renderObjectToCanvas(obj: FabricObject): HTMLCanvasElement | null {
  const bounds = obj.getBoundingRect();
  if (bounds.width <= 0 || bounds.height <= 0) return null;
  const canvas = document.createElement('canvas');
  canvas.width = Math.ceil(bounds.width);
  canvas.height = Math.ceil(bounds.height);
  const ctx = canvas.getContext('2d');
  if (!ctx) return null;
  const left = obj.left || 0;
  const top = obj.top || 0;
  obj.set({ left: -bounds.left, top: -bounds.top });
  obj.render(ctx);
  obj.set({ left, top });
  return canvas;
}

function applyEffectResultToObject(obj: FabricObject, effectCanvas: HTMLCanvasElement) {
  (obj as any)._effectCanvas = effectCanvas;
  fabricCanvas.value?.requestRenderAll();
}

function renderGridAndGuides() {
  const canvas = fabricCanvas.value;
  if (!canvas) return;
  const compWidth = store.width || 1920;
  const compHeight = store.height || 1080;

  const oldObjects = canvas.getObjects().filter((o: any) => o.isGridOrGuide);
  oldObjects.forEach(o => canvas.remove(o));

  if (showGrid.value) {
    const gridSize = 100;
    for (let x = 0; x <= compWidth; x += gridSize) {
      const line = new Rect({ left: x, top: 0, width: 1, height: compHeight, fill: 'rgba(80, 80, 80, 0.4)', selectable: false, evented: false });
      (line as any).isGridOrGuide = true;
      canvas.add(line as unknown as FabricObject);
      canvas.sendObjectToBack(line as unknown as FabricObject);
    }
    for (let y = 0; y <= compHeight; y += gridSize) {
      const line = new Rect({ left: 0, top: y, width: compWidth, height: 1, fill: 'rgba(80, 80, 80, 0.4)', selectable: false, evented: false });
      (line as any).isGridOrGuide = true;
      canvas.add(line as unknown as FabricObject);
      canvas.sendObjectToBack(line as unknown as FabricObject);
    }
  }

  if (showGuides.value) {
    [compWidth / 3, compWidth * 2 / 3].forEach(x => {
      const line = new Rect({ left: x, top: 0, width: 1, height: compHeight, fill: 'rgba(0, 180, 255, 0.4)', selectable: false, evented: false });
      (line as any).isGridOrGuide = true;
      canvas.add(line as unknown as FabricObject);
    });
    [compHeight / 3, compHeight * 2 / 3].forEach(y => {
      const line = new Rect({ left: 0, top: y, width: compWidth, height: 1, fill: 'rgba(0, 180, 255, 0.4)', selectable: false, evented: false });
      (line as any).isGridOrGuide = true;
      canvas.add(line as unknown as FabricObject);
    });
    const cx = compWidth / 2;
    const cy = compHeight / 2;
    const size = 30;
    const hLine = new Rect({ left: cx - size, top: cy, width: size * 2, height: 1, fill: 'rgba(255, 100, 100, 0.6)', selectable: false, evented: false });
    const vLine = new Rect({ left: cx, top: cy - size, width: 1, height: size * 2, fill: 'rgba(255, 100, 100, 0.6)', selectable: false, evented: false });
    (hLine as any).isGridOrGuide = true;
    (vLine as any).isGridOrGuide = true;
    canvas.add(hLine as unknown as FabricObject);
    canvas.add(vLine as unknown as FabricObject);
  }

  if (compositionBounds.value) {
    canvas.bringObjectForward(compositionBounds.value as unknown as FabricObject);
  }
  canvas.requestRenderAll();
}

watch(showGrid, renderGridAndGuides);
watch(showGuides, renderGridAndGuides);

defineExpose({
  fabricCanvas,
  fitToView,
  zoom,
  showGrid,
  showGuides,
  renderGridAndGuides,
  particleSystems,
  depthflowRenderers,
  textObjects,
  splineObjects,
  solidObjects,
  nullObjects,
  getParticleCount,
  getTextPathPosition,
  pathAnimationStates,
  effectCanvases
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
