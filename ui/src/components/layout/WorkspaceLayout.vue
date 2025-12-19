<template>
  <div class="workspace-layout">
    <!-- Top Toolbar -->
    <div class="toolbar">
      <div class="tool-group labeled-tools">
        <button
          :class="{ active: currentTool === 'select' }"
          @click="currentTool = 'select'"
          title="Select Tool (V) - Select and move layers"
        >
          <span class="icon">↖</span>
          <span class="tool-label">Select</span>
        </button>
        <button
          :class="{ active: currentTool === 'pen' }"
          @click="currentTool = 'pen'"
          title="Pen Tool (P) - Draw paths and shapes"
        >
          <span class="icon">✒</span>
          <span class="tool-label">Pen</span>
        </button>
        <button
          :class="{ active: currentTool === 'text' }"
          @click="currentTool = 'text'"
          title="Text Tool (T) - Add text layers"
        >
          <span class="icon">T</span>
          <span class="tool-label">Text</span>
        </button>
        <button
          :class="{ active: currentTool === 'hand' }"
          @click="currentTool = 'hand'"
          title="Hand Tool (H) - Pan the viewport"
        >
          <span class="icon">✋</span>
          <span class="tool-label">Pan</span>
        </button>
        <button
          :class="{ active: currentTool === 'zoom' }"
          @click="currentTool = 'zoom'"
          title="Zoom Tool (Z) - Zoom in/out the viewport"
        >
          <span class="icon">🔍</span>
          <span class="tool-label">Zoom</span>
        </button>
        <button
          :class="{ active: currentTool === 'segment' }"
          @click="currentTool = 'segment'"
          title="AI Segment (S) - Auto-select objects using AI"
        >
          <span class="icon">✨</span>
          <span class="tool-label">AI Seg</span>
        </button>
      </div>

      <div class="divider"></div>

      <!-- Import Button -->
      <div class="tool-group">
        <button
          @click="triggerAssetImport"
          title="Import Asset (Ctrl+I)"
          class="import-btn"
        >
          <span class="icon">📥</span>
          <span class="btn-label">Import</span>
        </button>
      </div>

      <!-- Segment Tool Options (shown when segment tool is active) -->
      <template v-if="currentTool === 'segment'">
        <div class="divider"></div>
        <div class="tool-group segment-options">
          <button
            :class="{ active: segmentMode === 'point' }"
            @click="setSegmentMode('point')"
            title="Point Mode - Click to segment"
          >
            <span class="icon">●</span> Point
          </button>
          <button
            :class="{ active: segmentMode === 'box' }"
            @click="setSegmentMode('box')"
            title="Box Mode - Draw rectangle to segment"
          >
            <span class="icon">▢</span> Box
          </button>
          <template v-if="segmentPendingMask">
            <div class="divider"></div>
            <button @click="confirmSegmentMask" class="confirm-btn" title="Create Layer from Selection">
              <span class="icon">✓</span> Create Layer
            </button>
            <button @click="clearSegmentMask" class="cancel-btn" title="Cancel Selection">
              <span class="icon">✕</span>
            </button>
          </template>
          <span v-if="segmentIsLoading" class="loading-indicator">Segmenting...</span>
        </div>
      </template>

      <div class="divider"></div>

      <div class="tool-group">
        <button @click="goToStart" title="Go to Start (Home)">
          <span class="icon">⏮</span>
        </button>
        <button @click="stepBackward" title="Step Backward">
          <span class="icon">⏪</span>
        </button>
        <button @click="togglePlay" :title="isPlaying ? 'Pause (Space)' : 'Play (Space)'">
          <span class="icon">{{ isPlaying ? '⏸' : '▶' }}</span>
        </button>
        <button @click="stepForward" title="Step Forward">
          <span class="icon">⏩</span>
        </button>
        <button @click="goToEnd" title="Go to End (End)">
          <span class="icon">⏭</span>
        </button>
      </div>

      <div class="timecode-display">
        {{ formattedTimecode }}
      </div>

      <div class="divider"></div>

      <div class="tool-group">
        <select v-model="activeWorkspace" class="workspace-selector">
          <option value="standard">Standard</option>
          <option value="animation">Animation</option>
          <option value="effects">Effects</option>
          <option value="minimal">Minimal</option>
        </select>
      </div>

      <div class="spacer"></div>

      <div class="tool-group">
        <span class="gpu-badge" :class="gpuTier">{{ gpuTier.toUpperCase() }}</span>
        <button @click="undo" :disabled="!canUndo" title="Undo (Ctrl+Z)">
          <span class="icon">↩</span>
        </button>
        <button @click="redo" :disabled="!canRedo" title="Redo (Ctrl+Shift+Z)">
          <span class="icon">↪</span>
        </button>
        <div class="divider"></div>
        <button @click="showHDPreview = true" title="HD Preview (`)">
          <span class="icon">🖥</span> HD
        </button>
        <button @click="showExportDialog = true" title="Export Matte">
          <span class="icon">📤</span> Matte
        </button>
        <button @click="showComfyUIExportDialog = true" title="Export to ComfyUI">
          <span class="icon">🎬</span> ComfyUI
        </button>
      </div>
    </div>

    <!-- Main Workspace with Splitpanes -->
    <div class="workspace-content">
      <Splitpanes class="default-theme horizontal-split">
        <!-- Left Panel: Project/Effects -->
        <Pane :size="12" :min-size="8" :max-size="20">
          <div class="panel left-panel">
            <div class="panel-tabs">
              <button
                :class="{ active: leftTab === 'project' }"
                @click="leftTab = 'project'"
              >
                Project
              </button>
              <button
                :class="{ active: leftTab === 'effects' }"
                @click="leftTab = 'effects'"
              >
                Effects
              </button>
              <button
                :class="{ active: leftTab === 'assets' }"
                @click="leftTab = 'assets'"
              >
                Assets
              </button>
            </div>
            <div class="panel-content">
              <ProjectPanel v-if="leftTab === 'project'" @openCompositionSettings="showCompositionSettingsDialog = true" />
              <EffectsPanel v-else-if="leftTab === 'effects'" />
              <AssetsPanel
                v-else-if="leftTab === 'assets'"
                @create-layers-from-svg="onCreateLayersFromSvg"
                @use-mesh-as-emitter="onUseMeshAsEmitter"
                @environment-update="onEnvironmentUpdate"
                @environment-load="onEnvironmentLoad"
                @environment-clear="onEnvironmentClear"
              />
            </div>
          </div>
        </Pane>

        <!-- Center: Viewport + Timeline -->
        <Pane :size="70" :min-size="40">
          <Splitpanes horizontal class="default-theme">
            <!-- Viewport -->
            <Pane :size="65" :min-size="20">
              <div class="panel viewport-panel">
                <div class="viewport-header">
                  <div class="viewport-tabs">
                    <button
                      :class="{ active: viewportTab === 'composition' }"
                      @click="viewportTab = 'composition'"
                    >
                      Composition
                    </button>
                    <button
                      :class="{ active: viewportTab === 'layer' }"
                      @click="viewportTab = 'layer'"
                    >
                      Layer
                    </button>
                    <button
                      :class="{ active: viewportTab === 'footage' }"
                      @click="viewportTab = 'footage'"
                    >
                      Footage
                    </button>
                  </div>
                  <div class="viewport-controls">
                    <select v-model="viewZoom" @change="handleZoomChange" class="zoom-select">
                      <option value="fit">Fit</option>
                      <option value="25">25%</option>
                      <option value="50">50%</option>
                      <option value="75">75%</option>
                      <option value="100">100%</option>
                      <option value="150">150%</option>
                      <option value="200">200%</option>
                    </select>
                    <button
                      :class="{ active: viewOptions.showRulers }"
                      @click="viewOptions.showRulers = !viewOptions.showRulers"
                      title="Toggle Rulers/Guides"
                    >
                      <span class="icon">📏</span>
                    </button>
                    <button
                      :class="{ active: viewOptions.showGrid }"
                      @click="viewOptions.showGrid = !viewOptions.showGrid"
                      title="Toggle Grid"
                    >
                      <span class="icon">▦</span>
                    </button>
                  </div>
                </div>
                <div class="viewport-content">
                  <!-- Rulers overlay -->
                  <div v-if="viewOptions.showRulers" class="rulers-overlay">
                    <div class="ruler ruler-horizontal">
                      <span v-for="i in 20" :key="'h'+i" class="tick" :style="{ left: (i * 5) + '%' }">
                        {{ Math.round((i * 5 / 100) * compWidth) }}
                      </span>
                    </div>
                    <div class="ruler ruler-vertical">
                      <span v-for="i in 20" :key="'v'+i" class="tick" :style="{ top: (i * 5) + '%' }">
                        {{ Math.round((i * 5 / 100) * compHeight) }}
                      </span>
                    </div>
                  </div>
                  <ThreeCanvas v-if="viewportTab === 'composition'" ref="threeCanvasRef" />
                  <ViewportRenderer
                    v-else
                    :camera="activeCamera"
                    :viewportState="viewportState"
                    :viewOptions="viewOptions"
                    :compWidth="compWidth"
                    :compHeight="compHeight"
                  />
                </div>
              </div>
            </Pane>

            <!-- Timeline + Graph Editor -->
            <Pane :size="35" :min-size="15">
              <Splitpanes v-if="showGraphEditor" horizontal class="default-theme">
                <Pane :size="50" :min-size="20">
                  <div class="panel timeline-panel">
                    <TimelinePanel @openCompositionSettings="showCompositionSettingsDialog = true" @openPathSuggestion="showPathSuggestionDialog = true" />
                  </div>
                </Pane>
                <Pane :size="50" :min-size="20">
                  <div class="panel graph-editor-panel">
                    <GraphEditor @close="showGraphEditor = false" />
                  </div>
                </Pane>
              </Splitpanes>
              <div v-else class="panel timeline-panel">
                <TimelinePanel @openCompositionSettings="showCompositionSettingsDialog = true" @openPathSuggestion="showPathSuggestionDialog = true" />
              </div>
            </Pane>
          </Splitpanes>
        </Pane>

        <!-- Right Panel: Effects/Properties/Camera -->
        <Pane :size="22" :min-size="15" :max-size="30">
          <div class="panel right-panel">
            <div class="panel-tabs">
              <button
                :class="{ active: rightTab === 'properties' }"
                @click="rightTab = 'properties'"
              >
                Properties
              </button>
              <button
                :class="{ active: rightTab === 'effects' }"
                @click="rightTab = 'effects'"
              >
                Effects
              </button>
              <button
                :class="{ active: rightTab === 'camera' }"
                @click="rightTab = 'camera'"
              >
                Cam
              </button>
              <button
                :class="{ active: rightTab === 'audio' }"
                @click="rightTab = 'audio'"
              >
                Audio
              </button>
              <button
                :class="{ active: rightTab === 'export' }"
                @click="rightTab = 'export'"
              >
                Export
              </button>
              <button
                :class="{ active: rightTab === 'preview' }"
                @click="rightTab = 'preview'"
              >
                Preview
              </button>
              <button
                :class="{ active: rightTab === 'ai' }"
                @click="rightTab = 'ai'"
                title="AI Compositor Agent"
              >
                AI
              </button>
            </div>
            <div class="panel-content">
              <EffectControlsPanel v-if="rightTab === 'effects'" />
              <PropertiesPanel v-else-if="rightTab === 'properties'" />
              <CameraProperties
                v-else-if="rightTab === 'camera'"
                :camera="activeCamera"
                @update:camera="updateCamera"
              />
              <AudioPanel v-else-if="rightTab === 'audio'" />
              <ExportPanel v-else-if="rightTab === 'export'" />
              <PreviewPanel v-else-if="rightTab === 'preview'" :engine="canvasEngine" />
              <AIChatPanel v-else-if="rightTab === 'ai'" />
            </div>
          </div>
        </Pane>
      </Splitpanes>
    </div>

    <!-- Status Bar -->
    <div class="status-bar">
      <div class="status-left">
        <span class="status-item">{{ projectName }}</span>
        <span class="status-divider">|</span>
        <span class="status-item">{{ compositionInfo }}</span>
      </div>
      <div class="status-center">
        <span v-if="renderProgress > 0" class="render-progress">
          Rendering: {{ Math.round(renderProgress * 100) }}%
        </span>
      </div>
      <div class="status-right">
        <span class="status-item">{{ memoryUsage }}</span>
        <span class="status-divider">|</span>
        <span class="status-item">{{ fps }} fps</span>
      </div>
    </div>

    <!-- Export Dialog -->
    <ExportDialog
      v-if="showExportDialog"
      @close="showExportDialog = false"
      @exported="onExportComplete"
    />

    <!-- ComfyUI Export Dialog -->
    <ComfyUIExportDialog
      v-if="showComfyUIExportDialog"
      :layers="store.layers"
      :camera-keyframes="activeCameraKeyframes"
      :current-frame="store.currentFrame"
      :total-frames="store.frameCount"
      @close="showComfyUIExportDialog = false"
      @exported="onComfyUIExportComplete"
    />

    <!-- Composition Settings Dialog -->
    <CompositionSettingsDialog
      :visible="showCompositionSettingsDialog"
      @close="showCompositionSettingsDialog = false"
      @confirm="onCompositionSettingsConfirm"
    />

    <!-- AI Path Suggestion Dialog -->
    <PathSuggestionDialog
      :visible="showPathSuggestionDialog"
      @close="onPathSuggestionClose"
      @accept="onPathSuggestionAccept"
      @preview="onPathSuggestionPreview"
    />

    <!-- HD Preview Window -->
    <HDPreviewWindow
      :visible="showHDPreview"
      :engine="canvasEngine"
      @close="showHDPreview = false"
    />

    <!-- Path Preview Overlay (shown in viewport when suggestions exist) -->
    <Teleport to=".viewport-content" v-if="pathSuggestions.length > 0">
      <PathPreviewOverlay
        :width="compWidth"
        :height="compHeight"
        :suggestions="pathSuggestions"
        :selectedIndex="selectedPathIndex"
        @select="selectedPathIndex = $event"
      />
    </Teleport>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted } from 'vue';
import { Splitpanes, Pane } from 'splitpanes';
import 'splitpanes/dist/splitpanes.css';

import { useCompositorStore } from '@/stores/compositorStore';
import { detectGPUTier, type GPUTier } from '@/services/gpuDetection';
import { createDefaultCamera, createDefaultViewportState } from '@/types/camera';
import type { Camera3D, ViewportState } from '@/types/camera';

// Panels
import ProjectPanel from '@/components/panels/ProjectPanel.vue';
import EffectsPanel from '@/components/panels/EffectsPanel.vue';
import EffectControlsPanel from '@/components/panels/EffectControlsPanel.vue';
import PropertiesPanel from '@/components/panels/PropertiesPanel.vue';
import CameraProperties from '@/components/panels/CameraProperties.vue';
import AudioPanel from '@/components/panels/AudioPanel.vue';
import AssetsPanel from '@/components/panels/AssetsPanel.vue';
import ExportPanel from '@/components/panels/ExportPanel.vue';
import PreviewPanel from '@/components/panels/PreviewPanel.vue';
import AIChatPanel from '@/components/panels/AIChatPanel.vue';

// Viewport
import ViewportRenderer from '@/components/viewport/ViewportRenderer.vue';
import ThreeCanvas from '@/components/canvas/ThreeCanvas.vue';

// Timeline
import TimelinePanel from '@/components/timeline/TimelinePanel.vue';
import GraphEditor from '@/components/graph-editor/GraphEditor.vue';

// Dialogs
import ExportDialog from '@/components/dialogs/ExportDialog.vue';
import ComfyUIExportDialog from '@/components/export/ComfyUIExportDialog.vue';
import CompositionSettingsDialog from '@/components/dialogs/CompositionSettingsDialog.vue';
import PathSuggestionDialog from '@/components/dialogs/PathSuggestionDialog.vue';

// Canvas overlays
import PathPreviewOverlay from '@/components/canvas/PathPreviewOverlay.vue';

// Preview
import HDPreviewWindow from '@/components/preview/HDPreviewWindow.vue';

// Stores
const store = useCompositorStore();
import { useAssetStore } from '@/stores/assetStore';
const assetStore = useAssetStore();

// Tool state - synced with store
const currentTool = computed({
  get: () => store.currentTool,
  set: (tool: 'select' | 'pen' | 'text' | 'hand' | 'zoom' | 'segment') => store.setTool(tool)
});

// Segmentation state - synced with store
const segmentMode = computed(() => store.segmentMode);
const segmentPendingMask = computed(() => store.segmentPendingMask);
const segmentIsLoading = computed(() => store.segmentIsLoading);

function setSegmentMode(mode: 'point' | 'box') {
  store.setSegmentMode(mode);
}

async function confirmSegmentMask() {
  await store.confirmSegmentMask();
}

function clearSegmentMask() {
  store.clearSegmentPendingMask();
}

const activeWorkspace = ref('standard');
const leftTab = ref<'project' | 'effects' | 'assets'>('project');
const rightTab = ref<'effects' | 'properties' | 'camera' | 'audio' | 'export' | 'preview' | 'ai'>('properties');
const viewportTab = ref<'composition' | 'layer' | 'footage'>('composition');

const viewZoom = ref('fit');
const showGraphEditor = ref(false);
const showExportDialog = ref(false);
const showComfyUIExportDialog = ref(false);
const showCompositionSettingsDialog = ref(false);
const showPathSuggestionDialog = ref(false);
const showHDPreview = ref(false);

// Vision authoring state
const pathSuggestions = ref<any[]>([]);
const selectedPathIndex = ref<number | null>(null);

const isPlaying = ref(false);
const gpuTier = ref<GPUTier['tier']>('cpu');

const threeCanvasRef = ref<InstanceType<typeof ThreeCanvas> | null>(null);

// Engine accessor for panels
const canvasEngine = computed(() => threeCanvasRef.value?.engine ?? null);

// Camera state - use computed to get from store, fallback to default
const activeCamera = computed<Camera3D>(() => {
  const cam = store.getActiveCameraAtFrame();
  if (cam) return cam;
  // Fallback to a default camera
  return createDefaultCamera('default', compWidth.value, compHeight.value);
});
const viewportState = ref<ViewportState>(createDefaultViewportState());
const viewOptions = ref({
  showGrid: true,
  showRulers: false,
  showAxes: true,
  showCameraFrustum: true,
  showCompositionBounds: true,
  showFocalPlane: false,
  showLayerOutlines: true,
  showSafeZones: false,
  gridSize: 100,
  gridDivisions: 10
});

// Composition dimensions
const compWidth = computed(() => store.project?.composition?.width || 1920);
const compHeight = computed(() => store.project?.composition?.height || 1080);

// Performance tracking
const fps = ref(60);
const memoryUsage = ref('0 MB');
const renderProgress = ref(0);

// Computed
const formattedTimecode = computed(() => {
  const frame = store.currentFrame;
  const fpsVal = store.project?.composition?.fps || 30;
  const totalSeconds = frame / fpsVal;
  const minutes = Math.floor(totalSeconds / 60);
  const seconds = Math.floor(totalSeconds % 60);
  const frames = frame % fpsVal;
  return `${String(minutes).padStart(2, '0')}:${String(seconds).padStart(2, '0')}:${String(frames).padStart(2, '0')}`;
});

const projectName = computed(() => {
  return store.project?.meta?.name || 'Untitled Project';
});

const compositionInfo = computed(() => {
  const comp = store.project?.composition;
  if (!comp) return 'No Composition';
  return `${comp.width}×${comp.height} @ ${comp.fps}fps`;
});

const canUndo = computed(() => store.canUndo);
const canRedo = computed(() => store.canRedo);

// Actions
function togglePlay() {
  isPlaying.value = !isPlaying.value;
  if (isPlaying.value) {
    store.play();
  } else {
    store.pause();
  }
}

function goToStart() {
  store.goToStart();
}

function goToEnd() {
  store.goToEnd();
}

function stepForward() {
  store.setFrame(store.currentFrame + 1);
}

function stepBackward() {
  store.setFrame(Math.max(0, store.currentFrame - 1));
}

function undo() {
  store.undo();
}

function redo() {
  store.redo();
}

function updateCamera(camera: Camera3D) {
  // Update the camera in the store
  if (store.activeCameraId) {
    store.updateCamera(camera.id, camera);
  }
}

function onExportComplete() {
  console.log('[Weyl] Matte export completed');
}

function onComfyUIExportComplete(result: any) {
  console.log('[Weyl] ComfyUI export completed', result);
  showComfyUIExportDialog.value = false;
}

function onCompositionSettingsConfirm(settings: {
  name: string;
  width: number;
  height: number;
  fps: number;
  frameCount: number;
  backgroundColor: string;
  autoResizeToContent: boolean;
}) {
  console.log('[Weyl] Composition settings updated:', settings);

  // Update active composition's settings
  store.updateCompositionSettings(store.activeCompositionId, {
    width: settings.width,
    height: settings.height,
    fps: settings.fps,
    frameCount: settings.frameCount,
    backgroundColor: settings.backgroundColor,
    autoResizeToContent: settings.autoResizeToContent
  });

  // Rename the composition
  store.renameComposition(store.activeCompositionId, settings.name);

  showCompositionSettingsDialog.value = false;
}

// Helper: Generate SVG path data from control points (for audio reactivity integration)
function generatePathDataFromPoints(
  points: Array<{ x: number; y: number; handleIn?: { x: number; y: number } | null; handleOut?: { x: number; y: number } | null }>,
  closed: boolean
): string {
  if (points.length === 0) return '';
  if (points.length === 1) return `M ${points[0].x} ${points[0].y}`;

  let d = `M ${points[0].x} ${points[0].y}`;

  for (let i = 0; i < points.length - 1; i++) {
    const p0 = points[i];
    const p1 = points[i + 1];

    // If both points have handles, use cubic bezier
    if (p0.handleOut && p1.handleIn) {
      const cp1x = p0.x + p0.handleOut.x;
      const cp1y = p0.y + p0.handleOut.y;
      const cp2x = p1.x + p1.handleIn.x;
      const cp2y = p1.y + p1.handleIn.y;
      d += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${p1.x} ${p1.y}`;
    } else if (p0.handleOut) {
      // Quadratic with control point from handleOut
      const cpx = p0.x + p0.handleOut.x;
      const cpy = p0.y + p0.handleOut.y;
      d += ` Q ${cpx} ${cpy}, ${p1.x} ${p1.y}`;
    } else if (p1.handleIn) {
      // Quadratic with control point from handleIn
      const cpx = p1.x + p1.handleIn.x;
      const cpy = p1.y + p1.handleIn.y;
      d += ` Q ${cpx} ${cpy}, ${p1.x} ${p1.y}`;
    } else {
      // Simple line
      d += ` L ${p1.x} ${p1.y}`;
    }
  }

  if (closed && points.length > 2) {
    d += ' Z';
  }

  return d;
}

// Path Suggestion handlers
function onPathSuggestionClose() {
  showPathSuggestionDialog.value = false;
  // Clear preview when dialog closes
  pathSuggestions.value = [];
  selectedPathIndex.value = null;
}

function onPathSuggestionPreview(suggestions: any[]) {
  pathSuggestions.value = suggestions;
  selectedPathIndex.value = suggestions.length > 0 ? 0 : null;
}

function onPathSuggestionAccept(result: { keyframes: any[]; splines: any[] }) {
  console.log('[Weyl] Path suggestion accepted:', result);

  // Apply keyframes to the store
  if (result.keyframes && result.keyframes.length > 0) {
    for (const batch of result.keyframes) {
      // batch contains layerId, propertyPath, and keyframes
      // Add keyframes to the appropriate layer/property
      for (const keyframe of batch.keyframes) {
        store.addKeyframe(batch.layerId, batch.propertyPath, keyframe.frame, keyframe.value, keyframe.easing);
      }
    }
  }

  // Create new spline layers if suggested
  if (result.splines && result.splines.length > 0) {
    for (const spline of result.splines) {
      // Create a new spline layer
      const layer = store.createSplineLayer();

      // Rename if name provided
      if (spline.name) {
        store.renameLayer(layer.id, spline.name);
      }

      // Convert points to control points format (preserve depth and handles from translator)
      const controlPoints = (spline.points || []).map((p: any, i: number) => ({
        id: p.id || `cp_${Date.now()}_${i}`,
        x: p.x,
        y: p.y,
        depth: p.depth ?? 0,  // Preserve z-space depth
        handleIn: p.handleIn || null,  // Preserve bezier handles from translator
        handleOut: p.handleOut || null,
        type: p.type || 'smooth' as const
      }));

      // Generate SVG path data from control points for audio reactivity
      const pathData = generatePathDataFromPoints(controlPoints, spline.closed || false);

      // Update the layer data with the points and pathData
      store.updateLayerData(layer.id, {
        controlPoints,
        pathData,
        closed: spline.closed || false
      });
    }
  }

  // Clear preview
  pathSuggestions.value = [];
  selectedPathIndex.value = null;
  showPathSuggestionDialog.value = false;
}

// Get camera keyframes for the active camera
const activeCameraKeyframes = computed(() => {
  const activeCam = store.getActiveCameraAtFrame();
  if (!activeCam) return [];
  return store.getCameraKeyframes(activeCam.id);
});

// Handle zoom dropdown change
function handleZoomChange() {
  if (!threeCanvasRef.value) return;

  if (viewZoom.value === 'fit') {
    threeCanvasRef.value.fitToView();
  } else {
    // Convert percentage string to decimal (e.g., '100' → 1.0, '200' → 2.0)
    const zoomLevel = parseInt(viewZoom.value) / 100;
    threeCanvasRef.value.setZoom(zoomLevel);
  }
}

// ========================================================================
// ASSETS PANEL HANDLERS
// ========================================================================

/**
 * Create layers from imported SVG paths
 */
function onCreateLayersFromSvg(svgId: string) {
  const storedSvg = assetStore.svgDocuments.get(svgId);
  if (!storedSvg) return;

  // Create a model layer for each path in the SVG
  storedSvg.document.paths.forEach((path, index) => {
    const config = storedSvg.layerConfigs[index];

    // Create a 3D model layer
    // Note: This would ideally create a proper ModelLayer with the extruded geometry
    // For now, we'll create a shape layer with the path data
    const layer = store.createShapeLayer();
    store.renameLayer(layer.id, `${storedSvg.name}_${path.id}`);

    // Store the SVG path reference in the layer data
    store.updateLayerData(layer.id, {
      svgDocumentId: svgId,
      svgPathId: path.id,
      svgPathIndex: index,
      extrusionConfig: config,
      // Set Z position based on layer depth
      transform: {
        ...layer.transform,
        position: {
          ...layer.transform.position,
          value: {
            ...layer.transform.position.value,
            z: config?.depth || 0
          }
        }
      }
    });
  });

  console.log(`[Weyl] Created ${storedSvg.document.paths.length} layers from SVG: ${storedSvg.name}`);
}

/**
 * Configure a particle emitter to use a mesh shape
 */
function onUseMeshAsEmitter(meshId: string) {
  const emitterConfig = assetStore.getMeshEmitterConfig(meshId);
  if (!emitterConfig) return;

  // Get the selected layer if it's a particle layer
  const selectedLayerIds = store.selectedLayerIds;
  if (selectedLayerIds.length === 0) {
    console.warn('[Weyl] No layer selected for mesh emitter');
    return;
  }

  const layer = store.layers.find(l => l.id === selectedLayerIds[0]);
  if (!layer || layer.type !== 'particle') {
    console.warn('[Weyl] Selected layer is not a particle layer');
    return;
  }

  // Update the particle layer's emitter config with mesh vertices
  store.updateLayerData(layer.id, {
    emitter: {
      ...(layer.data as any).emitter,
      shape: 'mesh',
      meshVertices: emitterConfig.meshVertices,
      meshNormals: emitterConfig.meshNormals,
    }
  });

  console.log(`[Weyl] Set mesh emitter for layer: ${layer.name}`);
}

/**
 * Update environment settings in the engine
 */
function onEnvironmentUpdate(settings: any) {
  if (!threeCanvasRef.value) return;
  const engine = threeCanvasRef.value.getEngine?.();
  if (!engine) return;

  engine.setEnvironmentConfig(settings);
}

/**
 * Load environment map into the engine
 */
async function onEnvironmentLoad(settings: any) {
  if (!threeCanvasRef.value) return;
  const engine = threeCanvasRef.value.getEngine?.();
  if (!engine) return;

  if (settings.url) {
    try {
      await engine.loadEnvironmentMap(settings.url, {
        intensity: settings.intensity,
        rotation: settings.rotation,
        backgroundBlur: settings.backgroundBlur,
        useAsBackground: settings.useAsBackground,
      });
      console.log('[Weyl] Environment map loaded');
    } catch (error) {
      console.error('[Weyl] Failed to load environment map:', error);
    }
  }
}

/**
 * Clear environment map from the engine
 */
function onEnvironmentClear() {
  if (!threeCanvasRef.value) return;
  const engine = threeCanvasRef.value.getEngine?.();
  if (!engine) return;

  engine.setEnvironmentEnabled(false);
}

// Keyboard shortcuts
function handleKeydown(e: KeyboardEvent) {
  // Don't handle if input is focused
  if (document.activeElement?.tagName === 'INPUT' ||
      document.activeElement?.tagName === 'TEXTAREA') {
    return;
  }

  switch (e.key.toLowerCase()) {
    case ' ':
      e.preventDefault();
      togglePlay();
      break;
    case 'p':
      currentTool.value = 'pen';
      break;
    case 't':
      currentTool.value = 'text';
      break;
    case 'h':
      currentTool.value = 'hand';
      break;
    case 'z':
      if (e.ctrlKey || e.metaKey) {
        e.preventDefault();
        if (e.shiftKey) {
          redo();
        } else {
          undo();
        }
      } else {
        currentTool.value = 'zoom';
      }
      break;
    case 'home':
      e.preventDefault();
      goToStart();
      break;
    case 'end':
      e.preventDefault();
      goToEnd();
      break;
    case 'arrowleft':
      e.preventDefault();
      stepBackward();
      break;
    case 'arrowright':
      e.preventDefault();
      stepForward();
      break;
    case 'g':
      if (e.shiftKey) {
        showGraphEditor.value = !showGraphEditor.value;
      }
      break;
    case 'k':
      if (e.ctrlKey || e.metaKey) {
        e.preventDefault();
        showCompositionSettingsDialog.value = true;
      }
      break;
    case 'i':
      if (e.ctrlKey || e.metaKey) {
        e.preventDefault();
        triggerAssetImport();
      }
      break;
    case 'a':
      if (e.ctrlKey || e.metaKey) {
        // Select all layers
        e.preventDefault();
        store.selectAllLayers();
      } else {
        // Switch to Assets tab
        leftTab.value = 'assets';
      }
      break;
    case 'delete':
    case 'backspace':
      // Delete selected layers
      if (store.selectedLayerIds.length > 0) {
        e.preventDefault();
        store.deleteSelectedLayers();
      }
      break;
    case 'c':
      if (e.ctrlKey || e.metaKey) {
        // Copy selected layers
        e.preventDefault();
        store.copySelectedLayers();
      }
      break;
    case 'd':
      if (e.ctrlKey || e.metaKey) {
        // Duplicate selected layers
        e.preventDefault();
        store.duplicateSelectedLayers();
      }
      break;
    case 'v':
      if (e.ctrlKey || e.metaKey) {
        // Paste layers from clipboard
        e.preventDefault();
        store.pasteLayers();
      } else if (!e.shiftKey) {
        // Select tool (existing behavior)
        currentTool.value = 'select';
      }
      break;
    case 'x':
      if (e.ctrlKey || e.metaKey) {
        // Cut selected layers
        e.preventDefault();
        store.cutSelectedLayers();
      }
      break;
  }
}

// Import dialog trigger
const importFileInput = ref<HTMLInputElement | null>(null);

function triggerAssetImport() {
  // Create a temporary file input for import
  const input = document.createElement('input');
  input.type = 'file';
  input.accept = '.svg,.gltf,.glb,.obj,.fbx,.hdr,.exr,.png,.jpg';
  input.multiple = true;
  input.onchange = async (e) => {
    const files = (e.target as HTMLInputElement).files;
    if (!files) return;

    for (const file of files) {
      const ext = file.name.split('.').pop()?.toLowerCase();
      if (ext === 'svg') {
        await assetStore.importSvgFromFile(file);
      } else if (['hdr', 'exr'].includes(ext || '')) {
        await assetStore.loadEnvironment(file);
      }
      // Models and other assets handled by AssetsPanel
    }

    // Switch to assets tab to show imported items
    leftTab.value = 'assets';
  };
  input.click();
}

// Performance monitoring
let perfInterval: number;

function updatePerformanceStats() {
  // Memory usage (if available)
  if ('memory' in performance) {
    const mem = (performance as any).memory;
    const usedMB = Math.round(mem.usedJSHeapSize / 1024 / 1024);
    memoryUsage.value = `${usedMB} MB`;
  }
}

// Lifecycle
onMounted(async () => {
  const tierInfo = await detectGPUTier();
  gpuTier.value = tierInfo.tier;

  window.addEventListener('keydown', handleKeydown);

  perfInterval = window.setInterval(updatePerformanceStats, 1000);

  // Start autosave timer
  if (store.autosaveEnabled) {
    store.startAutosaveTimer();
  }
});

onUnmounted(() => {
  window.removeEventListener('keydown', handleKeydown);
  clearInterval(perfInterval);

  // Stop autosave timer
  store.stopAutosaveTimer();
});
</script>

<style scoped>
.workspace-layout {
  display: flex;
  flex-direction: column;
  height: 100vh;
  background: #1a1a1a;
  color: #e0e0e0;
  font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
  font-size: 12px;
}

/* Toolbar */
.toolbar {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 4px 8px;
  background: #2a2a2a;
  border-bottom: 1px solid #3a3a3a;
  min-height: 36px;
}

.tool-group {
  display: flex;
  align-items: center;
  gap: 2px;
}

.tool-group button {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 4px;
  min-width: 28px;
  height: 28px;
  padding: 0 6px;
  border: none;
  background: transparent;
  color: #aaa;
  border-radius: 4px;
  cursor: pointer;
  font-size: 12px;
}

.labeled-tools button {
  flex-direction: column;
  gap: 1px;
  min-width: 44px;
  height: 36px;
  padding: 2px 6px;
}

.tool-label {
  font-size: 9px;
  color: #888;
  line-height: 1;
}

.labeled-tools button.active .tool-label {
  color: #fff;
}

.labeled-tools button:hover .tool-label {
  color: #ccc;
}

.tool-group button:hover {
  background: #3a3a3a;
  color: #fff;
}

.tool-group button.active {
  background: #4a90d9;
  color: #fff;
}

.tool-group button:disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.icon {
  font-size: 14px;
}

.divider {
  width: 1px;
  height: 20px;
  background: #3a3a3a;
  margin: 0 4px;
}

.spacer {
  flex: 1;
}

.timecode-display {
  font-family: 'SF Mono', Monaco, monospace;
  font-size: 14px;
  padding: 4px 12px;
  background: #1a1a1a;
  border-radius: 4px;
  min-width: 90px;
  text-align: center;
}

.workspace-selector {
  padding: 4px 8px;
  background: #1a1a1a;
  border: 1px solid #3a3a3a;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 13px;
}

.gpu-badge {
  font-size: 11px;
  padding: 2px 6px;
  border-radius: 3px;
  font-weight: bold;
  text-transform: uppercase;
}

.gpu-badge.cpu { background: #555; }
.gpu-badge.webgl { background: #4a7c4a; }
.gpu-badge.webgpu { background: #4a6a9c; }
.gpu-badge.blackwell { background: #76b900; color: #000; }

.ai-btn {
  background: linear-gradient(135deg, #6366f1, #8b5cf6) !important;
  color: #fff !important;
}

.ai-btn:hover {
  background: linear-gradient(135deg, #7c7ff1, #9d7af6) !important;
}

/* Main Workspace */
.workspace-content {
  flex: 1;
  min-height: 0;
  overflow: hidden;
}

.horizontal-split {
  height: 100%;
}

/* Panels */
.panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: #1e1e1e;
  overflow: hidden;
}

.left-panel,
.right-panel {
  border-right: 1px solid #2a2a2a;
}

.right-panel {
  border-right: none;
  border-left: 1px solid #2a2a2a;
}

.panel-tabs {
  display: flex;
  background: #252525;
  border-bottom: 1px solid #2a2a2a;
}

.panel-tabs button {
  flex: 1;
  padding: 8px 12px;
  border: none;
  background: transparent;
  color: #888;
  font-size: 13px;
  cursor: pointer;
  border-bottom: 2px solid transparent;
}

.panel-tabs button:hover {
  color: #e0e0e0;
}

.panel-tabs button.active {
  color: #e0e0e0;
  border-bottom-color: #4a90d9;
}

.panel-content {
  flex: 1;
  overflow: hidden;
}

/* Viewport */
.viewport-panel {
  background: #1a1a1a;
}

.viewport-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 4px 8px;
  background: #252525;
  border-bottom: 1px solid #2a2a2a;
}

.viewport-tabs {
  display: flex;
  gap: 2px;
}

.viewport-tabs button {
  padding: 4px 10px;
  border: none;
  background: transparent;
  color: #888;
  font-size: 13px;
  border-radius: 4px;
  cursor: pointer;
}

.viewport-tabs button:hover {
  color: #e0e0e0;
}

.viewport-tabs button.active {
  background: #3a3a3a;
  color: #e0e0e0;
}

.viewport-controls {
  display: flex;
  align-items: center;
  gap: 4px;
}

.zoom-select {
  padding: 2px 6px;
  background: #1a1a1a;
  border: 1px solid #3a3a3a;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 12px;
}

.viewport-controls button {
  width: 24px;
  height: 24px;
  padding: 0;
  border: none;
  background: transparent;
  color: #666;
  border-radius: 3px;
  cursor: pointer;
  font-size: 12px;
}

.viewport-controls button:hover {
  background: #3a3a3a;
  color: #e0e0e0;
}

.viewport-controls button.active {
  color: #4a90d9;
}

.viewport-content {
  flex: 1;
  display: flex;
  align-items: center;
  justify-content: center;
  background: #111;
  overflow: hidden;
  position: relative;
}

/* Rulers */
.rulers-overlay {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 100;
}

.ruler {
  position: absolute;
  background: rgba(30, 30, 30, 0.9);
  font-size: 11px;
  color: #888;
}

.ruler-horizontal {
  top: 0;
  left: 20px;
  right: 0;
  height: 20px;
  border-bottom: 1px solid #444;
}

.ruler-vertical {
  top: 20px;
  left: 0;
  bottom: 0;
  width: 20px;
  border-right: 1px solid #444;
}

.ruler .tick {
  position: absolute;
  font-size: 11px;
  color: #666;
}

.ruler-horizontal .tick {
  transform: translateX(-50%);
  top: 4px;
}

.ruler-vertical .tick {
  transform: translateY(-50%) rotate(-90deg);
  left: 2px;
  white-space: nowrap;
}

/* Timeline Panel */
.timeline-panel {
  border-top: 1px solid #2a2a2a;
}

.graph-editor-panel {
  border-top: 1px solid #2a2a2a;
}

/* Status Bar */
.status-bar {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 4px 12px;
  background: #252525;
  border-top: 1px solid #2a2a2a;
  font-size: 12px;
  color: #888;
}

.status-left,
.status-center,
.status-right {
  display: flex;
  align-items: center;
  gap: 8px;
}

.status-divider {
  color: #444;
}

.render-progress {
  color: #4a90d9;
}

/* Splitpanes Theme Overrides */
:deep(.splitpanes.default-theme .splitpanes__pane) {
  background: transparent;
}

:deep(.splitpanes.default-theme .splitpanes__splitter) {
  background: #2a2a2a;
  border: none;
}

:deep(.splitpanes.default-theme .splitpanes__splitter:hover) {
  background: #4a90d9;
}

:deep(.splitpanes--vertical > .splitpanes__splitter) {
  width: 4px;
  min-width: 4px;
}

:deep(.splitpanes--horizontal > .splitpanes__splitter) {
  height: 4px;
  min-height: 4px;
}

/* Segmentation tool options */
.segment-options {
  display: flex;
  align-items: center;
  gap: 4px;
}

.segment-options .confirm-btn {
  background: #2d7a2d !important;
  color: #fff !important;
}

.segment-options .confirm-btn:hover {
  background: #3a9a3a !important;
}

.segment-options .cancel-btn {
  background: #7a2d2d !important;
  color: #fff !important;
}

.segment-options .cancel-btn:hover {
  background: #9a3a3a !important;
}

.loading-indicator {
  color: #00ff00;
  font-size: 13px;
  padding: 0 8px;
  animation: pulse 1s ease-in-out infinite;
}

@keyframes pulse {
  0%, 100% { opacity: 0.6; }
  50% { opacity: 1; }
}
</style>