<template>
  <div class="workspace-layout">
    <!-- Top Toolbar -->
    <div class="toolbar">
      <div class="tool-group">
        <button
          :class="{ active: currentTool === 'select' }"
          @click="currentTool = 'select'"
          title="Select (V)"
        >
          <span class="icon">↖</span>
        </button>
        <button
          :class="{ active: currentTool === 'pen' }"
          @click="currentTool = 'pen'"
          title="Pen Tool (P)"
        >
          <span class="icon">✒</span>
        </button>
        <button
          :class="{ active: currentTool === 'text' }"
          @click="currentTool = 'text'"
          title="Text Tool (T)"
        >
          <span class="icon">T</span>
        </button>
        <button
          :class="{ active: currentTool === 'hand' }"
          @click="currentTool = 'hand'"
          title="Hand Tool (H)"
        >
          <span class="icon">✋</span>
        </button>
        <button
          :class="{ active: currentTool === 'zoom' }"
          @click="currentTool = 'zoom'"
          title="Zoom Tool (Z)"
        >
          <span class="icon">🔍</span>
        </button>
      </div>

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
        <button @click="showExportDialog = true" title="Export">
          <span class="icon">📤</span> Export
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
            </div>
            <div class="panel-content">
              <ProjectPanel v-if="leftTab === 'project'" />
              <EffectsPanel v-else-if="leftTab === 'effects'" />
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
                      :class="{ active: showGuides }"
                      @click="showGuides = !showGuides"
                      title="Toggle Guides"
                    >
                      <span class="icon">📏</span>
                    </button>
                    <button
                      :class="{ active: showGrid }"
                      @click="showGrid = !showGrid"
                      title="Toggle Grid"
                    >
                      <span class="icon">▦</span>
                    </button>
                  </div>
                </div>
                <div class="viewport-content">
                  <CompositionCanvas v-if="viewportTab === 'composition'" ref="canvasRef" />
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
                    <TimelinePanel />
                  </div>
                </Pane>
                <Pane :size="50" :min-size="20">
                  <div class="panel graph-editor-panel">
                    <GraphEditor @close="showGraphEditor = false" />
                  </div>
                </Pane>
              </Splitpanes>
              <div v-else class="panel timeline-panel">
                <TimelinePanel />
              </div>
            </Pane>
          </Splitpanes>
        </Pane>

        <!-- Right Panel: Effects/Properties/Camera -->
        <Pane :size="18" :min-size="12" :max-size="25">
          <div class="panel right-panel">
            <div class="panel-tabs">
              <button
                :class="{ active: rightTab === 'effects' }"
                @click="rightTab = 'effects'"
              >
                Effects
              </button>
              <button
                :class="{ active: rightTab === 'properties' }"
                @click="rightTab = 'properties'"
              >
                Props
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
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted, watch } from 'vue';
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

// Viewport
import ViewportRenderer from '@/components/viewport/ViewportRenderer.vue';
import CompositionCanvas from '@/components/canvas/CompositionCanvas.vue';

// Timeline
import TimelinePanel from '@/components/timeline/TimelinePanel.vue';
import GraphEditor from '@/components/graph-editor/GraphEditor.vue';

// Dialogs
import ExportDialog from '@/components/dialogs/ExportDialog.vue';

// Store
const store = useCompositorStore();

// Tool state - synced with store
const currentTool = computed({
  get: () => store.currentTool,
  set: (tool: 'select' | 'pen' | 'text' | 'hand' | 'zoom') => store.setTool(tool)
});
const activeWorkspace = ref('standard');
const leftTab = ref<'project' | 'effects'>('project');
const rightTab = ref<'effects' | 'properties' | 'camera' | 'audio'>('effects');
const viewportTab = ref<'composition' | 'layer' | 'footage'>('composition');

const viewZoom = ref('fit');
const showGuides = ref(false);
const showGrid = ref(true);
const showGraphEditor = ref(false);
const showExportDialog = ref(false);

const isPlaying = ref(false);
const gpuTier = ref<GPUTier['tier']>('cpu');

const canvasRef = ref<InstanceType<typeof CompositionCanvas> | null>(null);

// Camera state
const activeCamera = ref<Camera3D>(createDefaultCamera());
const viewportState = ref<ViewportState>(createDefaultViewportState());
const viewOptions = ref({
  showGrid: true,
  showAxes: true,
  showCameraFrustum: true,
  showCompositionBounds: true,
  showFocalPlane: false,
  showLayerOutlines: true,
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
  activeCamera.value = camera;
}

function onExportComplete() {
  console.log('[Weyl] Export completed');
}

// Sync grid/guides state with canvas
watch(showGrid, (value) => {
  if (canvasRef.value) {
    canvasRef.value.showGrid = value;
  }
});

watch(showGuides, (value) => {
  if (canvasRef.value) {
    canvasRef.value.showGuides = value;
  }
});

// Handle zoom dropdown change
function handleZoomChange() {
  const canvas = canvasRef.value;
  if (!canvas) return;

  if (viewZoom.value === 'fit') {
    canvas.fitToView();
  } else {
    const zoomVal = parseInt(viewZoom.value) / 100;
    if (canvas.fabricCanvas) {
      canvas.fabricCanvas.setZoom(zoomVal);
      canvas.zoom = zoomVal;
      canvas.fabricCanvas.requestRenderAll();
    }
  }
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
    case 'v':
      currentTool.value = 'select';
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
  }
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
});

onUnmounted(() => {
  window.removeEventListener('keydown', handleKeydown);
  clearInterval(perfInterval);
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
  font-size: 11px;
}

.gpu-badge {
  font-size: 9px;
  padding: 2px 6px;
  border-radius: 3px;
  font-weight: bold;
  text-transform: uppercase;
}

.gpu-badge.cpu { background: #555; }
.gpu-badge.webgl { background: #4a7c4a; }
.gpu-badge.webgpu { background: #4a6a9c; }
.gpu-badge.blackwell { background: #76b900; color: #000; }

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
  font-size: 11px;
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
  font-size: 11px;
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
  font-size: 10px;
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
  font-size: 10px;
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
</style>