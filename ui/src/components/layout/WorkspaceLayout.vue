<!--
  @component WorkspaceLayout
  @description Main application layout component for Lattice Compositor.
  Orchestrates the complete motion graphics workspace including:
  - Top toolbar with drawing/selection tools
  - Left sidebar (Project/Effects panels)
  - Center canvas (ThreeCanvas renderer)
  - Right sidebar (Properties/AI Agent panels)
  - Bottom timeline panel
  - HD Preview window
  - Modal dialogs (composition settings, AI chat, exports)

  @features
  - Responsive panel sizing with splitters
  - Tool selection (select, pen, text, hand, segment)
  - Keyboard shortcut handling
  - AI agent integration for natural language animation
  - HD preview window toggle

  @emits None - root layout component
  @slots None
-->
<template>
  <div class="workspace-layout">
    <!-- Menu Bar -->
    <MenuBar
      @action="handleMenuAction"
      @showPreferences="showPreferencesDialog = true"
      @showProjectSettings="showCompositionSettingsDialog = true"
    />

    <!-- Top Toolbar -->
    <WorkspaceToolbar
      v-model:currentTool="currentTool"
      :isPlaying="isPlaying"
      :gpuTier="gpuTier"
      @import="triggerAssetImport"
      @showPreview="showHDPreview = true"
      @showExport="showExportDialog = true"
      @showComfyUI="showComfyUIExportDialog = true"
    />

    <!-- Main Workspace with Splitpanes -->
    <div class="workspace-content">
      <Splitpanes class="default-theme horizontal-split">
        <!-- Left Panel: Project/Effects -->
        <Pane :size="14" :min-size="10" :max-size="20">
          <div class="panel left-panel">
            <div class="panel-tabs" role="tablist" aria-label="Left panel tabs">
              <button
                role="tab"
                :aria-selected="leftTab === 'project'"
                aria-controls="left-panel-project"
                :class="{ active: leftTab === 'project' }"
                @click="leftTab = 'project'"
              >
                Project
              </button>
              <button
                role="tab"
                :aria-selected="leftTab === 'effects'"
                aria-controls="left-panel-effects"
                :class="{ active: leftTab === 'effects' }"
                @click="leftTab = 'effects'"
              >
                Effects
              </button>
              <button
                role="tab"
                :aria-selected="leftTab === 'assets'"
                aria-controls="left-panel-assets"
                :class="{ active: leftTab === 'assets' }"
                @click="leftTab = 'assets'"
              >
                Assets
              </button>
            </div>
            <div class="panel-content" role="tabpanel" :id="`left-panel-${leftTab}`">
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
        <Pane :size="66" :min-size="45">
          <Splitpanes horizontal class="default-theme">
            <!-- Viewport -->
            <Pane :size="65" :min-size="20">
              <div class="panel viewport-panel">
                <div class="viewport-header">
                  <div class="viewport-tabs" role="tablist" aria-label="Viewport tabs">
                    <button
                      role="tab"
                      :aria-selected="viewportTab === 'composition'"
                      :class="{ active: viewportTab === 'composition' }"
                      @click="viewportTab = 'composition'"
                    >
                      Composition
                    </button>
                    <button
                      role="tab"
                      :aria-selected="viewportTab === 'layer'"
                      :class="{ active: viewportTab === 'layer' }"
                      @click="viewportTab = 'layer'"
                    >
                      Layer
                    </button>
                    <button
                      role="tab"
                      :aria-selected="viewportTab === 'footage'"
                      :class="{ active: viewportTab === 'footage' }"
                      @click="viewportTab = 'footage'"
                    >
                      Footage
                    </button>
                  </div>
                  <div class="viewport-controls">
                    <button
                      :class="{ active: viewOptions.showRulers }"
                      @click="viewOptions.showRulers = !viewOptions.showRulers"
                      title="Toggle Rulers/Guides"
                      aria-label="Toggle rulers and guides"
                      :aria-pressed="viewOptions.showRulers"
                    >
                      <span class="icon" aria-hidden="true">📏</span>
                    </button>
                    <button
                      :class="{ active: viewOptions.showGrid }"
                      @click="viewOptions.showGrid = !viewOptions.showGrid"
                      title="Toggle Grid"
                      aria-label="Toggle grid"
                      :aria-pressed="viewOptions.showGrid"
                    >
                      <span class="icon">▦</span>
                    </button>
                  </div>
                </div>
                <div class="viewport-content" :class="{ 'rulers-active': viewOptions.showRulers }">
                  <!-- Grid overlay -->
                  <div v-if="viewOptions.showGrid" class="grid-overlay" :style="gridOverlayStyle"></div>

                  <!-- Guides overlay -->
                  <div v-if="guides.length > 0" class="guides-overlay">
                    <div
                      v-for="guide in guides"
                      :key="guide.id"
                      :class="['guide', guide.orientation]"
                      :style="getGuideStyle(guide)"
                      @mousedown="startGuideDrag(guide, $event)"
                      @contextmenu.prevent="showGuideContextMenu(guide, $event)"
                    >
                      <button
                        class="guide-delete-btn"
                        @click.stop="removeGuide(guide.id)"
                        @mousedown.stop
                        title="Delete guide"
                      >×</button>
                    </div>
                  </div>

                  <!-- Guide context menu -->
                  <Teleport to="body">
                    <div
                      v-if="guideContextMenu.visible"
                      class="guide-context-menu"
                      :style="{ left: guideContextMenu.x + 'px', top: guideContextMenu.y + 'px' }"
                      @click.stop
                    >
                      <button @click="deleteGuideFromMenu">Delete Guide</button>
                      <button @click="clearAllGuides">Clear All Guides</button>
                    </div>
                  </Teleport>

                  <!-- Rulers overlay -->
                  <div v-if="viewOptions.showRulers" class="rulers-overlay">
                    <div class="ruler ruler-horizontal" @mousedown="createGuideFromRuler('horizontal', $event)">
                      <span v-for="i in 20" :key="'h'+i" class="tick" :style="{ left: (i * 5) + '%' }">
                        {{ Math.round((i * 5 / 100) * compWidth) }}
                      </span>
                    </div>
                    <div class="ruler ruler-vertical" @mousedown="createGuideFromRuler('vertical', $event)">
                      <span v-for="i in 20" :key="'v'+i" class="tick" :style="{ top: (i * 5) + '%' }">
                        {{ Math.round((i * 5 / 100) * compHeight) }}
                      </span>
                    </div>
                  </div>

                  <!-- Snap indicator -->
                  <div v-if="snapEnabled && (snapIndicatorX || snapIndicatorY)" class="snap-indicator">
                    <div v-if="snapIndicatorX" class="snap-line vertical" :style="{ left: snapIndicatorX + 'px' }"></div>
                    <div v-if="snapIndicatorY" class="snap-line horizontal" :style="{ top: snapIndicatorY + 'px' }"></div>
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
              <Splitpanes v-if="showCurveEditor" horizontal class="default-theme">
                <Pane :size="50" :min-size="20">
                  <div class="panel timeline-panel">
                    <TimelinePanel @openCompositionSettings="showCompositionSettingsDialog = true" @openPathSuggestion="showPathSuggestionDialog = true" />
                  </div>
                </Pane>
                <Pane :size="50" :min-size="20">
                  <div class="panel curve-editor-panel">
                    <CurveEditor @close="showCurveEditor = false" />
                  </div>
                </Pane>
              </Splitpanes>
              <div v-else class="panel timeline-panel">
                <TimelinePanel @openCompositionSettings="showCompositionSettingsDialog = true" @openPathSuggestion="showPathSuggestionDialog = true" />
              </div>
            </Pane>
          </Splitpanes>
        </Pane>

        <!-- Right Panel: Stacked Collapsible Panels -->
        <Pane :size="20" :min-size="14" :max-size="30">
          <Splitpanes horizontal class="default-theme right-splitpanes">
            <!-- Main Properties Section -->
            <Pane :size="45" :min-size="25">
              <div class="panel right-panel stacked-panels">
                <div class="panel-content">
                  <!-- Properties Panel -->
                  <CollapsiblePanel title="Properties" :expanded="expandedPanels.properties" @toggle="expandedPanels.properties = $event">
                    <PropertiesPanel />
                  </CollapsiblePanel>

                  <!-- Effects Panel -->
                  <CollapsiblePanel title="Effects" :expanded="expandedPanels.effects" @toggle="expandedPanels.effects = $event">
                    <EffectControlsPanel />
                  </CollapsiblePanel>

                  <!-- Drivers Panel -->
                  <CollapsiblePanel title="Drivers" :expanded="expandedPanels.drivers" @toggle="expandedPanels.drivers = $event">
                    <DriverList />
                  </CollapsiblePanel>

                  <!-- Scopes Panel -->
                  <CollapsiblePanel title="Scopes" :expanded="expandedPanels.scopes" @toggle="expandedPanels.scopes = $event">
                    <ScopesPanel />
                  </CollapsiblePanel>

                  <!-- Camera Panel -->
                  <CollapsiblePanel title="Camera" :expanded="expandedPanels.camera" @toggle="expandedPanels.camera = $event">
                    <CameraProperties
                      :camera="activeCamera"
                      @update:camera="updateCamera"
                    />
                  </CollapsiblePanel>

                  <!-- Audio Panel -->
                  <CollapsiblePanel title="Audio" :expanded="expandedPanels.audio" @toggle="expandedPanels.audio = $event">
                    <AudioPanel />
                  </CollapsiblePanel>

                  <!-- Align Panel -->
                  <CollapsiblePanel title="Align" :expanded="expandedPanels.align" @toggle="expandedPanels.align = $event">
                    <AlignPanel />
                  </CollapsiblePanel>

                  <!-- Preview Panel -->
                  <CollapsiblePanel title="Preview" :expanded="expandedPanels.preview" @toggle="expandedPanels.preview = $event">
                    <PreviewPanel :engine="canvasEngine" />
                  </CollapsiblePanel>

                  <!-- Essential Graphics Panel -->
                  <CollapsiblePanel title="Essential Graphics" :expanded="expandedPanels.essentialGraphics" @toggle="expandedPanels.essentialGraphics = $event">
                    <EssentialGraphicsPanel />
                  </CollapsiblePanel>

                  <!-- Render Queue Panel -->
                  <CollapsiblePanel title="Render Queue" :expanded="expandedPanels.renderQueue" @toggle="expandedPanels.renderQueue = $event">
                    <RenderQueuePanel />
                  </CollapsiblePanel>
                </div>
              </div>
            </Pane>

            <!-- AI Section (Bottom) -->
            <Pane :size="55" :min-size="30">
              <div class="panel ai-section">
                <div class="ai-section-header">
                  <span class="ai-section-title">AI Tools</span>
                </div>
                <div class="ai-section-tabs">
                  <button
                    :class="{ active: aiTab === 'chat' }"
                    @click="aiTab = 'chat'"
                    title="AI Compositor Agent"
                  >
                    Chat
                  </button>
                  <button
                    :class="{ active: aiTab === 'generate' }"
                    @click="aiTab = 'generate'"
                    title="AI Generation (Depth, Normal, Segment)"
                  >
                    Generate
                  </button>
                  <button
                    :class="{ active: aiTab === 'flow' }"
                    @click="aiTab = 'flow'"
                    title="Generative Flow Trajectories for Wan-Move"
                  >
                    Flow
                  </button>
                  <button
                    :class="{ active: aiTab === 'decompose' }"
                    @click="aiTab = 'decompose'"
                    title="AI Layer Decomposition"
                  >
                    Decompose
                  </button>
                </div>
                <div class="ai-section-content">
                  <AIChatPanel v-if="aiTab === 'chat'" />
                  <AIGeneratePanel v-else-if="aiTab === 'generate'" />
                  <GenerativeFlowPanel v-else-if="aiTab === 'flow'" />
                  <LayerDecompositionPanel v-else-if="aiTab === 'decompose'" />
                </div>
              </div>
            </Pane>
          </Splitpanes>
        </Pane>
      </Splitpanes>
    </div>

    <!-- Status Bar removed - info relocated to toolbar and timeline -->

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

    <!-- Pre-compose Dialog -->
    <PrecomposeDialog
      :visible="showPrecomposeDialog"
      :layer-count="store.selectedLayerIds.length"
      @close="showPrecomposeDialog = false"
      @confirm="onPrecomposeConfirm"
    />

    <!-- Keyframe Interpolation Dialog -->
    <KeyframeInterpolationDialog
      :visible="showKeyframeInterpolationDialog"
      :keyframe-count="store.selectedKeyframeIds.length"
      @close="showKeyframeInterpolationDialog = false"
      @confirm="onKeyframeInterpolationConfirm"
    />

    <!-- Time Stretch Dialog -->
    <TimeStretchDialog
      :visible="showTimeStretchDialog"
      :layer-id="store.selectedLayerIds[0] ?? ''"
      @close="showTimeStretchDialog = false"
      @applied="showTimeStretchDialog = false"
    />

    <!-- Camera Tracking Import Dialog -->
    <CameraTrackingImportDialog
      :visible="showCameraTrackingImportDialog"
      @close="showCameraTrackingImportDialog = false"
      @imported="onCameraTrackingImported"
    />

    <!-- Preferences Dialog -->
    <PreferencesDialog
      :visible="showPreferencesDialog"
      @close="showPreferencesDialog = false"
      @save="handlePreferencesSave"
    />

    <!-- Keyboard Shortcuts Modal -->
    <KeyboardShortcutsModal
      :show="showKeyboardShortcutsModal"
      @close="showKeyboardShortcutsModal = false"
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

    <!-- Global Expression Editor -->
    <ExpressionInput
      :visible="expressionEditor.isVisible.value"
      :current-expression="expressionEditor.currentProperty.value?.expression"
      @close="expressionEditor.closeExpressionEditor()"
      @apply="expressionEditor.applyExpression($event)"
      @remove="expressionEditor.removeExpression()"
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

    <!-- Track Point Overlay (shown in viewport when camera tracking points exist) -->
    <Teleport to=".viewport-content" v-if="trackPointsState.tracks.value.length > 0">
      <TrackPointOverlay
        :width="compWidth"
        :height="compHeight"
        :currentFrame="currentFrame"
        :showTrails="viewOptions.showGuides"
        :showLabels="true"
        :editable="true"
      />
    </Teleport>

    <!-- Global Toast Notifications -->
    <ToastContainer />
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted, provide, type Ref } from 'vue';
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
import PreviewPanel from '@/components/panels/PreviewPanel.vue';
import AIChatPanel from '@/components/panels/AIChatPanel.vue';
import AIGeneratePanel from '@/components/panels/AIGeneratePanel.vue';
import GenerativeFlowPanel from '@/components/panels/GenerativeFlowPanel.vue';
import AlignPanel from '@/components/panels/AlignPanel.vue';
import EssentialGraphicsPanel from '@/components/panels/EssentialGraphicsPanel.vue';
import RenderQueuePanel from '@/components/panels/RenderQueuePanel.vue';
import ScopesPanel from '@/components/panels/ScopesPanel.vue';
import DriverList from '@/components/panels/DriverList.vue';
import LayerDecompositionPanel from '@/components/panels/LayerDecompositionPanel.vue';
import CollapsiblePanel from '@/components/panels/CollapsiblePanel.vue';

// Layout
import WorkspaceToolbar from '@/components/layout/WorkspaceToolbar.vue';
import MenuBar from '@/components/layout/MenuBar.vue';

// Viewport
import ViewportRenderer from '@/components/viewport/ViewportRenderer.vue';
import ThreeCanvas from '@/components/canvas/ThreeCanvas.vue';

// Timeline
import TimelinePanel from '@/components/timeline/TimelinePanel.vue';
import CurveEditor from '@/components/curve-editor/CurveEditor.vue';

// Dialogs
import ExportDialog from '@/components/dialogs/ExportDialog.vue';
import ComfyUIExportDialog from '@/components/export/ComfyUIExportDialog.vue';
import CompositionSettingsDialog from '@/components/dialogs/CompositionSettingsDialog.vue';
import PrecomposeDialog from '@/components/dialogs/PrecomposeDialog.vue';
import PathSuggestionDialog from '@/components/dialogs/PathSuggestionDialog.vue';
import KeyframeInterpolationDialog from '@/components/dialogs/KeyframeInterpolationDialog.vue';
import TimeStretchDialog from '@/components/dialogs/TimeStretchDialog.vue';
import CameraTrackingImportDialog from '@/components/dialogs/CameraTrackingImportDialog.vue';
import PreferencesDialog from '@/components/dialogs/PreferencesDialog.vue';
import KeyboardShortcutsModal from '@/components/dialogs/KeyboardShortcutsModal.vue';
import ExpressionInput from '@/components/properties/ExpressionInput.vue';
import { useExpressionEditor } from '@/composables/useExpressionEditor';
import { useGuides } from '@/composables/useGuides';
import { useKeyboardShortcuts } from '@/composables/useKeyboardShortcuts';
import { useSelectionStore } from '@/stores/selectionStore';

// Canvas overlays
import PathPreviewOverlay from '@/components/canvas/PathPreviewOverlay.vue';
import TrackPointOverlay from '@/components/canvas/TrackPointOverlay.vue';

// Track point service
import { useTrackPoints } from '@/services/trackPointService';

// Preview
import HDPreviewWindow from '@/components/preview/HDPreviewWindow.vue';
import ToastContainer from '@/components/ui/ToastContainer.vue';

// Stores
const store = useCompositorStore();
import { useAssetStore } from '@/stores/assetStore';
const assetStore = useAssetStore();
import { useAudioStore } from '@/stores/audioStore';
import { usePlaybackStore } from '@/stores/playbackStore';
import { useHistoryStore } from '@/stores/historyStore';
const audioStore = useAudioStore();
const playbackStore = usePlaybackStore();
const historyStore = useHistoryStore();

// Expression editor composable
const expressionEditor = useExpressionEditor();

// Track points state for camera tracking overlay
const trackPointsState = useTrackPoints();

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

const leftTab = ref<'project' | 'effects' | 'assets'>('project');
const rightTab = ref<'effects' | 'properties' | 'camera' | 'audio' | 'preview' | 'ai' | 'generate'>('properties');

// Collapsible panel states
const expandedPanels = ref({
  properties: true,
  effects: false,
  drivers: false,
  scopes: false,
  camera: false,
  audio: false,
  align: false,
  preview: false,
  essentialGraphics: false,
  renderQueue: false
});

// AI section tab
const aiTab = ref<'chat' | 'generate' | 'flow' | 'decompose'>('chat');
const viewportTab = ref<'composition' | 'layer' | 'footage'>('composition');

const viewZoom = ref('fit');
const showCurveEditor = ref(false);
const showExportDialog = ref(false);
const showComfyUIExportDialog = ref(false);
const showCompositionSettingsDialog = ref(false);
const showPrecomposeDialog = ref(false);
const showPathSuggestionDialog = ref(false);
const showKeyframeInterpolationDialog = ref(false);
const showTimeStretchDialog = ref(false);
const showCameraTrackingImportDialog = ref(false);
const showPreferencesDialog = ref(false);
const showKeyboardShortcutsModal = ref(false);
const showHDPreview = ref(false);

// Vision authoring state
const pathSuggestions = ref<any[]>([]);
const selectedPathIndex = ref<number | null>(null);

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
  showGrid: false,
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

// Grid overlay computed style
const gridOverlayStyle = computed(() => {
  const size = viewOptions.value.gridSize || 100;
  const divisions = viewOptions.value.gridDivisions || 10;
  const minorSize = size / divisions;

  // Create a repeating grid pattern using CSS
  return {
    position: 'absolute',
    top: 0,
    left: 0,
    right: 0,
    bottom: 0,
    pointerEvents: 'none',
    zIndex: 5,
    backgroundImage: `
      linear-gradient(to right, ${gridColor.value} 1px, transparent 1px),
      linear-gradient(to bottom, ${gridColor.value} 1px, transparent 1px),
      linear-gradient(to right, ${gridMajorColor.value} 1px, transparent 1px),
      linear-gradient(to bottom, ${gridMajorColor.value} 1px, transparent 1px)
    `,
    backgroundSize: `
      ${minorSize}px ${minorSize}px,
      ${minorSize}px ${minorSize}px,
      ${size}px ${size}px,
      ${size}px ${size}px
    `,
    opacity: 0.5
  };
});

// Snap indicator state (for visual feedback)
const snapIndicatorX = ref<number | null>(null);
const snapIndicatorY = ref<number | null>(null);

// Composition dimensions
const compWidth = computed(() => store.project?.composition?.width || 1920);
const compHeight = computed(() => store.project?.composition?.height || 1080);

// ========================================================================
// KEYBOARD SHORTCUTS COMPOSABLE
// ========================================================================
const keyboard = useKeyboardShortcuts({
  showExportDialog,
  showCompositionSettingsDialog,
  showKeyframeInterpolationDialog,
  showPrecomposeDialog,
  showCurveEditor,
  showTimeStretchDialog,
  showCameraTrackingImportDialog,
  showKeyboardShortcutsModal,
  currentTool: currentTool as unknown as Ref<string>,
  leftTab: leftTab as unknown as Ref<string>,
  viewOptions,
  threeCanvasRef,
  viewZoom,
  compWidth,
  compHeight,
  assetStore
});

// Destructure commonly used values from keyboard composable
const {
  isPlaying,
  soloedProperty,
  soloedProperties,
  workAreaStart,
  workAreaEnd,
  showHiddenLayers,
  previewUpdatesPaused,
  showTransparencyGrid,
  gridColor,
  gridMajorColor,
  rulerUnits,
  snapEnabled,
  snapToGrid,
  snapToGuides,
  snapToLayers,
  snapTolerance,
  timelineZoom,
  viewerZoom,
  togglePlay,
  goToStart,
  goToEnd,
  stepForward,
  stepBackward,
  undo,
  redo,
  handleKeydown,
  setupProvides: setupKeyboardProvides,
  triggerAssetImport,
  toggleLayerHidden,
  clearWorkArea,
  setGridSize,
  toggleSnap
} = keyboard;

// Set up provides from keyboard composable
setupKeyboardProvides();

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

// ========================================================================
// GUIDES SYSTEM (using composable)
// ========================================================================
const {
  guides,
  guideContextMenu,
  addGuide,
  removeGuide,
  clearGuides,
  updateGuidePosition,
  showGuideContextMenu,
  deleteGuideFromMenu,
  clearAllGuides,
  getGuideStyle,
  createGuideFromRuler,
  startGuideDrag
} = useGuides();

// Provide guides state
provide('guides', guides);
provide('addGuide', addGuide);
provide('removeGuide', removeGuide);
provide('clearGuides', clearGuides);
provide('updateGuidePosition', updateGuidePosition);

// Provide frame capture for MOGRT export and other features
provide('captureFrame', async (): Promise<string | null> => {
  return threeCanvasRef.value?.captureFrame() ?? null;
});

// ========================================================================
// SNAP POINT CALCULATION (uses both guides and keyboard composable state)
// ========================================================================
function getSnapPoint(x: number, y: number): { x: number; y: number; snappedX: boolean; snappedY: boolean } {
  if (!snapEnabled.value) {
    return { x, y, snappedX: false, snappedY: false };
  }

  let snappedX = false;
  let snappedY = false;
  let resultX = x;
  let resultY = y;

  // Snap to grid (uses viewOptions.showGrid and viewOptions.gridSize)
  if (snapToGrid.value && viewOptions.value.showGrid) {
    const currentGridSize = viewOptions.value.gridSize || 50;
    const gridX = Math.round(x / currentGridSize) * currentGridSize;
    const gridY = Math.round(y / currentGridSize) * currentGridSize;

    if (Math.abs(x - gridX) < snapTolerance.value) {
      resultX = gridX;
      snappedX = true;
    }
    if (Math.abs(y - gridY) < snapTolerance.value) {
      resultY = gridY;
      snappedY = true;
    }
  }

  // Snap to guides
  if (snapToGuides.value) {
    for (const guide of guides.value) {
      if (guide.orientation === 'vertical' && Math.abs(x - guide.position) < snapTolerance.value) {
        resultX = guide.position;
        snappedX = true;
      }
      if (guide.orientation === 'horizontal' && Math.abs(y - guide.position) < snapTolerance.value) {
        resultY = guide.position;
        snappedY = true;
      }
    }
  }

  // Snap to composition edges and center
  const compCenterX = compWidth.value / 2;
  const compCenterY = compHeight.value / 2;

  if (Math.abs(x - compCenterX) < snapTolerance.value) {
    resultX = compCenterX;
    snappedX = true;
  }
  if (Math.abs(y - compCenterY) < snapTolerance.value) {
    resultY = compCenterY;
    snappedY = true;
  }
  if (Math.abs(x) < snapTolerance.value) {
    resultX = 0;
    snappedX = true;
  }
  if (Math.abs(y) < snapTolerance.value) {
    resultY = 0;
    snappedY = true;
  }
  if (Math.abs(x - compWidth.value) < snapTolerance.value) {
    resultX = compWidth.value;
    snappedX = true;
  }
  if (Math.abs(y - compHeight.value) < snapTolerance.value) {
    resultY = compHeight.value;
    snappedY = true;
  }

  return { x: resultX, y: resultY, snappedX, snappedY };
}

// Provide getSnapPoint (snap state already provided by keyboard composable)
provide('getSnapPoint', getSnapPoint);

function updateCamera(camera: Camera3D) {
  // Update the camera in the store
  if (store.activeCameraId) {
    store.updateCamera(camera.id, camera);
  }
}

// Play a notification chime when export completes
function playExportChime() {
  try {
    const audioCtx = new (window.AudioContext || (window as any).webkitAudioContext)();
    const gainNode = audioCtx.createGain();
    gainNode.connect(audioCtx.destination);
    gainNode.gain.setValueAtTime(0.3, audioCtx.currentTime);
    gainNode.gain.exponentialRampToValueAtTime(0.01, audioCtx.currentTime + 0.5);

    // Two-tone chime (pleasant major third)
    const freqs = [523.25, 659.25]; // C5, E5
    freqs.forEach((freq, i) => {
      const osc = audioCtx.createOscillator();
      osc.type = 'sine';
      osc.frequency.setValueAtTime(freq, audioCtx.currentTime + i * 0.1);
      osc.connect(gainNode);
      osc.start(audioCtx.currentTime + i * 0.1);
      osc.stop(audioCtx.currentTime + 0.5 + i * 0.1);
    });
  } catch (e) {
    // Silently fail if audio not available
    console.warn('[Lattice] Audio notification not available:', e);
  }
}

function onExportComplete() {
  console.log('[Lattice] Matte export completed');
  playExportChime();
}

function onComfyUIExportComplete(result: any) {
  console.log('[Lattice] ComfyUI export completed', result);
  showComfyUIExportDialog.value = false;
  playExportChime();
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
  console.log('[Lattice] Composition settings updated:', settings);

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

function onPrecomposeConfirm(name: string) {
  if (store.selectedLayerIds.length > 0) {
    store.nestSelectedLayers(name);
    showPrecomposeDialog.value = false;
  }
}

// Camera tracking import handler
function onCameraTrackingImported(result: { cameraLayerId?: string; warnings?: string[] }) {
  showCameraTrackingImportDialog.value = false;

  if (result.cameraLayerId) {
    // Select the imported camera
    store.selectLayer(result.cameraLayerId);
    console.log('Camera tracking imported successfully:', result.cameraLayerId);
  }

  if (result.warnings && result.warnings.length > 0) {
    console.warn('Camera tracking import warnings:', result.warnings);
  }
}

// Keyframe interpolation dialog handler
function onKeyframeInterpolationConfirm(settings: {
  interpolation: 'linear' | 'bezier' | 'hold';
  easingPreset: string;
  controlMode: 'symmetric' | 'smooth' | 'corner';
}) {
  const selectedKeyframeIds = store.selectedKeyframeIds;
  if (selectedKeyframeIds.length === 0) return;

  // Get the layers that contain these keyframes
  const layers = store.layers;
  for (const layer of layers) {
    const transform = layer.transform as any;
    if (!transform) continue;

    // Check all animatable properties for keyframes
    const props = ['position', 'rotation', 'scale', 'anchor', 'opacity'];
    for (const propName of props) {
      const prop = transform[propName];
      if (!prop?.keyframes) continue;

      for (const kf of prop.keyframes) {
        if (selectedKeyframeIds.includes(kf.id)) {
          // Update interpolation
          kf.interpolation = settings.interpolation;
          kf.controlMode = settings.controlMode;

          // For bezier, set easing preset handles
          if (settings.interpolation === 'bezier' && settings.easingPreset) {
            // Apply preset handle positions based on easing type
            const presetHandles = getEasingPresetHandles(settings.easingPreset);
            if (presetHandles) {
              kf.outHandle = { x: presetHandles.outX, y: presetHandles.outY };
              kf.inHandle = { x: presetHandles.inX, y: presetHandles.inY };
            }
          }
        }
      }
    }
  }

  // Mark dirty and log
  console.log(`[Lattice] Applied ${settings.interpolation} interpolation to ${selectedKeyframeIds.length} keyframes`);
  showKeyframeInterpolationDialog.value = false;
}

// Get bezier handle positions for easing presets
function getEasingPresetHandles(preset: string): { outX: number; outY: number; inX: number; inY: number } | null {
  // Standard easing preset handle positions
  const presets: Record<string, { outX: number; outY: number; inX: number; inY: number }> = {
    // Ease In
    'easeInSine': { outX: 0.47, outY: 0, inX: 0.745, inY: 0.715 },
    'easeInQuad': { outX: 0.55, outY: 0.085, inX: 0.68, inY: 0.53 },
    'easeInCubic': { outX: 0.55, outY: 0.055, inX: 0.675, inY: 0.19 },
    'easeInQuart': { outX: 0.895, outY: 0.03, inX: 0.685, inY: 0.22 },
    'easeInQuint': { outX: 0.755, outY: 0.05, inX: 0.855, inY: 0.06 },
    'easeInExpo': { outX: 0.95, outY: 0.05, inX: 0.795, inY: 0.035 },
    'easeInCirc': { outX: 0.6, outY: 0.04, inX: 0.98, inY: 0.335 },
    'easeInBack': { outX: 0.6, outY: -0.28, inX: 0.735, inY: 0.045 },
    'easeInElastic': { outX: 0.5, outY: -0.5, inX: 0.7, inY: 0 },

    // Ease Out
    'easeOutSine': { outX: 0.39, outY: 0.575, inX: 0.565, inY: 1 },
    'easeOutQuad': { outX: 0.25, outY: 0.46, inX: 0.45, inY: 0.94 },
    'easeOutCubic': { outX: 0.215, outY: 0.61, inX: 0.355, inY: 1 },
    'easeOutQuart': { outX: 0.165, outY: 0.84, inX: 0.44, inY: 1 },
    'easeOutQuint': { outX: 0.23, outY: 1, inX: 0.32, inY: 1 },
    'easeOutExpo': { outX: 0.19, outY: 1, inX: 0.22, inY: 1 },
    'easeOutCirc': { outX: 0.075, outY: 0.82, inX: 0.165, inY: 1 },
    'easeOutBack': { outX: 0.175, outY: 0.885, inX: 0.32, inY: 1.275 },
    'easeOutElastic': { outX: 0.3, outY: 1, inX: 0.5, inY: 1.5 },
    'easeOutBounce': { outX: 0.2, outY: 0.9, inX: 0.3, inY: 1 },

    // Ease In/Out
    'easeInOutSine': { outX: 0.445, outY: 0.05, inX: 0.55, inY: 0.95 },
    'easeInOutQuad': { outX: 0.455, outY: 0.03, inX: 0.515, inY: 0.955 },
    'easeInOutCubic': { outX: 0.645, outY: 0.045, inX: 0.355, inY: 1 },
    'easeInOutQuart': { outX: 0.77, outY: 0, inX: 0.175, inY: 1 },
    'easeInOutQuint': { outX: 0.86, outY: 0, inX: 0.07, inY: 1 },
    'easeInOutExpo': { outX: 1, outY: 0, inX: 0, inY: 1 },
    'easeInOutCirc': { outX: 0.785, outY: 0.135, inX: 0.15, inY: 0.86 },
    'easeInOutBack': { outX: 0.68, outY: -0.55, inX: 0.265, inY: 1.55 },
    'easeInOutElastic': { outX: 0.5, outY: -0.3, inX: 0.5, inY: 1.3 },
  };

  return presets[preset] || null;
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
  console.log('[Lattice] Path suggestion accepted:', result);

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
// MENU BAR ACTION HANDLER
// ========================================================================

/**
 * Handle actions from the menu bar
 */
function handleMenuAction(action: string) {
  switch (action) {
    // File menu
    case 'newProject':
      if (confirm('Create a new project? Unsaved changes will be lost.')) {
        store.newProject();
      }
      break;
    case 'openProject':
      triggerProjectOpen();
      break;
    case 'saveProject':
      store.saveProject();
      break;
    case 'saveProjectAs':
      store.saveProjectAs();
      break;
    case 'import':
      triggerAssetImport();
      break;
    case 'export':
      showExportDialog.value = true;
      break;

    // Edit menu
    case 'undo':
      historyStore.undo();
      break;
    case 'redo':
      historyStore.redo();
      break;
    case 'cut':
      store.cutSelected();
      break;
    case 'copy':
      store.copySelected();
      break;
    case 'paste':
      store.paste();
      break;
    case 'duplicate':
      store.duplicateSelectedLayers();
      break;
    case 'delete':
      store.deleteSelectedLayers();
      break;
    case 'selectAll':
      store.selectAllLayers();
      break;
    case 'deselectAll':
      store.clearSelection();
      break;

    // Create menu - layer types
    case 'createSolid':
      store.createLayer('solid');
      break;
    case 'createText':
      store.createLayer('text');
      break;
    case 'createShape':
      store.createLayer('spline');
      break;
    case 'createPath':
      store.createLayer('path');
      break;
    case 'createCamera':
      store.createLayer('camera');
      break;
    case 'createLight':
      store.createLayer('light');
      break;
    case 'createControl':
      store.createLayer('control');
      break;
    case 'createParticle':
      store.createLayer('particle');
      break;
    case 'createDepth':
      store.createLayer('depth');
      break;
    case 'createNormal':
      store.createLayer('normal');
      break;
    case 'createGenerated':
      store.createLayer('generated');
      break;
    case 'createGroup':
      store.createLayer('group');
      break;
    case 'createEffectLayer':
      store.createLayer('effectLayer');
      break;
    case 'createMatte':
      store.createLayer('matte');
      break;

    // Layer menu
    case 'precompose':
      showPrecomposeDialog.value = true;
      break;
    case 'splitLayer':
      store.splitLayerAtPlayhead();
      break;
    case 'timeStretch':
      showTimeStretchDialog.value = true;
      break;
    case 'timeReverse':
      store.reverseSelectedLayers();
      break;
    case 'freezeFrame':
      store.freezeFrameAtPlayhead();
      break;
    case 'lockLayer':
      store.toggleLayerLock();
      break;
    case 'toggleVisibility':
      store.toggleLayerVisibility();
      break;
    case 'isolateLayer':
      store.toggleLayerSolo();
      break;
    case 'bringToFront':
      store.bringToFront();
      break;
    case 'sendToBack':
      store.sendToBack();
      break;
    case 'bringForward':
      store.bringForward();
      break;
    case 'sendBackward':
      store.sendBackward();
      break;

    // View menu
    case 'zoomIn':
      handleZoomIn();
      break;
    case 'zoomOut':
      handleZoomOut();
      break;
    case 'zoomFit':
      viewZoom.value = 'fit';
      handleZoomChange();
      break;
    case 'zoom100':
      viewZoom.value = '100';
      handleZoomChange();
      break;
    case 'toggleCurveEditor':
      showCurveEditor.value = !showCurveEditor.value;
      break;

    // Window menu - panel visibility
    case 'showProperties':
      expandedPanels.value.properties = true;
      break;
    case 'showEffects':
      leftTab.value = 'effects';
      break;
    case 'showCamera':
      expandedPanels.value.camera = true;
      break;
    case 'showAudio':
      expandedPanels.value.audio = true;
      break;
    case 'showAlign':
      expandedPanels.value.align = true;
      break;
    case 'showAIChat':
      aiTab.value = 'chat';
      break;
    case 'showAIGenerate':
      aiTab.value = 'generate';
      break;
    case 'showExport':
      showExportDialog.value = true;
      break;
    case 'showPreview':
      showHDPreview.value = true;
      break;

    // Help menu
    case 'showKeyboardShortcuts':
      showPreferencesDialog.value = true;
      // Switch to shortcuts tab after dialog opens
      break;
    case 'showDocumentation':
      window.open('https://github.com/justinfleek/lattice-compositor', '_blank');
      break;
    case 'showAbout':
      alert('Lattice Compositor v7.6\n\nProfessional motion graphics compositor for ComfyUI.\n\nBuilt with Vue 3, Three.js, and Pinia.');
      break;

    default:
      console.warn('Unhandled menu action:', action);
  }
}

function handleZoomIn() {
  const levels = ['25', '50', '75', '100', '150', '200'];
  const currentIndex = levels.indexOf(viewZoom.value);
  if (currentIndex < levels.length - 1 && currentIndex >= 0) {
    viewZoom.value = levels[currentIndex + 1];
    handleZoomChange();
  } else if (viewZoom.value === 'fit') {
    viewZoom.value = '100';
    handleZoomChange();
  }
}

function handleZoomOut() {
  const levels = ['25', '50', '75', '100', '150', '200'];
  const currentIndex = levels.indexOf(viewZoom.value);
  if (currentIndex > 0) {
    viewZoom.value = levels[currentIndex - 1];
    handleZoomChange();
  }
}

function triggerProjectOpen() {
  const input = document.createElement('input');
  input.type = 'file';
  input.accept = '.lattice,.json';
  input.onchange = async (e) => {
    const file = (e.target as HTMLInputElement).files?.[0];
    if (file) {
      await store.loadProjectFromFile(file);
    }
  };
  input.click();
}

/**
 * Handle preferences save
 */
function handlePreferencesSave(preferences: any) {
  console.log('Preferences saved:', preferences);
  // Apply relevant preferences immediately
  if (preferences.theme) {
    // Theme would be applied via themeStore
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

  console.log(`[Lattice] Created ${storedSvg.document.paths.length} layers from SVG: ${storedSvg.name}`);
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
    console.warn('[Lattice] No layer selected for mesh emitter');
    return;
  }

  const layer = store.layers.find(l => l.id === selectedLayerIds[0]);
  if (!layer || layer.type !== 'particle') {
    console.warn('[Lattice] Selected layer is not a particle layer');
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

  console.log(`[Lattice] Set mesh emitter for layer: ${layer.name}`);
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
      console.log('[Lattice] Environment map loaded');
    } catch (error) {
      console.error('[Lattice] Failed to load environment map:', error);
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

// Freeze frame at playhead (available via Layer menu)
function freezeFrameSelectedLayers() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  for (const id of selectedIds) {
    store.freezeFrameAtPlayhead(id);
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
  /* Use 100% height for ComfyUI sidebar compatibility, fallback to 100vh for standalone */
  height: 100%;
  min-height: 100vh;
  background: var(--lattice-void, #0a0a0a);
  color: var(--lattice-text-primary, #e5e5e5);
  font-family: var(--lattice-font-sans, -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif);
  font-size: var(--lattice-text-base, 12px);
  /* Increased padding for floating panel effect */
  padding: 8px;
  gap: 8px;
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

/* Panels - floating islands with visible borders */
.panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--lattice-surface-1, #0f0f0f);
  border-radius: var(--lattice-radius-lg, 6px);
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  overflow: hidden;
}

.left-panel,
.right-panel {
  /* Visible borders for panel separation */
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  min-width: 180px;
}

.right-panel {
  /* Properties panel needs more space for controls */
  min-width: 200px;
}

.panel-tabs {
  display: flex;
  background: var(--lattice-surface-0, #0a0a0a);
  padding: 10px 10px 0 10px;
  gap: 4px;
  border-bottom: 1px solid var(--lattice-border-default, #2a2a2a);
}

.panel-tabs button {
  flex: 1;
  padding: 12px 14px;
  border: none;
  background: var(--lattice-surface-1, #0f0f0f);
  color: var(--lattice-text-muted, #6B7280);
  font-size: var(--lattice-text-base, 13px);
  font-weight: 600;
  cursor: pointer;
  border-radius: var(--lattice-radius-md, 4px) var(--lattice-radius-md, 4px) 0 0;
  transition: var(--lattice-transition-fast, 100ms ease);
  border-bottom: 2px solid transparent;
  margin-bottom: -1px;
}

.panel-tabs button:hover {
  color: var(--lattice-text-primary, #e5e5e5);
  background: var(--lattice-surface-2, #1a1a1a);
}

.panel-tabs button.active {
  color: white;
  background: var(--lattice-surface-1, #0f0f0f);
  font-weight: 600;
  border-bottom: 2px solid var(--lattice-accent, #8B5CF6);
}

.panel-tabs button:focus-visible {
  outline: 2px solid var(--lattice-accent, #8B5CF6);
  outline-offset: 2px;
}

.panel-content {
  flex: 1;
  overflow-y: auto;
  overflow-x: hidden;
}

/* Custom scrollbar styling for dark theme */
.panel-content::-webkit-scrollbar {
  width: 8px;
}

.panel-content::-webkit-scrollbar-track {
  background: var(--lattice-surface-1, #121212);
}

.panel-content::-webkit-scrollbar-thumb {
  background: var(--lattice-surface-3, #333);
  border-radius: 4px;
}

.panel-content::-webkit-scrollbar-thumb:hover {
  background: var(--lattice-surface-4, #444);
}

/* Stacked Collapsible Panels */
.stacked-panels {
  display: flex;
  flex-direction: column;
}

.stacked-panels .panel-content {
  padding: 0;
}

/* Right Splitpanes styling */
.right-splitpanes {
  height: 100%;
}

/* AI Section */
.ai-section {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--lattice-surface-1, #0f0f0f);
  border-radius: var(--lattice-radius-lg, 6px);
  border: 1px solid var(--lattice-border-subtle, #1a1a1a);
  overflow: hidden;
}

.ai-section-header {
  display: flex;
  align-items: center;
  padding: 12px 14px;
  background: linear-gradient(135deg, rgba(139, 92, 246, 0.15), rgba(236, 72, 153, 0.15));
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
}

.ai-section-title {
  font-size: var(--lattice-text-md, 14px);
  font-weight: 600;
  color: var(--lattice-accent, #8B5CF6);
}

.ai-section-tabs {
  display: flex;
  padding: 8px;
  gap: 4px;
  background: var(--lattice-surface-0, #0a0a0a);
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
}

.ai-section-tabs button {
  flex: 1;
  padding: 10px 14px;
  border: none;
  background: transparent;
  color: var(--lattice-text-secondary, #9CA3AF);
  font-size: var(--lattice-text-base, 13px);
  font-weight: 600;
  cursor: pointer;
  border-radius: var(--lattice-radius-md, 4px);
  transition: var(--lattice-transition-fast, 100ms ease);
}

.ai-section-tabs button:hover {
  color: var(--lattice-text-primary, #e5e5e5);
  background: var(--lattice-surface-3, #1e1e1e);
}

.ai-section-tabs button.active {
  color: white;
  background: var(--lattice-accent, #8B5CF6);
  font-weight: 600;
}

.ai-section-content {
  flex: 1;
  overflow-y: auto;
  overflow-x: hidden;
}

/* Viewport */
.viewport-panel {
  background: var(--lattice-surface-0, #080808);
}

.viewport-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 6px 12px;
  background: var(--lattice-surface-2, #161616);
  border-bottom: 1px solid var(--lattice-border-default, #2a2a2a);
  gap: 8px;
}

.viewport-tabs {
  display: flex;
  gap: 4px;
  background: var(--lattice-surface-0, #0a0a0a);
  padding: 4px;
  border-radius: var(--lattice-radius-md, 4px);
}

.viewport-tabs button {
  padding: 8px 16px;
  border: none;
  background: var(--lattice-surface-2, #1a1a1a);
  color: var(--lattice-text-secondary, #9CA3AF);
  font-size: var(--lattice-text-base, 13px);
  font-weight: 600;
  border-radius: var(--lattice-radius-sm, 2px);
  cursor: pointer;
  transition: var(--lattice-transition-fast, 100ms ease);
}

.viewport-tabs button:hover {
  color: var(--lattice-text-primary, #e5e5e5);
  background: var(--lattice-surface-3, #2a2a2a);
}

.viewport-tabs button.active {
  background: var(--lattice-accent, #8B5CF6);
  color: white;
  box-shadow: 0 1px 2px rgba(0,0,0,0.3);
}

.viewport-controls {
  display: flex;
  align-items: center;
  gap: 4px;
}

.zoom-select {
  padding: 4px 8px;
  background: var(--lattice-surface-2, #1a1a1a);
  border: none;
  color: var(--lattice-text-primary, #e5e5e5);
  border-radius: var(--lattice-radius-md, 4px);
  font-size: var(--lattice-text-sm, 11px);
}

.viewport-controls button {
  width: 32px;
  height: 32px;
  padding: 0;
  border: none;
  background: var(--lattice-surface-2, #1a1a1a);
  color: var(--lattice-text-secondary, #9CA3AF);
  border-radius: var(--lattice-radius-md, 4px);
  cursor: pointer;
  font-size: 16px;
  transition: var(--lattice-transition-fast, 100ms ease);
}

.viewport-controls button:hover {
  background: var(--lattice-surface-3, #2a2a2a);
  color: var(--lattice-text-primary, #e5e5e5);
}

.viewport-controls button.active {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.2));
  color: var(--lattice-accent, #8B5CF6);
}

.viewport-content {
  flex: 1;
  display: flex;
  align-items: center;
  justify-content: center;
  background: var(--lattice-surface-0, #0a0a0a);
  overflow: hidden;
  position: relative;
}

.viewport-content.rulers-active {
  padding-top: 20px;
  padding-left: 20px;
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

/* Make rulers interactive for guide creation */
.ruler-horizontal,
.ruler-vertical {
  pointer-events: auto;
  cursor: pointer;
}

.ruler-horizontal:hover {
  background: rgba(0, 191, 255, 0.1);
}

.ruler-vertical:hover {
  background: rgba(0, 191, 255, 0.1);
}

/* Grid Overlay */
.grid-overlay {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 5;
}

/* Guides Overlay */
.guides-overlay {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 10;
}

.guides-overlay .guide {
  pointer-events: auto;
  transition: background 0.1s;
  position: relative;
}

.guides-overlay .guide:hover {
  /* Change gradient color to red on hover */
}

.guides-overlay .guide.horizontal:hover {
  background: linear-gradient(to bottom, transparent 5px, #FF6B6B 5px, #FF6B6B 6px, transparent 6px) !important;
}

.guides-overlay .guide.vertical:hover {
  background: linear-gradient(to right, transparent 5px, #FF6B6B 5px, #FF6B6B 6px, transparent 6px) !important;
}

.guides-overlay .guide.horizontal {
  width: 100%;
}

.guides-overlay .guide.vertical {
  height: 100%;
}

/* Guide delete button - shown on hover */
.guide-delete-btn {
  position: absolute;
  width: 16px;
  height: 16px;
  border-radius: 50%;
  background: #FF4444;
  color: white;
  border: none;
  font-size: 12px;
  line-height: 14px;
  cursor: pointer;
  opacity: 0;
  transition: opacity 0.15s;
  display: flex;
  align-items: center;
  justify-content: center;
  padding: 0;
}

.guide:hover .guide-delete-btn {
  opacity: 1;
}

.guide.horizontal .guide-delete-btn {
  right: 4px;
  top: -2px;
}

.guide.vertical .guide-delete-btn {
  top: 4px;
  left: -2px;
}

.guide-delete-btn:hover {
  background: #FF0000;
  transform: scale(1.1);
}

/* Guide context menu */
.guide-context-menu {
  position: fixed;
  background: var(--lattice-surface-3, #222);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 4px;
  padding: 4px 0;
  min-width: 140px;
  box-shadow: 0 4px 12px rgba(0,0,0,0.3);
  z-index: 10000;
}

.guide-context-menu button {
  display: block;
  width: 100%;
  padding: 8px 12px;
  background: none;
  border: none;
  color: var(--lattice-text-primary, #e5e5e5);
  text-align: left;
  cursor: pointer;
  font-size: 12px;
}

.guide-context-menu button:hover {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.2));
}

/* Snap Indicator */
.snap-indicator {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 15;
}

.snap-line {
  position: absolute;
  background-color: #FF00FF;
  opacity: 0.8;
}

.snap-line.vertical {
  width: 1px;
  top: 0;
  bottom: 0;
}

.snap-line.horizontal {
  height: 1px;
  left: 0;
  right: 0;
}

/* Timeline Panel */
.timeline-panel {
  /* No borders - floating panel */
}

.curve-editor-panel {
  /* No borders - floating panel */
}

/* Status bar removed - info now in toolbar */

/* Splitpanes Theme Overrides */
:deep(.splitpanes.default-theme .splitpanes__pane) {
  background: transparent;
  /* Allow dropdowns to overflow outside pane boundaries */
  overflow: visible !important;
}

:deep(.splitpanes.default-theme .splitpanes__splitter) {
  background: transparent;
  border: none;
}

:deep(.splitpanes.default-theme .splitpanes__splitter:hover) {
  background: var(--lattice-accent, #8B5CF6);
}

/* Vertical splitters (between columns) - add breathing room */
:deep(.splitpanes--vertical > .splitpanes__splitter) {
  width: 8px;
  min-width: 8px;
  background: var(--lattice-void, #0a0a0a);
}

:deep(.splitpanes--vertical > .splitpanes__splitter:hover) {
  background: var(--lattice-accent, #8B5CF6);
}

/* Horizontal splitters (between rows) */
:deep(.splitpanes--horizontal > .splitpanes__splitter) {
  height: 6px;
  min-height: 6px;
  background: var(--lattice-void, #0a0a0a);
}

:deep(.splitpanes--horizontal > .splitpanes__splitter:hover) {
  background: var(--lattice-accent, #8B5CF6);
}

/* Ensure timeline pane allows dropdown overflow */
:deep(.splitpanes--horizontal .splitpanes__pane:last-child) {
  overflow: visible !important;
}

/* Segmentation tool options */
.segment-options {
  display: flex;
  align-items: center;
  gap: 4px;
}

.segment-options .confirm-btn {
  background: var(--lattice-success, #10B981) !important;
  color: white !important;
}

.segment-options .confirm-btn:hover {
  filter: brightness(1.1);
}

.segment-options .cancel-btn {
  background: var(--lattice-error, #F43F5E) !important;
  color: white !important;
}

.segment-options .cancel-btn:hover {
  filter: brightness(1.1);
}

.loading-indicator {
  color: var(--lattice-success, #10B981);
  font-size: var(--lattice-text-base, 12px);
  padding: 0 8px;
  animation: pulse 1s ease-in-out infinite;
}

@keyframes pulse {
  0%, 100% { opacity: 0.6; }
  50% { opacity: 1; }
}
</style>