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
      @showTemplateBuilder="showTemplateBuilderDialog = true"
    />

    <!-- Main Workspace with Splitpanes -->
    <div class="workspace-content">
      <Splitpanes class="default-theme horizontal-split">
        <!-- Left Panel: Project/Effects -->
        <Pane :size="14" :min-size="10" :max-size="20">
          <LeftSidebar
            v-model="leftTab"
            @openCompositionSettings="showCompositionSettingsDialog = true"
            @createLayersFromSvg="onCreateLayersFromSvg"
            @useMeshAsEmitter="onUseMeshAsEmitter"
            @environmentUpdate="onEnvironmentUpdate"
            @environmentLoad="onEnvironmentLoad"
            @environmentClear="onEnvironmentClear"
          />
        </Pane>

        <!-- Center: Viewport + Timeline -->
        <Pane :size="66" :min-size="45">
          <CenterViewport
            ref="centerViewportRef"
            v-model:viewportTab="viewportTab"
            v-model:showCurveEditor="showCurveEditor"
            :viewOptions="viewOptions"
            :guides="guides"
            :guideContextMenu="guideContextMenu"
            :snapEnabled="snapEnabled"
            :snapIndicatorX="snapIndicatorX"
            :snapIndicatorY="snapIndicatorY"
            :compWidth="compWidth"
            :compHeight="compHeight"
            :gridOverlayStyle="gridOverlayStyle"
            :activeCamera="activeCamera"
            :viewportState="viewportState"
            @update:viewOptions="viewOptions = $event"
            @openCompositionSettings="showCompositionSettingsDialog = true"
            @openPathSuggestion="showPathSuggestionDialog = true"
            @startGuideDrag="startGuideDrag"
            @showGuideContextMenu="showGuideContextMenu"
            @removeGuide="removeGuide"
            @deleteGuideFromMenu="deleteGuideFromMenu"
            @clearAllGuides="clearAllGuides"
            @createGuideFromRuler="createGuideFromRuler"
          />
        </Pane>

        <!-- Right Panel: Stacked Collapsible Panels -->
        <Pane :size="20" :min-size="14" :max-size="30">
          <RightSidebar
            v-model:expandedPanels="expandedPanels"
            v-model:aiTab="aiTab"
            :camera="activeCamera"
            :engine="canvasEngine"
            @updateCamera="updateCamera"
          />
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
      :layers="projectStore.getActiveCompLayers()"
      :camera-keyframes="activeCameraKeyframes"
      :current-frame="animationStore.currentFrame"
      :total-frames="projectStore.getFrameCount()"
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
      :layer-count="selectionStore.selectedLayerIds.length"
      @close="showPrecomposeDialog = false"
      @confirm="onPrecomposeConfirm"
    />

    <!-- Keyframe Interpolation Dialog -->
    <KeyframeInterpolationDialog
      :visible="showKeyframeInterpolationDialog"
      :keyframe-count="selectionStore.selectedKeyframeIds.length"
      @close="showKeyframeInterpolationDialog = false"
      @confirm="onKeyframeInterpolationConfirm"
    />

    <!-- Keyframe Velocity Dialog -->
    <KeyframeVelocityDialog
      :visible="showKeyframeVelocityDialog"
      :keyframe-count="selectionStore.selectedKeyframeIds.length"
      @close="showKeyframeVelocityDialog = false"
      @confirm="onKeyframeVelocityConfirm"
    />

    <!-- Frame Interpolation Dialog (RIFE) -->
    <FrameInterpolationDialog
      v-if="showFrameInterpolationDialog"
      @close="showFrameInterpolationDialog = false"
      @complete="onFrameInterpolationComplete"
    />

    <!-- Time Stretch Dialog -->
    <TimeStretchDialog
      :visible="showTimeStretchDialog"
      :layer-id="selectedLayerIdForTimeStretch"
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

    <!-- Template Builder Dialog -->
    <TemplateBuilderDialog
      :visible="showTemplateBuilderDialog"
      @close="showTemplateBuilderDialog = false"
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
      :current-expression="getCurrentExpression()"
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
        :currentFrame="animationStore.currentFrame"
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
import { computed, onMounted, onUnmounted, provide, type Ref, ref } from "vue";
import "splitpanes/dist/splitpanes.css";

import type CenterViewport from "@/components/layout/CenterViewport.vue";
import { useAssetHandlers } from "@/composables/useAssetHandlers";
import { useExpressionEditor } from "@/composables/useExpressionEditor";
import { useGuides } from "@/composables/useGuides";
import { useKeyboardShortcuts } from "@/composables/useKeyboardShortcuts";
import { useMenuActions } from "@/composables/useMenuActions";
import { detectGPUTier, type GPUTier } from "@/services/gpuDetection";
// Track point service
import { useTrackPoints } from "@/services/trackPointService";
import { useAnimationStore } from "@/stores/animationStore";
import { useCameraStore } from "@/stores/cameraStore";
import { useCompositionStore } from "@/stores/compositionStore";
import { useLayerStore } from "@/stores/layerStore";
import { useKeyframeStore } from "@/stores/keyframeStore";
import { useProjectStore } from "@/stores/projectStore";
import { useSegmentationStore } from "@/stores/segmentationStore";
import { useSelectionStore } from "@/stores/selectionStore";
import type { Camera3D, ViewportState } from "@/types/camera";
import {
  createDefaultCamera,
  createDefaultViewportState,
} from "@/types/camera";
import type { BaseInterpolationType, ControlMode, ControlPoint, AnimatableProperty } from "@/types/project";
import type { PropertyValue, Keyframe } from "@/types/animation";
import { hasXY, isObject } from "@/utils/typeGuards";
import type { JSONValue } from "@/types/dataAsset";

// Stores
const projectStore = useProjectStore();
const animationStore = useAnimationStore();
const segmentationStore = useSegmentationStore();
const selectionStore = useSelectionStore();
const cameraStore = useCameraStore();
const compositionStore = useCompositionStore();
const layerStore = useLayerStore();
const keyframeStore = useKeyframeStore();

// Helper function to create CompositionStoreAccess
function getCompositionStoreAccess() {
  return {
    project: projectStore.project,
    activeCompositionId: projectStore.activeCompositionId,
    openCompositionIds: projectStore.openCompositionIds,
    compositionBreadcrumbs: projectStore.compositionBreadcrumbs,
    selectedLayerIds: selectionStore.selectedLayerIds,
    getActiveComp: () => projectStore.getActiveComp(),
    switchComposition: (id: string) => compositionStore.switchComposition(getCompositionStoreAccess(), id),
    pushHistory: () => projectStore.pushHistory(),
  };
}

// Helper function to set tool (handles segmentation)
function setTool(tool: "select" | "pen" | "text" | "hand" | "zoom" | "segment") {
  if (tool === "segment") {
    segmentationStore.setSegmentToolActive(true);
  } else {
    segmentationStore.setSegmentToolActive(false);
    selectionStore.setTool(tool);
    segmentationStore.clearSegmentPendingMask();
  }
}

// Helper function to confirm segment mask
async function confirmSegmentMask(layerName?: string) {
  if (!segmentationStore.segmentPendingMask || !projectStore.sourceImage) {
    throw new Error("[WorkspaceLayout] Cannot confirm segment mask: segmentPendingMask or sourceImage is not available");
  }

  const layer = await segmentationStore.createLayerFromMask(
    projectStore.sourceImage,
    segmentationStore.segmentPendingMask,
    layerName,
    false,
  );

  segmentationStore.clearSegmentPendingMask();

  return layer;
}

import { useAssetStore } from "@/stores/assetStore";

const assetStore = useAssetStore();

import { useAudioStore } from "@/stores/audioStore";
import { usePlaybackStore } from "@/stores/playbackStore";

const _audioStore = useAudioStore();
const _playbackStore = usePlaybackStore();

// Expression editor composable
const expressionEditor = useExpressionEditor();

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
function getCurrentExpression() {
  const currentProperty = expressionEditor.currentProperty.value;
  const expression = (currentProperty != null && typeof currentProperty === "object" && "expression" in currentProperty && currentProperty.expression != null) ? currentProperty.expression : undefined;
  return expression;
}

// Track points state for camera tracking overlay
const trackPointsState = useTrackPoints();

// Tool state - synced with store
const currentTool = computed({
  get: () => selectionStore.currentTool,
  set: (tool: "select" | "pen" | "text" | "hand" | "zoom" | "segment") =>
    setTool(tool),
});

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
// Computed property for selected layer ID (defaults to empty string if none selected)
const selectedLayerIdForTimeStretch = computed(() => {
  const selectedIds = selectionStore.selectedLayerIds;
  return (Array.isArray(selectedIds) && selectedIds.length > 0 && typeof selectedIds[0] === "string") ? selectedIds[0] : "";
});

// Segmentation state - synced with segmentationStore
const _segmentMode = computed(() => segmentationStore.segmentMode);
const _segmentPendingMask = computed(() => segmentationStore.segmentPendingMask);
const _segmentIsLoading = computed(() => segmentationStore.segmentIsLoading);

function _setSegmentMode(mode: "point" | "box") {
  segmentationStore.setSegmentMode(mode);
}

async function _confirmSegmentMask() {
  await confirmSegmentMask();
}

function _clearSegmentMask() {
  segmentationStore.clearSegmentPendingMask();
}

const leftTab = ref<"project" | "effects" | "assets">("project");
const _rightTab = ref<
  "effects" | "properties" | "camera" | "audio" | "preview" | "ai" | "generate"
>("properties");

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
  renderQueue: false,
  physics: false,
  styles: false,
});

// AI section tab
const aiTab = ref<"chat" | "generate" | "flow" | "decompose">("chat");
const viewportTab = ref<"composition" | "layer" | "footage">("composition");

const viewZoom = ref("fit");
const showCurveEditor = ref(false);
const showExportDialog = ref(false);
const showComfyUIExportDialog = ref(false);
const showCompositionSettingsDialog = ref(false);
const showPrecomposeDialog = ref(false);
const showPathSuggestionDialog = ref(false);
const showKeyframeInterpolationDialog = ref(false);
const showKeyframeVelocityDialog = ref(false);
const showFrameInterpolationDialog = ref(false);
const showTimeStretchDialog = ref(false);
const showCameraTrackingImportDialog = ref(false);
const showPreferencesDialog = ref(false);
const showKeyboardShortcutsModal = ref(false);
const showHDPreview = ref(false);
const showTemplateBuilderDialog = ref(false);

// Vision authoring state
interface PathSuggestion {
  points: Array<{
    id?: string;
    x: number;
    y: number;
    depth?: number;
    handleIn?: { x: number; y: number } | null;
    handleOut?: { x: number; y: number } | null;
    type?: "smooth" | "corner" | "bezier";
  }>;
  closed?: boolean;
  name?: string;
}

const pathSuggestions = ref<PathSuggestion[]>([]);
const selectedPathIndex = ref<number | null>(null);

const gpuTier = ref<GPUTier["tier"]>("cpu");

// CenterViewport ref - Vue exposes properties via defineExpose
// TypeScript doesn't automatically know about exposed properties
// We use InstanceType and runtime checks to safely access exposed properties
const centerViewportRef = ref<InstanceType<typeof CenterViewport> | null>(null);

// Helper to safely access threeCanvasRef from exposed properties
// Vue exposes refs/computeds directly via defineExpose - use runtime property check with type guards
function getThreeCanvasRef(): InstanceType<typeof import("@/components/canvas/ThreeCanvas.vue").default> {
  const viewport = centerViewportRef.value;
  if (!viewport || !isObject(viewport)) {
    throw new Error("[WorkspaceLayout] Cannot get ThreeCanvas ref: viewport is not available");
  }
  // Runtime check: Vue exposes threeCanvasRef as a Ref object
  // Use property access with runtime check - TypeScript can't know about exposed properties
  const threeCanvasRefProp = viewport.threeCanvasRef;
  if (isObject(threeCanvasRefProp) && "value" in threeCanvasRefProp) {
    const refValue = threeCanvasRefProp.value;
    // Type guard: verify it's the expected component instance type
    if (refValue && isObject(refValue)) {
      return refValue as InstanceType<typeof import("@/components/canvas/ThreeCanvas.vue").default>;
    }
  }
  throw new Error("[WorkspaceLayout] Cannot get ThreeCanvas ref: threeCanvasRef is not available or invalid");
}

// Computed ref to access threeCanvasRef through CenterViewport
const threeCanvasRef = computed(() => getThreeCanvasRef());

// Helper to safely access engine from exposed properties
// Vue exposes computed refs directly via defineExpose - use runtime property check with type guards
function getCanvasEngine(): import("@/engine/LatticeEngine").LatticeEngine {
  const viewport = centerViewportRef.value;
  if (!viewport || !isObject(viewport)) {
    throw new Error("[WorkspaceLayout] Cannot get canvas engine: viewport is not available");
  }
  // Runtime check: Vue exposes engine as a ComputedRef object
  // Use property access with runtime check - TypeScript can't know about exposed properties
  const engineProp = viewport.engine;
  if (isObject(engineProp) && "value" in engineProp) {
    const engineValue = engineProp.value;
    // Type guard: verify it's the expected engine type
    if (engineValue && isObject(engineValue)) {
      return engineValue as import("@/engine/LatticeEngine").LatticeEngine;
    }
  }
  throw new Error("[WorkspaceLayout] Cannot get canvas engine: engine is not available or invalid");
}

// Engine accessor for panels
const canvasEngine = computed(() => getCanvasEngine());

// Asset handlers composable
const {
  onCreateLayersFromSvg,
  onUseMeshAsEmitter,
  onEnvironmentUpdate,
  onEnvironmentLoad,
  onEnvironmentClear,
} = useAssetHandlers({ 
  canvasRef: centerViewportRef,
});

// Camera state - use computed to get from store, fallback to default
const activeCamera = computed<Camera3D>(() => {
  const cam = cameraStore.getActiveCameraAtFrame();
  if (cam) return cam;
  // Fallback to a default camera
  return createDefaultCamera("default", compWidth.value, compHeight.value);
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
  showGuides: true,
  gridSize: 100,
  gridDivisions: 10,
});

// Grid overlay computed style
const gridOverlayStyle = computed(() => {
  const size = viewOptions.value.gridSize || 100;
  const divisions = viewOptions.value.gridDivisions || 10;
  const minorSize = size / divisions;

  // Create a repeating grid pattern using CSS
  return {
    position: "absolute",
    top: 0,
    left: 0,
    right: 0,
    bottom: 0,
    pointerEvents: "none",
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
    opacity: 0.5,
  };
});

// Snap indicator state (for visual feedback)
const snapIndicatorX = ref<number | null>(null);
const snapIndicatorY = ref<number | null>(null);

// Composition dimensions
const compWidth = computed(() => projectStore.getWidth());
const compHeight = computed(() => projectStore.getHeight());

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                      // keyboard // shortcuts // composable
// ═══════════════════════════════════════════════════════════════════════════
const keyboard = useKeyboardShortcuts({
  showExportDialog,
  showCompositionSettingsDialog,
  showKeyframeInterpolationDialog,
  showKeyframeVelocityDialog,
  showPrecomposeDialog,
  showCurveEditor,
  showTimeStretchDialog,
  showCameraTrackingImportDialog,
  showKeyboardShortcutsModal,
  currentTool: currentTool as Ref<"select" | "pen" | "text" | "hand" | "zoom" | "segment">,
  leftTab: leftTab as Ref<"project" | "effects" | "assets">,
  viewOptions,
  threeCanvasRef,
  viewZoom,
  compWidth,
  compHeight,
  assetStore,
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
  toggleSnap,
} = keyboard;

// Set up provides from keyboard composable
setupKeyboardProvides();

// Performance tracking
const _fps = ref(60);
const memoryUsage = ref("0 MB");
const _renderProgress = ref(0);

// Computed
const _formattedTimecode = computed(() => {
  const frame = animationStore.currentFrame;
  const fpsVal = projectStore.getFps();
  const totalSeconds = frame / fpsVal;
  const minutes = Math.floor(totalSeconds / 60);
  const seconds = Math.floor(totalSeconds % 60);
  const frames = frame % fpsVal;
  return `${String(minutes).padStart(2, "0")}:${String(seconds).padStart(2, "0")}:${String(frames).padStart(2, "0")}`;
});

const _projectName = computed(() => {
  return projectStore.project.meta.name || "Untitled Project";
});

const _compositionInfo = computed(() => {
  const width = projectStore.getWidth();
  const height = projectStore.getHeight();
  const fps = projectStore.getFps();
  return `${width}×${height} @ ${fps}fps`;
});

const _canUndo = computed(() => projectStore.canUndo);
const _canRedo = computed(() => projectStore.canRedo);

// ═══════════════════════════════════════════════════════════════════════════
// GUIDES SYSTEM (using composable)
// ═══════════════════════════════════════════════════════════════════════════
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
  startGuideDrag,
} = useGuides();

// Provide guides state
provide("guides", guides);
provide("addGuide", addGuide);
provide("removeGuide", removeGuide);
provide("clearGuides", clearGuides);
provide("updateGuidePosition", updateGuidePosition);

// Provide frame capture for template export and other features
provide("captureFrame", async (): Promise<string | null> => {
  const canvas = threeCanvasRef.value;
  // ThreeCanvas exposes captureFrame via defineExpose - use runtime property check
  if (canvas && isObject(canvas) && "captureFrame" in canvas && typeof canvas.captureFrame === "function") {
    return await canvas.captureFrame();
  }
  throw new Error("[WorkspaceLayout] Cannot capture frame: ThreeCanvas is not available or captureFrame method is not accessible");
});

// ═══════════════════════════════════════════════════════════════════════════
// SNAP POINT CALCULATION (uses both guides and keyboard composable state)
// ═══════════════════════════════════════════════════════════════════════════
function getSnapPoint(
  x: number,
  y: number,
): { x: number; y: number; snappedX: boolean; snappedY: boolean } {
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
      if (
        guide.orientation === "vertical" &&
        Math.abs(x - guide.position) < snapTolerance.value
      ) {
        resultX = guide.position;
        snappedX = true;
      }
      if (
        guide.orientation === "horizontal" &&
        Math.abs(y - guide.position) < snapTolerance.value
      ) {
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
provide("getSnapPoint", getSnapPoint);

function updateCamera(camera: Camera3D) {
  // Update the camera in the store
  const activeCameraId = cameraStore.activeCameraId;
  if (activeCameraId) {
    cameraStore.updateCamera(camera.id, camera);
  }
}

// Play a notification chime when export completes
function playExportChime() {
  try {
    const AudioContextClass = window.AudioContext || (window as typeof window & { webkitAudioContext?: typeof AudioContext }).webkitAudioContext;
    if (!AudioContextClass) {
      throw new Error("AudioContext not available");
    }
    const audioCtx = new AudioContextClass();
    const gainNode = audioCtx.createGain();
    gainNode.connect(audioCtx.destination);
    gainNode.gain.setValueAtTime(0.3, audioCtx.currentTime);
    gainNode.gain.exponentialRampToValueAtTime(
      0.01,
      audioCtx.currentTime + 0.5,
    );

    // Two-tone chime (pleasant major third)
    const freqs = [523.25, 659.25]; // C5, E5
    freqs.forEach((freq, i) => {
      const osc = audioCtx.createOscillator();
      osc.type = "sine";
      osc.frequency.setValueAtTime(freq, audioCtx.currentTime + i * 0.1);
      osc.connect(gainNode);
      osc.start(audioCtx.currentTime + i * 0.1);
      osc.stop(audioCtx.currentTime + 0.5 + i * 0.1);
    });
  } catch (e) {
    // Silently fail if audio not available
    console.warn("[Lattice] Audio notification not available:", e);
  }
}

function onExportComplete() {
  console.log("[Lattice] Matte export completed");
  playExportChime();
}

/**
 * ComfyUI export result structure
 */
interface ComfyUIExportResult {
  success: boolean;
  workflowId?: string;
  promptId?: string;
  error?: string;
  exportedFiles?: string[];
  [key: string]: boolean | string | string[] | undefined;
}

function onComfyUIExportComplete(result: ComfyUIExportResult) {
  console.log("[Lattice] ComfyUI export completed", result);
  showComfyUIExportDialog.value = false;
  playExportChime();
}

function onFrameInterpolationComplete(frames: string[]) {
  console.log("[Lattice] Frame interpolation completed:", frames.length, "frames");
  showFrameInterpolationDialog.value = false;
  playExportChime();
  // TODO: Allow user to save frames or add to project
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
  console.log("[Lattice] Composition settings updated:", settings);

  // Update active composition's settings
  const compId = projectStore.activeCompositionId;
  const selectionStore = useSelectionStore();
  compositionStore.updateCompositionSettings(
    {
      project: {
        compositions: projectStore.project.compositions,
        mainCompositionId: projectStore.project.mainCompositionId,
        composition: projectStore.project.composition,
        meta: projectStore.project.meta,
      },
      activeCompositionId: compId,
      openCompositionIds: projectStore.openCompositionIds,
      compositionBreadcrumbs: projectStore.compositionBreadcrumbs,
      selectedLayerIds: selectionStore.selectedLayerIds,
      getActiveComp: () => projectStore.getActiveComp(),
      switchComposition: (id: string) => compositionStore.switchComposition(getCompositionStoreAccess(), id),
      pushHistory: () => projectStore.pushHistory(),
    },
    compId,
    {
    width: settings.width,
    height: settings.height,
    fps: settings.fps,
    frameCount: settings.frameCount,
    backgroundColor: settings.backgroundColor,
    autoResizeToContent: settings.autoResizeToContent,
  });

  // Rename the composition
  const renameCompId = projectStore.activeCompositionId;
  compositionStore.renameComposition(
    {
      project: {
        compositions: projectStore.project.compositions,
        mainCompositionId: projectStore.project.mainCompositionId,
        composition: projectStore.project.composition,
        meta: projectStore.project.meta,
      },
      activeCompositionId: renameCompId,
      openCompositionIds: projectStore.openCompositionIds,
      compositionBreadcrumbs: projectStore.compositionBreadcrumbs,
      selectedLayerIds: selectionStore.selectedLayerIds,
      getActiveComp: () => projectStore.getActiveComp(),
      switchComposition: (id: string) => compositionStore.switchComposition(getCompositionStoreAccess(), id),
      pushHistory: () => projectStore.pushHistory(),
    },
    renameCompId,
    settings.name,
  );

  showCompositionSettingsDialog.value = false;
}

function onPrecomposeConfirm(name: string) {
  if (selectionStore.selectedLayerIds.length > 0) {
    compositionStore.nestSelectedLayers(name);
    showPrecomposeDialog.value = false;
  }
}

// Camera tracking import handler
function onCameraTrackingImported(result: {
  cameraLayerId?: string;
  warnings?: string[];
}) {
  showCameraTrackingImportDialog.value = false;

  if (result.cameraLayerId) {
    // Select the imported camera
    layerStore.selectLayer(result.cameraLayerId);
    console.log("Camera tracking imported successfully:", result.cameraLayerId);
  }

  if (result.warnings && result.warnings.length > 0) {
    console.warn("Camera tracking import warnings:", result.warnings);
  }
}

/**
 * Keyframe interpolation dialog handler.
 * Uses store actions for proper undo/redo support.
 */
function onKeyframeInterpolationConfirm(settings: {
  interpolation: BaseInterpolationType;
  easingPreset: string;
  controlMode: ControlMode;
}) {
  const selectedKeyframeIds = selectionStore.selectedKeyframeIds;
  if (selectedKeyframeIds.length === 0) return;

  let appliedCount = 0;

  // Get the layers that contain these keyframes
  const layers = projectStore.getActiveCompLayers();
  for (const layer of layers) {
    const transform = layer.transform;
    if (!transform) continue;

    // Check all animatable properties for keyframes
    // Note: "anchor" maps to origin/anchorPoint, "opacity" is on layer not transform
    const transformProps: Array<{ name: string; prop: AnimatableProperty<PropertyValue> | undefined }> = [
      { name: "position", prop: transform.position },
      { name: "rotation", prop: transform.rotation },
      { name: "scale", prop: transform.scale },
      { name: "anchor", prop: transform.origin || transform.anchorPoint },
    ];
    
    for (const { name: propName, prop } of transformProps) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const propKeyframes = (prop != null && typeof prop === "object" && "keyframes" in prop && Array.isArray(prop.keyframes)) ? prop.keyframes : undefined;
      if (!propKeyframes) continue;

      const propertyPath = `transform.${propName === "anchor" ? "origin" : propName}`;

      // Sort keyframes by frame for proper next-keyframe lookup
      const sortedKeyframes = [...propKeyframes].sort(
        (a: import("@/types/animation").Keyframe<import("@/types/animation").PropertyValue>, b: import("@/types/animation").Keyframe<import("@/types/animation").PropertyValue>) => a.frame - b.frame,
      );

      for (let i = 0; i < sortedKeyframes.length; i++) {
        const kf = sortedKeyframes[i];
        if (selectedKeyframeIds.includes(kf.id)) {
          // Use store actions for proper undo/redo support
          keyframeStore.setKeyframeInterpolation(
            layer.id,
            propertyPath,
            kf.id,
            settings.interpolation,
          );
          keyframeStore.setKeyframeControlMode(
            layer.id,
            propertyPath,
            kf.id,
            settings.controlMode,
          );
          appliedCount++;

          // For bezier, set easing preset handles
          if (settings.interpolation === "bezier" && settings.easingPreset) {
            const presetHandles = getEasingPresetHandles(settings.easingPreset);
            if (presetHandles) {
              // Find next keyframe to calculate frame duration and value delta
              const nextKf = sortedKeyframes[i + 1];
              if (nextKf) {
                const frameDuration = nextKf.frame - kf.frame;
                // Get scalar value delta (for vectors, use magnitude)
                const kfValue =
                  typeof kf.value === "number"
                    ? kf.value
                    : hasXY(kf.value)
                      ? Math.sqrt(kf.value.x ** 2 + kf.value.y ** 2)
                      : 0;
                const nextValue =
                  typeof nextKf.value === "number"
                    ? nextKf.value
                    : hasXY(nextKf.value)
                      ? Math.sqrt(nextKf.value.x ** 2 + nextKf.value.y ** 2)
                      : 0;
                const valueDelta = nextValue - kfValue;

                // Use store action to set outHandle on current keyframe
                keyframeStore.setKeyframeHandle(layer.id, propertyPath, kf.id, "out", {
                  frame: presetHandles.outX * frameDuration,
                  value: presetHandles.outY * valueDelta,
                  enabled: true,
                });
                // Use store action to set inHandle on next keyframe
                keyframeStore.setKeyframeHandle(
                  layer.id,
                  propertyPath,
                  nextKf.id,
                  "in",
                  {
                    frame: -(1 - presetHandles.inX) * frameDuration,
                    value: (1 - presetHandles.inY) * valueDelta,
                    enabled: true,
                  },
                );
              }
            }
          }
        }
      }
    }
    
    // Check opacity separately (it's on layer, not transform)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
    const opacity = (layer != null && typeof layer === "object" && "opacity" in layer && layer.opacity != null && typeof layer.opacity === "object") ? layer.opacity : undefined;
    const opacityKeyframes = (opacity != null && typeof opacity === "object" && "keyframes" in opacity && Array.isArray(opacity.keyframes)) ? opacity.keyframes : undefined;
    if (opacityKeyframes != null) {
      const sortedKeyframes = [...opacityKeyframes].sort(
        (a: Keyframe<number>, b: Keyframe<number>) => {
          const aFrame = (typeof a.frame === "number" && Number.isFinite(a.frame)) ? a.frame : 0;
          const bFrame = (typeof b.frame === "number" && Number.isFinite(b.frame)) ? b.frame : 0;
          return aFrame - bFrame;
        },
      );
      
      for (let i = 0; i < sortedKeyframes.length; i++) {
        const kf = sortedKeyframes[i];
        if (selectedKeyframeIds.includes(kf.id)) {
          keyframeStore.setKeyframeInterpolation(
            layer.id,
            "opacity",
            kf.id,
            settings.interpolation,
          );
          keyframeStore.setKeyframeControlMode(
            layer.id,
            "opacity",
            kf.id,
            settings.controlMode,
          );
          appliedCount++;
          
          // For bezier, set easing preset handles
          if (settings.interpolation === "bezier" && settings.easingPreset) {
            const presetHandles = getEasingPresetHandles(settings.easingPreset);
            if (presetHandles) {
              const nextKf = sortedKeyframes[i + 1];
              if (nextKf) {
                const frameDuration = nextKf.frame - kf.frame;
                const kfValue = typeof kf.value === "number" ? kf.value : 0;
                const nextValue = typeof nextKf.value === "number" ? nextKf.value : 0;
                const valueDelta = nextValue - kfValue;
                
                keyframeStore.setKeyframeHandle(layer.id, "opacity", kf.id, "out", {
                  frame: presetHandles.outX * frameDuration,
                  value: presetHandles.outY * valueDelta,
                  enabled: true,
                });
                keyframeStore.setKeyframeHandle(layer.id, "opacity", nextKf.id, "in", {
                  frame: -(1 - presetHandles.inX) * frameDuration,
                  value: (1 - presetHandles.inY) * valueDelta,
                  enabled: true,
                });
              }
            }
          }
        }
      }
    }
  }

  console.log(
    `[Lattice] Applied ${settings.interpolation} interpolation to ${appliedCount} keyframes`,
  );
  showKeyframeInterpolationDialog.value = false;
}

/**
 * Handle keyframe velocity dialog confirmation.
 * Applies velocity/influence settings to all selected keyframes via store action.
 */
function onKeyframeVelocityConfirm(settings: {
  incomingVelocity: number;
  outgoingVelocity: number;
  incomingInfluence: number;
  outgoingInfluence: number;
}) {
  const selectedKeyframeIds = selectionStore.selectedKeyframeIds;
  if (selectedKeyframeIds.length === 0) return;

  // Get the layers that contain these keyframes
  const layers = projectStore.getActiveCompLayers();
  let appliedCount = 0;

  for (const layer of layers) {
    const transform = layer.transform;
    if (!transform) continue;

    // Check all animatable properties for keyframes
    // Note: "anchor" maps to origin/anchorPoint, "opacity" is on layer not transform
    const transformProps: Array<{ name: string; prop: AnimatableProperty<PropertyValue> | undefined }> = [
      { name: "position", prop: transform.position },
      { name: "rotation", prop: transform.rotation },
      { name: "scale", prop: transform.scale },
      { name: "anchor", prop: transform.origin || transform.anchorPoint },
    ];
    
    for (const { name: propName, prop } of transformProps) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const propKeyframes = (prop != null && typeof prop === "object" && "keyframes" in prop && Array.isArray(prop.keyframes)) ? prop.keyframes : undefined;
      if (!propKeyframes) continue;

      const propertyPath = `transform.${propName === "anchor" ? "origin" : propName}`;
      for (const kf of propKeyframes) {
        if (selectedKeyframeIds.includes(kf.id)) {
          // Use store action for proper undo/redo support
          const success = keyframeStore.applyKeyframeVelocity(
            layer.id,
            propertyPath,
            kf.id,
            settings,
          );
          if (success) appliedCount++;
        }
      }
    }
    
    // Check opacity separately (it's on layer, not transform)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const opacity = (layer != null && typeof layer === "object" && "opacity" in layer && layer.opacity != null && typeof layer.opacity === "object") ? layer.opacity : undefined;
    const opacityKeyframes = (opacity != null && typeof opacity === "object" && "keyframes" in opacity && Array.isArray(opacity.keyframes)) ? opacity.keyframes : undefined;
    if (opacityKeyframes != null) {
      for (const kf of opacityKeyframes) {
        if (selectedKeyframeIds.includes(kf.id)) {
          const success = keyframeStore.applyKeyframeVelocity(
            layer.id,
            "opacity",
            kf.id,
            settings,
          );
          if (success) appliedCount++;
        }
      }
    }
  }

  console.log(
    `[Lattice] Applied velocity settings to ${appliedCount} keyframes`,
  );
  showKeyframeVelocityDialog.value = false;
}

// Get bezier handle positions for easing presets
function getEasingPresetHandles(
  preset: string,
): { outX: number; outY: number; inX: number; inY: number } | null {
  // Standard easing preset handle positions
  const presets: Record<
    string,
    { outX: number; outY: number; inX: number; inY: number }
  > = {
    // Ease In
    easeInSine: { outX: 0.47, outY: 0, inX: 0.745, inY: 0.715 },
    easeInQuad: { outX: 0.55, outY: 0.085, inX: 0.68, inY: 0.53 },
    easeInCubic: { outX: 0.55, outY: 0.055, inX: 0.675, inY: 0.19 },
    easeInQuart: { outX: 0.895, outY: 0.03, inX: 0.685, inY: 0.22 },
    easeInQuint: { outX: 0.755, outY: 0.05, inX: 0.855, inY: 0.06 },
    easeInExpo: { outX: 0.95, outY: 0.05, inX: 0.795, inY: 0.035 },
    easeInCirc: { outX: 0.6, outY: 0.04, inX: 0.98, inY: 0.335 },
    easeInBack: { outX: 0.6, outY: -0.28, inX: 0.735, inY: 0.045 },
    easeInElastic: { outX: 0.5, outY: -0.5, inX: 0.7, inY: 0 },

    // Ease Out
    easeOutSine: { outX: 0.39, outY: 0.575, inX: 0.565, inY: 1 },
    easeOutQuad: { outX: 0.25, outY: 0.46, inX: 0.45, inY: 0.94 },
    easeOutCubic: { outX: 0.215, outY: 0.61, inX: 0.355, inY: 1 },
    easeOutQuart: { outX: 0.165, outY: 0.84, inX: 0.44, inY: 1 },
    easeOutQuint: { outX: 0.23, outY: 1, inX: 0.32, inY: 1 },
    easeOutExpo: { outX: 0.19, outY: 1, inX: 0.22, inY: 1 },
    easeOutCirc: { outX: 0.075, outY: 0.82, inX: 0.165, inY: 1 },
    easeOutBack: { outX: 0.175, outY: 0.885, inX: 0.32, inY: 1.275 },
    easeOutElastic: { outX: 0.3, outY: 1, inX: 0.5, inY: 1.5 },
    easeOutBounce: { outX: 0.2, outY: 0.9, inX: 0.3, inY: 1 },

    // Ease In/Out
    easeInOutSine: { outX: 0.445, outY: 0.05, inX: 0.55, inY: 0.95 },
    easeInOutQuad: { outX: 0.455, outY: 0.03, inX: 0.515, inY: 0.955 },
    easeInOutCubic: { outX: 0.645, outY: 0.045, inX: 0.355, inY: 1 },
    easeInOutQuart: { outX: 0.77, outY: 0, inX: 0.175, inY: 1 },
    easeInOutQuint: { outX: 0.86, outY: 0, inX: 0.07, inY: 1 },
    easeInOutExpo: { outX: 1, outY: 0, inX: 0, inY: 1 },
    easeInOutCirc: { outX: 0.785, outY: 0.135, inX: 0.15, inY: 0.86 },
    easeInOutBack: { outX: 0.68, outY: -0.55, inX: 0.265, inY: 1.55 },
    easeInOutElastic: { outX: 0.5, outY: -0.3, inX: 0.5, inY: 1.3 },
  };

  return presets[preset] || null;
}

// Helper: Generate SVG path data from control points (for audio reactivity integration)
function generatePathDataFromPoints(
  points: Array<{
    x: number;
    y: number;
    handleIn?: { x: number; y: number } | null;
    handleOut?: { x: number; y: number } | null;
  }>,
  closed: boolean,
): string {
  if (points.length === 0) return "";
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
    d += " Z";
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

function onPathSuggestionPreview(suggestions: PathSuggestion[]) {
  pathSuggestions.value = suggestions;
  selectedPathIndex.value = suggestions.length > 0 ? 0 : null;
}

interface PathSuggestionResult {
  keyframes: Array<{
    layerId: string;
    propertyPath: string;
    keyframes: Array<{
      value: PropertyValue;
      frame: number;
    }>;
  }>;
  splines: PathSuggestion[];
}

function onPathSuggestionAccept(result: PathSuggestionResult) {
  console.log("[Lattice] Path suggestion accepted:", result);

  // Apply keyframes to the store
  if (result.keyframes && result.keyframes.length > 0) {
    for (const batch of result.keyframes) {
      // batch contains layerId, propertyPath, and keyframes
      // Add keyframes to the appropriate layer/property
      // addKeyframe signature: (layerId, propertyPath, value, atFrame?)
      for (const keyframe of batch.keyframes) {
        keyframeStore.addKeyframe(
          batch.layerId,
          batch.propertyPath,
          keyframe.value,
          keyframe.frame,
        );
      }
    }
  }

  // Create new spline layers if suggested
  if (result.splines && result.splines.length > 0) {
    for (const spline of result.splines) {
      // Create a new spline layer
      const layer = layerStore.createSplineLayer();

      // Rename if name provided
      if (spline.name) {
        layerStore.renameLayer(layer.id, spline.name);
      }

      // Convert points to control points format (preserve depth and handles from translator)
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      const points = (Array.isArray(spline.points)) ? spline.points : [];
      const controlPoints: ControlPoint[] = points.map((p, i: number) => {
        const depth = (typeof p.depth === "number" && Number.isFinite(p.depth)) ? p.depth : 0;
        return {
          id: p.id || `cp_${Date.now()}_${i}`,
          x: p.x,
          y: p.y,
          depth, // Preserve z-space depth
          handleIn: p.handleIn || null, // Preserve bezier handles from translator
          handleOut: p.handleOut || null,
          type: (p.type || "smooth") as "corner" | "smooth" | "symmetric",
        };
      });

      // Generate SVG path data from control points for audio reactivity
      const pathData = generatePathDataFromPoints(
        controlPoints,
        spline.closed || false,
      );

      // Update the layer data with the points and pathData
      layerStore.updateLayerData(layer.id, {
        controlPoints,
        pathData,
        closed: spline.closed || false,
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
  const activeCam = cameraStore.getActiveCameraAtFrame();
  if (!activeCam) return [];
  return cameraStore.getCameraKeyframes(activeCam.id);
});

// Handle zoom dropdown change
function handleZoomChange() {
  const canvas = threeCanvasRef.value;
  if (!canvas) return;

  const canvasInstance = threeCanvasRef.value;
  if (!canvasInstance || !isObject(canvasInstance)) return;
  
  // ThreeCanvas exposes fitToView and setZoom via defineExpose - use runtime property checks
  if (viewZoom.value === "fit") {
    if ("fitToView" in canvasInstance && typeof canvasInstance.fitToView === "function") {
      canvasInstance.fitToView();
    }
  } else {
    // Convert percentage string to decimal (e.g., '100' → 1.0, '200' → 2.0)
    const zoomLevel = parseInt(viewZoom.value, 10) / 100;
    if ("setZoom" in canvasInstance && typeof canvasInstance.setZoom === "function") {
      canvasInstance.setZoom(zoomLevel);
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// MENU BAR ACTION HANDLER (using composable)
// ═══════════════════════════════════════════════════════════════════════════
const { handleMenuAction } = useMenuActions({
  showExportDialog,
  showPrecomposeDialog,
  showTimeStretchDialog,
  showFrameInterpolationDialog,
  showPreferencesDialog,
  showHDPreview,
  leftTab,
  aiTab,
  viewZoom,
  showCurveEditor,
  expandedPanels,
  triggerAssetImport,
  triggerProjectOpen,
  handleZoomChange,
});

function triggerProjectOpen() {
  const input = document.createElement("input");
  input.type = "file";
  input.accept = ".lattice,.json";
  input.onchange = async (e) => {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const target = e.target as HTMLInputElement;
    const files = (target != null && typeof target === "object" && "files" in target && target.files != null && target.files.length > 0) ? target.files : null;
    const file = (files != null && files.length > 0) ? files[0] : undefined;
    if (file) {
      await projectStore.loadProjectFromFile(file, () => projectStore.pushHistory());
    }
  };
  input.click();
}

/**
 * Handle preferences save
 */
interface Preferences {
  theme?: string;
  [key: string]: JSONValue;
}

function handlePreferencesSave(preferences: Preferences) {
  console.log("Preferences saved:", preferences);
  // Apply relevant preferences immediately
  if (preferences.theme) {
    // Theme would be applied via themeStore
  }
}

// Freeze frame at playhead (available via Layer menu)
function _freezeFrameSelectedLayers() {
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  for (const id of selectedIds) {
    layerStore.freezeFrameAtPlayhead(id);
  }
}

// Performance monitoring
let perfInterval: number;

interface PerformanceMemory {
  usedJSHeapSize: number;
  totalJSHeapSize: number;
  jsHeapSizeLimit: number;
}

function updatePerformanceStats() {
  // Memory usage (if available)
  if ("memory" in performance) {
    const mem = (performance as Performance & { memory?: PerformanceMemory }).memory;
    if (mem) {
      const usedMB = Math.round(mem.usedJSHeapSize / 1024 / 1024);
      memoryUsage.value = `${usedMB} MB`;
    }
  }
}

// Lifecycle
onMounted(async () => {
  const tierInfo = await detectGPUTier();
  gpuTier.value = tierInfo.tier;

  window.addEventListener("keydown", handleKeydown);

  perfInterval = window.setInterval(updatePerformanceStats, 1000);

  // Start autosave timer
  if (projectStore.autosaveEnabled) {
    // Note: startAutosaveTimer is managed by projectStore, not compositorStore
    // Autosave is configured via projectStore.configureAutosave()
  }
});

onUnmounted(() => {
  window.removeEventListener("keydown", handleKeydown);
  clearInterval(perfInterval);

  // Stop autosave timer
  projectStore.stopAutosave();
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
  padding: 4px;
  gap: 4px;
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

/* Panels - floating islands */
.panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--lattice-surface-1, #0f0f0f);
  border-radius: var(--lattice-radius-lg, 6px);
  overflow: hidden;
}

.left-panel,
.right-panel {
  min-width: 180px;
}

.right-panel {
  min-width: 200px;
}

.panel-tabs {
  display: flex;
  background: var(--lattice-surface-1, #0f0f0f);
  padding: 4px;
  gap: 0;
  border-radius: var(--lattice-radius-md, 4px);
  margin: 8px;
}

.panel-tabs button {
  flex: 1;
  padding: 10px 14px;
  border: none;
  background: transparent;
  color: var(--lattice-text-muted, #6B7280);
  font-size: var(--lattice-text-base, 13px);
  font-weight: 500;
  cursor: pointer;
  border-radius: var(--lattice-radius-sm, 2px);
  transition: var(--lattice-transition-fast, 100ms ease);
}

.panel-tabs button:hover {
  color: var(--lattice-text-primary, #e5e5e5);
}

.panel-tabs button.active {
  color: white;
  background: var(--lattice-accent, #8B5CF6);
  font-weight: 600;
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
  padding: 8px 12px;
  background: var(--lattice-surface-1, #0f0f0f);
  gap: 12px;
}

.viewport-tabs {
  display: flex;
  gap: 2px;
}

.viewport-tabs button {
  padding: 8px 18px;
  border: none;
  background: transparent;
  color: var(--lattice-text-muted, #6B7280);
  font-size: var(--lattice-text-base, 13px);
  font-weight: 500;
  border-radius: var(--lattice-radius-sm, 2px);
  cursor: pointer;
  transition: var(--lattice-transition-fast, 100ms ease);
}

.viewport-tabs button:hover {
  color: var(--lattice-text-primary, #e5e5e5);
}

.viewport-tabs button.active {
  background: var(--lattice-accent, #8B5CF6);
  color: white;
  font-weight: 600;
}

.viewport-controls {
  display: flex;
  align-items: center;
  gap: 2px;
}

.zoom-select {
  padding: 6px 10px;
  background: transparent;
  border: none;
  color: var(--lattice-text-primary, #e5e5e5);
  border-radius: var(--lattice-radius-sm, 2px);
  font-size: var(--lattice-text-sm, 12px);
}

.viewport-controls button {
  width: 36px;
  height: 36px;
  padding: 0;
  border: none;
  background: transparent;
  color: var(--lattice-text-secondary, #9CA3AF);
  border-radius: var(--lattice-radius-sm, 2px);
  cursor: pointer;
  font-size: 20px;
  transition: var(--lattice-transition-fast, 100ms ease);
}

.viewport-controls button:hover {
  color: var(--lattice-text-primary, #e5e5e5);
}

.viewport-controls button.active {
  background: var(--lattice-accent, #8B5CF6);
  color: white;
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

/* Vertical splitters (between columns) */
:deep(.splitpanes--vertical > .splitpanes__splitter) {
  width: 4px;
  min-width: 4px;
  background: var(--lattice-void, #050505);
}

:deep(.splitpanes--vertical > .splitpanes__splitter:hover) {
  background: var(--lattice-accent, #8B5CF6);
}

/* Horizontal splitters (between rows) */
:deep(.splitpanes--horizontal > .splitpanes__splitter) {
  height: 3px;
  min-height: 3px;
  background: var(--lattice-void, #050505);
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