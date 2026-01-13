import { type ComputedRef, computed, provide, type Ref, ref } from "vue";
import { useAudioStore } from "@/stores/audioStore";
import { useCompositorStore } from "@/stores/compositorStore";
import { useLayerStore } from "@/stores/layerStore";
import { usePlaybackStore } from "@/stores/playbackStore";
import { useSelectionStore } from "@/stores/selectionStore";
import { useKeyframeStore } from "@/stores/keyframeStore";
import { useAnimationStore } from "@/stores/animationStore";
import { useProjectStore } from "@/stores/projectStore";
import { useMarkerStore } from "@/stores/markerStore";
import type { AnimatableProperty } from "@/types/animation";
import type { LayerTransform } from "@/types/transform";

// Internal types for dynamic property access

/** Transform property keys that can be iterated for easing operations */
type EasingTransformKey = "position" | "scale" | "rotation" | "anchor" | "opacity";

/** Layer data with optional dimension/asset properties (used by fit-to-comp and reveal operations) */
interface LayerDataWithDimensions {
  width?: number;
  height?: number;
  assetId?: string | null;
  compositionId?: string;
  [key: string]: unknown;
}

/** Type-safe transform property accessor for easing operations */
function getTransformProperty(
  transform: LayerTransform,
  key: EasingTransformKey,
): AnimatableProperty<unknown> | undefined {
  // Map "anchor" to "origin" (the new property name)
  if (key === "anchor") {
    return transform.origin as AnimatableProperty<unknown>;
  }
  // For other keys, access directly
  if (key === "position") return transform.position as AnimatableProperty<unknown>;
  if (key === "scale") return transform.scale as AnimatableProperty<unknown>;
  if (key === "rotation") return transform.rotation as AnimatableProperty<unknown>;
  return undefined;
}

// Types
export type SoloPropertyType =
  | "position"
  | "scale"
  | "rotation"
  | "opacity"
  | "anchor"
  | "animated"
  | "modified"
  | "expressions"
  | "effects"
  | "masks";

export interface KeyboardShortcutsOptions {
  // Refs for dialogs
  showExportDialog: Ref<boolean>;
  showCompositionSettingsDialog: Ref<boolean>;
  showKeyframeInterpolationDialog: Ref<boolean>;
  showKeyframeVelocityDialog: Ref<boolean>;
  showPrecomposeDialog: Ref<boolean>;
  showCurveEditor: Ref<boolean>;
  showTimeStretchDialog: Ref<boolean>;
  showCameraTrackingImportDialog: Ref<boolean>;
  showKeyboardShortcutsModal?: Ref<boolean>;

  // UI state refs
  currentTool: Ref<string>;
  leftTab: Ref<string>;
  viewOptions: Ref<{
    showGrid: boolean;
    showRulers: boolean;
    gridSize: number;
  }>;

  // Canvas/viewer refs
  threeCanvasRef: Ref<any>;
  viewZoom: Ref<string>;

  // Computed values
  compWidth: ComputedRef<number>;
  compHeight: ComputedRef<number>;

  // Asset store for imports
  assetStore: ReturnType<typeof import("@/stores/assetStore").useAssetStore>;
}

export function useKeyboardShortcuts(options: KeyboardShortcutsOptions) {
  const store = useCompositorStore();
  const layerStore = useLayerStore();
  const playbackStore = usePlaybackStore();
  const audioStore = useAudioStore();
  const keyframeStore = useKeyframeStore();
  const animationStore = useAnimationStore();
  const projectStore = useProjectStore();
  const markerStore = useMarkerStore();

  const {
    showExportDialog,
    showCompositionSettingsDialog,
    showKeyframeInterpolationDialog,
    showKeyframeVelocityDialog,
    showPrecomposeDialog,
    showCurveEditor,
    showTimeStretchDialog,
    showCameraTrackingImportDialog,
    showKeyboardShortcutsModal,
    currentTool,
    leftTab,
    viewOptions,
    threeCanvasRef,
    viewZoom,
    compWidth,
    compHeight,
    assetStore,
  } = options;

  // ========================================================================
  // PLAYBACK STATE
  // ========================================================================
  const isPlaying = ref(false);

  function togglePlay() {
    isPlaying.value = !isPlaying.value;
    if (isPlaying.value) {
      store.play();
    } else {
      store.pause();
    }
  }

  function goToStart() {
    animationStore.goToStart(store);
  }

  function goToEnd() {
    animationStore.goToEnd(store);
  }

  function stepForward(frames: number = 1) {
    const currentFrame = animationStore.getCurrentFrame(store);
    animationStore.setFrame(store, Math.min(currentFrame + frames, projectStore.getFrameCount(store) - 1));
  }

  function stepBackward(frames: number = 1) {
    const currentFrame = animationStore.getCurrentFrame(store);
    animationStore.setFrame(store, Math.max(0, currentFrame - frames));
  }

  // ========================================================================
  // SMOOTH EASING (F9)
  // ========================================================================
  function applySmoothEasing() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    let keyframesUpdated = 0;

    for (const layerId of selectedIds) {
      const layer = layerStore.getLayerById(store, layerId);
      if (!layer?.transform) continue;

      const transform = layer.transform;
      const easingKeys: EasingTransformKey[] = ["position", "scale", "rotation", "anchor"];
      for (const propKey of easingKeys) {
        const prop = getTransformProperty(transform, propKey);
        if (prop?.animated && prop?.keyframes) {
          for (const kf of prop.keyframes) {
            keyframeStore.setKeyframeInterpolation(
              store,
              layerId,
              `transform.${propKey}`,
              kf.id,
              "bezier",
            );
            keyframesUpdated++;
          }
        }
      }

      if (layer.opacity?.animated && layer.opacity?.keyframes) {
        for (const kf of layer.opacity.keyframes) {
          keyframeStore.setKeyframeInterpolation(store, layerId, "opacity", kf.id, "bezier");
          keyframesUpdated++;
        }
      }
    }

    if (keyframesUpdated > 0) {
      console.log(
        `[Lattice] Applied smooth easing to ${keyframesUpdated} keyframes`,
      );
    }
  }

  function applySmoothEaseIn() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    let keyframesUpdated = 0;

    for (const layerId of selectedIds) {
      const layer = layerStore.getLayerById(store, layerId);
      if (!layer?.transform) continue;

      const transform = layer.transform;
      const easingKeys: EasingTransformKey[] = ["position", "scale", "rotation", "anchor"];
      for (const propKey of easingKeys) {
        const prop = getTransformProperty(transform, propKey);
        if (prop?.animated && prop?.keyframes) {
          for (const kf of prop.keyframes) {
            keyframeStore.setKeyframeInterpolation(
              store,
              layerId,
              `transform.${propKey}`,
              kf.id,
              "bezier",
            );
            keyframeStore.setKeyframeHandle(
              store,
              layerId,
              `transform.${propKey}`,
              kf.id,
              "out",
              { frame: 0.1, value: 0, enabled: true },
            );
            keyframeStore.setKeyframeHandle(
              store,
              layerId,
              `transform.${propKey}`,
              kf.id,
              "in",
              { frame: -0.42, value: 0, enabled: true },
            );
            keyframesUpdated++;
          }
        }
      }
    }

    if (keyframesUpdated > 0) {
      console.log(
        `[Lattice] Applied Smooth In to ${keyframesUpdated} keyframes`,
      );
    }
  }

  function applySmoothEaseOut() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    let keyframesUpdated = 0;

    for (const layerId of selectedIds) {
      const layer = layerStore.getLayerById(store, layerId);
      if (!layer?.transform) continue;

      const transform = layer.transform;
      const easingKeys: EasingTransformKey[] = ["position", "scale", "rotation", "anchor"];
      for (const propKey of easingKeys) {
        const prop = getTransformProperty(transform, propKey);
        if (prop?.animated && prop?.keyframes) {
          for (const kf of prop.keyframes) {
            keyframeStore.setKeyframeInterpolation(
              store,
              layerId,
              `transform.${propKey}`,
              kf.id,
              "bezier",
            );
            keyframeStore.setKeyframeHandle(
              store,
              layerId,
              `transform.${propKey}`,
              kf.id,
              "out",
              { frame: 0.42, value: 0, enabled: true },
            );
            keyframeStore.setKeyframeHandle(
              store,
              layerId,
              `transform.${propKey}`,
              kf.id,
              "in",
              { frame: -0.1, value: 0, enabled: true },
            );
            keyframesUpdated++;
          }
        }
      }
    }

    if (keyframesUpdated > 0) {
      console.log(
        `[Lattice] Applied Smooth Out to ${keyframesUpdated} keyframes`,
      );
    }
  }

  // ========================================================================
  // KEYFRAME NAVIGATION (J/K)
  // ========================================================================
  function goToPrevKeyframe() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    let prevFrame = -1;
    const currentFrame = animationStore.getCurrentFrame(store);

    for (const layerId of selectedIds) {
      const layer = layerStore.getLayerById(store, layerId);
      if (!layer?.transform) continue;

      const transform = layer.transform;
      const easingKeys: EasingTransformKey[] = ["position", "scale", "rotation", "anchor"];
      for (const propKey of easingKeys) {
        const prop = getTransformProperty(transform, propKey);
        if (prop?.animated && prop?.keyframes) {
          for (const kf of prop.keyframes) {
            if (kf.frame < currentFrame && kf.frame > prevFrame) {
              prevFrame = kf.frame;
            }
          }
        }
      }
    }

    if (prevFrame >= 0) {
      animationStore.setFrame(store, prevFrame);
    }
  }

  function goToNextKeyframe() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    let nextFrame = Infinity;
    const currentFrame = animationStore.getCurrentFrame(store);

    for (const layerId of selectedIds) {
      const layer = layerStore.getLayerById(store, layerId);
      if (!layer?.transform) continue;

      const transform = layer.transform;
      const easingKeys: EasingTransformKey[] = ["position", "scale", "rotation", "anchor"];
      for (const propKey of easingKeys) {
        const prop = getTransformProperty(transform, propKey);
        if (prop?.animated && prop?.keyframes) {
          for (const kf of prop.keyframes) {
            if (kf.frame > currentFrame && kf.frame < nextFrame) {
              nextFrame = kf.frame;
            }
          }
        }
      }
    }

    if (nextFrame < Infinity) {
      animationStore.setFrame(store, nextFrame);
    }
  }

  // ========================================================================
  // PROPERTY SOLO (P, S, R, T, A, U)
  // ========================================================================
  const soloedProperties = ref<Set<SoloPropertyType>>(new Set());

  function soloProperty(prop: SoloPropertyType, additive: boolean = false) {
    if (additive) {
      if (soloedProperties.value.has(prop)) {
        soloedProperties.value.delete(prop);
      } else {
        soloedProperties.value.add(prop);
      }
      soloedProperties.value = new Set(soloedProperties.value);
    } else {
      if (
        soloedProperties.value.size === 1 &&
        soloedProperties.value.has(prop)
      ) {
        soloedProperties.value = new Set();
      } else {
        soloedProperties.value = new Set([prop]);
      }
    }
  }

  const soloedProperty = computed(() => {
    const arr = Array.from(soloedProperties.value);
    return arr.length > 0 ? arr[0] : null;
  });

  // ========================================================================
  // DOUBLE-TAP DETECTION (UU, EE, MM)
  // ========================================================================
  const lastKeyPress = ref<{ key: string; time: number } | null>(null);
  const DOUBLE_TAP_THRESHOLD = 300;

  function isDoubleTap(key: string): boolean {
    const now = Date.now();
    const last = lastKeyPress.value;

    lastKeyPress.value = { key, time: now };

    if (last && last.key === key && now - last.time < DOUBLE_TAP_THRESHOLD) {
      lastKeyPress.value = null;
      return true;
    }

    return false;
  }

  // ========================================================================
  // RENDER RANGE (B/N)
  // ========================================================================
  const workAreaStart = ref<number | null>(null);
  const workAreaEnd = ref<number | null>(null);

  function setWorkAreaStart() {
    workAreaStart.value = animationStore.getCurrentFrame(store);
    playbackStore.setWorkArea(workAreaStart.value, workAreaEnd.value);
    console.log(
      `[Lattice] Render range start set to frame ${animationStore.getCurrentFrame(store)}`,
    );
  }

  function setWorkAreaEnd() {
    workAreaEnd.value = animationStore.getCurrentFrame(store);
    playbackStore.setWorkArea(workAreaStart.value, workAreaEnd.value);
    console.log(
      `[Lattice] Render range end set to frame ${animationStore.getCurrentFrame(store)}`,
    );
  }

  function clearWorkArea() {
    workAreaStart.value = null;
    workAreaEnd.value = null;
    playbackStore.clearWorkArea();
    console.log("[Lattice] Render range cleared");
  }

  // ========================================================================
  // HIDDEN LAYERS (Ctrl+Shift+Y)
  // ========================================================================
  const showHiddenLayers = ref(true);

  function toggleHiddenLayersVisibility() {
    showHiddenLayers.value = !showHiddenLayers.value;
    console.log(
      `[Lattice] Hidden layers visibility: ${showHiddenLayers.value ? "shown" : "hidden"}`,
    );
  }

  function toggleLayerHidden(layerId: string) {
    const layer = layerStore.getLayerById(store, layerId);
    if (layer) {
      // Layer uses 'visible' property (true = visible, false = hidden)
      layerStore.updateLayer(store, layerId, { visible: !layer.visible });
    }
  }

  // ========================================================================
  // PREVIEW PAUSE (Caps Lock)
  // ========================================================================
  const previewUpdatesPaused = ref(false);

  function togglePreviewPause() {
    previewUpdatesPaused.value = !previewUpdatesPaused.value;
    console.log(
      `[Lattice] Preview updates: ${previewUpdatesPaused.value ? "PAUSED" : "active"}`,
    );
  }

  // ========================================================================
  // TRANSPARENCY GRID (Ctrl+Shift+H)
  // ========================================================================
  const showTransparencyGrid = ref(false);

  function toggleTransparencyGrid() {
    showTransparencyGrid.value = !showTransparencyGrid.value;
    console.log(
      `[Lattice] Transparency grid: ${showTransparencyGrid.value ? "ON" : "OFF"}`,
    );
  }

  // ========================================================================
  // GRID OVERLAY (Ctrl+')
  // ========================================================================
  const gridColor = ref("#444444");
  const gridMajorColor = ref("#666666");

  function toggleGrid() {
    viewOptions.value.showGrid = !viewOptions.value.showGrid;
    console.log(`[Lattice] Grid: ${viewOptions.value.showGrid ? "ON" : "OFF"}`);
  }

  function setGridSize(size: number) {
    viewOptions.value.gridSize = Math.max(10, Math.min(200, size));
  }

  // ========================================================================
  // RULERS (Ctrl+Shift+R)
  // ========================================================================
  const rulerUnits = ref<"pixels" | "percent">("pixels");

  function toggleRulers() {
    viewOptions.value.showRulers = !viewOptions.value.showRulers;
    console.log(
      `[Lattice] Rulers: ${viewOptions.value.showRulers ? "ON" : "OFF"}`,
    );
  }

  // ========================================================================
  // SNAP (Ctrl+Shift+;)
  // ========================================================================
  const snapEnabled = ref(false);
  const snapToGrid = ref(true);
  const snapToGuides = ref(true);
  const snapToLayers = ref(true);
  const snapTolerance = ref(10);

  function toggleSnap() {
    snapEnabled.value = !snapEnabled.value;
    console.log(`[Lattice] Snap: ${snapEnabled.value ? "ON" : "OFF"}`);
  }

  // ========================================================================
  // UNDO/REDO (Ctrl+Z)
  // ========================================================================
  function undo() {
    store.undo();
  }

  function redo() {
    store.redo();
  }

  // ========================================================================
  // LAYER NAVIGATION (I/O - in/out points)
  // ========================================================================
  function goToLayerInPoint() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;
    const layer = layerStore.getLayerById(store, selectedIds[0]);
    if (layer) {
      animationStore.setFrame(store, layer.inPoint ?? 0);
    }
  }

  function goToLayerOutPoint() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;
    const layer = layerStore.getLayerById(store, selectedIds[0]);
    if (layer) {
      animationStore.setFrame(store, (layer.outPoint ?? projectStore.getFrameCount(store)) - 1);
    }
  }

  function moveLayerInPointToPlayhead() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;
    for (const id of selectedIds) {
      layerStore.updateLayer(store, id, { inPoint: animationStore.getCurrentFrame(store) });
    }
  }

  function moveLayerOutPointToPlayhead() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;
    for (const id of selectedIds) {
      layerStore.updateLayer(store, id, { outPoint: animationStore.getCurrentFrame(store) + 1 });
    }
  }

  function trimLayerInPoint() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;
    for (const id of selectedIds) {
      const layer = layerStore.getLayerById(store, id);
      if (layer) {
        const currentIn = layer.inPoint ?? 0;
        const currentFrame = animationStore.getCurrentFrame(store);
        if (currentFrame > currentIn) {
          layerStore.updateLayer(store, id, { inPoint: currentFrame });
        }
      }
    }
  }

  function trimLayerOutPoint() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;
    for (const id of selectedIds) {
      const layer = layerStore.getLayerById(store, id);
      if (layer) {
        const currentOut = layer.outPoint ?? projectStore.getFrameCount(store);
        const currentFrame = animationStore.getCurrentFrame(store);
        if (currentFrame < currentOut) {
          layerStore.updateLayer(store, id, { outPoint: currentFrame + 1 });
        }
      }
    }
  }

  // ========================================================================
  // LAYER SELECTION (Ctrl+Arrow)
  // ========================================================================
  function selectPreviousLayer(extend: boolean = false) {
    const layers = store.layers;
    if (layers.length === 0) return;

    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) {
      layerStore.selectLayer(store, layers[0].id);
      return;
    }

    const currentIndex = layers.findIndex((l) => l.id === selectedIds[0]);
    if (currentIndex > 0) {
      const targetLayer = layers[currentIndex - 1];
      if (extend) {
        layerStore.selectLayer(store, targetLayer.id);
      } else {
        layerStore.selectLayer(store, targetLayer.id);
      }
    }
  }

  function selectNextLayer(extend: boolean = false) {
    const layers = store.layers;
    if (layers.length === 0) return;

    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) {
      layerStore.selectLayer(store, layers[0].id);
      return;
    }

    const lastSelectedIndex = layers.findIndex(
      (l) => l.id === selectedIds[selectedIds.length - 1],
    );
    if (lastSelectedIndex < layers.length - 1) {
      const targetLayer = layers[lastSelectedIndex + 1];
      if (extend) {
        layerStore.selectLayer(store, targetLayer.id);
      } else {
        layerStore.selectLayer(store, targetLayer.id);
      }
    }
  }

  // ========================================================================
  // SPLIT LAYER (Ctrl+Shift+D)
  // ========================================================================
  function splitLayerAtPlayhead() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    for (const id of selectedIds) {
      const layer = layerStore.getLayerById(store, id);
      if (!layer) continue;

      const currentFrame = animationStore.getCurrentFrame(store);
      const inPoint = layer.inPoint ?? 0;
      const outPoint = layer.outPoint ?? projectStore.getFrameCount(store);

      if (currentFrame > inPoint && currentFrame < outPoint) {
        layerStore.updateLayer(store, id, { outPoint: currentFrame });

        const newLayer = layerStore.duplicateLayer(store, id);
        if (newLayer) {
          layerStore.updateLayer(store, newLayer.id, {
            inPoint: currentFrame,
            outPoint: outPoint,
          });
          layerStore.renameLayer(store, newLayer.id, `${layer.name} (split)`);
        }
      }
    }
  }

  // ========================================================================
  // REVERSE LAYER (Ctrl+Alt+R)
  // ========================================================================
  function reverseSelectedLayers() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    for (const id of selectedIds) {
      layerStore.reverseLayer(store, id);
    }
  }

  // ========================================================================
  // FREEZE FRAME (Alt+Shift+F)
  // ========================================================================
  function freezeSelectedLayers() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    for (const id of selectedIds) {
      layerStore.freezeFrameAtPlayhead(store, id);
    }
    console.log(
      "[Lattice] Freeze frame created at playhead for selected layers",
    );
  }

  // ========================================================================
  // TIMELINE ZOOM (=/- keys)
  // ========================================================================
  const timelineZoom = ref(1);

  function zoomTimelineIn() {
    timelineZoom.value = Math.min(timelineZoom.value * 1.5, 10);
    store.setTimelineZoom?.(timelineZoom.value);
  }

  function zoomTimelineOut() {
    timelineZoom.value = Math.max(timelineZoom.value / 1.5, 0.1);
    store.setTimelineZoom?.(timelineZoom.value);
  }

  function zoomTimelineToFit() {
    timelineZoom.value = 1;
    store.setTimelineZoom?.(1);
  }

  // ========================================================================
  // VIEWER ZOOM (Ctrl+=/Ctrl+-)
  // ========================================================================
  const viewerZoom = ref(1);

  function zoomViewerIn() {
    viewerZoom.value = Math.min(viewerZoom.value * 1.25, 8);
    if (threeCanvasRef.value) {
      threeCanvasRef.value.setZoom?.(viewerZoom.value);
    }
    const percent = Math.round(viewerZoom.value * 100);
    viewZoom.value = String(percent);
  }

  function zoomViewerOut() {
    viewerZoom.value = Math.max(viewerZoom.value / 1.25, 0.1);
    if (threeCanvasRef.value) {
      threeCanvasRef.value.setZoom?.(viewerZoom.value);
    }
    const percent = Math.round(viewerZoom.value * 100);
    viewZoom.value = String(percent);
  }

  function zoomViewerToFit() {
    viewerZoom.value = 1;
    viewZoom.value = "fit";
    if (threeCanvasRef.value) {
      threeCanvasRef.value.fitToView?.();
    }
  }

  function zoomViewerTo100() {
    viewerZoom.value = 1;
    viewZoom.value = "100";
    if (threeCanvasRef.value) {
      threeCanvasRef.value.setZoom?.(1);
    }
  }

  // ========================================================================
  // HOLD KEYFRAMES (Ctrl+Alt+H)
  // ========================================================================
  function convertToHoldKeyframes() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    let keyframesUpdated = 0;

    for (const layerId of selectedIds) {
      const layer = layerStore.getLayerById(store, layerId);
      if (!layer?.transform) continue;

      const transform = layer.transform;
      const easingKeys: EasingTransformKey[] = ["position", "scale", "rotation", "anchor"];
      for (const propKey of easingKeys) {
        const prop = getTransformProperty(transform, propKey);
        if (prop?.animated && prop?.keyframes) {
          for (const kf of prop.keyframes) {
            keyframeStore.setKeyframeInterpolation(
              store,
              layerId,
              `transform.${propKey}`,
              kf.id,
              "hold",
            );
            keyframesUpdated++;
          }
        }
      }
    }

    if (keyframesUpdated > 0) {
      console.log(`[Lattice] Converted ${keyframesUpdated} keyframes to hold`);
    }
  }

  // ========================================================================
  // TIME-REVERSE KEYFRAMES (Ctrl+Alt+R without layer)
  // ========================================================================
  function timeReverseKeyframes() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    let totalReversed = 0;
    for (const layerId of selectedIds) {
      // Use store action to reverse all transform property keyframes
      totalReversed += keyframeStore.timeReverseKeyframes(store, layerId);
    }

    if (totalReversed > 0) {
      console.log(`[Lattice] ${totalReversed} keyframes time-reversed`);
    }
  }

  // ========================================================================
  // FIT LAYER TO COMP (Ctrl+Alt+F)
  // ========================================================================
  function fitLayerToComp() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    const compW = compWidth.value;
    const compH = compHeight.value;

    for (const id of selectedIds) {
      const layer = layerStore.getLayerById(store, id);
      if (!layer) continue;

      const data = layer.data as unknown as LayerDataWithDimensions;
      const layerW = data?.width || compW;
      const layerH = data?.height || compH;

      const scaleX = compW / layerW;
      const scaleY = compH / layerH;
      const scale = Math.max(scaleX, scaleY);

      const centerX = compW / 2;
      const centerY = compH / 2;

      layerStore.updateLayerTransform(store, id, {
        position: { x: centerX, y: centerY, z: 0 },
        scale: { x: scale * 100, y: scale * 100, z: 100 },
        anchor: { x: layerW / 2, y: layerH / 2, z: 0 },
      });
    }

    console.log("[Lattice] Fit layer(s) to composition");
  }

  function fitLayerToCompWidth() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    const compW = compWidth.value;

    for (const id of selectedIds) {
      const layer = layerStore.getLayerById(store, id);
      if (!layer) continue;

      const data = layer.data as unknown as LayerDataWithDimensions;
      const layerW = data?.width || compW;

      const scale = compW / layerW;

      layerStore.updateLayerTransform(store, id, {
        scale: { x: scale * 100, y: scale * 100, z: 100 },
      });
    }

    console.log("[Lattice] Fit layer(s) to composition width");
  }

  function fitLayerToCompHeight() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    const compH = compHeight.value;

    for (const id of selectedIds) {
      const layer = layerStore.getLayerById(store, id);
      if (!layer) continue;

      const data = layer.data as unknown as LayerDataWithDimensions;
      const layerH = data?.height || compH;

      const scale = compH / layerH;

      layerStore.updateLayerTransform(store, id, {
        scale: { x: scale * 100, y: scale * 100, z: 100 },
      });
    }

    console.log("[Lattice] Fit layer(s) to composition height");
  }

  // ========================================================================
  // LOCK LAYER (Ctrl+L)
  // ========================================================================
  function toggleLayerLock() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    for (const id of selectedIds) {
      const layer = layerStore.getLayerById(store, id);
      if (layer) {
        layerStore.updateLayer(store, id, { locked: !layer.locked });
      }
    }
  }

  // ========================================================================
  // CENTER ANCHOR POINT (Ctrl+Alt+Home)
  // ========================================================================
  function centerAnchorPoint() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    for (const id of selectedIds) {
      const layer = layerStore.getLayerById(store, id);
      if (!layer) continue;

      const data = layer.data as unknown as LayerDataWithDimensions;
      const layerW = data?.width || compWidth.value;
      const layerH = data?.height || compHeight.value;

      const centerX = layerW / 2;
      const centerY = layerH / 2;

      const transform = layer.transform;
      // Use 'origin' (new name) or fall back to 'anchorPoint' (deprecated)
      const currentAnchor = transform.origin?.value ??
        transform.anchorPoint?.value ?? { x: 0, y: 0, z: 0 };
      const currentPos = transform.position?.value ?? { x: 0, y: 0, z: 0 };

      const offsetX = centerX - (currentAnchor.x || 0);
      const offsetY = centerY - (currentAnchor.y || 0);

      layerStore.updateLayerTransform(store, id, {
        anchor: { x: centerX, y: centerY, z: currentAnchor.z || 0 },
        position: {
          x: (currentPos.x || 0) + offsetX,
          y: (currentPos.y || 0) + offsetY,
          z: currentPos.z || 0,
        },
      });
    }

    console.log("[Lattice] Centered anchor point(s)");
  }

  // ========================================================================
  // CENTER LAYER IN COMP (Ctrl+Home)
  // ========================================================================
  function centerLayerInComp() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    const centerX = compWidth.value / 2;
    const centerY = compHeight.value / 2;

    for (const id of selectedIds) {
      const layer = layerStore.getLayerById(store, id);
      if (!layer) continue;

      const transform = layer.transform;
      const currentPos = transform.position?.value ?? { x: 0, y: 0, z: 0 };

      layerStore.updateLayerTransform(store, id, {
        position: { x: centerX, y: centerY, z: currentPos.z || 0 },
      });
    }

    console.log("[Lattice] Centered layer(s) in composition");
  }

  // ========================================================================
  // CREATE EFFECT LAYER (Ctrl+Alt+Y)
  // ========================================================================
  function createAdjustmentLayer() {
    layerStore.createLayer(store, "adjustment", "Effect Layer");
    console.log("[Lattice] Created effect layer");
  }

  // ========================================================================
  // CREATE CONTROL LAYER (Ctrl+Alt+Shift+Y)
  // ========================================================================
  function createNullLayer() {
    layerStore.createLayer(store, "null", "Control");
    console.log("[Lattice] Created control layer");
  }

  // ========================================================================
  // REVEAL SOURCE IN PROJECT (Ctrl+Alt+E)
  // ========================================================================
  function revealSourceInProject() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) {
      console.log("[Lattice] No layer selected to reveal source");
      return;
    }

    const layer = layerStore.getLayerById(store, selectedIds[0]);
    if (!layer) return;

    const data = layer.data as unknown as LayerDataWithDimensions;
    let assetId: string | null = null;

    if (data?.assetId) {
      assetId = data.assetId;
    } else if (layer.type === "nestedComp") {
      if (data?.compositionId) {
        leftTab.value = "comps";
        console.log(
          `[Lattice] Revealed nested comp source: ${data.compositionId}`,
        );
        return;
      }
    }

    if (assetId) {
      leftTab.value = "assets";
      if (typeof store.selectAsset === "function") {
        store.selectAsset(assetId);
      }
      console.log(`[Lattice] Revealed source asset: ${assetId}`);
    } else {
      console.log(`[Lattice] Layer type '${layer.type}' has no source asset`);
    }
  }

  // ========================================================================
  // SELECT ALL KEYFRAMES ON LAYERS (Ctrl+A)
  // ========================================================================
  function selectAllKeyframesOnSelectedLayers(): boolean {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return false;

    const keyframeIds: string[] = [];

    for (const layerId of selectedIds) {
      const layer = layerStore.getLayerById(store, layerId);
      if (!layer) continue;

      const transform = layer.transform;
      if (transform) {
        const easingKeys: EasingTransformKey[] = ["position", "rotation", "scale", "anchor"];
        for (const propName of easingKeys) {
          const prop = getTransformProperty(transform, propName);
          if (prop?.keyframes && Array.isArray(prop.keyframes)) {
            for (const kf of prop.keyframes) {
              if (kf.id) keyframeIds.push(kf.id);
            }
          }
        }
      }

      const data = layer.data as unknown as LayerDataWithDimensions;
      if (data) {
        const checkForKeyframes = (obj: unknown): void => {
          if (!obj || typeof obj !== "object" || obj === null) return;
          if (Array.isArray((obj as Record<string, unknown>).keyframes)) {
            const keyframes = (obj as Record<string, unknown>).keyframes as Array<{ id?: string }>;
            for (const kf of keyframes) {
              if (kf.id) keyframeIds.push(kf.id);
            }
          }
          for (const key of Object.keys(obj)) {
            const value = (obj as Record<string, unknown>)[key];
            if (typeof value === "object" && value !== null) checkForKeyframes(value);
          }
        };
        checkForKeyframes(data);
      }
    }

    if (keyframeIds.length > 0) {
      useSelectionStore().selectKeyframes(keyframeIds);
      console.log(
        `[Lattice] Selected ${keyframeIds.length} keyframes on ${selectedIds.length} layer(s)`,
      );
      return true;
    }
    return false;
  }

  // ========================================================================
  // SELECT LAYERS BY LABEL (Ctrl+Shift+G)
  // ========================================================================
  function selectLayersByLabel() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    const firstLayer = layerStore.getLayerById(store, selectedIds[0]);
    if (!firstLayer) return;

    const targetColor = firstLayer.labelColor || "#808080";

    const layers = store.layers;
    const matchingIds: string[] = [];

    for (const layer of layers) {
      const layerColor = layer.labelColor || "#808080";
      if (layerColor === targetColor) {
        matchingIds.push(layer.id);
      }
    }

    if (matchingIds.length > 0) {
      const selectionStore = useSelectionStore();
      selectionStore.selectLayers(matchingIds);
      console.log(
        `[Lattice] Selected ${matchingIds.length} layers with label color ${targetColor}`,
      );
    }
  }

  // ========================================================================
  // ASSET IMPORT (Ctrl+I)
  // ========================================================================
  function triggerAssetImport() {
    const input = document.createElement("input");
    input.type = "file";
    input.accept =
      ".svg,.gltf,.glb,.obj,.fbx,.hdr,.exr,.png,.jpg,.jpeg,.webp,.gif,.mp4,.webm,.mov";
    input.multiple = true;
    input.onchange = async (e) => {
      const files = (e.target as HTMLInputElement).files;
      if (!files) return;

      // Use Array.from() for explicit iteration (FileList is array-like)
      for (const file of Array.from(files)) {
        const ext = file.name.split(".").pop()?.toLowerCase();
        if (ext === "svg") {
          await assetStore.importSvgFromFile(file);
        } else if (["hdr", "exr"].includes(ext || "")) {
          await assetStore.loadEnvironment(file);
        } else if (["png", "jpg", "jpeg", "webp", "gif"].includes(ext || "")) {
          // Import image as layer
          const url = URL.createObjectURL(file);
          const img = new Image();
          img.onload = () => {
            const layerName = file.name.replace(/\.[^/.]+$/, "");
            const layer = layerStore.createLayer(store, "image", layerName);
            if (layer?.data) {
              const data = layer.data as unknown as Record<string, unknown>;
              data.src = url;
              data.width = img.width;
              data.height = img.height;
              data.originalFilename = file.name;
            }
          };
          img.src = url;
        } else if (["mp4", "webm", "mov"].includes(ext || "")) {
          // Import video as layer
          const url = URL.createObjectURL(file);
          const layerName = file.name.replace(/\.[^/.]+$/, "");
          layerStore.createVideoLayer(store, file).then((result) => {
            if (result.status === "success" && result.layer?.data) {
              const data = result.layer.data as unknown as Record<string, unknown>;
              data.originalFilename = file.name;
            }
          });
        } else if (["gltf", "glb", "obj", "fbx"].includes(ext || "")) {
          // Import 3D model
          const url = URL.createObjectURL(file);
          const layerName = file.name.replace(/\.[^/.]+$/, "");
          const layer = layerStore.createLayer(store, "model", layerName);
          if (layer?.data) {
            const data = layer.data as unknown as Record<string, unknown>;
            data.src = url;
            data.format = ext;
            data.originalFilename = file.name;
          }
        }
      }

      leftTab.value = "project";
    };
    input.click();
  }

  // ========================================================================
  // OPEN TIME STRETCH DIALOG (Ctrl+Alt+T)
  // ========================================================================
  function openTimeStretchDialog() {
    if (store.selectedLayerIds.length === 0) return;
    showTimeStretchDialog.value = true;
  }

  // ========================================================================
  // OPEN CAMERA TRACKING IMPORT DIALOG (Ctrl+Shift+I)
  // ========================================================================
  function openCameraTrackingImportDialog() {
    showCameraTrackingImportDialog.value = true;
  }

  // ========================================================================
  // KEYBOARD EVENT HANDLER
  // ========================================================================
  function handleKeydown(e: KeyboardEvent) {
    // Don't handle if input is focused
    if (
      document.activeElement?.tagName === "INPUT" ||
      document.activeElement?.tagName === "TEXTAREA"
    ) {
      return;
    }

    const hasSelectedLayer = store.selectedLayerIds.length > 0;

    switch (e.key.toLowerCase()) {
      case " ":
        e.preventDefault();
        togglePlay();
        break;

      // Property solo shortcuts
      case "p":
        if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
          e.preventDefault();
          soloProperty("position", e.shiftKey);
        } else if (!e.ctrlKey && !e.metaKey && !e.shiftKey) {
          currentTool.value = "pen";
        }
        break;
      case "s":
        if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
          e.preventDefault();
          soloProperty("scale", e.shiftKey);
        }
        break;
      case "t":
        if ((e.ctrlKey || e.metaKey) && e.altKey && hasSelectedLayer) {
          e.preventDefault();
          openTimeStretchDialog();
        } else if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
          e.preventDefault();
          soloProperty("opacity", e.shiftKey);
        } else if (!e.ctrlKey && !e.metaKey && !e.shiftKey) {
          currentTool.value = "text";
        }
        break;
      case "a":
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          if (hasSelectedLayer) {
            const selectedKeyframes = selectAllKeyframesOnSelectedLayers();
            if (!selectedKeyframes) {
              layerStore.selectAllLayers(store);
            }
          } else {
            layerStore.selectAllLayers(store);
          }
        } else if (hasSelectedLayer) {
          e.preventDefault();
          soloProperty("anchor", e.shiftKey);
        } else if (!e.shiftKey) {
          leftTab.value = "assets";
        }
        break;
      case "u":
        if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
          e.preventDefault();
          if (isDoubleTap("u")) {
            soloProperty("modified", e.shiftKey);
          } else {
            soloProperty("animated", e.shiftKey);
          }
        }
        break;

      case "e":
        if ((e.ctrlKey || e.metaKey) && e.altKey && hasSelectedLayer) {
          e.preventDefault();
          revealSourceInProject();
        } else if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
          e.preventDefault();
          if (isDoubleTap("e")) {
            soloProperty("expressions", e.shiftKey);
          } else {
            soloProperty("effects", e.shiftKey);
          }
        }
        break;

      case "m":
        if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
          e.preventDefault();
          if (isDoubleTap("m")) {
            soloProperty("masks", e.shiftKey);
            console.log("[Lattice] Showing all mask properties (MM)");
          } else {
            soloProperty("masks", e.shiftKey);
          }
        } else if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          showExportDialog.value = true;
        }
        break;

      case "h":
        if (e.ctrlKey && e.altKey) {
          e.preventDefault();
          convertToHoldKeyframes();
        } else if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
          e.preventDefault();
          toggleTransparencyGrid();
        } else if (!e.ctrlKey && !e.metaKey && !e.shiftKey && !e.altKey) {
          currentTool.value = "hand";
        }
        break;
      case "z":
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          if (e.shiftKey) {
            redo();
          } else {
            undo();
          }
        } else {
          currentTool.value = "zoom";
        }
        break;

      // Navigation
      case "end":
        e.preventDefault();
        goToEnd();
        break;
      case "pageup":
        e.preventDefault();
        stepBackward(e.shiftKey ? 10 : 1);
        break;
      case "pagedown":
        e.preventDefault();
        stepForward(e.shiftKey ? 10 : 1);
        break;
      case "arrowleft":
        e.preventDefault();
        stepBackward(e.shiftKey ? 10 : 1);
        break;
      case "arrowright":
        e.preventDefault();
        stepForward(e.shiftKey ? 10 : 1);
        break;

      // Keyframe/Marker navigation (J/K, Shift+J/K for markers)
      case "j":
        if (!e.ctrlKey && !e.metaKey) {
          e.preventDefault();
          if (e.shiftKey) {
            // Shift+J: Jump to previous marker
            store.jumpToPreviousMarker();
          } else {
            // J: Go to previous keyframe
            goToPrevKeyframe();
          }
        }
        break;
      case "k":
        if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
          e.preventDefault();
          if (store.selectedKeyframeIds.length > 0) {
            showKeyframeInterpolationDialog.value = true;
          } else {
            console.log(
              "[Lattice] No keyframes selected for interpolation dialog",
            );
          }
        } else if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          showCompositionSettingsDialog.value = true;
        } else if (e.shiftKey) {
          // Shift+K: Jump to next marker
          e.preventDefault();
          store.jumpToNextMarker();
        } else {
          e.preventDefault();
          goToNextKeyframe();
        }
        break;

      case "g":
        if ((e.ctrlKey || e.metaKey) && e.shiftKey && hasSelectedLayer) {
          e.preventDefault();
          selectLayersByLabel();
        } else if (e.shiftKey) {
          e.preventDefault();
          showCurveEditor.value = !showCurveEditor.value;
        }
        break;
      case "i":
        if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
          // Ctrl+Shift+I - Import Camera Tracking
          e.preventDefault();
          openCameraTrackingImportDialog();
        } else if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          triggerAssetImport();
        } else if (hasSelectedLayer) {
          e.preventDefault();
          goToLayerInPoint();
        }
        break;
      case "o":
        if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
          e.preventDefault();
          goToLayerOutPoint();
        }
        break;

      // Pre-compose (Ctrl+Shift+C)
      case "c":
        if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
          e.preventDefault();
          if (store.selectedLayerIds.length > 0) {
            showPrecomposeDialog.value = true;
          }
        } else if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          layerStore.copySelectedLayers(store);
        }
        break;
      case "delete":
      case "backspace":
        if (store.selectedLayerIds.length > 0) {
          e.preventDefault();
          layerStore.deleteSelectedLayers(store);
        }
        break;
      case "f9":
        e.preventDefault();
        if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
          applySmoothEaseOut();
        } else if (e.shiftKey) {
          applySmoothEaseIn();
        } else {
          applySmoothEasing();
        }
        break;
      case "v":
        if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
          // Ctrl+Shift+V - Keyframe Velocity Dialog
          e.preventDefault();
          if (store.selectedKeyframeIds.length > 0) {
            showKeyframeVelocityDialog.value = true;
          } else {
            console.log(
              "[Lattice] No keyframes selected for velocity dialog",
            );
          }
        } else if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          layerStore.pasteLayers(store);
        } else if (!e.shiftKey) {
          currentTool.value = "select";
        }
        break;
      case "x":
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          layerStore.cutSelectedLayers(store);
        }
        break;

      // Layer timing ([ and ])
      case "[":
        if (e.altKey) {
          e.preventDefault();
          trimLayerInPoint();
        } else if (hasSelectedLayer) {
          e.preventDefault();
          moveLayerInPointToPlayhead();
        }
        break;
      case "]":
        if (e.altKey) {
          e.preventDefault();
          trimLayerOutPoint();
        } else if (hasSelectedLayer) {
          e.preventDefault();
          moveLayerOutPointToPlayhead();
        }
        break;

      // Layer navigation (Ctrl+Arrow)
      case "arrowup":
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          selectPreviousLayer(e.shiftKey);
        }
        break;
      case "arrowdown":
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          selectNextLayer(e.shiftKey);
        }
        break;

      // Split/Duplicate layer
      case "d":
        if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
          e.preventDefault();
          splitLayerAtPlayhead();
        } else if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          layerStore.duplicateSelectedLayers(store);
        }
        break;

      // R key shortcuts
      case "r":
        if ((e.ctrlKey || e.metaKey) && e.shiftKey && !e.altKey) {
          e.preventDefault();
          toggleRulers();
        } else if ((e.ctrlKey || e.metaKey) && e.altKey && hasSelectedLayer) {
          e.preventDefault();
          reverseSelectedLayers();
        } else if ((e.ctrlKey || e.metaKey) && e.altKey) {
          e.preventDefault();
          timeReverseKeyframes();
        } else if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
          e.preventDefault();
          soloProperty("rotation", e.shiftKey);
        }
        break;

      // Timeline zoom
      case "=":
      case "+":
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          zoomViewerIn();
        } else {
          e.preventDefault();
          zoomTimelineIn();
        }
        break;
      case "-":
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          zoomViewerOut();
        } else {
          e.preventDefault();
          zoomTimelineOut();
        }
        break;
      case ";":
        if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
          e.preventDefault();
          toggleSnap();
        } else if (!e.ctrlKey && !e.metaKey) {
          e.preventDefault();
          zoomTimelineToFit();
        }
        break;
      case "0":
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          zoomViewerToFit();
        } else if (e.shiftKey && (e.ctrlKey || e.metaKey)) {
          e.preventDefault();
          zoomViewerTo100();
        }
        break;

      // Audio-only preview
      case ".":
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          audioStore.toggleAudioPlayback(animationStore.getCurrentFrame(store), projectStore.getFps(store));
        }
        break;

      // Work area
      case "b":
        if (!e.ctrlKey && !e.metaKey && !e.shiftKey) {
          e.preventDefault();
          setWorkAreaStart();
        }
        break;
      case "n":
        if (!e.ctrlKey && !e.metaKey && !e.shiftKey) {
          e.preventDefault();
          setWorkAreaEnd();
        }
        break;

      // Lock layer
      case "l":
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          toggleLayerLock();
        }
        break;

      // Preview pause
      case "capslock":
        e.preventDefault();
        togglePreviewPause();
        break;

      // Fit layer to comp / Freeze frame
      case "f":
        if ((e.ctrlKey || e.metaKey) && e.altKey) {
          e.preventDefault();
          if (e.shiftKey) {
            fitLayerToCompHeight();
          } else {
            fitLayerToComp();
          }
        } else if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
          e.preventDefault();
          fitLayerToCompWidth();
        } else if (e.altKey && e.shiftKey && hasSelectedLayer) {
          // Freeze frame at playhead (Alt+Shift+F)
          e.preventDefault();
          freezeSelectedLayers();
        }
        break;

      // Y key shortcuts
      case "y":
        if ((e.ctrlKey || e.metaKey) && e.altKey && e.shiftKey) {
          e.preventDefault();
          createNullLayer();
        } else if ((e.ctrlKey || e.metaKey) && e.altKey) {
          e.preventDefault();
          createAdjustmentLayer();
        } else if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
          e.preventDefault();
          toggleHiddenLayersVisibility();
        }
        break;

      // Home key shortcuts
      case "home":
        if ((e.ctrlKey || e.metaKey) && e.altKey) {
          e.preventDefault();
          centerAnchorPoint();
        } else if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          centerLayerInComp();
        } else {
          e.preventDefault();
          animationStore.setFrame(store, 0);
        }
        break;

      // Grid toggle
      case "'":
      case "`":
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          toggleGrid();
        }
        break;

      // Keyboard shortcuts modal
      case "?":
        e.preventDefault();
        if (showKeyboardShortcutsModal) {
          showKeyboardShortcutsModal.value = !showKeyboardShortcutsModal.value;
        }
        break;

      // Add marker at playhead (* on numpad or Shift+8)
      case "*":
      case "numpadmultiply":
        e.preventDefault();
        markerStore.addMarkers(store, [
          {
            frame: animationStore.getCurrentFrame(store),
            label: `Marker ${markerStore.getMarkers(store).length + 1}`,
            color: "#FFFF00",
          },
        ]);
        break;
    }
  }

  // ========================================================================
  // PROVIDE STATE TO CHILD COMPONENTS
  // ========================================================================
  function setupProvides() {
    provide("soloedProperty", soloedProperty);
    provide("soloedProperties", soloedProperties);
    provide("workAreaStart", workAreaStart);
    provide("workAreaEnd", workAreaEnd);
    provide("showHiddenLayers", showHiddenLayers);
    provide("toggleLayerHidden", toggleLayerHidden);
    provide("previewUpdatesPaused", previewUpdatesPaused);
    provide("showTransparencyGrid", showTransparencyGrid);
    provide("gridColor", gridColor);
    provide("gridMajorColor", gridMajorColor);
    provide("rulerUnits", rulerUnits);
    provide("snapEnabled", snapEnabled);
    provide("snapToGrid", snapToGrid);
    provide("snapToGuides", snapToGuides);
    provide("snapToLayers", snapToLayers);
    provide("snapTolerance", snapTolerance);
    provide("toggleSnap", toggleSnap);
  }

  return {
    // State
    isPlaying,
    soloedProperties,
    soloedProperty,
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

    // Actions
    togglePlay,
    goToStart,
    goToEnd,
    stepForward,
    stepBackward,
    applySmoothEasing,
    applySmoothEaseIn,
    applySmoothEaseOut,
    goToPrevKeyframe,
    goToNextKeyframe,
    soloProperty,
    isDoubleTap,
    setWorkAreaStart,
    setWorkAreaEnd,
    clearWorkArea,
    toggleHiddenLayersVisibility,
    toggleLayerHidden,
    togglePreviewPause,
    toggleTransparencyGrid,
    toggleGrid,
    setGridSize,
    toggleRulers,
    toggleSnap,
    undo,
    redo,
    goToLayerInPoint,
    goToLayerOutPoint,
    moveLayerInPointToPlayhead,
    moveLayerOutPointToPlayhead,
    trimLayerInPoint,
    trimLayerOutPoint,
    selectPreviousLayer,
    selectNextLayer,
    splitLayerAtPlayhead,
    reverseSelectedLayers,
    freezeSelectedLayers,
    zoomTimelineIn,
    zoomTimelineOut,
    zoomTimelineToFit,
    zoomViewerIn,
    zoomViewerOut,
    zoomViewerToFit,
    zoomViewerTo100,
    convertToHoldKeyframes,
    timeReverseKeyframes,
    fitLayerToComp,
    fitLayerToCompWidth,
    fitLayerToCompHeight,
    toggleLayerLock,
    centerAnchorPoint,
    centerLayerInComp,
    createAdjustmentLayer,
    createNullLayer,
    revealSourceInProject,
    selectAllKeyframesOnSelectedLayers,
    selectLayersByLabel,
    triggerAssetImport,
    openTimeStretchDialog,
    handleKeydown,
    setupProvides,
  };
}
