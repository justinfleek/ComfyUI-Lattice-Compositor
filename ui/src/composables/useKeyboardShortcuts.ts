import { type ComputedRef, computed, provide, type Ref, ref } from "vue";
import { useAudioStore } from "@/stores/audioStore";
import { useCompositorStore } from "@/stores/compositorStore";
import { usePlaybackStore } from "@/stores/playbackStore";
import { useSelectionStore } from "@/stores/selectionStore";

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
  assetStore: any;
}

export function useKeyboardShortcuts(options: KeyboardShortcutsOptions) {
  const store = useCompositorStore();
  const playbackStore = usePlaybackStore();
  const audioStore = useAudioStore();

  const {
    showExportDialog,
    showCompositionSettingsDialog,
    showKeyframeInterpolationDialog,
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
    store.goToStart();
  }

  function goToEnd() {
    store.goToEnd();
  }

  function stepForward(frames: number = 1) {
    store.setFrame(Math.min(store.currentFrame + frames, store.frameCount - 1));
  }

  function stepBackward(frames: number = 1) {
    store.setFrame(Math.max(0, store.currentFrame - frames));
  }

  // ========================================================================
  // SMOOTH EASING (F9)
  // ========================================================================
  function applySmoothEasing() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    let keyframesUpdated = 0;

    for (const layerId of selectedIds) {
      const layer = store.getLayerById(layerId);
      if (!layer?.transform) continue;

      const transform = layer.transform as any;
      for (const propKey of [
        "position",
        "scale",
        "rotation",
        "anchor",
        "opacity",
      ]) {
        const prop = transform[propKey];
        if (prop?.animated && prop?.keyframes) {
          for (const kf of prop.keyframes) {
            store.setKeyframeInterpolation(
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
          store.setKeyframeInterpolation(layerId, "opacity", kf.id, "bezier");
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
      const layer = store.getLayerById(layerId);
      if (!layer?.transform) continue;

      const transform = layer.transform as any;
      for (const propKey of [
        "position",
        "scale",
        "rotation",
        "anchor",
        "opacity",
      ]) {
        const prop = transform[propKey];
        if (prop?.animated && prop?.keyframes) {
          for (const kf of prop.keyframes) {
            store.setKeyframeInterpolation(
              layerId,
              `transform.${propKey}`,
              kf.id,
              "bezier",
            );
            store.updateKeyframeHandles?.(
              layerId,
              `transform.${propKey}`,
              kf.id,
              {
                inHandle: { x: -0.42, y: 0 },
                outHandle: { x: 0.1, y: 0 },
              },
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
      const layer = store.getLayerById(layerId);
      if (!layer?.transform) continue;

      const transform = layer.transform as any;
      for (const propKey of [
        "position",
        "scale",
        "rotation",
        "anchor",
        "opacity",
      ]) {
        const prop = transform[propKey];
        if (prop?.animated && prop?.keyframes) {
          for (const kf of prop.keyframes) {
            store.setKeyframeInterpolation(
              layerId,
              `transform.${propKey}`,
              kf.id,
              "bezier",
            );
            store.updateKeyframeHandles?.(
              layerId,
              `transform.${propKey}`,
              kf.id,
              {
                inHandle: { x: -0.1, y: 0 },
                outHandle: { x: 0.42, y: 0 },
              },
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
    const currentFrame = store.currentFrame;

    for (const layerId of selectedIds) {
      const layer = store.getLayerById(layerId);
      if (!layer?.transform) continue;

      const transform = layer.transform as any;
      for (const propKey of [
        "position",
        "scale",
        "rotation",
        "anchor",
        "opacity",
      ]) {
        const prop = transform[propKey];
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
      store.setFrame(prevFrame);
    }
  }

  function goToNextKeyframe() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    let nextFrame = Infinity;
    const currentFrame = store.currentFrame;

    for (const layerId of selectedIds) {
      const layer = store.getLayerById(layerId);
      if (!layer?.transform) continue;

      const transform = layer.transform as any;
      for (const propKey of [
        "position",
        "scale",
        "rotation",
        "anchor",
        "opacity",
      ]) {
        const prop = transform[propKey];
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
      store.setFrame(nextFrame);
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
    workAreaStart.value = store.currentFrame;
    playbackStore.setWorkArea(workAreaStart.value, workAreaEnd.value);
    console.log(
      `[Lattice] Render range start set to frame ${store.currentFrame}`,
    );
  }

  function setWorkAreaEnd() {
    workAreaEnd.value = store.currentFrame;
    playbackStore.setWorkArea(workAreaStart.value, workAreaEnd.value);
    console.log(
      `[Lattice] Render range end set to frame ${store.currentFrame}`,
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
    const layer = store.getLayerById(layerId);
    if (layer) {
      // Layer uses 'visible' property (true = visible, false = hidden)
      store.updateLayer(layerId, { visible: !layer.visible });
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
    const layer = store.getLayerById(selectedIds[0]);
    if (layer) {
      store.setFrame(layer.inPoint ?? 0);
    }
  }

  function goToLayerOutPoint() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;
    const layer = store.getLayerById(selectedIds[0]);
    if (layer) {
      store.setFrame((layer.outPoint ?? store.frameCount) - 1);
    }
  }

  function moveLayerInPointToPlayhead() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;
    for (const id of selectedIds) {
      store.updateLayer(id, { inPoint: store.currentFrame });
    }
  }

  function moveLayerOutPointToPlayhead() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;
    for (const id of selectedIds) {
      store.updateLayer(id, { outPoint: store.currentFrame + 1 });
    }
  }

  function trimLayerInPoint() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;
    for (const id of selectedIds) {
      const layer = store.getLayerById(id);
      if (layer) {
        const currentIn = layer.inPoint ?? 0;
        if (store.currentFrame > currentIn) {
          store.updateLayer(id, { inPoint: store.currentFrame });
        }
      }
    }
  }

  function trimLayerOutPoint() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;
    for (const id of selectedIds) {
      const layer = store.getLayerById(id);
      if (layer) {
        const currentOut = layer.outPoint ?? store.frameCount;
        if (store.currentFrame < currentOut) {
          store.updateLayer(id, { outPoint: store.currentFrame + 1 });
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
      store.selectLayer(layers[0].id);
      return;
    }

    const currentIndex = layers.findIndex((l) => l.id === selectedIds[0]);
    if (currentIndex > 0) {
      const targetLayer = layers[currentIndex - 1];
      if (extend) {
        store.selectLayer(targetLayer.id, true);
      } else {
        store.selectLayer(targetLayer.id);
      }
    }
  }

  function selectNextLayer(extend: boolean = false) {
    const layers = store.layers;
    if (layers.length === 0) return;

    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) {
      store.selectLayer(layers[0].id);
      return;
    }

    const lastSelectedIndex = layers.findIndex(
      (l) => l.id === selectedIds[selectedIds.length - 1],
    );
    if (lastSelectedIndex < layers.length - 1) {
      const targetLayer = layers[lastSelectedIndex + 1];
      if (extend) {
        store.selectLayer(targetLayer.id, true);
      } else {
        store.selectLayer(targetLayer.id);
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
      const layer = store.getLayerById(id);
      if (!layer) continue;

      const currentFrame = store.currentFrame;
      const inPoint = layer.inPoint ?? 0;
      const outPoint = layer.outPoint ?? store.frameCount;

      if (currentFrame > inPoint && currentFrame < outPoint) {
        store.updateLayer(id, { outPoint: currentFrame });

        const newLayer = store.duplicateLayer(id);
        if (newLayer) {
          store.updateLayer(newLayer.id, {
            inPoint: currentFrame,
            outPoint: outPoint,
          });
          store.renameLayer(newLayer.id, `${layer.name} (split)`);
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
      store.reverseLayer(id);
    }
  }

  // ========================================================================
  // FREEZE FRAME (Alt+Shift+F)
  // ========================================================================
  function freezeSelectedLayers() {
    const selectedIds = store.selectedLayerIds;
    if (selectedIds.length === 0) return;

    for (const id of selectedIds) {
      store.freezeFrameAtPlayhead(id);
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
      const layer = store.getLayerById(layerId);
      if (!layer?.transform) continue;

      const transform = layer.transform as any;
      for (const propKey of [
        "position",
        "scale",
        "rotation",
        "anchor",
        "opacity",
      ]) {
        const prop = transform[propKey];
        if (prop?.animated && prop?.keyframes) {
          for (const kf of prop.keyframes) {
            store.setKeyframeInterpolation(
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
      totalReversed += store.timeReverseKeyframes(layerId);
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
      const layer = store.getLayerById(id);
      if (!layer) continue;

      const data = layer.data as any;
      const layerW = data?.width || compW;
      const layerH = data?.height || compH;

      const scaleX = compW / layerW;
      const scaleY = compH / layerH;
      const scale = Math.max(scaleX, scaleY);

      const centerX = compW / 2;
      const centerY = compH / 2;

      store.updateLayerTransform?.(id, {
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
      const layer = store.getLayerById(id);
      if (!layer) continue;

      const data = layer.data as any;
      const layerW = data?.width || compW;

      const scale = compW / layerW;

      store.updateLayerTransform?.(id, {
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
      const layer = store.getLayerById(id);
      if (!layer) continue;

      const data = layer.data as any;
      const layerH = data?.height || compH;

      const scale = compH / layerH;

      store.updateLayerTransform?.(id, {
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
      const layer = store.getLayerById(id);
      if (layer) {
        store.updateLayer(id, { locked: !layer.locked });
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
      const layer = store.getLayerById(id);
      if (!layer) continue;

      const data = layer.data as any;
      const layerW = data?.width || compWidth.value;
      const layerH = data?.height || compHeight.value;

      const centerX = layerW / 2;
      const centerY = layerH / 2;

      const transform = layer.transform as any;
      const currentAnchor = transform?.anchor?.value ||
        transform?.anchor?.defaultValue || { x: 0, y: 0, z: 0 };
      const currentPos = transform?.position?.value ||
        transform?.position?.defaultValue || { x: 0, y: 0, z: 0 };

      const offsetX = centerX - (currentAnchor.x || 0);
      const offsetY = centerY - (currentAnchor.y || 0);

      store.updateLayerTransform?.(id, {
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
      const layer = store.getLayerById(id);
      if (!layer) continue;

      const transform = layer.transform as any;
      const currentPos = transform?.position?.value ||
        transform?.position?.defaultValue || { x: 0, y: 0, z: 0 };

      store.updateLayerTransform?.(id, {
        position: { x: centerX, y: centerY, z: currentPos.z || 0 },
      });
    }

    console.log("[Lattice] Centered layer(s) in composition");
  }

  // ========================================================================
  // CREATE EFFECT LAYER (Ctrl+Alt+Y)
  // ========================================================================
  function createAdjustmentLayer() {
    store.addLayer("adjustment", "Effect Layer");
    console.log("[Lattice] Created effect layer");
  }

  // ========================================================================
  // CREATE CONTROL LAYER (Ctrl+Alt+Shift+Y)
  // ========================================================================
  function createNullLayer() {
    store.addLayer("null", "Control");
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

    const layer = store.getLayerById(selectedIds[0]);
    if (!layer) return;

    const data = layer.data as any;
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
      const layer = store.getLayerById(layerId);
      if (!layer) continue;

      const transform = layer.transform as any;
      if (transform) {
        const props = ["position", "rotation", "scale", "anchor", "opacity"];
        for (const propName of props) {
          const prop = transform[propName];
          if (prop?.keyframes && Array.isArray(prop.keyframes)) {
            for (const kf of prop.keyframes) {
              if (kf.id) keyframeIds.push(kf.id);
            }
          }
        }
      }

      const data = layer.data as any;
      if (data) {
        const checkForKeyframes = (obj: any) => {
          if (!obj || typeof obj !== "object") return;
          if (Array.isArray(obj.keyframes)) {
            for (const kf of obj.keyframes) {
              if (kf.id) keyframeIds.push(kf.id);
            }
          }
          for (const key of Object.keys(obj)) {
            if (typeof obj[key] === "object") checkForKeyframes(obj[key]);
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

    const firstLayer = store.getLayerById(selectedIds[0]);
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
      if (store.selectLayers) {
        store.selectLayers(matchingIds);
      } else {
        matchingIds.forEach((id) => store.selectLayer(id, true));
      }
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
            const layer = store.addLayer("image", layerName);
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
          const layer = store.addLayer("video", layerName);
          if (layer?.data) {
            const data = layer.data as unknown as Record<string, unknown>;
            data.src = url;
            data.originalFilename = file.name;
          }
        } else if (["gltf", "glb", "obj", "fbx"].includes(ext || "")) {
          // Import 3D model
          const url = URL.createObjectURL(file);
          const layerName = file.name.replace(/\.[^/.]+$/, "");
          const layer = store.addLayer("model", layerName);
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
              store.selectAllLayers();
            }
          } else {
            store.selectAllLayers();
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

      // Keyframe navigation (J/K)
      case "j":
        if (!e.ctrlKey && !e.metaKey) {
          e.preventDefault();
          goToPrevKeyframe();
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
          store.copySelectedLayers();
        }
        break;
      case "delete":
      case "backspace":
        if (store.selectedLayerIds.length > 0) {
          e.preventDefault();
          store.deleteSelectedLayers();
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
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          store.pasteLayers();
        } else if (!e.shiftKey) {
          currentTool.value = "select";
        }
        break;
      case "x":
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          store.cutSelectedLayers();
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
          store.duplicateSelectedLayers();
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
          audioStore.toggleAudioPlayback(store.currentFrame, store.fps);
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
          store.setFrame(0);
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
