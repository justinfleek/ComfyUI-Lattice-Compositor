/**
 * @composable useCurveEditorInteraction
 * @description Handles mouse/keyboard interactions for the Curve Editor.
 * Extracted from CurveEditor.vue to reduce file size.
 */

import { type Ref, ref } from "vue";
import type { AnimatableProperty, Keyframe, PropertyValue } from "@/types/project";
import type { CurveMargin, CurveViewState } from "./useCurveEditorCoords";

// Types
export interface DragTarget {
  type: "keyframe" | "inHandle" | "outHandle" | "pan" | "select";
  propId?: string;
  index?: number;
  startX?: number;
  startY?: number;
}

export interface SelectedKeyframe {
  propId: string;
  index: number;
  keyframe: Keyframe<PropertyValue>;
}

export interface SelectionBox {
  x: number;
  y: number;
  width: number;
  height: number;
}

export interface CurveEditorInteractionOptions {
  // Canvas refs
  canvasRef: Ref<HTMLCanvasElement | null>;
  canvasWidth: Ref<number>;
  canvasHeight: Ref<number>;

  // View state
  viewState: CurveViewState;
  margin: CurveMargin;

  // Properties
  visibleProperties: Ref<AnimatableProperty<PropertyValue>[]>;
  animatableProperties: Ref<AnimatableProperty<PropertyValue>[]>;

  // Coordinate transforms
  frameToScreenX: (frame: number) => number;
  screenXToFrame: (screenX: number) => number;
  valueToScreenY: (value: number) => number;
  screenYToValue: (screenY: number) => number;
  getKeyframeScreenX: (kf: Keyframe<PropertyValue>) => number;
  getKeyframeScreenY: (
    prop: AnimatableProperty<PropertyValue>,
    kf: Keyframe<PropertyValue>,
  ) => number;
  getNumericValue: (value: PropertyValue) => number;
  getPropertyPath: (prop: AnimatableProperty<PropertyValue>) => string;

  // Callbacks
  drawGraph: () => void;
  store: ReturnType<typeof import("@/stores/compositorStore").useCompositorStore>;
  keyframeStore: ReturnType<typeof import("@/stores/keyframeStore").useKeyframeStore>;
}

export function useCurveEditorInteraction(
  options: CurveEditorInteractionOptions,
) {
  const {
    canvasRef,
    canvasWidth,
    canvasHeight,
    viewState,
    margin,
    visibleProperties,
    animatableProperties,
    frameToScreenX,
    screenXToFrame,
    valueToScreenY,
    screenYToValue,
    getKeyframeScreenX,
    getKeyframeScreenY,
    getNumericValue,
    getPropertyPath,
    drawGraph,
    store,
    keyframeStore,
  } = options;

  // State
  const dragTarget = ref<DragTarget | null>(null);
  const selectedKeyframes = ref<SelectedKeyframe[]>([]);
  const hoveredKeyframe = ref<{ propId: string; index: number } | null>(null);
  const selectionBox = ref<SelectionBox | null>(null);
  const contextMenu = ref<{ x: number; y: number } | null>(null);
  const clipboard = ref<Keyframe<PropertyValue>[] | null>(null);
  const snapEnabled = ref(false);
  const autoSelectNearby = ref(true);

  // Helper functions
  function isKeyframeSelected(propId: string, index: number): boolean {
    return selectedKeyframes.value.some(
      (sk) => sk.propId === propId && sk.index === index,
    );
  }

  function updateHoveredKeyframe(x: number, y: number): void {
    hoveredKeyframe.value = null;

    for (const prop of visibleProperties.value) {
      for (let i = 0; i < prop.keyframes.length; i++) {
        const kf = prop.keyframes[i];
        const kfX = getKeyframeScreenX(kf);
        const kfY = getKeyframeScreenY(prop, kf);

        const dist = Math.sqrt((x - kfX) ** 2 + (y - kfY) ** 2);
        if (dist < 10) {
          hoveredKeyframe.value = { propId: prop.id, index: i };
          return;
        }
      }
    }
  }

  // Mouse handlers
  function handleMouseDown(event: MouseEvent): void {
    const rect = canvasRef.value?.getBoundingClientRect();
    if (!rect) return;

    const x = event.clientX - rect.left;
    const y = event.clientY - rect.top;

    if (event.button === 1 || (event.button === 0 && event.altKey)) {
      // Middle click or Alt+left click: pan
      dragTarget.value = { type: "pan", startX: x, startY: y };
    } else if (event.button === 0) {
      // Left click: selection box
      if (!event.shiftKey) {
        selectedKeyframes.value = [];
      }
      selectionBox.value = { x, y, width: 0, height: 0 };
      dragTarget.value = { type: "select", startX: x, startY: y };
    }
  }

  function handleMouseMove(event: MouseEvent): void {
    const rect = canvasRef.value?.getBoundingClientRect();
    if (!rect) return;

    const x = event.clientX - rect.left;
    const y = event.clientY - rect.top;

    // Update hovered keyframe
    updateHoveredKeyframe(x, y);

    if (!dragTarget.value) return;

    if (dragTarget.value.type === "pan") {
      const dx = x - (dragTarget.value.startX ?? 0);
      const dy = y - (dragTarget.value.startY ?? 0);

      const graphWidth = canvasWidth.value - margin.left - margin.right;
      const graphHeight = canvasHeight.value - margin.top - margin.bottom;

      const frameShift =
        (-dx / graphWidth) * (viewState.frameEnd - viewState.frameStart);
      const valueShift =
        (dy / graphHeight) * (viewState.valueMax - viewState.valueMin);

      viewState.frameStart += frameShift;
      viewState.frameEnd += frameShift;
      viewState.valueMin += valueShift;
      viewState.valueMax += valueShift;

      dragTarget.value.startX = x;
      dragTarget.value.startY = y;
      drawGraph();
    } else if (dragTarget.value.type === "select" && selectionBox.value) {
      const startX = dragTarget.value.startX ?? 0;
      const startY = dragTarget.value.startY ?? 0;

      selectionBox.value = {
        x: Math.min(x, startX),
        y: Math.min(y, startY),
        width: Math.abs(x - startX),
        height: Math.abs(y - startY),
      };
    } else if (dragTarget.value.type === "keyframe") {
      moveSelectedKeyframes(x, y);
    } else if (
      dragTarget.value.type === "outHandle" ||
      dragTarget.value.type === "inHandle"
    ) {
      moveHandle(x, y);
    }
  }

  function handleMouseUp(): void {
    if (dragTarget.value?.type === "select" && selectionBox.value) {
      selectKeyframesInBox();
    }

    dragTarget.value = null;
    selectionBox.value = null;
  }

  function handleWheel(event: WheelEvent): void {
    event.preventDefault();

    const rect = canvasRef.value?.getBoundingClientRect();
    if (!rect) return;

    const x = event.clientX - rect.left;
    const zoomFactor = event.deltaY > 0 ? 1.1 : 0.9;

    // Zoom around cursor position
    const frameAtCursor = screenXToFrame(x);

    const newFrameStart =
      frameAtCursor - (frameAtCursor - viewState.frameStart) * zoomFactor;
    const newFrameEnd =
      frameAtCursor + (viewState.frameEnd - frameAtCursor) * zoomFactor;

    if (event.shiftKey) {
      // Zoom time only
      viewState.frameStart = newFrameStart;
      viewState.frameEnd = newFrameEnd;
    } else {
      // Zoom both axes
      viewState.frameStart = newFrameStart;
      viewState.frameEnd = newFrameEnd;

      const y = event.clientY - rect.top;
      const valueAtCursor = screenYToValue(y);
      viewState.valueMin =
        valueAtCursor - (valueAtCursor - viewState.valueMin) * zoomFactor;
      viewState.valueMax =
        valueAtCursor + (viewState.valueMax - valueAtCursor) * zoomFactor;
    }

    drawGraph();
  }

  // Keyframe interaction
  function onKeyframeMouseDown(
    propId: string,
    index: number,
    event: MouseEvent,
  ): void {
    const prop = animatableProperties.value.find((p) => p.id === propId);
    if (!prop) return;

    const kf = prop.keyframes[index];

    if (!event.shiftKey) {
      selectedKeyframes.value = [];
    }

    if (!isKeyframeSelected(propId, index)) {
      selectedKeyframes.value.push({ propId, index, keyframe: kf });
    }

    dragTarget.value = { type: "keyframe", propId, index };
  }

  function selectKeyframesInBox(): void {
    if (!selectionBox.value) return;

    const box = selectionBox.value;

    for (const prop of visibleProperties.value) {
      for (let i = 0; i < prop.keyframes.length; i++) {
        const kf = prop.keyframes[i];
        const x = getKeyframeScreenX(kf);
        const y = getKeyframeScreenY(prop, kf);

        if (
          x >= box.x &&
          x <= box.x + box.width &&
          y >= box.y &&
          y <= box.y + box.height
        ) {
          if (!isKeyframeSelected(prop.id, i)) {
            selectedKeyframes.value.push({
              propId: prop.id,
              index: i,
              keyframe: kf,
            });
          }
        }
      }
    }
  }

  function moveSelectedKeyframes(screenX: number, screenY: number): void {
    const newFrame = Math.round(screenXToFrame(screenX));
    const newValue = screenYToValue(screenY);

    const layer = store.selectedLayer;
    if (!layer) return;

    // For now, just move the first selected keyframe
    if (selectedKeyframes.value.length > 0) {
      const sk = selectedKeyframes.value[0];
      const prop = animatableProperties.value.find((p) => p.id === sk.propId);
      if (!prop) return;

      const frame = Math.max(0, Math.min(store.frameCount - 1, newFrame));
      const _value =
        typeof sk.keyframe.value === "number" ? newValue : sk.keyframe.value;

      // Get property path from property name
      const propertyPath = getPropertyPath(prop);

      // Call store method to persist the change
      keyframeStore.updateKeyframe(store, layer.id, propertyPath, sk.keyframe.id, {
        frame,
        value: typeof sk.keyframe.value === "number" ? newValue : undefined,
      });

      // Update local reference
      sk.keyframe.frame = frame;
      if (typeof sk.keyframe.value === "number") {
        sk.keyframe.value = newValue;
      }
    }

    drawGraph();
  }

  // Handle dragging
  function startDragHandle(
    type: "inHandle" | "outHandle",
    propId: string,
    index: number,
    _event: MouseEvent,
  ): void {
    dragTarget.value = { type, propId, index };
  }

  function moveHandle(screenX: number, screenY: number): void {
    if (!dragTarget.value || !dragTarget.value.propId) return;

    const layer = store.selectedLayer;
    if (!layer) return;

    const prop = animatableProperties.value.find(
      (p) => p.id === dragTarget.value?.propId,
    );
    if (!prop) return;

    const kfIndex = dragTarget.value.index!;
    const kf = prop.keyframes[kfIndex];
    if (!kf) return;

    const handleFrame = screenXToFrame(screenX);
    const handleValue = screenYToValue(screenY);
    const propertyPath = getPropertyPath(prop);

    if (dragTarget.value.type === "outHandle") {
      const nextKf = prop.keyframes[kfIndex + 1];

      // Calculate frame offset (positive = forward from keyframe)
      let frameOffset = handleFrame - kf.frame;
      // Constrain: cannot go past next keyframe or before current
      if (nextKf) {
        frameOffset = Math.max(
          0,
          Math.min(nextKf.frame - kf.frame, frameOffset),
        );
      } else {
        frameOffset = Math.max(0, frameOffset);
      }

      // Calculate value offset
      const valueOffset = handleValue - getNumericValue(kf.value);

      const newHandle = {
        frame: frameOffset,
        value: valueOffset,
        enabled: true,
      };

      // Call store method to persist
      keyframeStore.setKeyframeHandle(store, layer.id, propertyPath, kf.id, "out", newHandle);

      // Update local reference
      kf.outHandle = newHandle;
      kf.interpolation = "bezier";
    } else if (dragTarget.value.type === "inHandle") {
      const prevKf = prop.keyframes[kfIndex - 1];

      // Calculate frame offset (typically negative = backward from keyframe)
      let frameOffset = handleFrame - kf.frame;
      // Constrain: cannot go before previous keyframe or after current
      if (prevKf) {
        frameOffset = Math.max(
          prevKf.frame - kf.frame,
          Math.min(0, frameOffset),
        );
      } else {
        frameOffset = Math.min(0, frameOffset);
      }

      // Calculate value offset
      const valueOffset = handleValue - getNumericValue(kf.value);

      const newHandle = {
        frame: frameOffset,
        value: valueOffset,
        enabled: true,
      };

      // Call store method to persist
      keyframeStore.setKeyframeHandle(store, layer.id, propertyPath, kf.id, "in", newHandle);

      // Update local reference
      kf.inHandle = newHandle;
      kf.interpolation = "bezier";
    }

    drawGraph();
  }

  // Context menu actions
  function showContextMenu(event: MouseEvent): void {
    contextMenu.value = { x: event.offsetX, y: event.offsetY };
  }

  function hideContextMenu(): void {
    contextMenu.value = null;
  }

  function addKeyframeAtPosition(): void {
    if (!contextMenu.value) return;

    const layer = store.selectedLayer;
    if (!layer) return;

    const frame = Math.round(screenXToFrame(contextMenu.value.x));
    const value = screenYToValue(contextMenu.value.y);

    // Add to first visible property
    if (visibleProperties.value.length > 0) {
      const prop = visibleProperties.value[0];
      const propertyPath = getPropertyPath(prop);
      keyframeStore.addKeyframe(store, layer.id, propertyPath, value, frame);
    }

    contextMenu.value = null;
    drawGraph();
  }

  function deleteSelectedKeyframes(): void {
    const layer = store.selectedLayer;
    if (!layer) return;

    for (const sk of selectedKeyframes.value) {
      const prop = animatableProperties.value.find((p) => p.id === sk.propId);
      if (prop) {
        const propertyPath = getPropertyPath(prop);
        keyframeStore.removeKeyframe(store, layer.id, propertyPath, sk.keyframe.id);
      }
    }

    selectedKeyframes.value = [];
    contextMenu.value = null;
    drawGraph();
  }

  function copyKeyframes(): void {
    clipboard.value = selectedKeyframes.value.map((sk) => ({ ...sk.keyframe }));
    contextMenu.value = null;
  }

  function pasteKeyframes(): void {
    if (!clipboard.value) return;

    const layer = store.selectedLayer;
    if (!layer) return;

    // Paste at current frame, offset from first copied keyframe
    const currentFrame = store.currentFrame;
    const offsetFrame =
      clipboard.value.length > 0 ? clipboard.value[0].frame : 0;

    for (const kf of clipboard.value) {
      const newFrame = currentFrame + (kf.frame - offsetFrame);
      // Find property by ID - for now, paste to first visible property
      if (visibleProperties.value.length > 0) {
        const prop = visibleProperties.value[0];
        const propertyPath = getPropertyPath(prop);

        const newKeyframe = keyframeStore.addKeyframe(
          store,
          layer.id,
          propertyPath,
          kf.value,
          newFrame,
        );

        if (newKeyframe) {
          if (kf.interpolation !== "linear") {
            keyframeStore.setKeyframeInterpolation(
              store,
              layer.id,
              propertyPath,
              newKeyframe.id,
              kf.interpolation,
            );
          }
          if (kf.inHandle?.enabled) {
            keyframeStore.setKeyframeHandle(
              store,
              layer.id,
              propertyPath,
              newKeyframe.id,
              "in",
              kf.inHandle,
            );
          }
          if (kf.outHandle?.enabled) {
            keyframeStore.setKeyframeHandle(
              store,
              layer.id,
              propertyPath,
              newKeyframe.id,
              "out",
              kf.outHandle,
            );
          }
        }
      }
    }

    contextMenu.value = null;
    drawGraph();
  }

  function selectAllKeyframes(): void {
    selectedKeyframes.value = [];
    for (const prop of visibleProperties.value) {
      for (let i = 0; i < prop.keyframes.length; i++) {
        selectedKeyframes.value.push({
          propId: prop.id,
          index: i,
          keyframe: prop.keyframes[i],
        });
      }
    }
  }

  function invertSelection(): void {
    const newSelection: SelectedKeyframe[] = [];

    for (const prop of visibleProperties.value) {
      for (let i = 0; i < prop.keyframes.length; i++) {
        if (!isKeyframeSelected(prop.id, i)) {
          newSelection.push({
            propId: prop.id,
            index: i,
            keyframe: prop.keyframes[i],
          });
        }
      }
    }

    selectedKeyframes.value = newSelection;
  }

  // Keyboard handler
  function handleKeyDown(event: KeyboardEvent): void {
    if (event.key === "Delete" || event.key === "Backspace") {
      deleteSelectedKeyframes();
    } else if (event.key === "a" && (event.ctrlKey || event.metaKey)) {
      event.preventDefault();
      selectAllKeyframes();
    } else if (event.key === "c" && (event.ctrlKey || event.metaKey)) {
      copyKeyframes();
    } else if (event.key === "v" && (event.ctrlKey || event.metaKey)) {
      pasteKeyframes();
    } else if (event.key === "i" && (event.ctrlKey || event.metaKey)) {
      event.preventDefault();
      invertSelection();
    }
  }

  return {
    // State
    dragTarget,
    selectedKeyframes,
    hoveredKeyframe,
    selectionBox,
    contextMenu,
    clipboard,
    snapEnabled,
    autoSelectNearby,

    // Helpers
    isKeyframeSelected,

    // Mouse handlers
    handleMouseDown,
    handleMouseMove,
    handleMouseUp,
    handleWheel,
    onKeyframeMouseDown,
    startDragHandle,

    // Context menu
    showContextMenu,
    hideContextMenu,
    addKeyframeAtPosition,
    deleteSelectedKeyframes,
    copyKeyframes,
    pasteKeyframes,
    selectAllKeyframes,
    invertSelection,

    // Keyboard
    handleKeyDown,
  };
}
