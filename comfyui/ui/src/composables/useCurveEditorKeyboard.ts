/**
 * Curve Editor Keyboard Shortcuts
 *
 * Handles keyboard shortcuts for the curve editor including
 * navigation, easing presets, and keyframe manipulation.
 */

import type { Ref } from "vue";
import type { AnimatableProperty } from "@/types/project";
import type { CurveViewState } from "./useCurveEditorCoords";
import {
  fitSelectionToView,
  fitToView,
  type SelectedKeyframe,
  zoomIn,
  zoomOut,
} from "./useCurveEditorView";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                   // keyframe // navigation
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Navigate to previous keyframe
 */
export function goToPreviousKeyframe(
  currentFrame: number,
  visibleProperties: AnimatableProperty<any>[],
  setFrame: (frame: number) => void,
): void {
  const allKeyframes: number[] = [];

  for (const prop of visibleProperties) {
    for (const kf of prop.keyframes) {
      if (!allKeyframes.includes(kf.frame)) {
        allKeyframes.push(kf.frame);
      }
    }
  }

  allKeyframes.sort((a, b) => a - b);
  const prev = [...allKeyframes].reverse().find((f) => f < currentFrame);
  if (prev !== undefined) {
    setFrame(prev);
  }
}

/**
 * Navigate to next keyframe
 */
export function goToNextKeyframe(
  currentFrame: number,
  visibleProperties: AnimatableProperty<any>[],
  setFrame: (frame: number) => void,
): void {
  const allKeyframes: number[] = [];

  for (const prop of visibleProperties) {
    for (const kf of prop.keyframes) {
      if (!allKeyframes.includes(kf.frame)) {
        allKeyframes.push(kf.frame);
      }
    }
  }

  allKeyframes.sort((a, b) => a - b);
  const next = allKeyframes.find((f) => f > currentFrame);
  if (next !== undefined) {
    setFrame(next);
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                             // easy // ease
// ═══════════════════════════════════════════════════════════════════════════

export interface EasyEaseParams {
  selectedKeyframes: SelectedKeyframe[];
  animatableProperties: AnimatableProperty<any>[];
  direction: "both" | "in" | "out";
}

/**
 * Apply easy ease to selected keyframes
 */
export function applyEasyEase(params: EasyEaseParams): void {
  const { selectedKeyframes, animatableProperties, direction } = params;

  for (const sk of selectedKeyframes) {
    const prop = animatableProperties.find((p) => p.id === sk.propId);
    if (!prop) continue;

    const kf = sk.keyframe;
    const kfIndex = sk.index;

    // Get adjacent keyframes for duration calculation
    const prevKf = kfIndex > 0 ? prop.keyframes[kfIndex - 1] : null;
    const nextKf =
      kfIndex < prop.keyframes.length - 1 ? prop.keyframes[kfIndex + 1] : null;

    // Calculate segment durations
    const inDuration = prevKf ? kf.frame - prevKf.frame : 10;
    const outDuration = nextKf ? nextKf.frame - kf.frame : 10;

    // 33.33% influence
    const influence = 0.3333;

    if (direction === "both" || direction === "in") {
      // Easy ease in - deceleration
      kf.inHandle = {
        frame: -inDuration * influence,
        value: 0, // 0 velocity at keyframe
        enabled: true,
      };
    }

    if (direction === "both" || direction === "out") {
      // Easy ease out - acceleration
      kf.outHandle = {
        frame: outDuration * influence,
        value: 0, // 0 velocity at keyframe
        enabled: true,
      };
    }

    kf.interpolation = "bezier";
    kf.controlMode = "smooth";
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // keyboard // handler
// ═══════════════════════════════════════════════════════════════════════════

export interface CurveEditorKeyboardOptions {
  viewState: CurveViewState;
  selectedKeyframes: Ref<SelectedKeyframe[]>;
  visibleProperties: Ref<AnimatableProperty<any>[]>;
  animatableProperties: Ref<AnimatableProperty<any>[]>;
  currentFrame: number;
  setFrame: (frame: number) => void;
  deleteSelectedKeyframes: () => void;
  drawGraph: () => void;
}

/**
 * Create keyboard handler for curve editor
 */
export function createKeyboardHandler(options: CurveEditorKeyboardOptions) {
  const {
    viewState,
    selectedKeyframes,
    visibleProperties,
    animatableProperties,
    currentFrame,
    setFrame,
    deleteSelectedKeyframes,
    drawGraph,
  } = options;

  return function handleKeyDown(event: KeyboardEvent): void {
    // F9 Easy Ease
    if (event.key === "F9") {
      event.preventDefault();
      let direction: "both" | "in" | "out" = "both";
      if (event.ctrlKey && event.shiftKey) {
        direction = "out"; // Ctrl+Shift+F9
      } else if (event.shiftKey) {
        direction = "in"; // Shift+F9
      }
      applyEasyEase({
        selectedKeyframes: selectedKeyframes.value,
        animatableProperties: animatableProperties.value,
        direction,
      });
      drawGraph();
      return;
    }

    // J/K navigation
    if (event.key.toLowerCase() === "j") {
      event.preventDefault();
      goToPreviousKeyframe(currentFrame, visibleProperties.value, setFrame);
      return;
    }
    if (event.key.toLowerCase() === "k") {
      event.preventDefault();
      goToNextKeyframe(currentFrame, visibleProperties.value, setFrame);
      return;
    }

    // Delete selected keyframes
    if (event.key === "Delete" || event.key === "Backspace") {
      event.preventDefault();
      deleteSelectedKeyframes();
      return;
    }

    // F = Fit to view
    if (event.key.toLowerCase() === "f" && !event.ctrlKey) {
      event.preventDefault();
      if (event.shiftKey) {
        fitToView(viewState, visibleProperties.value);
      } else if (selectedKeyframes.value.length > 0) {
        fitSelectionToView(
          viewState,
          selectedKeyframes.value,
          visibleProperties.value,
        );
      } else {
        fitToView(viewState, visibleProperties.value);
      }
      drawGraph();
      return;
    }

    // Zoom in/out with = / -
    if (event.key === "=" || event.key === "+") {
      event.preventDefault();
      zoomIn(viewState);
      drawGraph();
      return;
    }
    if (event.key === "-" || event.key === "_") {
      event.preventDefault();
      zoomOut(viewState);
      drawGraph();
      return;
    }
  };
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                     // composable // export
// ═══════════════════════════════════════════════════════════════════════════

export function useCurveEditorKeyboard(options: CurveEditorKeyboardOptions) {
  const handleKeyDown = createKeyboardHandler(options);

  return {
    handleKeyDown,
    goToPreviousKeyframe: () =>
      goToPreviousKeyframe(
        options.currentFrame,
        options.visibleProperties.value,
        options.setFrame,
      ),
    goToNextKeyframe: () =>
      goToNextKeyframe(
        options.currentFrame,
        options.visibleProperties.value,
        options.setFrame,
      ),
    applyEasyEase: (direction: "both" | "in" | "out" = "both") => {
      applyEasyEase({
        selectedKeyframes: options.selectedKeyframes.value,
        animatableProperties: options.animatableProperties.value,
        direction,
      });
      options.drawGraph();
    },
  };
}
