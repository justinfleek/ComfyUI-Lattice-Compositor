/**
 * Keyframe Interpolation Operations
 *
 * Interpolation type, bezier handles, and control mode operations.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import type { BezierHandle, InterpolationType } from "@/types/project";
import { findPropertyByPath } from "./helpers";
import { useProjectStore } from "../projectStore";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                 // keyframe // interpolation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Set keyframe interpolation type.
 */
export function setKeyframeInterpolation(
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  interpolation: InterpolationType,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find((kf) => kf.id === keyframeId);
  if (!keyframe) return;

  keyframe.interpolation = interpolation;
  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
}

/**
 * Set keyframe bezier handle.
 */
export function setKeyframeHandle(
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  handleType: "in" | "out",
  handle: BezierHandle,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find((kf) => kf.id === keyframeId);
  if (!keyframe) return;

  if (handleType === "in") {
    keyframe.inHandle = { ...handle };
  } else {
    keyframe.outHandle = { ...handle };
  }

  // Enable bezier interpolation when handles are modified
  if (handle.enabled && keyframe.interpolation === "linear") {
    keyframe.interpolation = "bezier";
  }

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
}

/**
 * Set keyframe control mode (smooth, corner, etc.)
 */
export function setKeyframeControlMode(
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  controlMode: "smooth" | "corner" | "symmetric",
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find((kf) => kf.id === keyframeId);
  if (!keyframe) return;

  keyframe.controlMode = controlMode;
  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
}

// ════════════════════════════════════════════════════════════════════════════
//                                         // handle // with // control // mode
// ════════════════════════════════════════════════════════════════════════════

/**
 * Set keyframe bezier handle with control mode awareness.
 *
 * Control modes:
 * - 'symmetric': Both handles have same length and opposite direction
 * - 'smooth': Both handles maintain angle but can have different lengths
 * - 'corner': Handles are independent (broken)
 *
 * @param breakHandle - If true, sets controlMode to 'corner' (Ctrl+drag behavior)
 */
export function setKeyframeHandleWithMode(
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  handleType: "in" | "out",
  handle: BezierHandle,
  breakHandle: boolean = false,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find((kf) => kf.id === keyframeId);
  if (!keyframe) return;

  // If breaking handle (Ctrl+drag), set to corner mode
  if (breakHandle) {
    keyframe.controlMode = "corner";
    if (handleType === "in") {
      keyframe.inHandle = { ...handle };
    } else {
      keyframe.outHandle = { ...handle };
    }
  } else {
    // Respect existing control mode
    // Explicit check: controlMode is ControlMode (required field, but defensive check for runtime safety)
    const mode = (typeof keyframe.controlMode === "string" && (keyframe.controlMode === "symmetric" || keyframe.controlMode === "smooth" || keyframe.controlMode === "corner")) ? keyframe.controlMode : "smooth";

    if (handleType === "in") {
      keyframe.inHandle = { ...handle };

      if (mode === "symmetric") {
        // Mirror both angle and length to outHandle
        keyframe.outHandle = {
          frame: -handle.frame,
          value: -handle.value,
          enabled: handle.enabled,
        };
      } else if (mode === "smooth") {
        // Mirror angle, keep outHandle length
        const inLength = Math.sqrt(
          handle.frame * handle.frame + handle.value * handle.value,
        );
        const outLength = Math.sqrt(
          keyframe.outHandle.frame * keyframe.outHandle.frame +
            keyframe.outHandle.value * keyframe.outHandle.value,
        );

        if (inLength > 0) {
          const scale = outLength / inLength;
          keyframe.outHandle = {
            frame: -handle.frame * scale,
            value: -handle.value * scale,
            enabled: keyframe.outHandle.enabled,
          };
        }
      }
      // corner mode: no adjustment to other handle
    } else {
      keyframe.outHandle = { ...handle };

      if (mode === "symmetric") {
        // Mirror both angle and length to inHandle
        keyframe.inHandle = {
          frame: -handle.frame,
          value: -handle.value,
          enabled: handle.enabled,
        };
      } else if (mode === "smooth") {
        // Mirror angle, keep inHandle length
        const outLength = Math.sqrt(
          handle.frame * handle.frame + handle.value * handle.value,
        );
        const inLength = Math.sqrt(
          keyframe.inHandle.frame * keyframe.inHandle.frame +
            keyframe.inHandle.value * keyframe.inHandle.value,
        );

        if (outLength > 0) {
          const scale = inLength / outLength;
          keyframe.inHandle = {
            frame: -handle.frame * scale,
            value: -handle.value * scale,
            enabled: keyframe.inHandle.enabled,
          };
        }
      }
      // corner mode: no adjustment to other handle
    }
  }

  // Enable bezier interpolation when handles are modified
  if (handle.enabled && keyframe.interpolation === "linear") {
    keyframe.interpolation = "bezier";
  }

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
}
