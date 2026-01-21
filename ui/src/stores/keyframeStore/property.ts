/**
 * Property Animation State Operations
 *
 * Operations for property value and animation state management.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import { isFiniteNumber } from "@/utils/typeGuards";
import type { Keyframe, PropertyValue } from "@/types/project";
import { findPropertyByPath } from "./helpers";
import { useProjectStore } from "../projectStore";
import { useAnimationStore } from "../animationStore";
import { useLayerStore } from "../layerStore";

// ============================================================================
// PROPERTY ANIMATION STATE
// ============================================================================

/**
 * Set a property's value (for direct editing in timeline).
 */
export function setPropertyValue(
  layerId: string,
  propertyPath: string,
  value: PropertyValue,
): void {
  const projectStore = useProjectStore();
  const animationStore = useAnimationStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  property.value = value;

  // If animated and at a keyframe, update that keyframe's value too
  if (property.animated && property.keyframes.length > 0) {
    const currentFrame = animationStore.currentFrame;
    const existingKf = property.keyframes.find(
      (kf) => kf.frame === currentFrame,
    );
    if (existingKf) {
      existingKf.value = value;
    }
  }

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
}

/**
 * Set a property's animated state.
 */
export function setPropertyAnimated(
  layerId: string,
  propertyPath: string,
  animated: boolean,
  addKeyframeCallback?: () => void,
): void {
  const projectStore = useProjectStore();
  const animationStore = useAnimationStore();
  const layerStore = useLayerStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  property.animated = animated;

  // If enabling animation and no keyframes, add one at current frame
  if (animated && property.keyframes.length === 0) {
    if (addKeyframeCallback) {
      addKeyframeCallback();
    } else {
      // Direct implementation when no callback provided
      const comp = projectStore.getActiveComp();
      // Type proof: currentFrame ∈ ℕ ∪ {undefined} → ℕ
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const currentFrameValue = (comp != null && typeof comp === "object" && "currentFrame" in comp && typeof comp.currentFrame === "number") ? comp.currentFrame : undefined;
      const frame = isFiniteNumber(currentFrameValue) && Number.isInteger(currentFrameValue) && currentFrameValue >= 0 ? currentFrameValue : 0;

      const keyframe: Keyframe<PropertyValue> = {
        id: `kf_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
        frame,
        value: property.value,
        interpolation: "linear",
        inHandle: { frame: 0, value: 0, enabled: false },
        outHandle: { frame: 0, value: 0, enabled: false },
        controlMode: "smooth",
      };

      property.keyframes.push(keyframe);
    }
  }

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
}
