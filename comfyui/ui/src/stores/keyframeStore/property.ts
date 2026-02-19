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
import { generateKeyframeId } from "@/utils/uuid5";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                           // property // animation // state
// ═══════════════════════════════════════════════════════════════════════════

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
      // Regenerate keyframe ID based on new value for determinism
      // Same layer/property/frame but different value should produce different ID
      // Explicit check: value is PropertyValue (never null/undefined per type system)
      const valueStr = typeof value === "object" && value !== null && "x" in value && "y" in value
        ? `${(value as { x: number; y: number }).x},${(value as { x: number; y: number }).y}${"z" in value ? `,${(value as { x: number; y: number; z?: number }).z}` : ""}`
        : String(value);
      existingKf.id = generateKeyframeId(layerId, propertyPath, existingKf.frame, valueStr);
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

      // Deterministic ID generation: same layer/property/frame/value always produces same ID
      const valueStr = typeof property.value === "object" && property.value !== null && "x" in property.value && "y" in property.value
        ? `${(property.value as { x: number; y: number }).x},${(property.value as { x: number; y: number }).y}${"z" in property.value ? `,${(property.value as { x: number; y: number; z?: number }).z}` : ""}`
        : String(property.value);
      const keyframe: Keyframe<PropertyValue> = {
        id: generateKeyframeId(layerId, propertyPath, frame, valueStr),
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
