/**
 * Keyframe Clipboard Operations
 *
 * Copy, paste, and clipboard state management for keyframes.
 */

import { toRaw } from "vue";
import { markLayerDirty } from "@/services/layerEvaluationCache";
import type {
  AnimatableProperty,
  ClipboardKeyframe,
  Keyframe,
  PropertyValue,
} from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { findPropertyByPath } from "./helpers";
import type { ClipboardKeyframeStoreAccess, KeyframeState } from "./types";

// ============================================================================
// KEYFRAME CLIPBOARD (COPY/PASTE)
// ============================================================================

/**
 * Copy keyframes to clipboard.
 *
 * @param store - The compositor store with clipboard access
 * @param keyframeSelections - Array of keyframe selections with layerId, propertyPath, and keyframeId
 * @returns Number of keyframes copied
 */
export function copyKeyframes(
  store: ClipboardKeyframeStoreAccess,
  keyframeSelections: Array<{
    layerId: string;
    propertyPath: string;
    keyframeId: string;
  }>,
): number {
  if (keyframeSelections.length === 0) {
    storeLogger.debug("copyKeyframes: No keyframes selected");
    return 0;
  }

  // Group keyframes by layer and property
  const groupedByProperty = new Map<
    string,
    { layerId: string; propertyPath: string; keyframeIds: string[] }
  >();

  for (const sel of keyframeSelections) {
    const key = `${sel.layerId}:${sel.propertyPath}`;
    if (!groupedByProperty.has(key)) {
      groupedByProperty.set(key, {
        layerId: sel.layerId,
        propertyPath: sel.propertyPath,
        keyframeIds: [],
      });
    }
    groupedByProperty.get(key)?.keyframeIds.push(sel.keyframeId);
  }

  // Find the earliest frame among all selected keyframes (for relative timing)
  let earliestFrame = Infinity;
  const clipboardEntries: ClipboardKeyframe[] = [];

  for (const [, group] of groupedByProperty) {
    const layer = store
      .getActiveCompLayers()
      .find((l) => l.id === group.layerId);
    if (!layer) continue;

    const property = findPropertyByPath(layer, group.propertyPath);
    if (!property?.keyframes) continue;

    const selectedKeyframes = property.keyframes.filter((kf) =>
      group.keyframeIds.includes(kf.id),
    );
    for (const kf of selectedKeyframes) {
      if (kf.frame < earliestFrame) {
        earliestFrame = kf.frame;
      }
    }
  }

  if (earliestFrame === Infinity) {
    storeLogger.debug("copyKeyframes: No valid keyframes found");
    return 0;
  }

  // Build clipboard entries with relative frame offsets
  for (const [, group] of groupedByProperty) {
    const layer = store
      .getActiveCompLayers()
      .find((l) => l.id === group.layerId);
    if (!layer) continue;

    const property = findPropertyByPath(layer, group.propertyPath);
    if (!property?.keyframes) continue;

    const selectedKeyframes = property.keyframes.filter((kf) =>
      group.keyframeIds.includes(kf.id),
    );
    if (selectedKeyframes.length === 0) continue;

    // Deep clone keyframes and store relative frame offsets
    // Use toRaw to handle Vue reactive proxies before cloning
    const clonedKeyframes: Keyframe<PropertyValue>[] = selectedKeyframes.map(
      (kf) => ({
        ...structuredClone(toRaw(kf)),
        // Store frame as offset from earliest keyframe
        frame: kf.frame - earliestFrame,
      }),
    );

    clipboardEntries.push({
      layerId: group.layerId,
      propertyPath: group.propertyPath,
      keyframes: clonedKeyframes,
    });
  }

  // Store in clipboard
  store.clipboard.keyframes = clipboardEntries;

  const totalCopied = clipboardEntries.reduce(
    (sum, entry) => sum + entry.keyframes.length,
    0,
  );
  storeLogger.debug(`Copied ${totalCopied} keyframe(s) to clipboard`);

  return totalCopied;
}

/**
 * Paste keyframes from clipboard to a target property.
 *
 * @param store - The compositor store with clipboard access
 * @param targetLayerId - Target layer ID to paste to
 * @param targetPropertyPath - Target property path (optional - uses original if matching type)
 * @returns Array of newly created keyframes
 */
export function pasteKeyframes(
  store: ClipboardKeyframeStoreAccess,
  targetLayerId: string,
  targetPropertyPath?: string,
): Keyframe<PropertyValue>[] {
  if (store.clipboard.keyframes.length === 0) {
    storeLogger.debug("pasteKeyframes: No keyframes in clipboard");
    return [];
  }

  const targetLayer = store
    .getActiveCompLayers()
    .find((l) => l.id === targetLayerId);
  if (!targetLayer) {
    storeLogger.debug("pasteKeyframes: Target layer not found");
    return [];
  }

  const currentFrame = store.currentFrame;
  const createdKeyframes: Keyframe<PropertyValue>[] = [];

  for (const clipboardEntry of store.clipboard.keyframes) {
    // Determine which property to paste to
    const propPath = targetPropertyPath || clipboardEntry.propertyPath;
    const property = findPropertyByPath(targetLayer, propPath) as
      | AnimatableProperty<PropertyValue>
      | undefined;

    if (!property) {
      storeLogger.debug(
        `pasteKeyframes: Property ${propPath} not found on target layer`,
      );
      continue;
    }

    // Enable animation if not already
    property.animated = true;

    // Paste each keyframe with new IDs and adjusted frames
    for (const clipKf of clipboardEntry.keyframes) {
      const newFrame = currentFrame + clipKf.frame; // Apply offset from current frame

      // Create new keyframe with fresh ID
      // Use toRaw to handle Vue reactive proxies before cloning
      const newKeyframe: Keyframe<PropertyValue> = {
        ...structuredClone(toRaw(clipKf)),
        id: `kf_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
        frame: newFrame,
      };

      // Check for existing keyframe at this frame
      const existingIndex = property.keyframes.findIndex(
        (k) => k.frame === newFrame,
      );
      if (existingIndex >= 0) {
        // Replace existing keyframe
        property.keyframes[existingIndex] = newKeyframe;
      } else {
        // Add new keyframe
        property.keyframes.push(newKeyframe);
      }

      createdKeyframes.push(newKeyframe);
    }

    // Re-sort keyframes by frame
    property.keyframes.sort((a, b) => a.frame - b.frame);

    // Mark layer dirty
    markLayerDirty(targetLayerId);
  }

  if (createdKeyframes.length > 0) {
    store.project.meta.modified = new Date().toISOString();
    store.pushHistory();
    storeLogger.debug(`Pasted ${createdKeyframes.length} keyframe(s)`);
  }

  return createdKeyframes;
}

/**
 * Check if clipboard has keyframes.
 */
export function hasKeyframesInClipboard(
  state: KeyframeState,
): boolean {
  return state.clipboard.keyframes.length > 0;
}
