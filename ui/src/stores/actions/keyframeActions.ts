/**
 * Keyframe Actions
 *
 * All keyframe manipulation operations: add, remove, move, update, interpolation,
 * handles, and property animation state management.
 */

import { toRaw } from 'vue';
import { storeLogger } from '@/utils/logger';
import type { Layer, AnimatableProperty, Keyframe, InterpolationType, BezierHandle, PropertyExpression } from '@/types/project';
import { markLayerDirty } from '@/services/layerEvaluationCache';

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface KeyframeStore {
  project: {
    meta: { modified: string };
  };
  getActiveComp(): { currentFrame: number; layers: Layer[] } | null;
  getActiveCompLayers(): Layer[];
  getLayerById(id: string): Layer | null | undefined;
  pushHistory(): void;
}

// ============================================================================
// HELPER: FIND PROPERTY BY PATH
// ============================================================================

/**
 * Find a property by its path on a layer.
 * Supports both 'position' and 'transform.position' formats.
 */
export function findPropertyByPath(layer: Layer, propertyPath: string): AnimatableProperty<any> | undefined {
  // Normalize path - strip 'transform.' prefix if present
  const normalizedPath = propertyPath.replace(/^transform\./, '');

  // Check transform properties
  if (normalizedPath === 'position') {
    return layer.transform.position;
  }
  if (normalizedPath === 'scale') {
    return layer.transform.scale;
  }
  if (normalizedPath === 'rotation') {
    return layer.transform.rotation;
  }
  if (normalizedPath === 'anchorPoint') {
    return layer.transform.anchorPoint;
  }
  if (normalizedPath === 'origin') {
    return layer.transform.origin;
  }
  if (propertyPath === 'opacity') {
    return layer.opacity;
  }

  // Check 3D rotation properties
  if (normalizedPath === 'rotationX' && layer.transform.rotationX) {
    return layer.transform.rotationX;
  }
  if (normalizedPath === 'rotationY' && layer.transform.rotationY) {
    return layer.transform.rotationY;
  }
  if (normalizedPath === 'rotationZ' && layer.transform.rotationZ) {
    return layer.transform.rotationZ;
  }
  if (normalizedPath === 'orientation' && layer.transform.orientation) {
    return layer.transform.orientation;
  }

  // Check custom properties by name or id
  return layer.properties.find(p => p.name === propertyPath || p.id === propertyPath);
}

// ============================================================================
// KEYFRAME CREATION
// ============================================================================

/**
 * Add a keyframe to a property at the specified frame
 */
export function addKeyframe<T>(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  value: T,
  atFrame?: number
): Keyframe<T> | null {
  const comp = store.getActiveComp();
  const frame = atFrame ?? (comp?.currentFrame ?? 0);

  storeLogger.debug('addKeyframe called:', { layerId, propertyPath, value, frame });

  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    storeLogger.debug('addKeyframe: layer not found');
    return null;
  }

  const property = findPropertyByPath(layer, propertyPath) as AnimatableProperty<T> | undefined;
  if (!property) {
    storeLogger.debug('addKeyframe: property not found:', propertyPath);
    return null;
  }

  // Enable animation
  property.animated = true;

  // Create keyframe with default linear handles (disabled until graph editor enables them)
  const keyframe: Keyframe<T> = {
    id: `kf_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    frame,
    value,
    interpolation: 'linear',
    inHandle: { frame: 0, value: 0, enabled: false },
    outHandle: { frame: 0, value: 0, enabled: false },
    controlMode: 'smooth'
  };

  // Check for existing keyframe at this frame
  const existingIndex = property.keyframes.findIndex(k => k.frame === frame);
  if (existingIndex >= 0) {
    property.keyframes[existingIndex] = keyframe;
    storeLogger.debug('addKeyframe: replaced existing keyframe at frame', frame);
  } else {
    property.keyframes.push(keyframe);
    property.keyframes.sort((a, b) => a.frame - b.frame);
    storeLogger.debug('addKeyframe: added new keyframe at frame', frame, 'total keyframes:', property.keyframes.length);
  }

  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
  return keyframe;
}

// ============================================================================
// KEYFRAME REMOVAL
// ============================================================================

/**
 * Remove a keyframe by ID
 */
export function removeKeyframe(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  keyframeId: string
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const index = property.keyframes.findIndex(k => k.id === keyframeId);
  if (index >= 0) {
    property.keyframes.splice(index, 1);

    // Disable animation if no keyframes left
    if (property.keyframes.length === 0) {
      property.animated = false;
    }
  }

  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Remove all keyframes from a property
 */
export function clearKeyframes(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  property.keyframes = [];
  property.animated = false;

  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

// ============================================================================
// KEYFRAME MOVEMENT
// ============================================================================

/**
 * Move a keyframe to a new frame position
 */
export function moveKeyframe(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  newFrame: number
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find(kf => kf.id === keyframeId);
  if (!keyframe) return;

  // Check if there's already a keyframe at the target frame
  const existingAtTarget = property.keyframes.find(
    kf => kf.frame === newFrame && kf.id !== keyframeId
  );
  if (existingAtTarget) {
    // Remove the existing keyframe at target
    property.keyframes = property.keyframes.filter(kf => kf.id !== existingAtTarget.id);
  }

  keyframe.frame = newFrame;

  // Re-sort keyframes by frame
  property.keyframes.sort((a, b) => a.frame - b.frame);

  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Move multiple keyframes by a frame delta
 */
export function moveKeyframes(
  store: KeyframeStore,
  keyframes: Array<{ layerId: string; propertyPath: string; keyframeId: string }>,
  frameDelta: number
): void {
  for (const kf of keyframes) {
    const layer = store.getActiveCompLayers().find(l => l.id === kf.layerId);
    if (!layer) continue;

    const property = findPropertyByPath(layer, kf.propertyPath);
    if (!property) continue;

    const keyframe = property.keyframes.find(k => k.id === kf.keyframeId);
    if (!keyframe) continue;

    const newFrame = Math.max(0, keyframe.frame + frameDelta);
    keyframe.frame = newFrame;
  }

  // Re-sort all affected properties
  const layerIds = new Set(keyframes.map(kf => kf.layerId));
  for (const layerId of layerIds) {
    const layer = store.getActiveCompLayers().find(l => l.id === layerId);
    if (!layer) continue;

    const propertyPaths = new Set(
      keyframes.filter(kf => kf.layerId === layerId).map(kf => kf.propertyPath)
    );
    for (const propertyPath of propertyPaths) {
      const property = findPropertyByPath(layer, propertyPath);
      if (property) {
        property.keyframes.sort((a, b) => a.frame - b.frame);
      }
    }
  }

  // Mark all affected layers as dirty
  for (const layerId of layerIds) {
    markLayerDirty(layerId);
  }
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

// ============================================================================
// KEYFRAME VALUE UPDATES
// ============================================================================

/**
 * Update a keyframe's value
 */
export function setKeyframeValue(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  newValue: any
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find(kf => kf.id === keyframeId);
  if (!keyframe) return;

  // Handle vector values (Position X/Y are separated in graph editor)
  if (typeof keyframe.value === 'object' && keyframe.value !== null && typeof newValue === 'number') {
    storeLogger.warn('setKeyframeValue: Cannot directly update vector keyframes with scalar. Use separate dimension curves.');
    return;
  }

  keyframe.value = newValue;
  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Update keyframe frame position and/or value
 */
export function updateKeyframe(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  updates: { frame?: number; value?: any }
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find(kf => kf.id === keyframeId);
  if (!keyframe) return;

  if (updates.frame !== undefined) {
    // BUG-039 FIX: Check for existing keyframe at target frame (same pattern as moveKeyframe)
    const existingAtTarget = property.keyframes.find(
      kf => kf.frame === updates.frame && kf.id !== keyframeId
    );
    if (existingAtTarget) {
      // Remove the existing keyframe at target to prevent duplicates
      property.keyframes = property.keyframes.filter(kf => kf.id !== existingAtTarget.id);
    }
    keyframe.frame = updates.frame;
    // Re-sort keyframes by frame
    property.keyframes.sort((a, b) => a.frame - b.frame);
  }

  if (updates.value !== undefined) {
    keyframe.value = updates.value;
  }

  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

// ============================================================================
// KEYFRAME INTERPOLATION
// ============================================================================

/**
 * Set keyframe interpolation type
 */
export function setKeyframeInterpolation(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  interpolation: InterpolationType
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find(kf => kf.id === keyframeId);
  if (!keyframe) return;

  keyframe.interpolation = interpolation;
  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Set keyframe bezier handle
 */
export function setKeyframeHandle(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  handleType: 'in' | 'out',
  handle: BezierHandle
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find(kf => kf.id === keyframeId);
  if (!keyframe) return;

  if (handleType === 'in') {
    keyframe.inHandle = { ...handle };
  } else {
    keyframe.outHandle = { ...handle };
  }

  // Enable bezier interpolation when handles are modified
  if (handle.enabled && keyframe.interpolation === 'linear') {
    keyframe.interpolation = 'bezier';
  }

  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Set keyframe control mode (smooth, corner, etc.)
 */
export function setKeyframeControlMode(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  controlMode: 'smooth' | 'corner' | 'symmetric'
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find(kf => kf.id === keyframeId);
  if (!keyframe) return;

  keyframe.controlMode = controlMode;
  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

// ============================================================================
// PROPERTY ANIMATION STATE
// ============================================================================

/**
 * Set a property's value (for direct editing in timeline)
 */
export function setPropertyValue(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  value: any
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  property.value = value;

  // If animated and at a keyframe, update that keyframe's value too
  if (property.animated && property.keyframes.length > 0) {
    const currentFrame = store.getActiveComp()?.currentFrame ?? 0;
    const existingKf = property.keyframes.find(kf => kf.frame === currentFrame);
    if (existingKf) {
      existingKf.value = value;
    }
  }

  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Set a property's animated state
 */
export function setPropertyAnimated(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  animated: boolean,
  addKeyframeCallback?: () => void
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
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
      const comp = store.getActiveComp();
      const frame = comp?.currentFrame ?? 0;

      const keyframe: Keyframe<any> = {
        id: `kf_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
        frame,
        value: property.value,
        interpolation: 'linear',
        inHandle: { frame: 0, value: 0, enabled: false },
        outHandle: { frame: 0, value: 0, enabled: false },
        controlMode: 'smooth'
      };

      property.keyframes.push(keyframe);
    }
  }

  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

// ============================================================================
// KEYFRAME QUERY UTILITIES
// ============================================================================

/**
 * Get keyframes at a specific frame across all animated properties of a layer
 */
export function getKeyframesAtFrame(
  store: KeyframeStore,
  layerId: string,
  frame: number
): Array<{ propertyPath: string; keyframe: Keyframe<any> }> {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return [];

  const results: Array<{ propertyPath: string; keyframe: Keyframe<any> }> = [];

  // Check transform properties
  const transformProps = ['position', 'scale', 'rotation', 'anchorPoint'];
  for (const propName of transformProps) {
    const prop = (layer.transform as any)[propName];
    if (prop?.animated && prop.keyframes) {
      const kf = prop.keyframes.find((k: Keyframe<any>) => k.frame === frame);
      if (kf) {
        results.push({ propertyPath: propName, keyframe: kf });
      }
    }
  }

  // Check opacity
  if (layer.opacity?.animated && layer.opacity.keyframes) {
    const kf = layer.opacity.keyframes.find(k => k.frame === frame);
    if (kf) {
      results.push({ propertyPath: 'opacity', keyframe: kf });
    }
  }

  // Check 3D rotations
  const threeDProps = ['rotationX', 'rotationY', 'rotationZ', 'orientation'];
  for (const propName of threeDProps) {
    const prop = (layer.transform as any)[propName];
    if (prop?.animated && prop.keyframes) {
      const kf = prop.keyframes.find((k: Keyframe<any>) => k.frame === frame);
      if (kf) {
        results.push({ propertyPath: propName, keyframe: kf });
      }
    }
  }

  // Check custom properties
  for (const prop of layer.properties) {
    if (prop.animated && prop.keyframes) {
      const kf = prop.keyframes.find(k => k.frame === frame);
      if (kf) {
        results.push({ propertyPath: prop.name, keyframe: kf });
      }
    }
  }

  return results;
}

/**
 * Get all keyframe frames for a layer (for timeline display)
 */
export function getAllKeyframeFrames(store: KeyframeStore, layerId: string): number[] {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return [];

  const frames = new Set<number>();

  // Collect frames from transform properties
  const transformProps = ['position', 'scale', 'rotation', 'anchorPoint'];
  for (const propName of transformProps) {
    const prop = (layer.transform as any)[propName];
    if (prop?.animated && prop.keyframes) {
      for (const kf of prop.keyframes) {
        frames.add(kf.frame);
      }
    }
  }

  // Collect from opacity
  if (layer.opacity?.animated && layer.opacity.keyframes) {
    for (const kf of layer.opacity.keyframes) {
      frames.add(kf.frame);
    }
  }

  // Collect from 3D properties
  const threeDProps = ['rotationX', 'rotationY', 'rotationZ', 'orientation'];
  for (const propName of threeDProps) {
    const prop = (layer.transform as any)[propName];
    if (prop?.animated && prop.keyframes) {
      for (const kf of prop.keyframes) {
        frames.add(kf.frame);
      }
    }
  }

  // Collect from custom properties
  for (const prop of layer.properties) {
    if (prop.animated && prop.keyframes) {
      for (const kf of prop.keyframes) {
        frames.add(kf.frame);
      }
    }
  }

  return Array.from(frames).sort((a, b) => a - b);
}

/**
 * Find the nearest keyframes before and after a given frame
 */
export function findSurroundingKeyframes<T>(
  property: AnimatableProperty<T>,
  frame: number
): { before: Keyframe<T> | null; after: Keyframe<T> | null } {
  if (!property.keyframes || property.keyframes.length === 0) {
    return { before: null, after: null };
  }

  let before: Keyframe<T> | null = null;
  let after: Keyframe<T> | null = null;

  for (const kf of property.keyframes) {
    if (kf.frame <= frame) {
      before = kf;
    } else if (kf.frame > frame && after === null) {
      after = kf;
      break;
    }
  }

  return { before, after };
}

/**
 * Scale keyframe timing by a factor
 * Used for Alt+drag last keyframe to scale all keyframes proportionally
 *
 * @param store - The compositor store
 * @param layerId - Layer ID
 * @param propertyPath - Property path (or undefined for all transform properties)
 * @param scaleFactor - Factor to scale by (e.g., 2.0 = twice as long, 0.5 = half)
 * @param anchorFrame - Frame to anchor scaling from (default: 0)
 */
export function scaleKeyframeTiming(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string | undefined,
  scaleFactor: number,
  anchorFrame: number = 0
): number {
  const layer = store.getLayerById(layerId);
  if (!layer) return 0;

  // Determine which properties to scale
  const propertiesToScale: string[] = propertyPath
    ? [propertyPath]
    : ['position', 'scale', 'rotation', 'opacity', 'origin'];

  let scaledCount = 0;

  for (const propPath of propertiesToScale) {
    // findPropertyByPath already handles path normalization (opacity is at layer.opacity, not transform.opacity)
    const property = findPropertyByPath(layer, propPath);

    if (property?.keyframes && property.keyframes.length > 0) {
      // Scale each keyframe's frame number relative to anchor
      for (const kf of property.keyframes) {
        const relativeFrame = kf.frame - anchorFrame;
        kf.frame = Math.round(anchorFrame + relativeFrame * scaleFactor);
      }
      // Re-sort keyframes to maintain order
      property.keyframes.sort((a, b) => a.frame - b.frame);
      scaledCount += property.keyframes.length;
    }
  }

  if (scaledCount > 0) {
    markLayerDirty(layerId);
    store.project.meta.modified = new Date().toISOString();
    store.pushHistory();
  }

  return scaledCount;
}

/**
 * Reverse keyframe timing (values stay at same frames, but values swap)
 * This creates the effect of playing the animation backward
 *
 * @param store - The compositor store
 * @param layerId - Layer ID
 * @param propertyPath - Property path (or undefined for all transform properties)
 */
export function timeReverseKeyframes(
  store: KeyframeStore,
  layerId: string,
  propertyPath?: string
): number {
  const layer = store.getLayerById(layerId);
  if (!layer) return 0;

  // Determine which properties to reverse
  const propertiesToReverse: string[] = propertyPath
    ? [propertyPath]
    : ['position', 'scale', 'rotation', 'opacity', 'origin'];

  let reversedCount = 0;

  for (const propPath of propertiesToReverse) {
    // findPropertyByPath already handles path normalization (opacity is at layer.opacity, not transform.opacity)
    const property = findPropertyByPath(layer, propPath);

    if (property?.keyframes && property.keyframes.length >= 2) {
      // Collect values in order
      const values = property.keyframes.map(kf => kf.value);
      // Reverse the values
      values.reverse();
      // Assign reversed values back to keyframes (frames stay same)
      for (let i = 0; i < property.keyframes.length; i++) {
        property.keyframes[i].value = values[i];
      }
      reversedCount += property.keyframes.length;
    }
  }

  if (reversedCount > 0) {
    markLayerDirty(layerId);
    store.project.meta.modified = new Date().toISOString();
    store.pushHistory();
  }

  return reversedCount;
}

/**
 * Insert a keyframe at a specific position along a motion path
 * Used for Pen tool click on path to add control point
 *
 * @param store - The compositor store
 * @param layerId - Layer ID
 * @param frame - Frame number to insert at
 * @returns The created keyframe ID or null
 */
export function insertKeyframeOnPath(
  store: KeyframeStore,
  layerId: string,
  frame: number
): string | null {
  const layer = store.getLayerById(layerId);
  if (!layer) return null;

  const positionProp = findPropertyByPath(layer, 'transform.position');
  if (!positionProp || !positionProp.animated || !positionProp.keyframes || positionProp.keyframes.length < 2) {
    return null;
  }

  // Check if keyframe already exists at this frame
  const existing = positionProp.keyframes.find(kf => kf.frame === frame);
  if (existing) return existing.id;

  // Find surrounding keyframes
  const { before, after } = findSurroundingKeyframes(positionProp, frame);
  if (!before || !after) return null;

  // Interpolate the value at this frame
  const t = (frame - before.frame) / (after.frame - before.frame);
  const beforeVal = before.value as { x: number; y: number; z?: number };
  const afterVal = after.value as { x: number; y: number; z?: number };

  const interpolatedValue = {
    x: beforeVal.x + (afterVal.x - beforeVal.x) * t,
    y: beforeVal.y + (afterVal.y - beforeVal.y) * t,
    z: (beforeVal.z ?? 0) + ((afterVal.z ?? 0) - (beforeVal.z ?? 0)) * t
  };

  // Create the keyframe
  const newKf = addKeyframe(store, layerId, 'transform.position', interpolatedValue, frame);

  return newKf?.id ?? null;
}

// ============================================================================
// ROVING KEYFRAMES
// ============================================================================

export interface RovingKeyframeStore extends KeyframeStore {
  getLayerById(id: string): Layer | undefined;
}

/**
 * Apply roving keyframes to a position property.
 * Redistributes intermediate keyframe timing for constant velocity.
 *
 * @param store - Store with layer access
 * @param layerId - Target layer ID
 * @returns true if roving was applied successfully
 */
export function applyRovingToPosition(
  store: RovingKeyframeStore,
  layerId: string
): boolean {
  const layer = store.getLayerById(layerId);
  if (!layer) {
    storeLogger.debug('applyRovingToPosition: layer not found');
    return false;
  }

  const positionProp = findPropertyByPath(layer, 'transform.position');
  if (!positionProp || !positionProp.animated || !positionProp.keyframes) {
    storeLogger.debug('applyRovingToPosition: no animated position keyframes');
    return false;
  }

  if (positionProp.keyframes.length < 3) {
    storeLogger.debug('applyRovingToPosition: need at least 3 keyframes for roving');
    return false;
  }

  // Import and apply roving
  // Note: Using dynamic import to avoid circular dependency
  import('@/services/rovingKeyframes').then(({ applyRovingKeyframes }) => {
    const result = applyRovingKeyframes(positionProp.keyframes as Keyframe<number[]>[]);

    if (result.success) {
      // Update keyframe frames in place
      result.keyframes.forEach((newKf, index) => {
        if (positionProp.keyframes![index]) {
          positionProp.keyframes![index].frame = newKf.frame;
        }
      });

      // Mark layer as dirty
      markLayerDirty(layerId);

      // Update modified timestamp
      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();

      storeLogger.info('applyRovingToPosition: applied roving keyframes', {
        layerId,
        totalLength: result.totalLength,
        keyframeCount: result.keyframes.length
      });
    } else {
      storeLogger.warn('applyRovingToPosition: roving failed', result.error);
    }
  });

  return true;
}

/**
 * Check if roving would significantly change keyframe timing
 *
 * @param store - Store with layer access
 * @param layerId - Target layer ID
 * @returns true if roving would make significant changes
 */
export function checkRovingImpact(
  store: RovingKeyframeStore,
  layerId: string
): boolean {
  const layer = store.getLayerById(layerId);
  if (!layer) return false;

  const positionProp = findPropertyByPath(layer, 'transform.position');
  if (!positionProp || !positionProp.animated || !positionProp.keyframes) {
    return false;
  }

  // Import and check
  // Using synchronous check would be better, but for now this works
  return positionProp.keyframes.length >= 3;
}

// ============================================================================
// KEYFRAME CLIPBOARD (COPY/PASTE)
// ============================================================================

import type { ClipboardKeyframe, PropertyValue } from '@/types/project';

export interface ClipboardKeyframeStore extends KeyframeStore {
  clipboard: {
    keyframes: ClipboardKeyframe[];
  };
  currentFrame: number;
}

/**
 * Copy keyframes to clipboard
 *
 * @param store - The compositor store with clipboard access
 * @param keyframeSelections - Array of keyframe selections with layerId, propertyPath, and keyframeId
 * @returns Number of keyframes copied
 */
export function copyKeyframes(
  store: ClipboardKeyframeStore,
  keyframeSelections: Array<{ layerId: string; propertyPath: string; keyframeId: string }>
): number {
  if (keyframeSelections.length === 0) {
    storeLogger.debug('copyKeyframes: No keyframes selected');
    return 0;
  }

  // Group keyframes by layer and property
  const groupedByProperty = new Map<string, { layerId: string; propertyPath: string; keyframeIds: string[] }>();

  for (const sel of keyframeSelections) {
    const key = `${sel.layerId}:${sel.propertyPath}`;
    if (!groupedByProperty.has(key)) {
      groupedByProperty.set(key, { layerId: sel.layerId, propertyPath: sel.propertyPath, keyframeIds: [] });
    }
    groupedByProperty.get(key)!.keyframeIds.push(sel.keyframeId);
  }

  // Find the earliest frame among all selected keyframes (for relative timing)
  let earliestFrame = Infinity;
  const clipboardEntries: ClipboardKeyframe[] = [];

  for (const [, group] of groupedByProperty) {
    const layer = store.getActiveCompLayers().find(l => l.id === group.layerId);
    if (!layer) continue;

    const property = findPropertyByPath(layer, group.propertyPath);
    if (!property?.keyframes) continue;

    const selectedKeyframes = property.keyframes.filter(kf => group.keyframeIds.includes(kf.id));
    for (const kf of selectedKeyframes) {
      if (kf.frame < earliestFrame) {
        earliestFrame = kf.frame;
      }
    }
  }

  if (earliestFrame === Infinity) {
    storeLogger.debug('copyKeyframes: No valid keyframes found');
    return 0;
  }

  // Build clipboard entries with relative frame offsets
  for (const [, group] of groupedByProperty) {
    const layer = store.getActiveCompLayers().find(l => l.id === group.layerId);
    if (!layer) continue;

    const property = findPropertyByPath(layer, group.propertyPath);
    if (!property?.keyframes) continue;

    const selectedKeyframes = property.keyframes.filter(kf => group.keyframeIds.includes(kf.id));
    if (selectedKeyframes.length === 0) continue;

    // Deep clone keyframes and store relative frame offsets
    // Use toRaw to handle Vue reactive proxies before cloning
    const clonedKeyframes: Keyframe<PropertyValue>[] = selectedKeyframes.map(kf => ({
      ...structuredClone(toRaw(kf)),
      // Store frame as offset from earliest keyframe
      frame: kf.frame - earliestFrame
    }));

    clipboardEntries.push({
      layerId: group.layerId,
      propertyPath: group.propertyPath,
      keyframes: clonedKeyframes
    });
  }

  // Store in clipboard
  store.clipboard.keyframes = clipboardEntries;

  const totalCopied = clipboardEntries.reduce((sum, entry) => sum + entry.keyframes.length, 0);
  storeLogger.debug(`Copied ${totalCopied} keyframe(s) to clipboard`);

  return totalCopied;
}

/**
 * Paste keyframes from clipboard to a target property
 *
 * @param store - The compositor store with clipboard access
 * @param targetLayerId - Target layer ID to paste to
 * @param targetPropertyPath - Target property path (optional - uses original if matching type)
 * @returns Array of newly created keyframes
 */
export function pasteKeyframes(
  store: ClipboardKeyframeStore,
  targetLayerId: string,
  targetPropertyPath?: string
): Keyframe<PropertyValue>[] {
  if (store.clipboard.keyframes.length === 0) {
    storeLogger.debug('pasteKeyframes: No keyframes in clipboard');
    return [];
  }

  const targetLayer = store.getActiveCompLayers().find(l => l.id === targetLayerId);
  if (!targetLayer) {
    storeLogger.debug('pasteKeyframes: Target layer not found');
    return [];
  }

  const currentFrame = store.currentFrame;
  const createdKeyframes: Keyframe<PropertyValue>[] = [];

  for (const clipboardEntry of store.clipboard.keyframes) {
    // Determine which property to paste to
    const propPath = targetPropertyPath || clipboardEntry.propertyPath;
    const property = findPropertyByPath(targetLayer, propPath) as AnimatableProperty<PropertyValue> | undefined;

    if (!property) {
      storeLogger.debug(`pasteKeyframes: Property ${propPath} not found on target layer`);
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
        frame: newFrame
      };

      // Check for existing keyframe at this frame
      const existingIndex = property.keyframes.findIndex(k => k.frame === newFrame);
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
 * Check if clipboard has keyframes
 */
export function hasKeyframesInClipboard(store: ClipboardKeyframeStore): boolean {
  return store.clipboard.keyframes.length > 0;
}

// ============================================================================
// EXPRESSION METHODS
// ============================================================================

/**
 * Set an expression on a property
 */
export function setPropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  expression: PropertyExpression
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    storeLogger.warn('setPropertyExpression: layer not found:', layerId);
    return false;
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    storeLogger.warn('setPropertyExpression: property not found:', propertyPath);
    return false;
  }

  property.expression = expression;
  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  store.pushHistory();

  storeLogger.debug('Set expression on', propertyPath, ':', expression.name);
  return true;
}

/**
 * Enable expression on a property (creates default if not exists)
 */
export function enablePropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  expressionName: string = 'custom',
  params: Record<string, number | string | boolean> = {}
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return false;

  const expression: PropertyExpression = {
    enabled: true,
    type: expressionName === 'custom' ? 'custom' : 'preset',
    name: expressionName,
    params
  };

  property.expression = expression;
  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  store.pushHistory();

  return true;
}

/**
 * Disable expression on a property (keeps expression data for re-enabling)
 */
export function disablePropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || !property.expression) return false;

  property.expression.enabled = false;
  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  store.pushHistory();

  return true;
}

/**
 * Toggle expression enabled state
 */
export function togglePropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || !property.expression) return false;

  property.expression.enabled = !property.expression.enabled;
  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  store.pushHistory();

  return property.expression.enabled;
}

/**
 * Remove expression from a property
 */
export function removePropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return false;

  delete property.expression;
  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  store.pushHistory();

  return true;
}

/**
 * Get expression on a property
 */
export function getPropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): PropertyExpression | undefined {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return undefined;

  const property = findPropertyByPath(layer, propertyPath);
  return property?.expression;
}

/**
 * Check if property has an expression
 */
export function hasPropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  return property?.expression !== undefined;
}

/**
 * Update expression parameters
 */
export function updateExpressionParams(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  params: Record<string, number | string | boolean>
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || !property.expression) return false;

  property.expression.params = { ...property.expression.params, ...params };
  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  store.pushHistory();

  return true;
}

// ============================================================================
// KEYFRAME VELOCITY
// ============================================================================

export interface VelocityStore extends KeyframeStore {
  fps: number;
}

export interface VelocitySettings {
  incomingVelocity: number;
  outgoingVelocity: number;
  incomingInfluence: number;  // 0-100 percentage
  outgoingInfluence: number;  // 0-100 percentage
}

/**
 * Apply velocity settings to a keyframe.
 * Converts velocity and influence to bezier handle values.
 *
 * @param store - The compositor store
 * @param layerId - Layer ID
 * @param propertyPath - Property path
 * @param keyframeId - Keyframe ID
 * @param settings - Velocity settings
 */
export function applyKeyframeVelocity(
  store: VelocityStore,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  settings: VelocitySettings
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property?.keyframes) return false;

  const kfIndex = property.keyframes.findIndex(kf => kf.id === keyframeId);
  if (kfIndex < 0) return false;

  const keyframe = property.keyframes[kfIndex];
  const prevKf = kfIndex > 0 ? property.keyframes[kfIndex - 1] : null;
  const nextKf = kfIndex < property.keyframes.length - 1 ? property.keyframes[kfIndex + 1] : null;

  // Calculate handle frame offsets from influence percentages
  const inDuration = prevKf ? keyframe.frame - prevKf.frame : 10;
  const outDuration = nextKf ? nextKf.frame - keyframe.frame : 10;

  const inInfluence = settings.incomingInfluence / 100;
  const outInfluence = settings.outgoingInfluence / 100;

  // Convert velocity to value offset
  // Velocity is in units per second, convert to units per frame segment
  const fps = store.fps ?? 16;
  const inVelocityPerFrame = settings.incomingVelocity / fps;
  const outVelocityPerFrame = settings.outgoingVelocity / fps;

  // Set bezier handles
  keyframe.inHandle = {
    frame: -inDuration * inInfluence,
    value: -inVelocityPerFrame * inDuration * inInfluence,
    enabled: true
  };

  keyframe.outHandle = {
    frame: outDuration * outInfluence,
    value: outVelocityPerFrame * outDuration * outInfluence,
    enabled: true
  };

  // Ensure interpolation is bezier
  keyframe.interpolation = 'bezier';

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return true;
}

/**
 * Get the current velocity settings from a keyframe's handles
 */
export function getKeyframeVelocity(
  store: VelocityStore,
  layerId: string,
  propertyPath: string,
  keyframeId: string
): VelocitySettings | null {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return null;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property?.keyframes) return null;

  const kfIndex = property.keyframes.findIndex(kf => kf.id === keyframeId);
  if (kfIndex < 0) return null;

  const keyframe = property.keyframes[kfIndex];
  const prevKf = kfIndex > 0 ? property.keyframes[kfIndex - 1] : null;
  const nextKf = kfIndex < property.keyframes.length - 1 ? property.keyframes[kfIndex + 1] : null;

  // Calculate durations
  const inDuration = prevKf ? keyframe.frame - prevKf.frame : 10;
  const outDuration = nextKf ? nextKf.frame - keyframe.frame : 10;

  // Extract influence from handle frame offset
  const inInfluence = keyframe.inHandle?.enabled && inDuration > 0
    ? Math.abs(keyframe.inHandle.frame) / inDuration * 100
    : 33.33;

  const outInfluence = keyframe.outHandle?.enabled && outDuration > 0
    ? keyframe.outHandle.frame / outDuration * 100
    : 33.33;

  // Convert value offset back to velocity
  const fps = store.fps ?? 16;
  const inVelocity = keyframe.inHandle?.enabled && keyframe.inHandle.frame !== 0
    ? -keyframe.inHandle.value / Math.abs(keyframe.inHandle.frame) * fps
    : 0;

  const outVelocity = keyframe.outHandle?.enabled && keyframe.outHandle.frame !== 0
    ? keyframe.outHandle.value / keyframe.outHandle.frame * fps
    : 0;

  return {
    incomingVelocity: inVelocity,
    outgoingVelocity: outVelocity,
    incomingInfluence: Math.min(100, Math.max(0, inInfluence)),
    outgoingInfluence: Math.min(100, Math.max(0, outInfluence))
  };
}

// ============================================================================
// CONVERT EXPRESSION TO KEYFRAMES
// ============================================================================

export interface BakeExpressionStore extends KeyframeStore {
  fps: number;
  frameCount: number;
  evaluatePropertyAtFrame(layerId: string, propertyPath: string, frame: number): any;
}

/**
 * Convert an expression to keyframes by sampling at every frame.
 * This "bakes" the expression result into keyframes.
 *
 * @param store - Store with expression evaluation capability
 * @param layerId - Layer ID
 * @param propertyPath - Property path with expression
 * @param startFrame - Start frame (default: 0)
 * @param endFrame - End frame (default: composition duration)
 * @param sampleRate - Sample every N frames (default: 1 = every frame)
 * @returns Number of keyframes created
 */
export function convertExpressionToKeyframes(
  store: BakeExpressionStore,
  layerId: string,
  propertyPath: string,
  startFrame?: number,
  endFrame?: number,
  sampleRate: number = 1
): number {
  const layer = store.getLayerById(layerId);
  if (!layer) {
    storeLogger.warn('convertExpressionToKeyframes: layer not found:', layerId);
    return 0;
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    storeLogger.warn('convertExpressionToKeyframes: property not found:', propertyPath);
    return 0;
  }

  if (!property.expression?.enabled) {
    storeLogger.warn('convertExpressionToKeyframes: no active expression on property');
    return 0;
  }

  const start = startFrame ?? 0;
  const end = endFrame ?? store.frameCount;
  const rate = Math.max(1, Math.round(sampleRate));

  // Clear existing keyframes
  property.keyframes = [];
  property.animated = true;

  let keyframesCreated = 0;

  // Sample expression at each frame
  for (let frame = start; frame <= end; frame += rate) {
    const value = store.evaluatePropertyAtFrame(layerId, propertyPath, frame);

    if (value !== undefined && value !== null) {
      const keyframe: Keyframe<any> = {
        id: `kf_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
        frame,
        value,
        interpolation: 'linear',
        inHandle: { frame: 0, value: 0, enabled: false },
        outHandle: { frame: 0, value: 0, enabled: false },
        controlMode: 'smooth'
      };

      property.keyframes.push(keyframe);
      keyframesCreated++;
    }
  }

  // Disable the expression after baking
  if (property.expression) {
    property.expression.enabled = false;
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  storeLogger.info('convertExpressionToKeyframes: created', keyframesCreated, 'keyframes');
  return keyframesCreated;
}

/**
 * Check if a property has a bakeable expression
 */
export function canBakeExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): boolean {
  const layer = store.getLayerById(layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return false;

  return property.expression?.enabled === true;
}

// ============================================================================
// AUTO BEZIER TANGENT CALCULATION
// ============================================================================

/**
 * Auto-calculate bezier tangents for a keyframe based on surrounding keyframes.
 * This creates smooth curves through keyframe values.
 *
 * Algorithm:
 * - For keyframes with both neighbors: tangent angle points from prev to next
 * - For first keyframe: tangent is horizontal
 * - For last keyframe: tangent is horizontal
 * - Tangent magnitude is proportional to segment length
 */
export function autoCalculateBezierTangents(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  keyframeId: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || property.keyframes.length < 2) return false;

  // Sort keyframes by frame
  const sorted = [...property.keyframes].sort((a, b) => a.frame - b.frame);
  const kfIndex = sorted.findIndex(kf => kf.id === keyframeId);
  if (kfIndex === -1) return false;

  const keyframe = sorted[kfIndex];
  const prevKf = kfIndex > 0 ? sorted[kfIndex - 1] : null;
  const nextKf = kfIndex < sorted.length - 1 ? sorted[kfIndex + 1] : null;

  const getValue = (kf: Keyframe<any>) => typeof kf.value === 'number' ? kf.value : 0;
  const currentValue = getValue(keyframe);

  // Calculate tangent direction (slope from prev to next)
  let slopeFrame = 0;
  let slopeValue = 0;

  if (prevKf && nextKf) {
    // Middle keyframe: slope from prev to next
    const prevValue = getValue(prevKf);
    const nextValue = getValue(nextKf);
    const frameDelta = nextKf.frame - prevKf.frame;
    const valueDelta = nextValue - prevValue;

    slopeFrame = frameDelta / 2;
    slopeValue = valueDelta / 2;
  } else if (prevKf) {
    // Last keyframe: use slope from previous segment
    const prevValue = getValue(prevKf);
    const frameDelta = keyframe.frame - prevKf.frame;
    const valueDelta = currentValue - prevValue;

    slopeFrame = frameDelta / 3;
    slopeValue = valueDelta / 3;
  } else if (nextKf) {
    // First keyframe: use slope to next segment
    const nextValue = getValue(nextKf);
    const frameDelta = nextKf.frame - keyframe.frame;
    const valueDelta = nextValue - currentValue;

    slopeFrame = frameDelta / 3;
    slopeValue = valueDelta / 3;
  }

  // Set handles with calculated tangents
  keyframe.inHandle = {
    frame: -slopeFrame,
    value: -slopeValue,
    enabled: true
  };
  keyframe.outHandle = {
    frame: slopeFrame,
    value: slopeValue,
    enabled: true
  };
  keyframe.interpolation = 'bezier';
  keyframe.controlMode = 'smooth';

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return true;
}

/**
 * Auto-calculate bezier tangents for ALL keyframes on a property.
 * Useful when converting from linear to bezier interpolation.
 */
export function autoCalculateAllBezierTangents(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): number {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return 0;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || property.keyframes.length < 2) return 0;

  // Sort keyframes by frame
  const sorted = [...property.keyframes].sort((a, b) => a.frame - b.frame);
  let count = 0;

  for (let i = 0; i < sorted.length; i++) {
    const keyframe = sorted[i];
    const prevKf = i > 0 ? sorted[i - 1] : null;
    const nextKf = i < sorted.length - 1 ? sorted[i + 1] : null;

    const getValue = (kf: Keyframe<any>) => typeof kf.value === 'number' ? kf.value : 0;
    const currentValue = getValue(keyframe);

    let slopeFrame = 0;
    let slopeValue = 0;

    if (prevKf && nextKf) {
      const prevValue = getValue(prevKf);
      const nextValue = getValue(nextKf);
      const frameDelta = nextKf.frame - prevKf.frame;
      const valueDelta = nextValue - prevValue;

      slopeFrame = frameDelta / 4; // Less aggressive for all-at-once
      slopeValue = valueDelta / 4;
    } else if (prevKf) {
      const prevValue = getValue(prevKf);
      const frameDelta = keyframe.frame - prevKf.frame;
      const valueDelta = currentValue - prevValue;

      slopeFrame = frameDelta / 3;
      slopeValue = valueDelta / 3;
    } else if (nextKf) {
      const nextValue = getValue(nextKf);
      const frameDelta = nextKf.frame - keyframe.frame;
      const valueDelta = nextValue - currentValue;

      slopeFrame = frameDelta / 3;
      slopeValue = valueDelta / 3;
    }

    keyframe.inHandle = {
      frame: -slopeFrame,
      value: -slopeValue,
      enabled: true
    };
    keyframe.outHandle = {
      frame: slopeFrame,
      value: slopeValue,
      enabled: true
    };
    keyframe.interpolation = 'bezier';
    keyframe.controlMode = 'smooth';
    count++;
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return count;
}

// ============================================================================
// HANDLE WITH CONTROL MODE (BREAK HANDLES)
// ============================================================================

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
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  handleType: 'in' | 'out',
  handle: BezierHandle,
  breakHandle: boolean = false
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find(kf => kf.id === keyframeId);
  if (!keyframe) return;

  // If breaking handle (Ctrl+drag), set to corner mode
  if (breakHandle) {
    keyframe.controlMode = 'corner';
    if (handleType === 'in') {
      keyframe.inHandle = { ...handle };
    } else {
      keyframe.outHandle = { ...handle };
    }
  } else {
    // Respect existing control mode
    const mode = keyframe.controlMode || 'smooth';

    if (handleType === 'in') {
      keyframe.inHandle = { ...handle };

      if (mode === 'symmetric') {
        // Mirror both angle and length to outHandle
        keyframe.outHandle = {
          frame: -handle.frame,
          value: -handle.value,
          enabled: handle.enabled
        };
      } else if (mode === 'smooth') {
        // Mirror angle, keep outHandle length
        const inLength = Math.sqrt(handle.frame * handle.frame + handle.value * handle.value);
        const outLength = Math.sqrt(
          keyframe.outHandle.frame * keyframe.outHandle.frame +
          keyframe.outHandle.value * keyframe.outHandle.value
        );

        if (inLength > 0) {
          const scale = outLength / inLength;
          keyframe.outHandle = {
            frame: -handle.frame * scale,
            value: -handle.value * scale,
            enabled: keyframe.outHandle.enabled
          };
        }
      }
      // corner mode: no adjustment to other handle
    } else {
      keyframe.outHandle = { ...handle };

      if (mode === 'symmetric') {
        // Mirror both angle and length to inHandle
        keyframe.inHandle = {
          frame: -handle.frame,
          value: -handle.value,
          enabled: handle.enabled
        };
      } else if (mode === 'smooth') {
        // Mirror angle, keep inHandle length
        const outLength = Math.sqrt(handle.frame * handle.frame + handle.value * handle.value);
        const inLength = Math.sqrt(
          keyframe.inHandle.frame * keyframe.inHandle.frame +
          keyframe.inHandle.value * keyframe.inHandle.value
        );

        if (outLength > 0) {
          const scale = inLength / outLength;
          keyframe.inHandle = {
            frame: -handle.frame * scale,
            value: -handle.value * scale,
            enabled: keyframe.inHandle.enabled
          };
        }
      }
      // corner mode: no adjustment to other handle
    }
  }

  // Enable bezier interpolation when handles are modified
  if (handle.enabled && keyframe.interpolation === 'linear') {
    keyframe.interpolation = 'bezier';
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

// ============================================================================
// SEPARATE DIMENSIONS
// ============================================================================

import {
  separatePositionDimensions,
  linkPositionDimensions,
  separateScaleDimensions,
  linkScaleDimensions
} from '@/types/transform';

/**
 * Separate position into individual X, Y, Z properties for independent keyframing.
 * After separation, positionX, positionY, positionZ can have different keyframes.
 */
export function separatePositionDimensionsAction(
  store: KeyframeStore,
  layerId: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  separatePositionDimensions(layer.transform);

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return true;
}

/**
 * Link position dimensions back into a combined property.
 * Merges X, Y, Z keyframes at each unique frame.
 */
export function linkPositionDimensionsAction(
  store: KeyframeStore,
  layerId: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  linkPositionDimensions(layer.transform);

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return true;
}

/**
 * Separate scale into individual X, Y, Z properties.
 */
export function separateScaleDimensionsAction(
  store: KeyframeStore,
  layerId: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  separateScaleDimensions(layer.transform);

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return true;
}

/**
 * Link scale dimensions back into a combined property.
 */
export function linkScaleDimensionsAction(
  store: KeyframeStore,
  layerId: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  linkScaleDimensions(layer.transform);

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return true;
}

/**
 * Check if a layer has separated position dimensions.
 */
export function hasPositionSeparated(
  store: KeyframeStore,
  layerId: string
): boolean {
  const layer = store.getLayerById(layerId);
  if (!layer) return false;
  return layer.transform.separateDimensions?.position === true;
}

/**
 * Check if a layer has separated scale dimensions.
 */
export function hasScaleSeparated(
  store: KeyframeStore,
  layerId: string
): boolean {
  const layer = store.getLayerById(layerId);
  if (!layer) return false;
  return layer.transform.separateDimensions?.scale === true;
}
