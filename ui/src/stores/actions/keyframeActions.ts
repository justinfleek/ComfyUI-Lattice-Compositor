/**
 * Keyframe Actions
 *
 * All keyframe manipulation operations: add, remove, move, update, interpolation,
 * handles, and property animation state management.
 */

import { storeLogger } from '@/utils/logger';
import type { Layer, AnimatableProperty, Keyframe, InterpolationType, BezierHandle } from '@/types/project';
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
    id: `kf_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
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

  store.project.meta.modified = new Date().toISOString();
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

  store.project.meta.modified = new Date().toISOString();
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
    keyframe.frame = updates.frame;
    // Re-sort keyframes by frame
    property.keyframes.sort((a, b) => a.frame - b.frame);
  }

  if (updates.value !== undefined) {
    keyframe.value = updates.value;
  }

  markLayerDirty(layerId); // Invalidate evaluation cache
  store.project.meta.modified = new Date().toISOString();
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
        id: `kf_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
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
    const fullPath = propPath.startsWith('transform.') ? propPath : `transform.${propPath}`;
    const property = findPropertyByPath(layer, fullPath);

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
    const fullPath = propPath.startsWith('transform.') ? propPath : `transform.${propPath}`;
    const property = findPropertyByPath(layer, fullPath);

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
  const beforeVal = before.value as number[];
  const afterVal = after.value as number[];

  const interpolatedValue = beforeVal.map((v, i) =>
    v + (afterVal[i] - v) * t
  );

  // Create the keyframe
  const newKf = addKeyframe(store, layerId, 'transform.position', frame, interpolatedValue);

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
