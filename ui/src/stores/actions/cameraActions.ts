/**
 * Camera Actions
 *
 * Camera management including creation, deletion, keyframes, and interpolation.
 */

import { storeLogger } from '@/utils/logger';
import type { Layer, CameraLayerData, AnimatableProperty } from '@/types/project';
import type { Camera3D, CameraKeyframe, ViewportState, ViewOptions } from '@/types/camera';
import { createDefaultCamera, createDefaultViewportState, createDefaultViewOptions } from '@/types/camera';
import { interpolateCameraAtFrame } from '@/services/export/cameraExportFormats';
import { createDefaultTransform, createAnimatableProperty } from '@/types/project';
import { useSelectionStore } from '../selectionStore';

/**
 * Safely compare frame numbers, handling NaN values
 */
function framesEqual(a: number, b: number): boolean {
  if (!Number.isFinite(a) || !Number.isFinite(b)) return false;
  return a === b;
}

/**
 * Validate and sanitize frame number input
 */
function safeFrame(frame: number | undefined | null, fallback = 0): number {
  return Number.isFinite(frame) ? frame! : fallback;
}

export interface CameraStore {
  cameras: Map<string, Camera3D>;
  cameraKeyframes: Map<string, CameraKeyframe[]>;
  activeCameraId: string | null;
  viewportState: ViewportState;
  viewOptions: ViewOptions;
  project: {
    composition: { fps: number };
    meta: { modified: string };
  };
  currentFrame: number;
  getActiveComp(): { settings: { width: number; height: number; frameCount: number } } | null;
  getActiveCompLayers(): Layer[];
  pushHistory(): void;
  selectLayer(layerId: string): void;
}

/**
 * Create a new camera and corresponding layer
 */
export function createCameraLayer(
  store: CameraStore,
  name?: string
): { camera: Camera3D; layer: Layer } {
  const comp = store.getActiveComp();
  const layers = store.getActiveCompLayers();

  const cameraId = `camera_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
  const cameraName = name || `Camera ${store.cameras.size + 1}`;

  // Create the camera object
  const camera = createDefaultCamera(
    cameraId,
    comp?.settings.width || 1024,
    comp?.settings.height || 1024
  );
  camera.name = cameraName;

  // Add to cameras map
  store.cameras.set(cameraId, camera);

  // If this is the first camera, make it active
  if (!store.activeCameraId) {
    store.activeCameraId = cameraId;
  }

  // Create the layer
  const layerId = `layer_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
  const frameCount = (comp?.settings.frameCount || 81) - 1;
  const layer: Layer = {
    id: layerId,
    name: cameraName,
    type: 'camera',
    visible: true,
    locked: false,
    isolate: false,
    threeD: true,
    motionBlur: false,
    // Timing (primary properties)
    startFrame: 0,
    endFrame: frameCount,
    // Backwards compatibility aliases
    inPoint: 0,
    outPoint: frameCount,
    parentId: null,
    blendMode: 'normal',
    opacity: createAnimatableProperty('opacity', 100, 'number'),
    transform: createDefaultTransform(),
    properties: [],
    effects: [],
    data: {
      cameraId,
      isActiveCamera: !store.activeCameraId || store.activeCameraId === cameraId
    } as CameraLayerData
  };

  layers.unshift(layer);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  // Auto-select the new camera layer
  store.selectLayer(layerId);

  return { camera, layer };
}

/**
 * Get a camera by ID
 */
export function getCamera(store: CameraStore, cameraId: string): Camera3D | null {
  return store.cameras.get(cameraId) || null;
}

/**
 * Update camera properties
 */
export function updateCamera(
  store: CameraStore,
  cameraId: string,
  updates: Partial<Camera3D>
): void {
  const camera = store.cameras.get(cameraId);
  if (!camera) return;

  Object.assign(camera, updates);
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Set the active camera
 */
export function setActiveCamera(store: CameraStore, cameraId: string): void {
  if (!store.cameras.has(cameraId)) return;

  store.activeCameraId = cameraId;

  // Update all camera layers' isActiveCamera flag
  const layers = store.getActiveCompLayers();
  for (const layer of layers) {
    if (layer.type === 'camera' && layer.data) {
      const cameraData = layer.data as CameraLayerData;
      cameraData.isActiveCamera = cameraData.cameraId === cameraId;
    }
  }

  store.project.meta.modified = new Date().toISOString();
}

/**
 * Delete a camera (and its layer)
 */
export function deleteCamera(store: CameraStore, cameraId: string): void {
  const layers = store.getActiveCompLayers();

  // Find the associated layer
  const layerIndex = layers.findIndex(
    l => l.type === 'camera' && (l.data as CameraLayerData)?.cameraId === cameraId
  );

  // Remove the layer if found
  if (layerIndex !== -1) {
    const layerId = layers[layerIndex].id;
    layers.splice(layerIndex, 1);
    useSelectionStore().removeFromSelection(layerId);
  }

  // Remove camera keyframes
  store.cameraKeyframes.delete(cameraId);

  // Remove the camera
  store.cameras.delete(cameraId);

  // If this was the active camera, select another or set to null
  if (store.activeCameraId === cameraId) {
    const remaining = Array.from(store.cameras.keys());
    store.activeCameraId = remaining.length > 0 ? remaining[0] : null;

    // Update layer flags
    if (store.activeCameraId) {
      setActiveCamera(store, store.activeCameraId);
    }
  }

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Get camera keyframes for a specific camera
 */
export function getCameraKeyframes(
  store: CameraStore,
  cameraId: string
): CameraKeyframe[] {
  return store.cameraKeyframes.get(cameraId) || [];
}

/**
 * Add a keyframe to a camera
 */
export function addCameraKeyframe(
  store: CameraStore,
  cameraId: string,
  keyframe: CameraKeyframe
): void {
  let keyframes = store.cameraKeyframes.get(cameraId);
  if (!keyframes) {
    keyframes = [];
    store.cameraKeyframes.set(cameraId, keyframes);
  }

  // Remove existing keyframe at same frame (use framesEqual to handle NaN)
  const existingIndex = keyframes.findIndex(k => framesEqual(k.frame, keyframe.frame));
  if (existingIndex >= 0) {
    keyframes[existingIndex] = keyframe;
  } else {
    keyframes.push(keyframe);
    // Keep sorted by frame
    keyframes.sort((a, b) => a.frame - b.frame);
  }

  store.project.meta.modified = new Date().toISOString();
}

/**
 * Remove a keyframe from a camera
 */
export function removeCameraKeyframe(
  store: CameraStore,
  cameraId: string,
  frame: number
): void {
  const keyframes = store.cameraKeyframes.get(cameraId);
  if (!keyframes) return;

  const index = keyframes.findIndex(k => framesEqual(k.frame, frame));
  if (index >= 0) {
    keyframes.splice(index, 1);
    store.project.meta.modified = new Date().toISOString();
  }
}

/**
 * Get camera with keyframe interpolation applied at a specific frame
 */
export function getCameraAtFrame(
  store: CameraStore,
  cameraId: string,
  frame: number
): Camera3D | null {
  const camera = store.cameras.get(cameraId);
  if (!camera) return null;

  const keyframes = store.cameraKeyframes.get(cameraId);
  if (!keyframes || keyframes.length === 0) {
    return camera; // No animation, return base camera
  }

  // Validate frame before passing to interpolation
  const validFrame = safeFrame(frame, 0);
  const interpolated = interpolateCameraAtFrame(camera, keyframes, validFrame);

  // Merge interpolated values back onto camera (return modified copy, not original)
  return {
    ...camera,
    position: interpolated.position,
    orientation: interpolated.rotation,
    focalLength: interpolated.focalLength,
    zoom: interpolated.zoom,
    depthOfField: {
      ...camera.depthOfField,
      focusDistance: interpolated.focusDistance,
    },
  };
}

/**
 * Get the active camera with interpolation at current frame
 */
export function getActiveCameraAtFrame(
  store: CameraStore,
  frame?: number
): Camera3D | null {
  if (!store.activeCameraId) return null;
  // Use safeFrame to handle NaN (nullish coalescing doesn't catch NaN)
  const targetFrame = safeFrame(frame, store.currentFrame);
  return getCameraAtFrame(store, store.activeCameraId, targetFrame);
}

/**
 * Update viewport state
 */
export function updateViewportState(
  store: CameraStore,
  updates: Partial<ViewportState>
): void {
  Object.assign(store.viewportState, updates);
}

/**
 * Update view options
 */
export function updateViewOptions(
  store: CameraStore,
  updates: Partial<ViewOptions>
): void {
  Object.assign(store.viewOptions, updates);
}
