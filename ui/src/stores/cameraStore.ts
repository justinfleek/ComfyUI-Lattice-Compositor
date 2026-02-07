/**
 * Camera Store
 *
 * Domain store for 3D camera operations.
 * Contains camera management, keyframes, and interpolation logic.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md Phase 4
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import { defineStore } from "pinia";
import { interpolateCameraAtFrame } from "@/services/export/cameraExportFormats";
import type {
  Camera3D,
  CameraKeyframe,
  ViewOptions,
  ViewportState,
} from "@/types/camera";
import { createDefaultCamera, createDefaultViewportState, createDefaultViewOptions } from "@/types/camera";
import type { CameraLayerData, Layer } from "@/types/project";
import {
  createAnimatableProperty,
  createDefaultTransform,
} from "@/types/project";
import { useLayerStore } from "@/stores/layerStore";
import { useSelectionStore } from "./selectionStore";
import { useProjectStore } from "./projectStore";
import { useAnimationStore } from "./animationStore";

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

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
/**
 * Safe frame number with explicit validation
 * Deterministic: Explicit null check - Number.isFinite ensures frame is finite number
 */
function safeFrame(frame: number | undefined | null, fallback = 0): number {
  if (frame !== undefined && frame !== null && typeof frame === "number" && Number.isFinite(frame)) {
    return frame;
  }
  return fallback;
}

// ============================================================================
// STORE ACCESS INTERFACE
// ============================================================================

/**
 * Interface for compositorStore access during transition period.
 * Will be removed in Phase 5 when compositorStore is deleted.
 */
export interface CameraStoreAccess {
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
  getActiveComp(): {
    settings: { width: number; height: number; frameCount: number };
  } | null;
  getActiveCompLayers(): Layer[];
  pushHistory(): void;
  selectLayer(layerId: string): void;
}

// ============================================================================
// PINIA STORE
// ============================================================================

export const useCameraStore = defineStore("camera", {
  state: () => ({
    cameras: new Map<string, Camera3D>(),
    cameraKeyframes: new Map<string, CameraKeyframe[]>(),
    activeCameraId: null as string | null,
    viewportState: createDefaultViewportState(),
    viewOptions: createDefaultViewOptions(),
  }),
  
  getters: {
    activeCamera(): Camera3D {
      if (!this.activeCameraId) {
        throw new Error("[CameraStore] Cannot get active camera: No active camera ID set");
      }
      const camera = this.cameras.get(this.activeCameraId);
      if (!camera) {
        throw new Error(`[CameraStore] Cannot get active camera: Camera "${this.activeCameraId}" not found`);
      }
      return camera;
    },
    allCameras(): Camera3D[] {
      return Array.from(this.cameras.values());
    },
  },
  
  actions: {
    // ========================================================================
    // Camera CRUD
    // ========================================================================

    createCameraLayer(name?: string): { camera: Camera3D; layer: Layer } {
      const projectStore = useProjectStore();
      const comp = projectStore.getActiveComp();
      const layers = projectStore.getActiveCompLayers();

      const cameraId = `camera_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
      const cameraName = name || `Camera ${this.cameras.size + 1}`;

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const compSettings = (comp != null && typeof comp === "object" && "settings" in comp && comp.settings != null && typeof comp.settings === "object") ? comp.settings : undefined;
      const compWidth = (compSettings != null && typeof compSettings === "object" && "width" in compSettings && typeof compSettings.width === "number") ? compSettings.width : undefined;
      const compHeight = (compSettings != null && typeof compSettings === "object" && "height" in compSettings && typeof compSettings.height === "number") ? compSettings.height : undefined;
      const camera = createDefaultCamera(
        cameraId,
        compWidth != null ? compWidth : 1024,
        compHeight != null ? compHeight : 1024,
      );
      camera.name = cameraName;

      this.cameras.set(cameraId, camera);

      if (!this.activeCameraId) {
        this.activeCameraId = cameraId;
      }

      const layerId = `layer_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
      const compFrameCount = (compSettings != null && typeof compSettings === "object" && "frameCount" in compSettings && typeof compSettings.frameCount === "number") ? compSettings.frameCount : undefined;
      const frameCount = (compFrameCount != null ? compFrameCount : 81) - 1;
      const layer: Layer = {
        id: layerId,
        name: cameraName,
        type: "camera",
        visible: true,
        locked: false,
        isolate: false,
        threeD: true,
        motionBlur: false,
        startFrame: 0,
        endFrame: frameCount,
        inPoint: 0,
        outPoint: frameCount,
        parentId: null,
        blendMode: "normal",
        opacity: createAnimatableProperty("opacity", 100, "number"),
        transform: createDefaultTransform(),
        properties: [],
        effects: [],
        data: {
          cameraId,
          isActiveCamera: !this.activeCameraId || this.activeCameraId === cameraId,
        } as CameraLayerData,
      };

      layers.unshift(layer);
      projectStore.project.meta.modified = new Date().toISOString();
      projectStore.pushHistory();

      useSelectionStore().selectLayer(layerId);

      return { camera, layer };
    },

    getCamera(cameraId: string): Camera3D | null {
      return this.cameras.get(cameraId) || null;
    },

    updateCamera(cameraId: string, updates: Partial<Camera3D>): void {
      const camera = this.cameras.get(cameraId);
      if (!camera) return;

      Object.assign(camera, updates);
      const projectStore = useProjectStore();
      projectStore.project.meta.modified = new Date().toISOString();
    },

    setActiveCamera(cameraId: string): void {
      if (!this.cameras.has(cameraId)) return;

      this.activeCameraId = cameraId;

      const projectStore = useProjectStore();
      const layers = projectStore.getActiveCompLayers();
      for (const layer of layers) {
        if (layer.type === "camera" && layer.data) {
          const cameraData = layer.data as CameraLayerData;
          cameraData.isActiveCamera = cameraData.cameraId === cameraId;
        }
      }

      projectStore.project.meta.modified = new Date().toISOString();
    },

    deleteCamera(cameraId: string): void {
      const projectStore = useProjectStore();
      const layers = projectStore.getActiveCompLayers();

      const layerIndex = layers.findIndex(
        (l) => {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          const layerData = (l != null && typeof l === "object" && "data" in l && l.data != null) ? l.data as CameraLayerData : undefined;
          const layerCameraId = (layerData != null && typeof layerData === "object" && "cameraId" in layerData && typeof layerData.cameraId === "string") ? layerData.cameraId : undefined;
          return l.type === "camera" && layerCameraId === cameraId;
        },
      );

      if (layerIndex !== -1) {
        const layerId = layers[layerIndex].id;
        layers.splice(layerIndex, 1);
        useSelectionStore().removeFromSelection(layerId);
      }

      this.cameraKeyframes.delete(cameraId);
      this.cameras.delete(cameraId);

      if (this.activeCameraId === cameraId) {
        const remaining = Array.from(this.cameras.keys());
        this.activeCameraId = remaining.length > 0 ? remaining[0] : null;

        if (this.activeCameraId) {
          this.setActiveCamera(this.activeCameraId);
        }
      }

      projectStore.project.meta.modified = new Date().toISOString();
      projectStore.pushHistory();
    },

    // ========================================================================
    // Camera Keyframes
    // ========================================================================

    getCameraKeyframes(cameraId: string): CameraKeyframe[] {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      const keyframes = this.cameraKeyframes.get(cameraId);
      return (keyframes !== null && keyframes !== undefined && Array.isArray(keyframes)) ? keyframes : [];
    },

    addCameraKeyframe(cameraId: string, keyframe: CameraKeyframe): void {
      let keyframes = this.cameraKeyframes.get(cameraId);
      if (!keyframes) {
        keyframes = [];
        this.cameraKeyframes.set(cameraId, keyframes);
      }

      const existingIndex = keyframes.findIndex((k) =>
        framesEqual(k.frame, keyframe.frame),
      );
      if (existingIndex >= 0) {
        keyframes[existingIndex] = keyframe;
      } else {
        keyframes.push(keyframe);
        keyframes.sort((a, b) => a.frame - b.frame);
      }

      const projectStore = useProjectStore();
      projectStore.project.meta.modified = new Date().toISOString();
    },

    removeCameraKeyframe(cameraId: string, frame: number): void {
      const keyframes = this.cameraKeyframes.get(cameraId);
      if (!keyframes) return;

      const index = keyframes.findIndex((k) => framesEqual(k.frame, frame));
      if (index >= 0) {
        keyframes.splice(index, 1);
        const projectStore = useProjectStore();
        projectStore.project.meta.modified = new Date().toISOString();
      }
    },

    // ========================================================================
    // Camera Interpolation
    // ========================================================================

    getCameraAtFrame(cameraId: string, frame: number): Camera3D {
      const camera = this.cameras.get(cameraId);
      if (!camera) {
        throw new Error(`[CameraStore] Cannot get camera at frame: Camera "${cameraId}" not found`);
      }

      const keyframes = this.cameraKeyframes.get(cameraId);
      if (!keyframes || keyframes.length === 0) {
        return camera;
      }

      const validFrame = safeFrame(frame, 0);
      const interpolated = interpolateCameraAtFrame(camera, keyframes, validFrame);

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
    },

    getActiveCameraAtFrame(frame?: number): Camera3D {
      if (!this.activeCameraId) {
        throw new Error("[CameraStore] Cannot get active camera at frame: No active camera ID set");
      }
      const animationStore = useAnimationStore();
      const projectStore = useProjectStore();
      // Type proof: currentFrame ∈ ℕ ∪ {undefined} → ℕ
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const activeComp = projectStore.getActiveComp();
      const compCurrentFrameValue = (activeComp != null && typeof activeComp === "object" && "currentFrame" in activeComp && typeof activeComp.currentFrame === "number") ? activeComp.currentFrame : undefined;
      const currentFrame = isFiniteNumber(compCurrentFrameValue) && Number.isInteger(compCurrentFrameValue) && compCurrentFrameValue >= 0 ? compCurrentFrameValue : 0;
      const targetFrame = safeFrame(frame, currentFrame);
      return this.getCameraAtFrame(this.activeCameraId, targetFrame);
    },

    updateViewportState(updates: Partial<ViewportState>): void {
      Object.assign(this.viewportState, updates);
    },

    updateViewOptions(updates: Partial<ViewOptions>): void {
      Object.assign(this.viewOptions, updates);
    },
  },
});
