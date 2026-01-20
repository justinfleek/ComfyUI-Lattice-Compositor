/**
 * Camera Store
 *
 * Domain store for 3D camera operations.
 * Contains camera management, keyframes, and interpolation logic.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md Phase 4
 */

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
function safeFrame(frame: number | undefined | null, fallback = 0): number {
  return Number.isFinite(frame) ? frame! : fallback;
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
    activeCamera(): Camera3D | null {
      if (!this.activeCameraId) return null;
      return this.cameras.get(this.activeCameraId) || null;
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

      const camera = createDefaultCamera(
        cameraId,
        comp?.settings.width || 1024,
        comp?.settings.height || 1024,
      );
      camera.name = cameraName;

      this.cameras.set(cameraId, camera);

      if (!this.activeCameraId) {
        this.activeCameraId = cameraId;
      }

      const layerId = `layer_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
      const frameCount = (comp?.settings.frameCount || 81) - 1;
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
        (l) =>
          l.type === "camera" && (l.data as CameraLayerData)?.cameraId === cameraId,
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
      return this.cameraKeyframes.get(cameraId) || [];
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

    getCameraAtFrame(cameraId: string, frame: number): Camera3D | null {
      const camera = this.cameras.get(cameraId);
      if (!camera) return null;

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

    getActiveCameraAtFrame(frame?: number): Camera3D | null {
      if (!this.activeCameraId) return null;
      const animationStore = useAnimationStore();
      const projectStore = useProjectStore();
      const currentFrame = projectStore.getActiveComp()?.currentFrame ?? 0;
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
