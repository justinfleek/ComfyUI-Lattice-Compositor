/**
 * Viewport Guides Composable
 *
 * Handles computation of resolution crop guides and safe frame overlays
 * for the ThreeCanvas viewport.
 */

import { ref, computed, type Ref, type ComputedRef } from 'vue';
import * as THREE from 'three';
import { useCompositorStore } from '@/stores/compositorStore';
import type { LatticeEngine } from '@/engine';

export interface SafeFrameBounds {
  left: number;
  top: number;
  right: number;
  bottom: number;
}

export interface ResolutionGuide {
  name: string;
  color: string;
  resolution: string;
  visible: boolean;
  style: {
    left: string;
    top: string;
    width: string;
    height: string;
    borderColor: string;
  };
}

// Standard resolution presets
const RESOLUTION_PRESETS = [
  { name: '480p', width: 854, height: 480, color: '#F59E0B' },   // Amber
  { name: '720p', width: 1280, height: 720, color: '#8B5CF6' },  // Purple
  { name: '1080p', width: 1920, height: 1080, color: '#06B6D4' } // Cyan
];

export interface UseViewportGuidesOptions {
  containerRef: Ref<HTMLDivElement | null>;
  engine: Ref<LatticeEngine | null>;
  canvasWidth: Ref<number>;
  canvasHeight: Ref<number>;
  zoom: Ref<number>;
  viewportTransform: Ref<number[]>;
}

export function useViewportGuides(options: UseViewportGuidesOptions) {
  const {
    containerRef,
    engine,
    canvasWidth,
    canvasHeight,
    zoom,
    viewportTransform
  } = options;

  const store = useCompositorStore();

  // Camera update trigger - increment to force boundary recalculation
  const cameraUpdateTrigger = ref(0);

  // Guide visibility toggles
  const showSafeFrameGuides = ref(false);
  const showResolutionGuides = ref(true);

  /**
   * Force update of guide positions (call after camera changes)
   */
  function triggerGuideUpdate() {
    cameraUpdateTrigger.value++;
  }

  /**
   * Safe frame guide positions - CSS-based overlays for out-of-frame areas
   * Project the 3D composition bounds to screen space for accurate overlay positioning
   */
  const safeFrameBounds: ComputedRef<SafeFrameBounds> = computed(() => {
    // Reactive dependencies: these trigger recompute when camera changes
    // eslint-disable-next-line @typescript-eslint/no-unused-vars
    const _ = [zoom.value, viewportTransform.value, canvasWidth.value, canvasHeight.value, cameraUpdateTrigger.value];

    if (!containerRef.value || !engine.value) {
      return { left: 0, top: 0, right: 0, bottom: 0 };
    }

    const viewportWidth = canvasWidth.value;
    const viewportHeight = canvasHeight.value;
    const compWidth = store.width || 1920;
    const compHeight = store.height || 1080;

    // Check for valid viewport dimensions
    if (viewportWidth <= 0 || viewportHeight <= 0) {
      return { left: 0, top: 0, right: 0, bottom: 0 };
    }

    // Get the camera to project 3D points to screen
    const camera = engine.value.getCameraController().camera;

    // Ensure camera matrices are up to date
    camera.updateMatrixWorld(true);
    camera.updateProjectionMatrix();

    // Composition corners in world space (Y is negated in Three.js coordinate system)
    const topLeft = new THREE.Vector3(0, 0, 0);
    const bottomRight = new THREE.Vector3(compWidth, -compHeight, 0);

    // Project to normalized device coordinates (-1 to 1)
    topLeft.project(camera);
    bottomRight.project(camera);

    // Convert to screen pixels
    const left = (topLeft.x + 1) / 2 * viewportWidth;
    const top = (-topLeft.y + 1) / 2 * viewportHeight;
    const right = (bottomRight.x + 1) / 2 * viewportWidth;
    const bottom = (-bottomRight.y + 1) / 2 * viewportHeight;

    return { left, top, right, bottom };
  });

  // Safe frame overlay styles
  const safeFrameLeftStyle = computed(() => {
    const bounds = safeFrameBounds.value;
    return {
      left: '0',
      top: '0',
      width: `${Math.max(0, bounds.left)}px`,
      height: '100%'
    };
  });

  const safeFrameRightStyle = computed(() => {
    const bounds = safeFrameBounds.value;
    return {
      left: `${bounds.right}px`,
      top: '0',
      width: `calc(100% - ${bounds.right}px)`,
      height: '100%'
    };
  });

  const safeFrameTopStyle = computed(() => {
    const bounds = safeFrameBounds.value;
    return {
      left: `${Math.max(0, bounds.left)}px`,
      top: '0',
      width: `${bounds.right - Math.max(0, bounds.left)}px`,
      height: `${Math.max(0, bounds.top)}px`
    };
  });

  const safeFrameBottomStyle = computed(() => {
    const bounds = safeFrameBounds.value;
    return {
      left: `${Math.max(0, bounds.left)}px`,
      top: `${bounds.bottom}px`,
      width: `${bounds.right - Math.max(0, bounds.left)}px`,
      height: `calc(100% - ${bounds.bottom}px)`
    };
  });

  /**
   * CSS-based composition boundary - always crisp regardless of zoom
   * Uses the same projection as safeFrameBounds but renders as a border
   */
  const compositionBoundaryStyle = computed(() => {
    const bounds = safeFrameBounds.value;
    const width = bounds.right - bounds.left;
    const height = bounds.bottom - bounds.top;

    // Only show if the bounds are valid
    if (width <= 0 || height <= 0) {
      return { display: 'none' };
    }

    return {
      left: `${bounds.left}px`,
      top: `${bounds.top}px`,
      width: `${width}px`,
      height: `${height}px`
    };
  });

  /**
   * Resolution crop guides - center-based boxes for standard resolutions
   * These show where 480p/720p/1080p would crop from center of the composition
   */
  const resolutionCropGuides: ComputedRef<ResolutionGuide[]> = computed(() => {
    // Reactive dependencies
    // eslint-disable-next-line @typescript-eslint/no-unused-vars
    const _ = [zoom.value, viewportTransform.value, canvasWidth.value, canvasHeight.value, cameraUpdateTrigger.value];

    if (!containerRef.value || !engine.value) {
      return [];
    }

    const viewportWidth = canvasWidth.value;
    const viewportHeight = canvasHeight.value;
    const compWidth = store.width || 1920;
    const compHeight = store.height || 1080;

    // Check for valid dimensions
    if (viewportWidth <= 0 || viewportHeight <= 0 || compWidth <= 0 || compHeight <= 0) {
      return [];
    }

    // Get the camera to project 3D points to screen
    const camera = engine.value.getCameraController().camera;

    const guides: ResolutionGuide[] = [];

    for (const preset of RESOLUTION_PRESETS) {
      // Only show guides for resolutions smaller than or equal to the composition
      if (preset.width > compWidth || preset.height > compHeight) {
        continue;
      }

      // Calculate the 3D bounds for this resolution crop (center-based)
      const halfCropWidth = preset.width / 2;
      const halfCropHeight = preset.height / 2;

      // Project corner points to screen space
      const topLeft3D = new THREE.Vector3(-halfCropWidth, halfCropHeight, 0);
      const bottomRight3D = new THREE.Vector3(halfCropWidth, -halfCropHeight, 0);

      topLeft3D.project(camera);
      bottomRight3D.project(camera);

      // Convert from NDC (-1 to 1) to screen pixels
      const left = (topLeft3D.x + 1) / 2 * viewportWidth;
      const top = (-topLeft3D.y + 1) / 2 * viewportHeight;
      const right = (bottomRight3D.x + 1) / 2 * viewportWidth;
      const bottom = (-bottomRight3D.y + 1) / 2 * viewportHeight;

      const boxWidth = right - left;
      const boxHeight = bottom - top;

      // Only show if the box has valid dimensions and is visible
      if (boxWidth > 0 && boxHeight > 0) {
        guides.push({
          name: preset.name,
          color: preset.color,
          resolution: `${preset.width}×${preset.height}`,
          visible: true,
          style: {
            left: `${left}px`,
            top: `${top}px`,
            width: `${boxWidth}px`,
            height: `${boxHeight}px`,
            borderColor: preset.color
          }
        });
      }
    }

    return guides;
  });

  /**
   * Toggle safe frame guides visibility
   */
  function toggleSafeFrameGuides() {
    showSafeFrameGuides.value = !showSafeFrameGuides.value;
  }

  /**
   * Toggle resolution crop guides visibility
   */
  function toggleResolutionGuides() {
    showResolutionGuides.value = !showResolutionGuides.value;
  }

  return {
    // State
    showSafeFrameGuides,
    showResolutionGuides,
    cameraUpdateTrigger,

    // Computed
    safeFrameBounds,
    safeFrameLeftStyle,
    safeFrameRightStyle,
    safeFrameTopStyle,
    safeFrameBottomStyle,
    compositionBoundaryStyle,
    resolutionCropGuides,

    // Methods
    triggerGuideUpdate,
    toggleSafeFrameGuides,
    toggleResolutionGuides
  };
}
