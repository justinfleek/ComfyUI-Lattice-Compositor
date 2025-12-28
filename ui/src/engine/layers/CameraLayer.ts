/**
 * CameraLayer - Camera Transform Layer
 *
 * Represents a camera in the composition that can be:
 * - Positioned and animated in 3D space
 * - Used as the active render camera
 * - Exported for ComfyUI workflows (MotionCtrl, CameraCtrl, etc.)
 *
 * The actual Camera3D data is stored in the compositor store.
 * This layer links to it via cameraId and provides:
 * - Visual wireframe representation in editor
 * - Transform hierarchy participation
 * - Keyframe evaluation for camera properties
 */

import * as THREE from 'three';
import type { Layer, CameraLayerData, CameraPathFollowing } from '@/types/project';
import type { Camera3D } from '@/types/camera';
import type { SplineQueryResult } from '@/services/particleSystem';
import { interpolateProperty } from '@/services/interpolation';
import { BaseLayer } from './BaseLayer';

/** Spline path provider callback type for camera path following */
export type CameraSplineProvider = (
  layerId: string,
  t: number,
  frame: number
) => SplineQueryResult | null;

// ============================================================================
// TYPES
// ============================================================================

/** Callback to get Camera3D data from store */
export type CameraGetter = (cameraId: string) => Camera3D | null;

/** Callback to get Camera3D data with keyframe interpolation at a specific frame */
export type CameraAtFrameGetter = (cameraId: string, frame: number) => Camera3D | null;

/** Callback to update Camera3D data in store */
export type CameraUpdater = (cameraId: string, updates: Partial<Camera3D>) => void;

// ============================================================================
// CAMERA LAYER
// ============================================================================

export class CameraLayer extends BaseLayer {
  // Camera data reference
  private cameraData: CameraLayerData;

  // Callbacks to store
  private cameraGetter?: CameraGetter;
  private cameraAtFrameGetter?: CameraAtFrameGetter;
  private cameraUpdater?: CameraUpdater;

  // Track current frame for interpolation
  private currentFrame: number = 0;

  // Visual wireframe (shown in editor)
  private wireframe: THREE.Group | null = null;
  private wireframeVisible: boolean = true;

  // Frustum visualization
  private frustumHelper: THREE.Group | null = null;
  private showFrustum: boolean = true;

  // Track last camera state for frustum updates
  private lastFrustumState: { fov: number; near: number; far: number; aspect: number } | null = null;

  // Composition aspect ratio for frustum visualization
  private compositionAspect: number = 16 / 9;

  // Spline provider for path following
  private splineProvider: CameraSplineProvider | null = null;

  // Auto-advance parameter (for autoAdvance mode)
  private autoAdvanceT: number = 0;

  constructor(layerData: Layer) {
    super(layerData);

    // Camera layers are always 3D
    this.threeD = true;

    // Extract camera data
    this.cameraData = this.extractCameraData(layerData);

    // Create visual representation
    this.createWireframe();
  }

  // ============================================================================
  // INITIALIZATION
  // ============================================================================

  /**
   * Extract camera layer data with defaults
   */
  private extractCameraData(layerData: Layer): CameraLayerData {
    const data = layerData.data as CameraLayerData | null;

    return {
      cameraId: data?.cameraId ?? '',
      isActiveCamera: data?.isActiveCamera ?? false,
      pathFollowing: data?.pathFollowing,
    };
  }

  /**
   * Set callbacks to access Camera3D data from store
   */
  setCameraCallbacks(
    getter: CameraGetter,
    updater: CameraUpdater,
    atFrameGetter?: CameraAtFrameGetter
  ): void {
    this.cameraGetter = getter;
    this.cameraUpdater = updater;
    this.cameraAtFrameGetter = atFrameGetter;
  }

  /**
   * Set the spline provider for path following
   */
  setSplineProvider(provider: CameraSplineProvider | null): void {
    this.splineProvider = provider;
  }

  /**
   * Set composition aspect ratio for frustum visualization
   */
  setCompositionAspect(aspect: number): void {
    // Validate aspect ratio (NaN/0 would corrupt frustum calculations)
    this.compositionAspect = (Number.isFinite(aspect) && aspect > 0) ? aspect : 16 / 9;
  }

  /**
   * Get path following configuration
   */
  getPathFollowing(): CameraPathFollowing | undefined {
    return this.cameraData.pathFollowing;
  }

  /**
   * Check if path following is active
   */
  isFollowingPath(): boolean {
    return this.cameraData.pathFollowing?.enabled ?? false;
  }

  /**
   * Reset auto-advance parameter (for deterministic scrubbing)
   */
  resetAutoAdvance(): void {
    this.autoAdvanceT = 0;
  }

  // ============================================================================
  // WIREFRAME VISUALIZATION
  // ============================================================================

  /**
   * Create camera wireframe indicator
   */
  private createWireframe(): void {
    this.wireframe = new THREE.Group();
    this.wireframe.name = `camera_wireframe_${this.id}`;

    const color = this.cameraData.isActiveCamera ? 0x00aaff : 0xffaa00;

    // Camera body (box)
    const bodySize = 40;
    const bodyGeometry = new THREE.BoxGeometry(bodySize, bodySize * 0.6, bodySize * 0.8);
    const bodyMaterial = new THREE.MeshBasicMaterial({
      color,
      wireframe: true,
      transparent: true,
      opacity: 0.8,
      depthTest: false,
    });
    const body = new THREE.Mesh(bodyGeometry, bodyMaterial);
    this.wireframe.add(body);

    // Lens cone
    const coneGeometry = new THREE.ConeGeometry(bodySize * 0.3, bodySize * 0.6, 8);
    const coneMaterial = new THREE.MeshBasicMaterial({
      color,
      wireframe: true,
      transparent: true,
      opacity: 0.6,
      depthTest: false,
    });
    const cone = new THREE.Mesh(coneGeometry, coneMaterial);
    cone.rotation.x = Math.PI / 2;
    cone.position.z = bodySize * 0.7;
    this.wireframe.add(cone);

    // Film plane indicator
    const planeGeometry = new THREE.PlaneGeometry(bodySize * 0.8, bodySize * 0.5);
    const planeMaterial = new THREE.MeshBasicMaterial({
      color,
      transparent: true,
      opacity: 0.2,
      side: THREE.DoubleSide,
      depthTest: false,
    });
    const plane = new THREE.Mesh(planeGeometry, planeMaterial);
    plane.position.z = -bodySize * 0.4;
    this.wireframe.add(plane);

    // Up vector indicator
    const upPoints = [
      new THREE.Vector3(0, bodySize * 0.4, 0),
      new THREE.Vector3(0, bodySize * 0.7, 0),
      new THREE.Vector3(-bodySize * 0.1, bodySize * 0.55, 0),
      new THREE.Vector3(0, bodySize * 0.7, 0),
      new THREE.Vector3(bodySize * 0.1, bodySize * 0.55, 0),
    ];
    const upGeometry = new THREE.BufferGeometry().setFromPoints(upPoints);
    const upMaterial = new THREE.LineBasicMaterial({
      color: 0x00ff00,
      transparent: true,
      opacity: 0.8,
      depthTest: false,
    });
    const upLine = new THREE.Line(upGeometry, upMaterial);
    this.wireframe.add(upLine);

    // Add to group
    this.group.add(this.wireframe);
    this.wireframe.renderOrder = 998;
  }

  /**
   * Create frustum visualization
   */
  private createFrustum(): void {
    const camera = this.getCamera();
    if (!camera) return;

    this.frustumHelper = new THREE.Group();
    this.frustumHelper.name = `camera_frustum_${this.id}`;

    const color = this.cameraData.isActiveCamera ? 0x00aaff : 0xffaa00;

    // Calculate frustum dimensions based on camera properties
    // Validate all camera values (NaN would corrupt geometry calculations)
    const near = (Number.isFinite(camera.nearClip) && camera.nearClip > 0) ? camera.nearClip : 0.1;
    const rawFar = Number.isFinite(camera.farClip) ? camera.farClip : 1000;
    const far = Math.min(rawFar, 2000); // Cap for visualization
    const rawAngle = Number.isFinite(camera.angleOfView) ? camera.angleOfView : 50;
    const fov = rawAngle * (Math.PI / 180);
    const aspect = this.compositionAspect;

    const nearHeight = 2 * Math.tan(fov / 2) * near;
    const nearWidth = nearHeight * aspect;
    const farHeight = 2 * Math.tan(fov / 2) * far;
    const farWidth = farHeight * aspect;

    // Frustum lines
    const frustumMaterial = new THREE.LineBasicMaterial({
      color,
      transparent: true,
      opacity: 0.3,
      depthTest: false,
    });

    // Near plane corners
    const nearTL = new THREE.Vector3(-nearWidth / 2, nearHeight / 2, near);
    const nearTR = new THREE.Vector3(nearWidth / 2, nearHeight / 2, near);
    const nearBL = new THREE.Vector3(-nearWidth / 2, -nearHeight / 2, near);
    const nearBR = new THREE.Vector3(nearWidth / 2, -nearHeight / 2, near);

    // Far plane corners
    const farTL = new THREE.Vector3(-farWidth / 2, farHeight / 2, far);
    const farTR = new THREE.Vector3(farWidth / 2, farHeight / 2, far);
    const farBL = new THREE.Vector3(-farWidth / 2, -farHeight / 2, far);
    const farBR = new THREE.Vector3(farWidth / 2, -farHeight / 2, far);

    // Near plane
    const nearPlane = new THREE.BufferGeometry().setFromPoints([
      nearTL, nearTR, nearBR, nearBL, nearTL
    ]);
    this.frustumHelper.add(new THREE.Line(nearPlane, frustumMaterial));

    // Far plane
    const farPlane = new THREE.BufferGeometry().setFromPoints([
      farTL, farTR, farBR, farBL, farTL
    ]);
    this.frustumHelper.add(new THREE.Line(farPlane, frustumMaterial));

    // Connecting lines
    const edges = [
      [nearTL, farTL], [nearTR, farTR],
      [nearBL, farBL], [nearBR, farBR]
    ];

    for (const [start, end] of edges) {
      const edgeGeom = new THREE.BufferGeometry().setFromPoints([start, end]);
      this.frustumHelper.add(new THREE.Line(edgeGeom, frustumMaterial));
    }

    this.group.add(this.frustumHelper);
    this.frustumHelper.renderOrder = 997;
    this.frustumHelper.visible = this.showFrustum;
  }

  /**
   * Update wireframe color based on active state
   */
  private updateWireframeColor(): void {
    if (!this.wireframe) return;

    const color = this.cameraData.isActiveCamera ? 0x00aaff : 0xffaa00;

    this.wireframe.traverse((child) => {
      if (child instanceof THREE.Mesh || child instanceof THREE.Line) {
        // Skip the up vector indicator (green line)
        const material = child.material as THREE.MeshBasicMaterial | THREE.LineBasicMaterial;
        if (material.color.getHex() === 0x00ff00) return;
        material.color.setHex(color);
      }
    });
  }

  // ============================================================================
  // CAMERA ACCESS
  // ============================================================================

  /**
   * Get the linked Camera3D object (base, without interpolation)
   */
  getCamera(): Camera3D | null {
    if (!this.cameraGetter || !this.cameraData.cameraId) return null;
    return this.cameraGetter(this.cameraData.cameraId);
  }

  /**
   * Get the camera with keyframe interpolation applied at the current frame
   */
  getCameraAtCurrentFrame(): Camera3D | null {
    if (!this.cameraData.cameraId) return null;

    // If we have a frame-aware getter, use it for interpolation
    if (this.cameraAtFrameGetter) {
      return this.cameraAtFrameGetter(this.cameraData.cameraId, this.currentFrame);
    }

    // Fallback to base camera if no frame getter
    return this.getCamera();
  }

  /**
   * Get camera ID
   */
  getCameraId(): string {
    return this.cameraData.cameraId;
  }

  /**
   * Check if this is the active camera
   */
  isActiveCamera(): boolean {
    return this.cameraData.isActiveCamera;
  }

  /**
   * Set as active camera
   */
  setActiveCamera(active: boolean): void {
    this.cameraData.isActiveCamera = active;
    this.updateWireframeColor();

    // Rebuild frustum with new color
    if (this.frustumHelper) {
      this.group.remove(this.frustumHelper);
      this.disposeFrustum();
      this.createFrustum();
    }
  }

  // ============================================================================
  // VISIBILITY CONTROLS
  // ============================================================================

  /**
   * Set wireframe visibility
   */
  setWireframeVisible(visible: boolean): void {
    this.wireframeVisible = visible;
    if (this.wireframe) {
      this.wireframe.visible = visible;
    }
  }

  /**
   * Set frustum visibility
   */
  setFrustumVisible(visible: boolean): void {
    this.showFrustum = visible;
    if (this.frustumHelper) {
      this.frustumHelper.visible = visible;
    }
  }

  // ============================================================================
  // FRAME EVALUATION
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Track current frame for interpolation
    this.currentFrame = frame;

    // Get interpolated camera at current frame
    const camera = this.getCameraAtCurrentFrame();
    if (!camera) return;

    const degToRad = Math.PI / 180;

    // Check for path following
    const pathFollowing = this.cameraData.pathFollowing;
    const usePathFollowing = pathFollowing?.enabled &&
                             pathFollowing.pathLayerId &&
                             this.splineProvider;

    if (usePathFollowing && pathFollowing) {
      // Apply path following
      this.applyPathFollowing(frame, pathFollowing, camera);
    } else {
      // Standard camera positioning
      this.group.position.set(
        camera.position.x,
        camera.position.y,
        camera.position.z
      );

      // For two-node camera, orient towards point of interest
      if (camera.type === 'two-node' && camera.pointOfInterest) {
        const poi = new THREE.Vector3(
          camera.pointOfInterest.x,
          camera.pointOfInterest.y,
          camera.pointOfInterest.z
        );
        this.group.lookAt(poi);

        // Apply additional rotations
        this.group.rotation.z += camera.zRotation * degToRad;
      } else {
        // One-node camera: use direct rotation
        this.group.rotation.set(
          (camera.orientation.x + camera.xRotation) * degToRad,
          (camera.orientation.y + camera.yRotation) * degToRad,
          (camera.orientation.z + camera.zRotation) * degToRad,
          'YXZ' // Standard 3D rotation order (heading-pitch-roll)
        );
      }
    }

    // Update frustum only if camera properties changed (avoid recreating every frame)
    const currentState = {
      fov: camera.angleOfView,
      near: camera.nearClip,
      far: camera.farClip,
      aspect: this.compositionAspect,
    };

    const needsFrustumUpdate = !this.lastFrustumState ||
      this.lastFrustumState.fov !== currentState.fov ||
      this.lastFrustumState.near !== currentState.near ||
      this.lastFrustumState.far !== currentState.far ||
      this.lastFrustumState.aspect !== currentState.aspect;

    if (needsFrustumUpdate) {
      if (this.frustumHelper) {
        this.group.remove(this.frustumHelper);
        this.disposeFrustum();
      }
      this.createFrustum();
      this.lastFrustumState = currentState;
    }
  }

  protected override onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    const props = state.properties;

    // Apply evaluated path parameter if using path following
    if (props['pathParameter'] !== undefined && this.cameraData.pathFollowing?.enabled) {
      // Update the parameter value directly for the next evaluation
      this.cameraData.pathFollowing.parameter.value = props['pathParameter'] as number;
    }
    // Note: pathPosition audio modifier is applied in applyPathFollowing() where the actual
    // path query happens, ensuring it's applied regardless of evaluation path (legacy or new)
  }

  /**
   * Apply path following to camera position and orientation
   * DETERMINISM: Uses interpolateProperty for animated parameter
   */
  private applyPathFollowing(
    frame: number,
    pathFollowing: CameraPathFollowing,
    camera: Camera3D
  ): void {
    if (!this.splineProvider) return;

    // Get the path parameter (0-1)
    let t: number;

    if (pathFollowing.autoAdvance) {
      // Auto-advance mode: calculate t from frame
      // DETERMINISM: t is calculated from frame, not accumulated state
      // Validate autoAdvanceSpeed (NaN would propagate through modulo)
      const validSpeed = Number.isFinite(pathFollowing.autoAdvanceSpeed) ? pathFollowing.autoAdvanceSpeed : 0.01;
      const validFrame = Number.isFinite(frame) ? frame : 0;
      t = (validFrame * validSpeed) % 1;
    } else {
      // Manual/keyframed mode: interpolate from animated property
      t = interpolateProperty(pathFollowing.parameter, frame, this.compositionFps, this.id);
    }

    // Validate t after interpolation (could return NaN from expression)
    if (!Number.isFinite(t)) t = 0;

    // Apply pathPosition audio modifier to t
    // pathPosition is 0-1, additive to the path parameter
    const audioMod = this.currentAudioModifiers;
    if (audioMod.pathPosition !== undefined && Number.isFinite(audioMod.pathPosition) && audioMod.pathPosition !== 0) {
      t += audioMod.pathPosition;
    }

    // Clamp t to valid range (after NaN validation)
    t = Math.max(0, Math.min(1, t));

    // Query spline for current position
    const pathResult = this.splineProvider(pathFollowing.pathLayerId, t, frame);

    if (!pathResult) {
      // Fall back to camera position if spline not found
      this.group.position.set(camera.position.x, camera.position.y, camera.position.z);
      return;
    }

    // Calculate look-ahead position for orientation
    let lookTarget: SplineQueryResult | null = null;
    // Validate lookAhead (NaN would produce NaN lookAheadT)
    const validLookAhead = Number.isFinite(pathFollowing.lookAhead) ? pathFollowing.lookAhead : 0;
    if (pathFollowing.alignToPath && validLookAhead > 0) {
      const lookAheadT = Math.min(1, t + validLookAhead);
      lookTarget = this.splineProvider(pathFollowing.pathLayerId, lookAheadT, frame);
    }

    // Set camera position
    // Validate offsetY (NaN would corrupt position)
    const validOffsetY = Number.isFinite(pathFollowing.offsetY) ? pathFollowing.offsetY : 0;
    const position = new THREE.Vector3(
      pathResult.point.x,
      pathResult.point.y + validOffsetY,
      pathResult.point.z
    );
    this.group.position.copy(position);

    // Set camera orientation
    if (pathFollowing.alignToPath) {
      if (lookTarget) {
        // Look at the ahead point
        const target = new THREE.Vector3(
          lookTarget.point.x,
          lookTarget.point.y + validOffsetY,
          lookTarget.point.z
        );
        this.group.lookAt(target);
      } else {
        // Use tangent direction
        const tangent = new THREE.Vector3(
          pathResult.tangent.x,
          pathResult.tangent.y,
          0
        ).normalize();

        // Calculate rotation from tangent
        const forward = new THREE.Vector3(0, 0, 1);
        const quaternion = new THREE.Quaternion();
        quaternion.setFromUnitVectors(forward, tangent);
        this.group.quaternion.copy(quaternion);
      }

      // Apply banking on turns
      // Validate bankingStrength (NaN would corrupt rotation)
      const validBankingStrength = Number.isFinite(pathFollowing.bankingStrength) ? pathFollowing.bankingStrength : 0;
      if (validBankingStrength > 0) {
        // Calculate curvature from tangent change
        // Get tangent at slightly different positions
        const epsilon = 0.01;
        const tBefore = Math.max(0, t - epsilon);
        const tAfter = Math.min(1, t + epsilon);

        const before = this.splineProvider(pathFollowing.pathLayerId, tBefore, frame);
        const after = this.splineProvider(pathFollowing.pathLayerId, tAfter, frame);

        if (before && after) {
          // Calculate turn direction
          const tangent1 = new THREE.Vector2(before.tangent.x, before.tangent.y).normalize();
          const tangent2 = new THREE.Vector2(after.tangent.x, after.tangent.y).normalize();

          // Cross product for turn direction (positive = right turn)
          const cross = tangent1.x * tangent2.y - tangent1.y * tangent2.x;

          // Apply banking rotation (validate cross in case of zero-length tangents)
          if (Number.isFinite(cross)) {
            const bankAngle = cross * validBankingStrength * Math.PI / 4;
            this.group.rotateZ(bankAngle);
          }
        }
      }
    }
  }

  // ============================================================================
  // LAYER UPDATE
  // ============================================================================

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<CameraLayerData> | undefined;

    if (data) {
      if (data.cameraId !== undefined) {
        this.cameraData.cameraId = data.cameraId;
        // Recreate frustum with new camera data
        if (this.frustumHelper) {
          this.group.remove(this.frustumHelper);
          this.disposeFrustum();
        }
        this.createFrustum();
      }

      if (data.isActiveCamera !== undefined) {
        this.setActiveCamera(data.isActiveCamera);
      }

      if (data.pathFollowing !== undefined) {
        this.cameraData.pathFollowing = data.pathFollowing;
        // Reset auto-advance when path changes
        if (data.pathFollowing?.autoAdvance) {
          this.autoAdvanceT = 0;
        }
      }
    }
  }

  // ============================================================================
  // EXPORT HELPERS
  // ============================================================================

  /**
   * Get camera transform data for export/render
   * Returns position, rotation, and lens data at current frame (with interpolation)
   */
  getExportData(): {
    position: { x: number; y: number; z: number };
    rotation: { x: number; y: number; z: number };
    fov: number;
    focalLength: number;
    nearClip: number;
    farClip: number;
  } | null {
    // Use interpolated camera for accurate rendering
    const camera = this.getCameraAtCurrentFrame();
    if (!camera) return null;

    return {
      position: { ...camera.position },
      rotation: {
        x: camera.orientation.x + camera.xRotation,
        y: camera.orientation.y + camera.yRotation,
        z: camera.orientation.z + camera.zRotation,
      },
      fov: camera.angleOfView,
      focalLength: camera.focalLength,
      nearClip: camera.nearClip,
      farClip: camera.farClip,
    };
  }

  // ============================================================================
  // DISPOSAL
  // ============================================================================

  private disposeWireframe(): void {
    if (!this.wireframe) return;

    this.wireframe.traverse((child) => {
      if (child instanceof THREE.Mesh || child instanceof THREE.Line) {
        child.geometry.dispose();
        (child.material as THREE.Material).dispose();
      }
    });

    this.wireframe.clear();
    this.wireframe = null;
  }

  private disposeFrustum(): void {
    if (!this.frustumHelper) return;

    this.frustumHelper.traverse((child) => {
      if (child instanceof THREE.Line) {
        child.geometry.dispose();
        (child.material as THREE.Material).dispose();
      }
    });

    this.frustumHelper.clear();
    this.frustumHelper = null;
  }

  protected onDispose(): void {
    this.disposeWireframe();
    this.disposeFrustum();
  }
}
