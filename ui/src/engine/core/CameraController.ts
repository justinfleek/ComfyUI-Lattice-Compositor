/**
 * CameraController - Camera Management and Animation
 *
 * Controls the Three.js camera for 2.5D/3D compositing:
 * - Perspective camera for 3D depth
 * - OrbitControls for 3D navigation (right-click orbit, middle-click pan)
 * - Animation support via keyframe evaluation
 * - Screen-space coordinate conversion
 */

import * as THREE from 'three';
import { OrbitControls } from 'three/examples/jsm/controls/OrbitControls.js';
import type { AnimatableProperty } from '@/types/project';
import type { CameraState, CameraAnimationProps } from '../types';
import { KeyframeEvaluator } from '../animation/KeyframeEvaluator';

export class CameraController {
  /** The main camera */
  public readonly camera: THREE.PerspectiveCamera;

  /** OrbitControls for 3D navigation */
  public orbitControls: OrbitControls | null = null;

  /** Keyframe evaluator for animations */
  private readonly evaluator: KeyframeEvaluator;

  /** Composition dimensions */
  private width: number;
  private height: number;

  /** Default camera state for reset */
  private defaultPosition: THREE.Vector3;
  private defaultTarget: THREE.Vector3;
  private defaultFov: number = 50;

  /** Animation properties */
  private positionProp?: AnimatableProperty<{ x: number; y: number; z: number }>;
  private targetProp?: AnimatableProperty<{ x: number; y: number; z: number }>;
  private fovProp?: AnimatableProperty<number>;

  /** Current target position (for lookAt) */
  private target: THREE.Vector3;

  constructor(width: number, height: number) {
    this.width = width;
    this.height = height;
    this.evaluator = new KeyframeEvaluator();

    // Create perspective camera
    this.camera = new THREE.PerspectiveCamera(
      this.defaultFov,  // Field of view
      width / height,   // Aspect ratio
      0.1,              // Near plane
      10000             // Far plane
    );

    // Default camera position: centered on composition, looking at center
    // Position camera to see full composition width at z=0
    const fovRad = THREE.MathUtils.degToRad(this.camera.fov);
    const distance = (height / 2) / Math.tan(fovRad / 2);

    // Store default position for reset
    this.defaultPosition = new THREE.Vector3(width / 2, -height / 2, distance);
    this.defaultTarget = new THREE.Vector3(width / 2, -height / 2, 0);

    this.camera.position.copy(this.defaultPosition);
    this.target = this.defaultTarget.clone();
    this.camera.lookAt(this.target);

    this.camera.updateProjectionMatrix();
  }

  // ============================================================================
  // ORBIT CONTROLS (3D Navigation)
  // ============================================================================

  /**
   * Enable orbit controls for 3D navigation
   * @param domElement The canvas element to attach controls to
   */
  enableOrbitControls(domElement: HTMLCanvasElement): void {
    if (this.orbitControls) {
      this.orbitControls.dispose();
    }

    this.orbitControls = new OrbitControls(this.camera, domElement);

    // Configure controls for proper 2.5D/3D navigation:
    // - Left mouse = reserved for selection (handled externally)
    // - Middle mouse = pan (move camera parallel to view plane)
    // - Right mouse = orbit (rotate around target)
    // - Scroll wheel = dolly (zoom in/out along view axis)
    this.orbitControls.mouseButtons = {
      LEFT: undefined as any,  // Reserved for selection/tools
      MIDDLE: THREE.MOUSE.PAN,
      RIGHT: THREE.MOUSE.ROTATE,
    };

    // Set orbit target to composition center
    this.orbitControls.target.copy(this.target);

    // Disable damping - causes unwanted drift and rotation artifacts
    this.orbitControls.enableDamping = false;

    // DISABLE OrbitControls zoom - ThreeCanvas handles zoom via viewportTransform
    // This prevents the conflict where both systems try to handle scroll wheel
    // OrbitControls dolly uses spherical coordinates which can cause rotation artifacts
    this.orbitControls.enableZoom = false;
    this.orbitControls.minDistance = 10;
    this.orbitControls.maxDistance = 50000;

    // Pan settings - middle mouse moves camera in screen space
    this.orbitControls.enablePan = true;
    this.orbitControls.panSpeed = 1.0;
    this.orbitControls.screenSpacePanning = true;

    // Rotation settings - only on right-click drag, NOT on scroll
    this.orbitControls.enableRotate = true;
    this.orbitControls.rotateSpeed = 0.5;

    // Don't auto-rotate
    this.orbitControls.autoRotate = false;

    // IMPORTANT: Ensure camera starts perfectly aligned (front view)
    // Reset to default 2D position to avoid any initial tilt
    this.resetToDefault();

    console.log('[CameraController] Orbit controls enabled (scroll=zoom only, right-click=orbit)');
  }

  /**
   * Disable orbit controls
   */
  disableOrbitControls(): void {
    if (this.orbitControls) {
      this.orbitControls.dispose();
      this.orbitControls = null;
    }
  }

  /**
   * Update orbit controls (call in animation loop)
   */
  updateOrbitControls(): void {
    if (this.orbitControls) {
      this.orbitControls.update();
      // Sync target from orbit controls
      this.target.copy(this.orbitControls.target);
    }
  }

  /**
   * Reset camera to default viewing position - PERFECT 2D FRONT VIEW
   * Camera looks straight at composition center, no rotation/tilt
   * This is the "Sync to Home" state - as if there's no 3D at all
   */
  resetToDefault(): void {
    // Calculate the exact distance needed to see full composition
    const fovRad = THREE.MathUtils.degToRad(this.defaultFov);
    const distance = (this.height / 2) / Math.tan(fovRad / 2);

    // Position camera directly in front of composition center
    // Camera at (centerX, -centerY, distance) looking at (centerX, -centerY, 0)
    const centerX = this.width / 2;
    const centerY = -this.height / 2;

    this.camera.position.set(centerX, centerY, distance);
    this.target.set(centerX, centerY, 0);
    this.camera.fov = this.defaultFov;

    // Reset camera rotation to look straight at target (no roll/pitch)
    this.camera.up.set(0, 1, 0);
    this.camera.lookAt(this.target);
    this.camera.updateProjectionMatrix();

    // Sync orbit controls to this exact position
    if (this.orbitControls) {
      this.orbitControls.target.copy(this.target);
      this.orbitControls.update();
    }

    // Reset viewport zoom/pan state
    this.zoomLevel = 1;
    this.panOffset.set(0, 0);

    console.log('[CameraController] Camera reset to perfect 2D front view');
  }

  /**
   * Check if orbit controls are enabled
   */
  hasOrbitControls(): boolean {
    return this.orbitControls !== null;
  }

  // ============================================================================
  // POSITION & ORIENTATION
  // ============================================================================

  /**
   * Set camera position
   * Note: Y is negated for screen coordinates (Y down)
   */
  setPosition(x: number, y: number, z: number): void {
    this.camera.position.set(x, -y, z);
    this.camera.lookAt(this.target);
    this.camera.updateProjectionMatrix();
  }

  /**
   * Get camera position (in screen coordinates)
   */
  getPosition(): { x: number; y: number; z: number } {
    return {
      x: this.camera.position.x,
      y: -this.camera.position.y, // Convert back to screen coords
      z: this.camera.position.z,
    };
  }

  /**
   * Set camera target (look-at point)
   * Note: Y is negated for screen coordinates
   */
  setTarget(x: number, y: number, z: number): void {
    this.target.set(x, -y, z);
    this.camera.lookAt(this.target);
    this.camera.updateProjectionMatrix();
  }

  /**
   * Set camera position directly (no coordinate transformation)
   * Used by MotionEngine when applying pre-evaluated camera state.
   */
  setPositionDirect(x: number, y: number, z: number): void {
    this.camera.position.set(x, -y, z);
    this.camera.lookAt(this.target);
    this.camera.updateProjectionMatrix();
  }

  /**
   * Set camera target directly (no coordinate transformation)
   * Used by MotionEngine when applying pre-evaluated camera state.
   */
  setTargetDirect(x: number, y: number, z: number): void {
    this.target.set(x, -y, z);
    this.camera.lookAt(this.target);
    this.camera.updateProjectionMatrix();
  }

  /**
   * Get camera target (in screen coordinates)
   */
  getTarget(): { x: number; y: number; z: number } {
    return {
      x: this.target.x,
      y: -this.target.y,
      z: this.target.z,
    };
  }

  /**
   * Set camera rotation directly (Euler angles in degrees)
   */
  setRotation(x: number, y: number, z: number): void {
    this.camera.rotation.set(
      THREE.MathUtils.degToRad(x),
      THREE.MathUtils.degToRad(y),
      THREE.MathUtils.degToRad(z)
    );
    this.camera.updateProjectionMatrix();
  }

  // ============================================================================
  // PROJECTION
  // ============================================================================

  /**
   * Set field of view (in degrees)
   */
  setFOV(fov: number): void {
    this.camera.fov = THREE.MathUtils.clamp(fov, 1, 179);
    this.camera.updateProjectionMatrix();
  }

  /**
   * Get field of view
   */
  getFOV(): number {
    return this.camera.fov;
  }

  /**
   * Set near and far planes
   */
  setClipPlanes(near: number, far: number): void {
    this.camera.near = Math.max(0.001, near);
    this.camera.far = Math.max(this.camera.near + 1, far);
    this.camera.updateProjectionMatrix();
  }

  // ============================================================================
  // VIEWPORT ZOOM/PAN
  // ============================================================================

  /** Pan offset for viewport navigation */
  private panOffset: THREE.Vector2 = new THREE.Vector2(0, 0);
  private zoomLevel: number = 1;

  /**
   * Set zoom level for viewport navigation
   * This adjusts the camera's effective view without changing FOV
   */
  setZoom(zoom: number): void {
    this.zoomLevel = Math.max(0.1, Math.min(10, zoom));
    this.updateCameraForViewport();
  }

  /**
   * Get current zoom level
   */
  getZoom(): number {
    return this.zoomLevel;
  }

  /**
   * Set pan offset for viewport navigation (in WORLD units, not screen pixels)
   * Positive X pans right (camera moves left), positive Y pans down (camera moves up)
   */
  setPan(x: number, y: number): void {
    this.panOffset.set(x, y);
    this.updateCameraForViewport();
  }

  /**
   * Get current pan offset
   */
  getPan(): { x: number; y: number } {
    return { x: this.panOffset.x, y: this.panOffset.y };
  }

  /**
   * Update camera position based on zoom and pan
   * Camera always looks straight at the composition plane (perfect 2D front view)
   */
  private updateCameraForViewport(): void {
    // Calculate base camera distance for full composition view
    const fovRad = THREE.MathUtils.degToRad(this.camera.fov);
    const baseDistance = (this.height / 2) / Math.tan(fovRad / 2);

    // Adjust distance based on zoom (zoom in = closer)
    const distance = baseDistance / this.zoomLevel;

    // Camera is centered on composition center, offset by pan
    // Pan offset is in world units (same as composition dimensions)
    const centerX = (this.width / 2) + this.panOffset.x;
    const centerY = (this.height / 2) + this.panOffset.y;

    // Update camera position - straight-on view at composition plane
    this.camera.position.set(centerX, -centerY, distance);
    this.target.set(centerX, -centerY, 0);

    // CRITICAL: Ensure camera is perfectly aligned with NO rotation
    this.camera.up.set(0, 1, 0);
    this.camera.lookAt(this.target);
    this.camera.rotation.z = 0;

    this.camera.updateProjectionMatrix();
  }

  // ============================================================================
  // ANIMATION
  // ============================================================================

  /**
   * Set animated properties for keyframe evaluation
   */
  setAnimationProperties(props: CameraAnimationProps): void {
    this.positionProp = props.position;
    this.targetProp = props.target;
    this.fovProp = props.fov;
  }

  /**
   * Clear animation properties
   */
  clearAnimationProperties(): void {
    this.positionProp = undefined;
    this.targetProp = undefined;
    this.fovProp = undefined;
  }

  /**
   * Evaluate animated properties at a given frame
   */
  evaluateFrame(frame: number): void {
    if (this.positionProp) {
      const pos = this.evaluator.evaluate(this.positionProp, frame);
      this.setPosition(pos.x, pos.y, pos.z ?? this.camera.position.z);
    }

    if (this.targetProp) {
      const target = this.evaluator.evaluate(this.targetProp, frame);
      this.setTarget(target.x, target.y, target.z ?? 0);
    }

    if (this.fovProp) {
      const fov = this.evaluator.evaluate(this.fovProp, frame);
      this.setFOV(fov);
    }
  }

  // ============================================================================
  // RESIZE
  // ============================================================================

  /**
   * Resize camera for new COMPOSITION dimensions
   * Note: The aspect ratio should be set separately using setViewportAspect()
   */
  resize(width: number, height: number): void {
    this.width = width;
    this.height = height;

    // Don't change aspect here - it should be set to VIEWPORT aspect, not composition
    // The caller (WeylEngine.resize) should call setViewportAspect() separately

    // Recenter camera on composition
    this.resetToDefault();
  }

  /**
   * Set camera aspect ratio to match viewport dimensions
   * This should be called with VIEWPORT dimensions, not composition
   */
  setViewportAspect(viewportWidth: number, viewportHeight: number): void {
    this.camera.aspect = viewportWidth / viewportHeight;
    this.camera.updateProjectionMatrix();
  }

  // ============================================================================
  // COORDINATE CONVERSION
  // ============================================================================

  /**
   * Convert screen coordinates to world position at a given Z depth
   */
  screenToWorld(screenX: number, screenY: number, z: number = 0): THREE.Vector3 {
    // Normalize to NDC (-1 to 1)
    const ndcX = (screenX / this.width) * 2 - 1;
    const ndcY = -(screenY / this.height) * 2 + 1;

    // Create vector in clip space
    const vector = new THREE.Vector3(ndcX, ndcY, 0.5);

    // Unproject to world space
    vector.unproject(this.camera);

    // Get direction from camera
    const dir = vector.sub(this.camera.position).normalize();

    // Calculate distance to target Z plane
    const distance = (z - this.camera.position.z) / dir.z;

    // Calculate world position
    return this.camera.position.clone().add(dir.multiplyScalar(distance));
  }

  /**
   * Convert world position to screen coordinates
   */
  worldToScreen(worldX: number, worldY: number, worldZ: number = 0): { x: number; y: number } {
    const vector = new THREE.Vector3(worldX, -worldY, worldZ);
    vector.project(this.camera);

    return {
      x: ((vector.x + 1) / 2) * this.width,
      y: ((-vector.y + 1) / 2) * this.height,
    };
  }

  // ============================================================================
  // STATE
  // ============================================================================

  /**
   * Get the Three.js camera object directly
   */
  getCamera(): THREE.PerspectiveCamera {
    return this.camera;
  }

  /**
   * Get complete camera state
   */
  getState(): CameraState {
    return {
      position: this.getPosition(),
      target: this.getTarget(),
      fov: this.camera.fov,
      near: this.camera.near,
      far: this.camera.far,
    };
  }

  /**
   * Set complete camera state
   */
  setState(state: Partial<CameraState>): void {
    if (state.position) {
      this.setPosition(state.position.x, state.position.y, state.position.z);
    }
    if (state.target) {
      this.setTarget(state.target.x, state.target.y, state.target.z);
    }
    if (state.fov !== undefined) {
      this.setFOV(state.fov);
    }
    if (state.near !== undefined || state.far !== undefined) {
      this.setClipPlanes(
        state.near ?? this.camera.near,
        state.far ?? this.camera.far
      );
    }
  }

  /**
   * Reset camera to default position for current composition size
   */
  reset(): void {
    const fovRad = THREE.MathUtils.degToRad(50);
    const distance = (this.height / 2) / Math.tan(fovRad / 2);

    this.camera.fov = 50;
    this.camera.position.set(this.width / 2, -this.height / 2, distance);
    this.target.set(this.width / 2, -this.height / 2, 0);
    this.camera.lookAt(this.target);
    this.camera.updateProjectionMatrix();
  }

  // ============================================================================
  // ORTHOGRAPHIC
  // ============================================================================

  /**
   * Create an orthographic camera for 2D rendering
   */
  createOrthographic(): THREE.OrthographicCamera {
    const ortho = new THREE.OrthographicCamera(
      0,              // Left
      this.width,     // Right
      0,              // Top (in screen coords)
      -this.height,   // Bottom
      0.1,            // Near
      10000           // Far
    );

    ortho.position.set(0, 0, 1000);
    ortho.lookAt(0, 0, 0);

    return ortho;
  }

  // ============================================================================
  // 3D ORBIT CONTROLS
  // ============================================================================

  /** Current spherical coordinates for orbit mode */
  private spherical = { radius: 1000, theta: 0, phi: Math.PI / 2 };

  /** Whether orbit mode is enabled */
  private orbitEnabled = false;

  /**
   * Enable orbit mode for 3D navigation
   * In orbit mode, the camera orbits around the target point
   */
  enableOrbitMode(): void {
    this.orbitEnabled = true;
    // Calculate current spherical coordinates from camera position
    const offset = new THREE.Vector3().subVectors(this.camera.position, this.target);
    this.spherical.radius = offset.length();
    this.spherical.theta = Math.atan2(offset.x - this.target.x, offset.z);
    this.spherical.phi = Math.acos(THREE.MathUtils.clamp(offset.y / this.spherical.radius, -1, 1));
  }

  /**
   * Disable orbit mode (return to pan/zoom mode)
   */
  disableOrbitMode(): void {
    this.orbitEnabled = false;
  }

  /**
   * Check if orbit mode is active
   */
  isOrbitMode(): boolean {
    return this.orbitEnabled;
  }

  /**
   * Orbit camera around target point
   * @param deltaTheta - Horizontal rotation in radians (around Y axis)
   * @param deltaPhi - Vertical rotation in radians (around X axis)
   */
  orbit(deltaTheta: number, deltaPhi: number): void {
    if (!this.orbitEnabled) return;

    // Update spherical coordinates
    this.spherical.theta -= deltaTheta;
    this.spherical.phi = THREE.MathUtils.clamp(
      this.spherical.phi - deltaPhi,
      0.01, // Prevent flipping at poles
      Math.PI - 0.01
    );

    this.updateCameraFromSpherical();
  }

  /**
   * Dolly (zoom in/out) in orbit mode
   * @param delta - Positive to zoom in, negative to zoom out
   */
  dolly(delta: number): void {
    if (!this.orbitEnabled) {
      // In non-orbit mode, use regular zoom
      this.setZoom(this.zoomLevel * (1 + delta * 0.1));
      return;
    }

    // Adjust radius
    this.spherical.radius = THREE.MathUtils.clamp(
      this.spherical.radius * (1 - delta * 0.1),
      10,     // Minimum distance
      50000   // Maximum distance
    );

    this.updateCameraFromSpherical();
  }

  /**
   * Pan camera in orbit mode (move target point)
   * @param deltaX - Horizontal pan in screen pixels
   * @param deltaY - Vertical pan in screen pixels
   */
  orbitPan(deltaX: number, deltaY: number): void {
    if (!this.orbitEnabled) {
      // Use regular pan
      this.setPan(this.panOffset.x + deltaX, this.panOffset.y + deltaY);
      return;
    }

    // Calculate pan speed based on distance
    const panSpeed = this.spherical.radius * 0.001;

    // Get camera right and up vectors
    const right = new THREE.Vector3();
    const up = new THREE.Vector3();
    right.setFromMatrixColumn(this.camera.matrix, 0);
    up.setFromMatrixColumn(this.camera.matrix, 1);

    // Apply pan
    const panOffset = new THREE.Vector3();
    panOffset.addScaledVector(right, -deltaX * panSpeed);
    panOffset.addScaledVector(up, deltaY * panSpeed);

    this.target.add(panOffset);
    this.updateCameraFromSpherical();
  }

  /**
   * Update camera position from spherical coordinates
   */
  private updateCameraFromSpherical(): void {
    // Convert spherical to Cartesian
    const x = this.spherical.radius * Math.sin(this.spherical.phi) * Math.sin(this.spherical.theta);
    const y = this.spherical.radius * Math.cos(this.spherical.phi);
    const z = this.spherical.radius * Math.sin(this.spherical.phi) * Math.cos(this.spherical.theta);

    this.camera.position.set(
      this.target.x + x,
      this.target.y + y,
      this.target.z + z
    );
    this.camera.lookAt(this.target);
    this.camera.updateProjectionMatrix();
  }

  // ============================================================================
  // VIEW PRESETS
  // ============================================================================

  /**
   * Available orthographic view presets
   */
  static readonly VIEW_PRESETS = {
    front: { theta: 0, phi: Math.PI / 2, name: 'Front' },
    back: { theta: Math.PI, phi: Math.PI / 2, name: 'Back' },
    left: { theta: -Math.PI / 2, phi: Math.PI / 2, name: 'Left' },
    right: { theta: Math.PI / 2, phi: Math.PI / 2, name: 'Right' },
    top: { theta: 0, phi: 0.01, name: 'Top' },
    bottom: { theta: 0, phi: Math.PI - 0.01, name: 'Bottom' },
    perspective: { theta: Math.PI / 4, phi: Math.PI / 3, name: 'Perspective' },
  } as const;

  /**
   * Switch to a predefined view preset
   * @param preset - Name of the view preset
   * @param animate - Whether to animate the transition (default: false)
   */
  setViewPreset(preset: keyof typeof CameraController.VIEW_PRESETS, animate = false): void {
    const view = CameraController.VIEW_PRESETS[preset];
    if (!view) return;

    // Enable orbit mode if not already
    if (!this.orbitEnabled) {
      this.enableOrbitMode();
    }

    if (animate) {
      // Store start values for animation
      const startTheta = this.spherical.theta;
      const startPhi = this.spherical.phi;
      const targetTheta = view.theta;
      const targetPhi = view.phi;

      // Animate over 300ms
      const duration = 300;
      const startTime = performance.now();

      const animateView = (currentTime: number) => {
        const elapsed = currentTime - startTime;
        const t = Math.min(elapsed / duration, 1);
        // Use smooth easing
        const eased = t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2;

        this.spherical.theta = startTheta + (targetTheta - startTheta) * eased;
        this.spherical.phi = startPhi + (targetPhi - startPhi) * eased;
        this.updateCameraFromSpherical();

        if (t < 1) {
          requestAnimationFrame(animateView);
        }
      };

      requestAnimationFrame(animateView);
    } else {
      this.spherical.theta = view.theta;
      this.spherical.phi = view.phi;
      this.updateCameraFromSpherical();
    }
  }

  /**
   * Reset camera to default 2D view (centered on composition)
   */
  resetTo2DView(): void {
    this.disableOrbitMode();
    this.panOffset.set(0, 0);
    this.zoomLevel = 1;
    this.reset();
  }

  /**
   * Reset orbit to center on composition
   */
  resetOrbit(): void {
    // Set target to composition center
    this.target.set(this.width / 2, -this.height / 2, 0);

    // Reset spherical to front-perspective view
    const fovRad = THREE.MathUtils.degToRad(this.camera.fov);
    this.spherical.radius = (this.height / 2) / Math.tan(fovRad / 2);
    this.spherical.theta = 0;
    this.spherical.phi = Math.PI / 2;

    if (this.orbitEnabled) {
      this.updateCameraFromSpherical();
    } else {
      this.reset();
    }
  }

  // ============================================================================
  // FOCUS & FRAMING
  // ============================================================================

  /**
   * Focus camera on a bounding box, framing it in view
   * @param bounds - { min: {x, y, z}, max: {x, y, z} }
   */
  focusOnBounds(bounds: {
    min: { x: number; y: number; z: number };
    max: { x: number; y: number; z: number };
  }): void {
    // Calculate center of bounds
    const center = new THREE.Vector3(
      (bounds.min.x + bounds.max.x) / 2,
      -(bounds.min.y + bounds.max.y) / 2, // Negate for screen coords
      (bounds.min.z + bounds.max.z) / 2
    );

    // Calculate size of bounds
    const size = new THREE.Vector3(
      bounds.max.x - bounds.min.x,
      bounds.max.y - bounds.min.y,
      bounds.max.z - bounds.min.z
    );

    // Calculate required distance to fit bounds in view
    const maxDim = Math.max(size.x, size.y, size.z);
    const fovRad = THREE.MathUtils.degToRad(this.camera.fov);
    const distance = (maxDim / 2) / Math.tan(fovRad / 2) * 1.5; // 1.5x padding

    // Update target and position
    this.target.copy(center);

    if (this.orbitEnabled) {
      this.spherical.radius = distance;
      this.updateCameraFromSpherical();
    } else {
      this.camera.position.set(center.x, center.y, center.z + distance);
      this.camera.lookAt(this.target);
      this.camera.updateProjectionMatrix();
    }
  }

  /**
   * Focus on a layer by its bounding rect
   * @param x - Layer X position
   * @param y - Layer Y position
   * @param width - Layer width
   * @param height - Layer height
   * @param z - Layer Z position (default 0)
   */
  focusOnLayer(x: number, y: number, width: number, height: number, z = 0): void {
    this.focusOnBounds({
      min: { x, y, z: z - 10 },
      max: { x: x + width, y: y + height, z: z + 10 },
    });
  }

  // ============================================================================
  // CAMERA BOOKMARKS
  // ============================================================================

  /** Stored camera bookmarks */
  private bookmarks: Map<string, {
    position: THREE.Vector3;
    target: THREE.Vector3;
    spherical: { radius: number; theta: number; phi: number };
    fov: number;
    orbitEnabled: boolean;
  }> = new Map();

  /**
   * Save current camera state as a bookmark
   * @param name - Name for the bookmark
   */
  saveBookmark(name: string): void {
    this.bookmarks.set(name, {
      position: this.camera.position.clone(),
      target: this.target.clone(),
      spherical: { ...this.spherical },
      fov: this.camera.fov,
      orbitEnabled: this.orbitEnabled,
    });
  }

  /**
   * Load a saved camera bookmark
   * @param name - Name of the bookmark
   * @param animate - Whether to animate transition
   */
  loadBookmark(name: string, animate = false): boolean {
    const bookmark = this.bookmarks.get(name);
    if (!bookmark) return false;

    if (animate) {
      // Animate transition
      const startPos = this.camera.position.clone();
      const startTarget = this.target.clone();
      const startFov = this.camera.fov;

      const duration = 500;
      const startTime = performance.now();

      const animateBookmark = (currentTime: number) => {
        const elapsed = currentTime - startTime;
        const t = Math.min(elapsed / duration, 1);
        const eased = t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2;

        this.camera.position.lerpVectors(startPos, bookmark.position, eased);
        this.target.lerpVectors(startTarget, bookmark.target, eased);
        this.camera.fov = startFov + (bookmark.fov - startFov) * eased;

        this.camera.lookAt(this.target);
        this.camera.updateProjectionMatrix();

        if (t < 1) {
          requestAnimationFrame(animateBookmark);
        } else {
          // Restore full state
          this.spherical = { ...bookmark.spherical };
          this.orbitEnabled = bookmark.orbitEnabled;
        }
      };

      requestAnimationFrame(animateBookmark);
    } else {
      this.camera.position.copy(bookmark.position);
      this.target.copy(bookmark.target);
      this.camera.fov = bookmark.fov;
      this.spherical = { ...bookmark.spherical };
      this.orbitEnabled = bookmark.orbitEnabled;
      this.camera.lookAt(this.target);
      this.camera.updateProjectionMatrix();
    }

    return true;
  }

  /**
   * Delete a bookmark
   * @param name - Name of the bookmark
   */
  deleteBookmark(name: string): boolean {
    return this.bookmarks.delete(name);
  }

  /**
   * Get list of bookmark names
   */
  getBookmarkNames(): string[] {
    return Array.from(this.bookmarks.keys());
  }

  /**
   * Export all bookmarks as JSON-serializable data
   */
  exportBookmarks(): Record<string, {
    position: { x: number; y: number; z: number };
    target: { x: number; y: number; z: number };
    spherical: { radius: number; theta: number; phi: number };
    fov: number;
    orbitEnabled: boolean;
  }> {
    const result: Record<string, any> = {};
    this.bookmarks.forEach((value, key) => {
      result[key] = {
        position: { x: value.position.x, y: value.position.y, z: value.position.z },
        target: { x: value.target.x, y: value.target.y, z: value.target.z },
        spherical: value.spherical,
        fov: value.fov,
        orbitEnabled: value.orbitEnabled,
      };
    });
    return result;
  }

  /**
   * Import bookmarks from JSON data
   */
  importBookmarks(data: Record<string, any>): void {
    Object.entries(data).forEach(([name, value]) => {
      this.bookmarks.set(name, {
        position: new THREE.Vector3(value.position.x, value.position.y, value.position.z),
        target: new THREE.Vector3(value.target.x, value.target.y, value.target.z),
        spherical: value.spherical,
        fov: value.fov,
        orbitEnabled: value.orbitEnabled,
      });
    });
  }
}
