/**
 * CameraController - Camera Management and Animation
 *
 * Controls the Three.js camera for 2.5D/3D compositing:
 * - Perspective camera for 3D depth
 * - Animation support via keyframe evaluation
 * - Screen-space coordinate conversion
 */

import * as THREE from 'three';
import type { AnimatableProperty } from '@/types/project';
import type { CameraState, CameraAnimationProps } from '../types';
import { KeyframeEvaluator } from '../animation/KeyframeEvaluator';

export class CameraController {
  /** The main camera */
  public readonly camera: THREE.PerspectiveCamera;

  /** Keyframe evaluator for animations */
  private readonly evaluator: KeyframeEvaluator;

  /** Composition dimensions */
  private width: number;
  private height: number;

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
      50,              // Field of view
      width / height,  // Aspect ratio
      0.1,             // Near plane
      10000            // Far plane
    );

    // Default camera position: centered on composition, looking at center
    // Position camera to see full composition width at z=0
    const fovRad = THREE.MathUtils.degToRad(this.camera.fov);
    const distance = (height / 2) / Math.tan(fovRad / 2);

    this.camera.position.set(width / 2, -height / 2, distance);
    this.target = new THREE.Vector3(width / 2, -height / 2, 0);
    this.camera.lookAt(this.target);

    this.camera.updateProjectionMatrix();
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
   * Set pan offset for viewport navigation
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
   */
  private updateCameraForViewport(): void {
    // Calculate base camera distance for full composition view
    const fovRad = THREE.MathUtils.degToRad(this.camera.fov);
    const baseDistance = (this.height / 2) / Math.tan(fovRad / 2);

    // Adjust distance based on zoom (zoom in = closer)
    const distance = baseDistance / this.zoomLevel;

    // Calculate camera center based on pan
    const centerX = (this.width / 2) - (this.panOffset.x / this.zoomLevel);
    const centerY = (this.height / 2) - (this.panOffset.y / this.zoomLevel);

    // Update camera position
    this.camera.position.set(centerX, -centerY, distance);
    this.target.set(centerX, -centerY, 0);
    this.camera.lookAt(this.target);
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
   * Resize camera for new viewport dimensions
   */
  resize(width: number, height: number): void {
    this.width = width;
    this.height = height;

    this.camera.aspect = width / height;
    this.camera.updateProjectionMatrix();

    // Recenter camera on composition
    const fovRad = THREE.MathUtils.degToRad(this.camera.fov);
    const distance = (height / 2) / Math.tan(fovRad / 2);

    this.camera.position.x = width / 2;
    this.camera.position.y = -height / 2;
    this.camera.position.z = distance;

    this.target.set(width / 2, -height / 2, 0);
    this.camera.lookAt(this.target);
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
}
