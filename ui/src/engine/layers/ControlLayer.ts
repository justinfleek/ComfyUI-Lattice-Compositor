/**
 * ControlLayer - Transform-Only Layer
 *
 * A control layer that provides transform hierarchy without visual content.
 * Used for:
 * - Grouping layers
 * - Parent transforms
 * - Camera targets
 * - Animation controllers
 */

import * as THREE from 'three';
import type { Layer } from '@/types/project';
import { BaseLayer } from './BaseLayer';

export class ControlLayer extends BaseLayer {
  /** Visual indicator (crosshair) for editor visibility */
  private indicator: THREE.Group | null = null;

  /** Whether to show the control indicator */
  private showIndicator: boolean;

  /** Indicator size */
  private indicatorSize: number;

  constructor(layerData: Layer, showIndicator: boolean = true) {
    super(layerData);

    this.showIndicator = showIndicator;
    this.indicatorSize = 50;

    if (this.showIndicator) {
      this.createIndicator();
    }
  }

  /**
   * Create visual indicator (crosshair) for the control layer
   */
  private createIndicator(): void {
    this.indicator = new THREE.Group();
    this.indicator.name = `control_indicator_${this.id}`;

    const size = this.indicatorSize;
    const color = 0xff6600; // Orange for visibility

    // Create crosshair lines
    const material = new THREE.LineBasicMaterial({
      color,
      transparent: true,
      opacity: 0.8,
      depthTest: false,
    });

    // Horizontal line
    const hPoints = [
      new THREE.Vector3(-size / 2, 0, 0),
      new THREE.Vector3(size / 2, 0, 0),
    ];
    const hGeometry = new THREE.BufferGeometry().setFromPoints(hPoints);
    const hLine = new THREE.Line(hGeometry, material);
    this.indicator.add(hLine);

    // Vertical line
    const vPoints = [
      new THREE.Vector3(0, -size / 2, 0),
      new THREE.Vector3(0, size / 2, 0),
    ];
    const vGeometry = new THREE.BufferGeometry().setFromPoints(vPoints);
    const vLine = new THREE.Line(vGeometry, material);
    this.indicator.add(vLine);

    // Z-axis line (for 3D)
    if (this.threeD) {
      const zPoints = [
        new THREE.Vector3(0, 0, -size / 2),
        new THREE.Vector3(0, 0, size / 2),
      ];
      const zGeometry = new THREE.BufferGeometry().setFromPoints(zPoints);
      const zLine = new THREE.Line(zGeometry, material);
      this.indicator.add(zLine);
    }

    // Center point
    const centerGeometry = new THREE.CircleGeometry(3, 16);
    const centerMaterial = new THREE.MeshBasicMaterial({
      color,
      transparent: true,
      opacity: 0.8,
      depthTest: false,
      side: THREE.DoubleSide,
    });
    const centerPoint = new THREE.Mesh(centerGeometry, centerMaterial);
    this.indicator.add(centerPoint);

    // Add indicator to group
    this.group.add(this.indicator);

    // Set render order to appear on top
    this.indicator.renderOrder = 999;
  }

  /**
   * Set indicator visibility
   */
  setIndicatorVisible(visible: boolean): void {
    if (this.indicator) {
      this.indicator.visible = visible;
    }
  }

  /**
   * Set indicator size
   */
  setIndicatorSize(size: number): void {
    // Validate size (NaN/0/negative/Infinity would corrupt indicator geometry)
    const validSize = (Number.isFinite(size) && size > 0) ? size : 50;
    if (validSize === this.indicatorSize) return;

    this.indicatorSize = validSize;

    // Recreate indicator with new size
    if (this.indicator) {
      this.group.remove(this.indicator);
      this.disposeIndicator();
      this.createIndicator();
    }
  }

  /**
   * Dispose indicator resources
   */
  private disposeIndicator(): void {
    if (!this.indicator) return;

    this.indicator.traverse((child) => {
      if (child instanceof THREE.Line) {
        child.geometry.dispose();
        (child.material as THREE.Material).dispose();
      }
      if (child instanceof THREE.Mesh) {
        child.geometry.dispose();
        (child.material as THREE.Material).dispose();
      }
    });

    this.indicator.clear();
    this.indicator = null;
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(_frame: number): void {
    // Control layers have no frame-specific content
    // Transform is handled by BaseLayer
  }

  protected override onApplyEvaluatedState(_state: import('../MotionEngine').EvaluatedLayer): void {
    // Control layers have no type-specific properties
    // All transforms are handled by BaseLayer
  }

  protected onUpdate(properties: Partial<Layer>): void {
    // Update 3D state if changed
    if (properties.threeD !== undefined && properties.threeD !== this.threeD) {
      this.threeD = properties.threeD;

      // Recreate indicator to add/remove Z axis
      if (this.indicator && this.showIndicator) {
        this.group.remove(this.indicator);
        this.disposeIndicator();
        this.createIndicator();
      }
    }
  }

  protected onDispose(): void {
    this.disposeIndicator();
  }
}
