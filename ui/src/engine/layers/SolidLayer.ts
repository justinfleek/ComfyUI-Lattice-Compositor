/**
 * SolidLayer - Solid Color Layer
 *
 * A simple colored rectangle layer, commonly used for:
 * - Backgrounds
 * - Color mattes
 * - Adjustment layer bases
 */

import * as THREE from 'three';
import type { Layer, AnimatableProperty } from '@/types/project';
import { BaseLayer } from './BaseLayer';

export interface SolidData {
  color: string;
  width: number;
  height: number;
  animatedColor?: AnimatableProperty<string>;  // Hex color animation support
}

export class SolidLayer extends BaseLayer {
  private mesh: THREE.Mesh;
  private geometry: THREE.PlaneGeometry;
  private material: THREE.MeshBasicMaterial;

  /** Solid color */
  private color: string;

  /** Solid dimensions */
  private width: number;
  private height: number;

  /** Animated color property */
  private animatedColor?: AnimatableProperty<string>;

  constructor(layerData: Layer) {
    super(layerData);

    // Extract solid-specific data
    const solidData = this.extractSolidData(layerData);
    this.color = solidData.color;
    this.width = solidData.width;
    this.height = solidData.height;
    this.animatedColor = solidData.animatedColor;

    // Create geometry
    this.geometry = new THREE.PlaneGeometry(this.width, this.height);

    // Create material
    this.material = new THREE.MeshBasicMaterial({
      color: this.color,
      transparent: true,
      side: THREE.DoubleSide,
      depthWrite: false,
    });

    // Create mesh
    this.mesh = new THREE.Mesh(this.geometry, this.material);
    this.mesh.name = `solid_${this.id}`;

    // Add to group
    this.group.add(this.mesh);

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  /**
   * Extract solid layer data from layer object
   */
  private extractSolidData(layerData: Layer): SolidData {
    // Solid data might be in layerData.data or direct properties
    const data = layerData.data as Partial<SolidData> | undefined;

    return {
      color: data?.color ?? '#808080',
      width: data?.width ?? 1920,
      height: data?.height ?? 1080,
      animatedColor: data?.animatedColor,
    };
  }

  /**
   * Set solid color
   */
  setColor(color: string): void {
    this.color = color;
    this.material.color.set(color);
    this.material.needsUpdate = true;
  }

  /**
   * Get current color
   */
  getColor(): string {
    return this.color;
  }

  /**
   * Set solid dimensions
   */
  setDimensions(width: number, height: number): void {
    if (width === this.width && height === this.height) {
      return;
    }

    this.width = width;
    this.height = height;

    // Recreate geometry
    this.geometry.dispose();
    this.geometry = new THREE.PlaneGeometry(width, height);
    this.mesh.geometry = this.geometry;
  }

  /**
   * Get dimensions
   */
  getDimensions(): { width: number; height: number } {
    return { width: this.width, height: this.height };
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Evaluate animated color if present
    if (this.animatedColor?.animated) {
      const color = this.evaluator.evaluate(this.animatedColor, frame);
      this.material.color.set(color);
      this.material.needsUpdate = true;
    }
  }

  protected override onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    // Apply evaluated color if present in properties
    if (state.properties['color'] !== undefined) {
      this.material.color.set(state.properties['color'] as string);
      this.material.needsUpdate = true;
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<SolidData> | undefined;

    if (data?.color !== undefined) {
      this.setColor(data.color);
    }

    if (data?.width !== undefined || data?.height !== undefined) {
      this.setDimensions(
        data?.width ?? this.width,
        data?.height ?? this.height
      );
    }

    // Update animated color property
    if (data?.animatedColor !== undefined) {
      this.animatedColor = data.animatedColor;
    }

    // Color can also be set directly
    if (data === undefined && (properties as any).labelColor !== undefined) {
      this.setColor((properties as any).labelColor);
    }
  }

  protected onDispose(): void {
    this.geometry.dispose();
    this.material.dispose();
  }
}
