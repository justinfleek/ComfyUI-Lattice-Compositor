/**
 * SolidLayer - Solid Color Layer
 *
 * A simple colored rectangle layer, commonly used for:
 * - Backgrounds
 * - Color mattes
 * - Adjustment layer bases
 * - Shadow catchers (transparent surface that only shows shadows)
 */

import * as THREE from 'three';
import type { Layer, AnimatableProperty } from '@/types/project';
import { BaseLayer } from './BaseLayer';

export interface SolidData {
  color: string;
  width: number;
  height: number;
  animatedColor?: AnimatableProperty<string>;  // Hex color animation support
  shadowCatcher?: boolean;                      // Shadow catcher mode
  shadowOpacity?: number;                       // Shadow opacity (0-100)
  shadowColor?: string;                         // Shadow color
  receiveShadow?: boolean;                      // Receive shadows from lights
}

export class SolidLayer extends BaseLayer {
  private mesh: THREE.Mesh;
  private geometry: THREE.PlaneGeometry;
  private material: THREE.Material;

  /** Solid color */
  private color: string;

  /** Solid dimensions */
  private width: number;
  private height: number;

  /** Animated color property */
  private animatedColor?: AnimatableProperty<string>;

  /** Shadow catcher mode */
  private shadowCatcher: boolean;

  /** Shadow opacity (0-100) */
  private shadowOpacity: number;

  /** Shadow color */
  private shadowColor: string;

  /** Receive shadows */
  private receiveShadow: boolean;

  constructor(layerData: Layer) {
    super(layerData);

    // Extract solid-specific data
    const solidData = this.extractSolidData(layerData);
    this.color = solidData.color;
    this.width = solidData.width;
    this.height = solidData.height;
    this.animatedColor = solidData.animatedColor;
    this.shadowCatcher = solidData.shadowCatcher ?? false;
    this.shadowOpacity = solidData.shadowOpacity ?? 50;
    this.shadowColor = solidData.shadowColor ?? '#000000';
    this.receiveShadow = solidData.receiveShadow ?? false;

    console.log('[SolidLayer] Creating solid:', {
      id: this.id,
      color: this.color,
      width: this.width,
      height: this.height,
      position: layerData.transform?.position?.value,
      visible: layerData.visible
    });

    // Create geometry
    this.geometry = new THREE.PlaneGeometry(this.width, this.height);

    // Create appropriate material based on mode
    this.material = this.createMaterial();

    // Create mesh
    this.mesh = new THREE.Mesh(this.geometry, this.material);
    this.mesh.name = `solid_${this.id}`;
    this.mesh.receiveShadow = this.receiveShadow || this.shadowCatcher;

    // Add to group
    this.group.add(this.mesh);

    console.log('[SolidLayer] Created mesh:', {
      meshName: this.mesh.name,
      geometrySize: { w: this.width, h: this.height },
      groupChildren: this.group.children.length
    });

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  /**
   * Create the appropriate material based on mode
   */
  private createMaterial(): THREE.Material {
    if (this.shadowCatcher) {
      // Shadow catcher mode - use ShadowMaterial for transparent shadow-only rendering
      const material = new THREE.ShadowMaterial({
        opacity: this.shadowOpacity / 100,
        color: new THREE.Color(this.shadowColor),
        transparent: true,
        depthWrite: false,
      });
      return material;
    } else if (this.receiveShadow) {
      // Standard mode with shadow receiving - use MeshStandardMaterial
      const material = new THREE.MeshStandardMaterial({
        color: this.color,
        transparent: true,
        side: THREE.DoubleSide,
        depthWrite: false,
        roughness: 1.0,
        metalness: 0.0,
      });
      return material;
    } else {
      // Basic mode - no shadows
      const material = new THREE.MeshBasicMaterial({
        color: this.color,
        transparent: true,
        side: THREE.DoubleSide,
        depthWrite: false,
      });
      return material;
    }
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
      shadowCatcher: data?.shadowCatcher ?? false,
      shadowOpacity: data?.shadowOpacity ?? 50,
      shadowColor: data?.shadowColor ?? '#000000',
      receiveShadow: data?.receiveShadow ?? false,
    };
  }

  /**
   * Set solid color
   */
  setColor(color: string): void {
    this.color = color;
    // Only set color on non-shadow materials
    if (!this.shadowCatcher && 'color' in this.material) {
      (this.material as THREE.MeshBasicMaterial | THREE.MeshStandardMaterial).color.set(color);
      this.material.needsUpdate = true;
    }
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
    // Validate dimensions (NaN/0 would create invalid geometry)
    const validWidth = (Number.isFinite(width) && width > 0) ? width : 1920;
    const validHeight = (Number.isFinite(height) && height > 0) ? height : 1080;

    if (validWidth === this.width && validHeight === this.height) {
      return;
    }

    this.width = validWidth;
    this.height = validHeight;

    // Recreate geometry
    this.geometry.dispose();
    this.geometry = new THREE.PlaneGeometry(validWidth, validHeight);
    this.mesh.geometry = this.geometry;
  }

  /**
   * Get dimensions
   */
  getDimensions(): { width: number; height: number } {
    return { width: this.width, height: this.height };
  }

  /**
   * Enable/disable shadow catcher mode
   */
  setShadowCatcher(enabled: boolean): void {
    if (enabled === this.shadowCatcher) return;

    this.shadowCatcher = enabled;
    this.rebuildMaterial();
  }

  /**
   * Set shadow opacity (0-100)
   */
  setShadowOpacity(opacity: number): void {
    // Validate opacity (NaN bypasses Math.max/min clamp)
    const validOpacity = Number.isFinite(opacity) ? opacity : 50;
    this.shadowOpacity = Math.max(0, Math.min(100, validOpacity));
    if (this.shadowCatcher && this.material instanceof THREE.ShadowMaterial) {
      this.material.opacity = this.shadowOpacity / 100;
      this.material.needsUpdate = true;
    }
  }

  /**
   * Set shadow color
   */
  setShadowColor(color: string): void {
    this.shadowColor = color;
    if (this.shadowCatcher && this.material instanceof THREE.ShadowMaterial) {
      this.material.color.set(color);
      this.material.needsUpdate = true;
    }
  }

  /**
   * Enable/disable shadow receiving
   */
  setReceiveShadow(enabled: boolean): void {
    if (enabled === this.receiveShadow) return;

    this.receiveShadow = enabled;
    this.mesh.receiveShadow = enabled || this.shadowCatcher;

    // Rebuild material if needed
    if (!this.shadowCatcher) {
      this.rebuildMaterial();
    }
  }

  /**
   * Rebuild the material (when mode changes)
   */
  private rebuildMaterial(): void {
    // Dispose old material
    this.material.dispose();

    // Create new material
    this.material = this.createMaterial();
    this.mesh.material = this.material;
    this.mesh.receiveShadow = this.receiveShadow || this.shadowCatcher;
  }

  /**
   * Get shadow catcher state
   */
  isShadowCatcher(): boolean {
    return this.shadowCatcher;
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Evaluate animated color if present (only for non-shadow catcher)
    if (this.animatedColor?.animated && !this.shadowCatcher) {
      const color = this.evaluator.evaluate(this.animatedColor, frame);
      if ('color' in this.material) {
        (this.material as THREE.MeshBasicMaterial | THREE.MeshStandardMaterial).color.set(color);
        this.material.needsUpdate = true;
      }
    }
  }

  protected override onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    // Apply evaluated color if present in properties (only for non-shadow catcher)
    if (state.properties['color'] !== undefined && !this.shadowCatcher) {
      if ('color' in this.material) {
        (this.material as THREE.MeshBasicMaterial | THREE.MeshStandardMaterial).color.set(state.properties['color'] as string);
        this.material.needsUpdate = true;
      }
    }

    // Apply shadow opacity
    if (state.properties['shadowOpacity'] !== undefined && this.shadowCatcher) {
      if (this.material instanceof THREE.ShadowMaterial) {
        this.material.opacity = (state.properties['shadowOpacity'] as number) / 100;
        this.material.needsUpdate = true;
      }
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<SolidData> | undefined;

    // Handle shadow catcher mode change (must be first - triggers material rebuild)
    if (data?.shadowCatcher !== undefined) {
      this.setShadowCatcher(data.shadowCatcher);
    }

    // Handle receive shadow change
    if (data?.receiveShadow !== undefined) {
      this.setReceiveShadow(data.receiveShadow);
    }

    if (data?.color !== undefined) {
      this.setColor(data.color);
    }

    if (data?.width !== undefined || data?.height !== undefined) {
      this.setDimensions(
        data?.width ?? this.width,
        data?.height ?? this.height
      );
    }

    // Shadow catcher specific properties
    if (data?.shadowOpacity !== undefined) {
      this.setShadowOpacity(data.shadowOpacity);
    }

    if (data?.shadowColor !== undefined) {
      this.setShadowColor(data.shadowColor);
    }

    // Update animated color property
    if (data?.animatedColor !== undefined) {
      this.animatedColor = data.animatedColor;
    }
    // Note: labelColor is for timeline organization only, not visual fill color
  }

  protected onDispose(): void {
    this.geometry.dispose();
    this.material.dispose();
  }
}
