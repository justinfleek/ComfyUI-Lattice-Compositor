/**
 * SolidLayer - Solid Color Layer
 *
 * A simple colored rectangle layer, commonly used for:
 * - Backgrounds
 * - Color mattes
 * - Adjustment layer bases
 * - Shadow catchers (transparent surface that only shows shadows)
 */

import * as THREE from "three";
import type { AnimatableProperty, Layer } from "@/types/project";
import { BaseLayer } from "./BaseLayer";

export interface SolidData {
  color: string;
  width: number;
  height: number;
  animatedColor?: AnimatableProperty<string>; // Hex color animation support
  shadowCatcher?: boolean; // Shadow catcher mode
  shadowOpacity?: number; // Shadow opacity (0-100)
  shadowColor?: string; // Shadow color
  receiveShadow?: boolean; // Receive shadows from lights
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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: shadowCatcher ∈ boolean | undefined → boolean (default false)
    this.shadowCatcher = (typeof solidData.shadowCatcher === "boolean") ? solidData.shadowCatcher : false;
    // Pattern match: shadowOpacity ∈ number | undefined → number (default 50)
    this.shadowOpacity = (typeof solidData.shadowOpacity === "number" && Number.isFinite(solidData.shadowOpacity)) ? solidData.shadowOpacity : 50;
    // Pattern match: shadowColor ∈ string | undefined → string (default "#000000")
    this.shadowColor = (typeof solidData.shadowColor === "string" && solidData.shadowColor.length > 0) ? solidData.shadowColor : "#000000";
    // Pattern match: receiveShadow ∈ boolean | undefined → boolean (default false)
    this.receiveShadow = (typeof solidData.receiveShadow === "boolean") ? solidData.receiveShadow : false;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const transform = (layerData != null && typeof layerData === "object" && "transform" in layerData && layerData.transform != null && typeof layerData.transform === "object") ? layerData.transform : undefined;
    const position = (transform != null && typeof transform === "object" && "position" in transform && transform.position != null && typeof transform.position === "object") ? transform.position : undefined;
    const positionValue = (position != null && typeof position === "object" && "value" in position && position.value != null && typeof position.value === "object") ? position.value : undefined;
    console.log("[SolidLayer] Creating solid:", {
      id: this.id,
      color: this.color,
      width: this.width,
      height: this.height,
      position: positionValue,
      visible: layerData.visible,
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

    console.log("[SolidLayer] Created mesh:", {
      meshName: this.mesh.name,
      geometrySize: { w: this.width, h: this.height },
      groupChildren: this.group.children.length,
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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: data ∈ Partial<SolidData> | undefined → SolidData (with explicit defaults)
    const data = (layerData.data !== null && typeof layerData.data === "object") ? layerData.data as Partial<SolidData> : undefined;
    
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: Extract each property with explicit type narrowing and defaults
    const colorValue = (data !== undefined && typeof data === "object" && data !== null && "color" in data && typeof data.color === "string" && data.color.length > 0) ? data.color : "#808080";
    const widthValue = (data !== undefined && typeof data === "object" && data !== null && "width" in data && typeof data.width === "number" && Number.isFinite(data.width)) ? data.width : 1920;
    const heightValue = (data !== undefined && typeof data === "object" && data !== null && "height" in data && typeof data.height === "number" && Number.isFinite(data.height)) ? data.height : 1080;
    const animatedColorValue = (data !== undefined && typeof data === "object" && data !== null && "animatedColor" in data) ? data.animatedColor : undefined;
    const shadowCatcherValue = (data !== undefined && typeof data === "object" && data !== null && "shadowCatcher" in data && typeof data.shadowCatcher === "boolean") ? data.shadowCatcher : false;
    const shadowOpacityValue = (data !== undefined && typeof data === "object" && data !== null && "shadowOpacity" in data && typeof data.shadowOpacity === "number" && Number.isFinite(data.shadowOpacity)) ? data.shadowOpacity : 50;
    const shadowColorValue = (data !== undefined && typeof data === "object" && data !== null && "shadowColor" in data && typeof data.shadowColor === "string" && data.shadowColor.length > 0) ? data.shadowColor : "#000000";
    const receiveShadowValue = (data !== undefined && typeof data === "object" && data !== null && "receiveShadow" in data && typeof data.receiveShadow === "boolean") ? data.receiveShadow : false;

    return {
      color: colorValue,
      width: widthValue,
      height: heightValue,
      animatedColor: animatedColorValue,
      shadowCatcher: shadowCatcherValue,
      shadowOpacity: shadowOpacityValue,
      shadowColor: shadowColorValue,
      receiveShadow: receiveShadowValue,
    };
  }

  /**
   * Set solid color
   */
  setColor(color: string): void {
    this.color = color;
    // Only set color on non-shadow materials
    if (!this.shadowCatcher && "color" in this.material) {
      (
        this.material as THREE.MeshBasicMaterial | THREE.MeshStandardMaterial
      ).color.set(color);
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
    const validWidth = Number.isFinite(width) && width > 0 ? width : 1920;
    const validHeight = Number.isFinite(height) && height > 0 ? height : 1080;

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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const animatedColor = this.animatedColor;
    const animatedColorAnimated = (animatedColor != null && typeof animatedColor === "object" && "animated" in animatedColor && typeof animatedColor.animated === "boolean" && animatedColor.animated) ? true : false;
    if (animatedColorAnimated && animatedColor && !this.shadowCatcher) {
      const color = this.evaluator.evaluate(animatedColor, frame);
      if ("color" in this.material) {
        (
          this.material as THREE.MeshBasicMaterial | THREE.MeshStandardMaterial
        ).color.set(color);
        this.material.needsUpdate = true;
      }
    }
  }

  protected override onApplyEvaluatedState(
    state: import("../MotionEngine").EvaluatedLayer,
  ): void {
    // Apply evaluated color if present in properties (only for non-shadow catcher)
    if (state.properties.color !== undefined && !this.shadowCatcher) {
      if ("color" in this.material) {
        (
          this.material as THREE.MeshBasicMaterial | THREE.MeshStandardMaterial
        ).color.set(state.properties.color as string);
        this.material.needsUpdate = true;
      }
    }

    // Apply shadow opacity
    if (state.properties.shadowOpacity !== undefined && this.shadowCatcher) {
      if (this.material instanceof THREE.ShadowMaterial) {
        this.material.opacity =
          (state.properties.shadowOpacity as number) / 100;
        this.material.needsUpdate = true;
      }
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<SolidData> | undefined;

    // Handle shadow catcher mode change (must be first - triggers material rebuild)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const shadowCatcher = (data != null && typeof data === "object" && "shadowCatcher" in data && typeof data.shadowCatcher === "boolean") ? data.shadowCatcher : undefined;
    if (shadowCatcher !== undefined) {
      this.setShadowCatcher(shadowCatcher);
    }

    // Handle receive shadow change
    const receiveShadow = (data != null && typeof data === "object" && "receiveShadow" in data && typeof data.receiveShadow === "boolean") ? data.receiveShadow : undefined;
    if (receiveShadow !== undefined) {
      this.setReceiveShadow(receiveShadow);
    }

    const color = (data != null && typeof data === "object" && "color" in data && typeof data.color === "string") ? data.color : undefined;
    if (color !== undefined) {
      this.setColor(color);
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: data.width ∈ number | undefined → boolean (check if defined)
    const dataValue = (properties.data !== null && typeof properties.data === "object") ? properties.data as Partial<SolidData> : undefined;
    const dataWidth = (dataValue !== undefined && typeof dataValue === "object" && dataValue !== null && "width" in dataValue && typeof dataValue.width === "number" && Number.isFinite(dataValue.width)) ? dataValue.width : undefined;
    const dataHeight = (dataValue !== undefined && typeof dataValue === "object" && dataValue !== null && "height" in dataValue && typeof dataValue.height === "number" && Number.isFinite(dataValue.height)) ? dataValue.height : undefined;
    
    if (dataWidth !== undefined || dataHeight !== undefined) {
      // Pattern match: data.width ∈ number | undefined → number (fallback to this.width)
      const widthUpdate = (dataWidth !== undefined) ? dataWidth : this.width;
      // Pattern match: data.height ∈ number | undefined → number (fallback to this.height)
      const heightUpdate = (dataHeight !== undefined) ? dataHeight : this.height;
      this.setDimensions(widthUpdate, heightUpdate);
    }

    // Shadow catcher specific properties
    const shadowOpacity = (data != null && typeof data === "object" && "shadowOpacity" in data && typeof data.shadowOpacity === "number") ? data.shadowOpacity : undefined;
    if (shadowOpacity !== undefined) {
      this.setShadowOpacity(shadowOpacity);
    }

    const shadowColor = (data != null && typeof data === "object" && "shadowColor" in data && typeof data.shadowColor === "string") ? data.shadowColor : undefined;
    if (shadowColor !== undefined) {
      this.setShadowColor(shadowColor);
    }

    // Update animated color property
    const animatedColor = (data != null && typeof data === "object" && "animatedColor" in data && data.animatedColor != null && typeof data.animatedColor === "object") ? data.animatedColor : undefined;
    if (animatedColor !== undefined) {
      this.animatedColor = animatedColor;
    }
    // Note: labelColor is for timeline organization only, not visual fill color
  }

  protected onDispose(): void {
    this.geometry.dispose();
    this.material.dispose();
  }
}
