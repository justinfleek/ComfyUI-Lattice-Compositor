/**
 * LightLayer - 3D Light Source Layer
 *
 * Provides lighting for 3D compositions:
 * - Point lights (omnidirectional)
 * - Spot lights (directional cone)
 * - Parallel/Directional lights (infinite distance, parallel rays)
 * - Ambient lights (uniform illumination)
 */

import * as THREE from 'three';
import type { Layer, AnimatableProperty } from '@/types/project';
import { BaseLayer } from './BaseLayer';
import { layerLogger } from '@/utils/logger';

export type LightType = 'point' | 'spot' | 'parallel' | 'ambient';
export type FalloffType = 'none' | 'smooth' | 'inverseSquareClamped';

export interface LightData {
  lightType: LightType;
  color: string;
  intensity: number;
  radius: number;
  falloff: FalloffType;
  falloffDistance: number;
  castShadows: boolean;
  shadowDarkness: number;
  shadowDiffusion: number;
  coneAngle?: number;
  coneFeather?: number;
  // Animated properties
  animatedIntensity?: AnimatableProperty<number>;
  animatedConeAngle?: AnimatableProperty<number>;
  animatedColor?: AnimatableProperty<string>;  // Hex color animation
}

export class LightLayer extends BaseLayer {
  private light: THREE.Light;
  private helper: THREE.Object3D | null = null;
  private lightData: LightData;

  constructor(layerData: Layer) {
    super(layerData);

    // Extract light-specific data
    this.lightData = this.extractLightData(layerData);

    // Create the appropriate light type
    this.light = this.createLight();
    this.group.add(this.light);

    // Add helper visualization (for editor view)
    this.createHelper();

    // Apply initial blend mode (lights don't use it, but maintain consistency)
    this.initializeBlendMode();
  }

  /**
   * Extract light data from layer object
   */
  private extractLightData(layerData: Layer): LightData {
    const data = layerData.data as any;

    return {
      lightType: data?.lightType ?? 'point',
      color: data?.color ?? '#ffffff',
      intensity: data?.intensity ?? 100,
      radius: data?.radius ?? 500,
      falloff: data?.falloff ?? 'none',
      falloffDistance: data?.falloffDistance ?? 500,
      castShadows: data?.castShadows ?? false,
      shadowDarkness: data?.shadowDarkness ?? 100,
      shadowDiffusion: data?.shadowDiffusion ?? 0,
      coneAngle: data?.coneAngle ?? 90,
      coneFeather: data?.coneFeather ?? 50,
      animatedIntensity: data?.animatedIntensity,
      animatedConeAngle: data?.animatedConeAngle,
      animatedColor: data?.animatedColor,
    };
  }

  /**
   * Create the Three.js light based on type
   */
  private createLight(): THREE.Light {
    const color = new THREE.Color(this.lightData.color);
    const intensity = this.lightData.intensity / 100; // Normalize from 0-100 to 0-1

    switch (this.lightData.lightType) {
      case 'point': {
        const light = new THREE.PointLight(color, intensity);
        light.distance = this.lightData.falloff === 'none' ? 0 : this.lightData.falloffDistance;
        light.decay = this.lightData.falloff === 'inverseSquareClamped' ? 2 : 1;
        this.configureShadows(light);
        return light;
      }

      case 'spot': {
        const light = new THREE.SpotLight(color, intensity);
        light.distance = this.lightData.falloff === 'none' ? 0 : this.lightData.falloffDistance;
        light.decay = this.lightData.falloff === 'inverseSquareClamped' ? 2 : 1;
        light.angle = THREE.MathUtils.degToRad((this.lightData.coneAngle ?? 90) / 2);
        light.penumbra = (this.lightData.coneFeather ?? 50) / 100;
        this.configureShadows(light);
        return light;
      }

      case 'parallel': {
        const light = new THREE.DirectionalLight(color, intensity);
        this.configureShadows(light);
        return light;
      }

      case 'ambient': {
        return new THREE.AmbientLight(color, intensity);
      }

      default:
        layerLogger.warn(`LightLayer: Unknown light type: ${this.lightData.lightType}, defaulting to point`);
        return new THREE.PointLight(color, intensity);
    }
  }

  /**
   * Configure shadow settings for shadow-capable lights
   */
  private configureShadows(light: THREE.PointLight | THREE.SpotLight | THREE.DirectionalLight): void {
    light.castShadow = this.lightData.castShadows;

    if (light.castShadow) {
      light.shadow.mapSize.width = 1024;
      light.shadow.mapSize.height = 1024;

      // Shadow darkness (bias adjustment)
      light.shadow.bias = -0.0001 * (100 - this.lightData.shadowDarkness) / 100;

      // Shadow diffusion (blur radius)
      light.shadow.radius = 1 + (this.lightData.shadowDiffusion / 10);

      // Near/far for shadow camera
      if (light instanceof THREE.SpotLight || light instanceof THREE.DirectionalLight) {
        light.shadow.camera.near = 1;
        light.shadow.camera.far = this.lightData.falloffDistance * 2;
      }
    }
  }

  /**
   * Create helper visualization for the editor
   */
  private createHelper(): void {
    // Remove existing helper
    if (this.helper) {
      this.group.remove(this.helper);
      if ((this.helper as any).dispose) {
        (this.helper as any).dispose();
      }
    }

    switch (this.lightData.lightType) {
      case 'point': {
        const helper = new THREE.PointLightHelper(this.light as THREE.PointLight, this.lightData.radius / 10);
        this.helper = helper;
        this.group.add(helper);
        break;
      }

      case 'spot': {
        const helper = new THREE.SpotLightHelper(this.light as THREE.SpotLight);
        this.helper = helper;
        this.group.add(helper);
        break;
      }

      case 'parallel': {
        const helper = new THREE.DirectionalLightHelper(this.light as THREE.DirectionalLight, 50);
        this.helper = helper;
        this.group.add(helper);
        break;
      }

      case 'ambient':
        // No helper for ambient lights
        break;
    }
  }

  /**
   * Update light type (requires recreating the light)
   */
  setLightType(type: LightType): void {
    if (type === this.lightData.lightType) return;

    this.lightData.lightType = type;

    // Remove old light
    this.group.remove(this.light);
    if ((this.light as any).dispose) {
      (this.light as any).dispose();
    }

    // Create new light
    this.light = this.createLight();
    this.group.add(this.light);

    // Recreate helper
    this.createHelper();
  }

  /**
   * Set light color
   */
  setColor(color: string): void {
    this.lightData.color = color;
    this.light.color.set(color);
  }

  /**
   * Set light intensity
   */
  setIntensity(intensity: number): void {
    this.lightData.intensity = intensity;
    this.light.intensity = intensity / 100;
  }

  /**
   * Set falloff distance
   */
  setFalloffDistance(distance: number): void {
    this.lightData.falloffDistance = distance;

    if (this.light instanceof THREE.PointLight || this.light instanceof THREE.SpotLight) {
      this.light.distance = this.lightData.falloff === 'none' ? 0 : distance;
    }
  }

  /**
   * Set cone angle (spot lights only)
   */
  setConeAngle(angle: number): void {
    if (this.light instanceof THREE.SpotLight) {
      this.lightData.coneAngle = angle;
      this.light.angle = THREE.MathUtils.degToRad(angle / 2);

      // Update helper
      if (this.helper instanceof THREE.SpotLightHelper) {
        this.helper.update();
      }
    }
  }

  /**
   * Set cone feather (spot lights only)
   */
  setConeFeather(feather: number): void {
    if (this.light instanceof THREE.SpotLight) {
      this.lightData.coneFeather = feather;
      this.light.penumbra = feather / 100;
    }
  }

  /**
   * Toggle shadow casting
   */
  setCastShadows(cast: boolean): void {
    this.lightData.castShadows = cast;

    if (this.light instanceof THREE.PointLight ||
        this.light instanceof THREE.SpotLight ||
        this.light instanceof THREE.DirectionalLight) {
      this.light.castShadow = cast;
    }
  }

  /**
   * Get the underlying Three.js light
   */
  getLight(): THREE.Light {
    return this.light;
  }

  /**
   * Get light data
   */
  getLightData(): LightData {
    return { ...this.lightData };
  }

  /**
   * Show/hide editor helper
   */
  setHelperVisible(visible: boolean): void {
    if (this.helper) {
      this.helper.visible = visible;
    }
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Evaluate animated intensity
    if (this.lightData.animatedIntensity?.animated) {
      const intensity = this.evaluator.evaluate(this.lightData.animatedIntensity, frame);
      this.light.intensity = intensity / 100;
    }

    // Evaluate animated cone angle (spot lights)
    if (this.lightData.animatedConeAngle?.animated && this.light instanceof THREE.SpotLight) {
      const angle = this.evaluator.evaluate(this.lightData.animatedConeAngle, frame);
      this.light.angle = THREE.MathUtils.degToRad(angle / 2);

      // Update helper
      if (this.helper instanceof THREE.SpotLightHelper) {
        this.helper.update();
      }
    }

    // Evaluate animated color
    if (this.lightData.animatedColor?.animated) {
      const color = this.evaluator.evaluate(this.lightData.animatedColor, frame);
      this.light.color.set(color);

      // Update helper color
      if (this.helper) {
        if (this.helper instanceof THREE.PointLightHelper) {
          this.helper.update();
        } else if (this.helper instanceof THREE.SpotLightHelper) {
          this.helper.update();
        } else if (this.helper instanceof THREE.DirectionalLightHelper) {
          this.helper.update();
        }
      }
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<LightData> | undefined;

    if (!data) return;

    if (data.lightType !== undefined && data.lightType !== this.lightData.lightType) {
      this.setLightType(data.lightType);
    }

    if (data.color !== undefined) {
      this.setColor(data.color);
    }

    if (data.intensity !== undefined) {
      this.setIntensity(data.intensity);
    }

    if (data.falloffDistance !== undefined) {
      this.setFalloffDistance(data.falloffDistance);
    }

    if (data.falloff !== undefined) {
      this.lightData.falloff = data.falloff;
      this.setFalloffDistance(this.lightData.falloffDistance);
    }

    if (data.coneAngle !== undefined) {
      this.setConeAngle(data.coneAngle);
    }

    if (data.coneFeather !== undefined) {
      this.setConeFeather(data.coneFeather);
    }

    if (data.castShadows !== undefined) {
      this.setCastShadows(data.castShadows);
    }

    if (data.shadowDarkness !== undefined || data.shadowDiffusion !== undefined) {
      this.lightData.shadowDarkness = data.shadowDarkness ?? this.lightData.shadowDarkness;
      this.lightData.shadowDiffusion = data.shadowDiffusion ?? this.lightData.shadowDiffusion;

      // Reconfigure shadows
      if (this.light instanceof THREE.PointLight ||
          this.light instanceof THREE.SpotLight ||
          this.light instanceof THREE.DirectionalLight) {
        this.configureShadows(this.light);
      }
    }

    // Update animated properties
    if (data.animatedIntensity !== undefined) {
      this.lightData.animatedIntensity = data.animatedIntensity;
    }

    if (data.animatedConeAngle !== undefined) {
      this.lightData.animatedConeAngle = data.animatedConeAngle;
    }

    if (data.animatedColor !== undefined) {
      this.lightData.animatedColor = data.animatedColor;
    }
  }

  protected onDispose(): void {
    // Dispose light
    if ((this.light as any).dispose) {
      (this.light as any).dispose();
    }

    // Dispose helper
    if (this.helper && (this.helper as any).dispose) {
      (this.helper as any).dispose();
    }
  }
}
