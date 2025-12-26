/**
 * LightLayer - Advanced 3D Light Source Layer
 *
 * Professional motion graphics lighting with:
 * - Point, Spot, Parallel, Ambient, and Area lights
 * - Point of Interest (lookAt target) with layer targeting
 * - Path animation (follow spline)
 * - Color temperature presets
 * - Enhanced shadow controls (PCF, VSM, soft shadows)
 * - Light linking (per-layer light masks)
 * - Animatable properties with driver system support
 */

import * as THREE from 'three';
import { RectAreaLightHelper } from 'three/addons/helpers/RectAreaLightHelper.js';
import { RectAreaLightUniformsLib } from 'three/addons/lights/RectAreaLightUniformsLib.js';
import type { Layer, AnimatableProperty } from '@/types/project';
import { BaseLayer } from './BaseLayer';
import { layerLogger } from '@/utils/logger';

// Initialize RectAreaLight uniforms (required for area lights)
let rectAreaLightInitialized = false;
function initRectAreaLight() {
  if (!rectAreaLightInitialized) {
    RectAreaLightUniformsLib.init();
    rectAreaLightInitialized = true;
  }
}

// ============================================================================
// TYPES
// ============================================================================

export type LightType = 'point' | 'spot' | 'parallel' | 'ambient' | 'area';
export type FalloffType = 'none' | 'smooth' | 'inverseSquareClamped';
export type ShadowType = 'basic' | 'pcf' | 'pcfSoft' | 'vsm';

/**
 * Color temperature presets in Kelvin
 */
export const COLOR_TEMPERATURE_PRESETS = {
  candle: 1900,
  tungsten40w: 2600,
  tungsten100w: 2850,
  halogen: 3200,
  carbonArc: 5200,
  directSunlight: 5500,
  daylight: 6500,
  cloudyDay: 7000,
  shade: 8000,
  blueSky: 10000,
} as const;

export type ColorTemperaturePreset = keyof typeof COLOR_TEMPERATURE_PRESETS;

/**
 * Point of Interest configuration
 */
export interface PointOfInterest {
  enabled: boolean;
  /** Target type: 'position' for fixed point, 'layer' for layer tracking */
  targetType: 'position' | 'layer';
  /** Fixed target position (when targetType is 'position') */
  position: AnimatableProperty<{ x: number; y: number; z: number }>;
  /** Target layer ID (when targetType is 'layer') */
  targetLayerId?: string;
  /** Offset from target layer's position */
  offset: { x: number; y: number; z: number };
  /** Smoothing factor for lookAt updates (0-1) */
  smoothing: number;
}

/**
 * Path following configuration
 */
export interface PathFollowing {
  enabled: boolean;
  /** Spline layer ID to follow */
  splineLayerId?: string;
  /** Progress along path (0-1) */
  progress: AnimatableProperty<number>;
  /** Auto-orient to path tangent */
  autoOrient: boolean;
  /** Bank angle when following curves */
  bankAngle: AnimatableProperty<number>;
}

/**
 * Enhanced shadow configuration
 */
export interface ShadowConfig {
  enabled: boolean;
  type: ShadowType;
  /** Shadow map resolution */
  mapSize: number;
  /** Shadow darkness (0-100) */
  darkness: number;
  /** Shadow softness/blur radius */
  radius: number;
  /** Shadow bias to prevent artifacts */
  bias: number;
  /** Normal bias for curved surfaces */
  normalBias: number;
  /** Shadow camera near plane */
  cameraNear: number;
  /** Shadow camera far plane */
  cameraFar: number;
  /** Shadow camera frustum size (directional lights) */
  cameraSize: number;
}

/**
 * Light linking - controls which layers this light affects
 */
export interface LightLinking {
  mode: 'include' | 'exclude';
  /** Layer IDs to include or exclude */
  layers: string[];
}

/**
 * Complete light data interface
 */
export interface LightData {
  lightType: LightType;

  // Color
  color: string;
  /** Color temperature in Kelvin (overrides color if set) */
  colorTemperature?: number;
  useColorTemperature: boolean;

  // Intensity
  intensity: number;
  /** Physical intensity in lumens (for PBR workflows) */
  physicalIntensity?: number;
  usePhysicalIntensity: boolean;

  // Falloff
  radius: number;
  falloff: FalloffType;
  falloffDistance: number;

  // Spot light specific
  coneAngle?: number;
  coneFeather?: number;

  // Area light specific
  areaWidth?: number;
  areaHeight?: number;

  // Point of Interest
  pointOfInterest: PointOfInterest;

  // Path following
  pathFollowing: PathFollowing;

  // Shadow configuration
  shadow: ShadowConfig;

  // Light linking
  lightLinking: LightLinking;

  // Animated properties
  animatedIntensity?: AnimatableProperty<number>;
  animatedConeAngle?: AnimatableProperty<number>;
  animatedColor?: AnimatableProperty<string>;
  animatedColorTemperature?: AnimatableProperty<number>;
}

// ============================================================================
// COLOR TEMPERATURE CONVERSION
// ============================================================================

/**
 * Convert color temperature (Kelvin) to RGB
 * Based on Tanner Helland's algorithm
 */
function kelvinToRGB(kelvin: number): { r: number; g: number; b: number } {
  const temp = kelvin / 100;
  let r: number, g: number, b: number;

  // Red
  if (temp <= 66) {
    r = 255;
  } else {
    r = temp - 60;
    r = 329.698727446 * Math.pow(r, -0.1332047592);
    r = Math.max(0, Math.min(255, r));
  }

  // Green
  if (temp <= 66) {
    g = temp;
    g = 99.4708025861 * Math.log(g) - 161.1195681661;
  } else {
    g = temp - 60;
    g = 288.1221695283 * Math.pow(g, -0.0755148492);
  }
  g = Math.max(0, Math.min(255, g));

  // Blue
  if (temp >= 66) {
    b = 255;
  } else if (temp <= 19) {
    b = 0;
  } else {
    b = temp - 10;
    b = 138.5177312231 * Math.log(b) - 305.0447927307;
    b = Math.max(0, Math.min(255, b));
  }

  return { r: r / 255, g: g / 255, b: b / 255 };
}

// ============================================================================
// LIGHT LAYER CLASS
// ============================================================================

export class LightLayer extends BaseLayer {
  private light: THREE.Light;
  private helper: THREE.Object3D | null = null;
  private lightData: LightData;

  // Point of Interest
  private poiTarget: THREE.Vector3 = new THREE.Vector3();
  private smoothedPOI: THREE.Vector3 = new THREE.Vector3();
  private lastPOIFrame: number = -1; // Track last frame for deterministic smoothing

  // Path following callback (set by LayerManager)
  private pathProvider: ((layerId: string, t: number, frame: number) => { point: { x: number; y: number; z: number }; tangent: { x: number; y: number } } | null) | null = null;

  // Layer position getter for POI layer tracking
  private layerPositionGetter: ((layerId: string) => THREE.Vector3 | null) | null = null;

  constructor(layerData: Layer) {
    super(layerData);

    // Extract light-specific data
    this.lightData = this.extractLightData(layerData);

    // Create the appropriate light type
    this.light = this.createLight();
    this.group.add(this.light);

    // Add helper visualization (for editor view)
    this.createHelper();

    // Initialize POI
    if (this.lightData.pointOfInterest.enabled) {
      this.updatePointOfInterest(0);
    }

    // Apply initial blend mode (lights don't use it, but maintain consistency)
    this.initializeBlendMode();
  }

  // ============================================================================
  // DATA EXTRACTION
  // ============================================================================

  private extractLightData(layerData: Layer): LightData {
    const data = layerData.data as any;

    return {
      lightType: data?.lightType ?? 'point',
      color: data?.color ?? '#ffffff',
      colorTemperature: data?.colorTemperature,
      useColorTemperature: data?.useColorTemperature ?? false,
      intensity: data?.intensity ?? 100,
      physicalIntensity: data?.physicalIntensity,
      usePhysicalIntensity: data?.usePhysicalIntensity ?? false,
      radius: data?.radius ?? 500,
      falloff: data?.falloff ?? 'none',
      falloffDistance: data?.falloffDistance ?? 500,
      coneAngle: data?.coneAngle ?? 90,
      coneFeather: data?.coneFeather ?? 50,
      areaWidth: data?.areaWidth ?? 100,
      areaHeight: data?.areaHeight ?? 100,

      pointOfInterest: {
        enabled: data?.pointOfInterest?.enabled ?? false,
        targetType: data?.pointOfInterest?.targetType ?? 'position',
        position: data?.pointOfInterest?.position ?? {
          id: 'poi_pos',
          name: 'POI Position',
          type: 'vector3',
          value: { x: 0, y: 0, z: 0 },
          animated: false,
          keyframes: []
        },
        targetLayerId: data?.pointOfInterest?.targetLayerId,
        offset: data?.pointOfInterest?.offset ?? { x: 0, y: 0, z: 0 },
        smoothing: data?.pointOfInterest?.smoothing ?? 0,
      },

      pathFollowing: {
        enabled: data?.pathFollowing?.enabled ?? false,
        splineLayerId: data?.pathFollowing?.splineLayerId,
        progress: data?.pathFollowing?.progress ?? {
          id: 'path_progress',
          name: 'Path Progress',
          type: 'number',
          value: 0,
          animated: false,
          keyframes: []
        },
        autoOrient: data?.pathFollowing?.autoOrient ?? true,
        bankAngle: data?.pathFollowing?.bankAngle ?? {
          id: 'bank_angle',
          name: 'Bank Angle',
          type: 'number',
          value: 0,
          animated: false,
          keyframes: []
        },
      },

      shadow: {
        enabled: data?.shadow?.enabled ?? data?.castShadows ?? false,
        type: data?.shadow?.type ?? 'pcf',
        mapSize: data?.shadow?.mapSize ?? 1024,
        darkness: data?.shadow?.darkness ?? data?.shadowDarkness ?? 100,
        radius: data?.shadow?.radius ?? data?.shadowDiffusion ?? 1,
        bias: data?.shadow?.bias ?? -0.0001,
        normalBias: data?.shadow?.normalBias ?? 0,
        cameraNear: data?.shadow?.cameraNear ?? 1,
        cameraFar: data?.shadow?.cameraFar ?? 1000,
        cameraSize: data?.shadow?.cameraSize ?? 500,
      },

      lightLinking: {
        mode: data?.lightLinking?.mode ?? 'include',
        layers: data?.lightLinking?.layers ?? [],
      },

      animatedIntensity: data?.animatedIntensity,
      animatedConeAngle: data?.animatedConeAngle,
      animatedColor: data?.animatedColor,
      animatedColorTemperature: data?.animatedColorTemperature,
    };
  }

  // ============================================================================
  // LIGHT CREATION
  // ============================================================================

  private createLight(): THREE.Light {
    const color = this.getEffectiveColor();
    const intensity = this.getEffectiveIntensity();

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

      case 'area': {
        initRectAreaLight();
        const light = new THREE.RectAreaLight(
          color,
          intensity,
          this.lightData.areaWidth ?? 100,
          this.lightData.areaHeight ?? 100
        );
        // Area lights don't cast shadows in Three.js by default
        return light;
      }

      default:
        layerLogger.warn(`LightLayer: Unknown light type: ${this.lightData.lightType}, defaulting to point`);
        return new THREE.PointLight(color, intensity);
    }
  }

  private getEffectiveColor(): THREE.Color {
    if (this.lightData.useColorTemperature && this.lightData.colorTemperature) {
      const rgb = kelvinToRGB(this.lightData.colorTemperature);
      return new THREE.Color(rgb.r, rgb.g, rgb.b);
    }
    return new THREE.Color(this.lightData.color);
  }

  private getEffectiveIntensity(): number {
    if (this.lightData.usePhysicalIntensity && this.lightData.physicalIntensity) {
      // Convert lumens to Three.js intensity (approximate)
      return this.lightData.physicalIntensity / 100;
    }
    return this.lightData.intensity / 100;
  }

  // ============================================================================
  // SHADOW CONFIGURATION
  // ============================================================================

  private configureShadows(light: THREE.PointLight | THREE.SpotLight | THREE.DirectionalLight): void {
    const shadowConfig = this.lightData.shadow;
    light.castShadow = shadowConfig.enabled;

    if (!light.castShadow) return;

    // Shadow map size
    light.shadow.mapSize.width = shadowConfig.mapSize;
    light.shadow.mapSize.height = shadowConfig.mapSize;

    // Shadow type
    switch (shadowConfig.type) {
      case 'basic':
        // BasicShadowMap is set on renderer, not per-light
        break;
      case 'pcf':
        light.shadow.radius = 1;
        break;
      case 'pcfSoft':
        light.shadow.radius = shadowConfig.radius;
        break;
      case 'vsm':
        // VSM requires renderer configuration
        light.shadow.radius = shadowConfig.radius;
        break;
    }

    // Bias
    light.shadow.bias = shadowConfig.bias;
    light.shadow.normalBias = shadowConfig.normalBias;

    // Shadow camera configuration
    if (light instanceof THREE.DirectionalLight) {
      const camera = light.shadow.camera as THREE.OrthographicCamera;
      camera.near = shadowConfig.cameraNear;
      camera.far = shadowConfig.cameraFar;
      camera.left = -shadowConfig.cameraSize / 2;
      camera.right = shadowConfig.cameraSize / 2;
      camera.top = shadowConfig.cameraSize / 2;
      camera.bottom = -shadowConfig.cameraSize / 2;
      camera.updateProjectionMatrix();
    } else if (light instanceof THREE.SpotLight) {
      light.shadow.camera.near = shadowConfig.cameraNear;
      light.shadow.camera.far = shadowConfig.cameraFar;
      light.shadow.camera.updateProjectionMatrix();
    }
  }

  // ============================================================================
  // HELPER VISUALIZATION
  // ============================================================================

  private createHelper(): void {
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

      case 'area': {
        const helper = new RectAreaLightHelper(this.light as THREE.RectAreaLight);
        this.helper = helper;
        this.group.add(helper);
        break;
      }

      case 'ambient':
        // No helper for ambient lights
        break;
    }
  }

  // ============================================================================
  // POINT OF INTEREST
  // ============================================================================

  /**
   * Set callback for getting layer positions (for POI layer tracking)
   */
  setLayerPositionGetter(getter: ((layerId: string) => THREE.Vector3 | null) | null): void {
    this.layerPositionGetter = getter;
  }

  /**
   * Update point of interest target
   */
  private updatePointOfInterest(frame: number): void {
    const poi = this.lightData.pointOfInterest;
    if (!poi.enabled) return;

    // Only spot and parallel lights can look at a target
    if (this.lightData.lightType !== 'spot' && this.lightData.lightType !== 'parallel') {
      return;
    }

    // Get target position
    if (poi.targetType === 'layer' && poi.targetLayerId && this.layerPositionGetter) {
      const layerPos = this.layerPositionGetter(poi.targetLayerId);
      if (layerPos) {
        this.poiTarget.copy(layerPos);
        this.poiTarget.x += poi.offset.x;
        this.poiTarget.y += poi.offset.y;
        this.poiTarget.z += poi.offset.z;
      }
    } else {
      // Use fixed position
      const pos = this.evaluator.evaluate(poi.position, frame);
      this.poiTarget.set(pos.x, pos.y, pos.z);
    }

    // Apply smoothing only on sequential frames for determinism
    // Non-sequential frame access (scrubbing, seeking) resets to target directly
    const isSequentialFrame = frame === this.lastPOIFrame + 1;
    this.lastPOIFrame = frame;

    if (poi.smoothing > 0 && isSequentialFrame) {
      this.smoothedPOI.lerp(this.poiTarget, 1 - poi.smoothing);
    } else {
      this.smoothedPOI.copy(this.poiTarget);
    }

    // Apply lookAt
    if (this.light instanceof THREE.SpotLight) {
      this.light.target.position.copy(this.smoothedPOI);
      this.light.target.updateMatrixWorld();
    } else if (this.light instanceof THREE.DirectionalLight) {
      this.light.target.position.copy(this.smoothedPOI);
      this.light.target.updateMatrixWorld();
    }
  }

  // ============================================================================
  // PATH FOLLOWING
  // ============================================================================

  /**
   * Set path provider callback (from LayerManager's spline provider)
   */
  setPathProvider(provider: ((layerId: string, t: number, frame: number) => { point: { x: number; y: number; z: number }; tangent: { x: number; y: number } } | null) | null): void {
    this.pathProvider = provider;
  }

  /**
   * Update position and orientation from path
   */
  private updatePathFollowing(frame: number): void {
    const path = this.lightData.pathFollowing;
    if (!path.enabled || !path.splineLayerId || !this.pathProvider) return;

    let progress = this.evaluator.evaluate(path.progress, frame);

    // BUG-094 fix: Apply pathPosition audio modifier
    // pathPosition is 0-1, additive to the path progress
    const audioMod = this.currentAudioModifiers;
    if (audioMod.pathPosition !== undefined && audioMod.pathPosition !== 0) {
      progress = Math.max(0, Math.min(1, progress + audioMod.pathPosition));
    }

    const result = this.pathProvider(path.splineLayerId, progress, frame);

    if (!result) return;

    // Update position
    this.group.position.set(result.point.x, -result.point.y, result.point.z);

    // Auto-orient to path tangent
    if (path.autoOrient) {
      const angle = Math.atan2(result.tangent.y, result.tangent.x);
      this.group.rotation.z = -angle;

      // Apply bank angle
      const bankAngle = this.evaluator.evaluate(path.bankAngle, frame);
      this.group.rotation.x = THREE.MathUtils.degToRad(bankAngle);
    }
  }

  // ============================================================================
  // PUBLIC SETTERS
  // ============================================================================

  setLightType(type: LightType): void {
    if (type === this.lightData.lightType) return;

    this.lightData.lightType = type;

    this.group.remove(this.light);
    if ((this.light as any).dispose) {
      (this.light as any).dispose();
    }

    this.light = this.createLight();
    this.group.add(this.light);
    this.createHelper();
  }

  setColor(color: string): void {
    this.lightData.color = color;
    this.lightData.useColorTemperature = false;
    this.light.color.set(color);
  }

  setColorTemperature(kelvin: number): void {
    this.lightData.colorTemperature = kelvin;
    this.lightData.useColorTemperature = true;
    const rgb = kelvinToRGB(kelvin);
    this.light.color.setRGB(rgb.r, rgb.g, rgb.b);
  }

  setIntensity(intensity: number): void {
    this.lightData.intensity = intensity;
    this.lightData.usePhysicalIntensity = false;
    this.light.intensity = intensity / 100;
  }

  setFalloffDistance(distance: number): void {
    this.lightData.falloffDistance = distance;
    if (this.light instanceof THREE.PointLight || this.light instanceof THREE.SpotLight) {
      this.light.distance = this.lightData.falloff === 'none' ? 0 : distance;
    }
  }

  setConeAngle(angle: number): void {
    if (this.light instanceof THREE.SpotLight) {
      this.lightData.coneAngle = angle;
      this.light.angle = THREE.MathUtils.degToRad(angle / 2);
      if (this.helper instanceof THREE.SpotLightHelper) {
        this.helper.update();
      }
    }
  }

  setConeFeather(feather: number): void {
    if (this.light instanceof THREE.SpotLight) {
      this.lightData.coneFeather = feather;
      this.light.penumbra = feather / 100;
    }
  }

  setAreaSize(width: number, height: number): void {
    if (this.light instanceof THREE.RectAreaLight) {
      this.lightData.areaWidth = width;
      this.lightData.areaHeight = height;
      this.light.width = width;
      this.light.height = height;
    }
  }

  setShadowEnabled(enabled: boolean): void {
    this.lightData.shadow.enabled = enabled;
    if (this.light instanceof THREE.PointLight ||
        this.light instanceof THREE.SpotLight ||
        this.light instanceof THREE.DirectionalLight) {
      this.light.castShadow = enabled;
    }
  }

  setShadowType(type: ShadowType): void {
    this.lightData.shadow.type = type;
    if (this.light instanceof THREE.PointLight ||
        this.light instanceof THREE.SpotLight ||
        this.light instanceof THREE.DirectionalLight) {
      this.configureShadows(this.light);
    }
  }

  setPointOfInterestEnabled(enabled: boolean): void {
    this.lightData.pointOfInterest.enabled = enabled;
  }

  setPointOfInterestTarget(layerId: string | null): void {
    if (layerId) {
      this.lightData.pointOfInterest.targetType = 'layer';
      this.lightData.pointOfInterest.targetLayerId = layerId;
    } else {
      this.lightData.pointOfInterest.targetType = 'position';
      this.lightData.pointOfInterest.targetLayerId = undefined;
    }
  }

  setPathFollowingEnabled(enabled: boolean): void {
    this.lightData.pathFollowing.enabled = enabled;
  }

  setPathSpline(splineLayerId: string | null): void {
    this.lightData.pathFollowing.splineLayerId = splineLayerId ?? undefined;
  }

  // ============================================================================
  // DRIVER PROPERTY ACCESS
  // ============================================================================

  /**
   * Get a light property value by driver property path
   * Used by PropertyDriverSystem for property-to-property linking
   */
  getDriverPropertyValue(path: string): number | null {
    switch (path) {
      case 'light.intensity':
        return this.lightData.intensity;
      case 'light.color.r':
        return this.light.color.r * 255;
      case 'light.color.g':
        return this.light.color.g * 255;
      case 'light.color.b':
        return this.light.color.b * 255;
      case 'light.colorTemperature':
        return this.lightData.colorTemperature ?? 6500;
      case 'light.coneAngle':
        return this.lightData.coneAngle ?? 90;
      case 'light.penumbra':
        return (this.lightData.coneFeather ?? 50);
      case 'light.falloff':
        return this.lightData.falloffDistance;
      case 'light.shadow.intensity':
        return this.lightData.shadow.darkness;
      case 'light.shadow.softness':
        return this.lightData.shadow.radius;
      case 'light.shadow.bias':
        return this.lightData.shadow.bias * 10000; // Scale for readability
      case 'light.poi.x':
        return this.poiTarget.x;
      case 'light.poi.y':
        return this.poiTarget.y;
      case 'light.poi.z':
        return this.poiTarget.z;
      case 'light.areaSize.width':
        return this.lightData.areaWidth ?? 100;
      case 'light.areaSize.height':
        return this.lightData.areaHeight ?? 100;
      case 'light.physicalIntensity':
        return this.lightData.physicalIntensity ?? (this.lightData.intensity * 100);
      default:
        return null;
    }
  }

  /**
   * Set a light property value by driver property path
   * Used by PropertyDriverSystem for driven values
   */
  setDriverPropertyValue(path: string, value: number): void {
    switch (path) {
      case 'light.intensity':
        this.light.intensity = value / 100;
        this.lightData.intensity = value;
        break;
      case 'light.color.r':
        this.light.color.r = Math.max(0, Math.min(1, value / 255));
        break;
      case 'light.color.g':
        this.light.color.g = Math.max(0, Math.min(1, value / 255));
        break;
      case 'light.color.b':
        this.light.color.b = Math.max(0, Math.min(1, value / 255));
        break;
      case 'light.colorTemperature':
        this.setColorTemperature(value);
        break;
      case 'light.coneAngle':
        this.setConeAngle(value);
        break;
      case 'light.penumbra':
        this.setConeFeather(value);
        break;
      case 'light.falloff':
        this.setFalloffDistance(value);
        break;
      case 'light.shadow.intensity':
        this.lightData.shadow.darkness = value;
        break;
      case 'light.shadow.softness':
        this.lightData.shadow.radius = value;
        if (this.light instanceof THREE.PointLight ||
            this.light instanceof THREE.SpotLight ||
            this.light instanceof THREE.DirectionalLight) {
          this.light.shadow.radius = value;
        }
        break;
      case 'light.shadow.bias':
        this.lightData.shadow.bias = value / 10000;
        if (this.light instanceof THREE.PointLight ||
            this.light instanceof THREE.SpotLight ||
            this.light instanceof THREE.DirectionalLight) {
          this.light.shadow.bias = value / 10000;
        }
        break;
      case 'light.poi.x':
        this.poiTarget.x = value;
        this.updatePointOfInterest(0);
        break;
      case 'light.poi.y':
        this.poiTarget.y = value;
        this.updatePointOfInterest(0);
        break;
      case 'light.poi.z':
        this.poiTarget.z = value;
        this.updatePointOfInterest(0);
        break;
      case 'light.areaSize.width':
        this.setAreaSize(value, this.lightData.areaHeight ?? 100);
        break;
      case 'light.areaSize.height':
        this.setAreaSize(this.lightData.areaWidth ?? 100, value);
        break;
      case 'light.physicalIntensity':
        this.lightData.physicalIntensity = value;
        if (this.lightData.usePhysicalIntensity) {
          this.light.intensity = value / 100;
        }
        break;
    }
  }

  // ============================================================================
  // GETTERS
  // ============================================================================

  getLight(): THREE.Light {
    return this.light;
  }

  getLightData(): LightData {
    return { ...this.lightData };
  }

  getLightLinking(): LightLinking {
    return { ...this.lightData.lightLinking };
  }

  /**
   * Check if this light should affect a given layer
   */
  shouldAffectLayer(layerId: string): boolean {
    const linking = this.lightData.lightLinking;

    if (linking.layers.length === 0) {
      // No layers specified - affect all
      return true;
    }

    const isInList = linking.layers.includes(layerId);

    if (linking.mode === 'include') {
      return isInList;
    } else {
      return !isInList;
    }
  }

  setHelperVisible(visible: boolean): void {
    if (this.helper) {
      this.helper.visible = visible;
    }
  }

  // ============================================================================
  // FRAME EVALUATION
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Path following (overrides transform)
    if (this.lightData.pathFollowing.enabled) {
      this.updatePathFollowing(frame);
    }

    // Point of Interest
    if (this.lightData.pointOfInterest.enabled) {
      this.updatePointOfInterest(frame);
    }

    // Animated intensity
    if (this.lightData.animatedIntensity?.animated) {
      const intensity = this.evaluator.evaluate(this.lightData.animatedIntensity, frame);
      this.light.intensity = intensity / 100;
    }

    // Animated cone angle
    if (this.lightData.animatedConeAngle?.animated && this.light instanceof THREE.SpotLight) {
      const angle = this.evaluator.evaluate(this.lightData.animatedConeAngle, frame);
      this.light.angle = THREE.MathUtils.degToRad(angle / 2);
      if (this.helper instanceof THREE.SpotLightHelper) {
        this.helper.update();
      }
    }

    // Animated color
    if (this.lightData.animatedColor?.animated) {
      const color = this.evaluator.evaluate(this.lightData.animatedColor, frame);
      this.light.color.set(color);
    }

    // Animated color temperature
    if (this.lightData.animatedColorTemperature?.animated && this.lightData.useColorTemperature) {
      const kelvin = this.evaluator.evaluate(this.lightData.animatedColorTemperature, frame);
      const rgb = kelvinToRGB(kelvin);
      this.light.color.setRGB(rgb.r, rgb.g, rgb.b);
    }

    // Update helpers
    if (this.helper) {
      if (this.helper instanceof THREE.PointLightHelper ||
          this.helper instanceof THREE.SpotLightHelper ||
          this.helper instanceof THREE.DirectionalLightHelper) {
        this.helper.update();
      }
    }
  }

  protected override onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    const props = state.properties;

    // Apply evaluated intensity
    if (props['intensity'] !== undefined) {
      this.light.intensity = (props['intensity'] as number) / 100;
    }

    // Apply evaluated cone angle
    if (props['coneAngle'] !== undefined && this.light instanceof THREE.SpotLight) {
      this.light.angle = THREE.MathUtils.degToRad((props['coneAngle'] as number) / 2);
      if (this.helper instanceof THREE.SpotLightHelper) {
        this.helper.update();
      }
    }

    // Apply evaluated color
    if (props['color'] !== undefined) {
      this.light.color.set(props['color'] as string);
    }

    // Apply evaluated color temperature
    if (props['colorTemperature'] !== undefined && this.lightData.useColorTemperature) {
      const rgb = kelvinToRGB(props['colorTemperature'] as number);
      this.light.color.setRGB(rgb.r, rgb.g, rgb.b);
    }

    // Apply evaluated falloff distance
    if (props['falloffDistance'] !== undefined) {
      if (this.light instanceof THREE.PointLight || this.light instanceof THREE.SpotLight) {
        this.light.distance = this.lightData.falloff === 'none' ? 0 : (props['falloffDistance'] as number);
      }
    }

    // Apply POI position
    if (props['poi.x'] !== undefined || props['poi.y'] !== undefined || props['poi.z'] !== undefined) {
      this.poiTarget.set(
        (props['poi.x'] as number) ?? this.poiTarget.x,
        (props['poi.y'] as number) ?? this.poiTarget.y,
        (props['poi.z'] as number) ?? this.poiTarget.z
      );
      this.updatePointOfInterest(0);
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

    if (data.colorTemperature !== undefined) {
      this.setColorTemperature(data.colorTemperature);
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

    if (data.areaWidth !== undefined || data.areaHeight !== undefined) {
      this.setAreaSize(
        data.areaWidth ?? this.lightData.areaWidth ?? 100,
        data.areaHeight ?? this.lightData.areaHeight ?? 100
      );
    }

    if (data.shadow !== undefined) {
      Object.assign(this.lightData.shadow, data.shadow);
      if (this.light instanceof THREE.PointLight ||
          this.light instanceof THREE.SpotLight ||
          this.light instanceof THREE.DirectionalLight) {
        this.configureShadows(this.light);
      }
    }

    if (data.pointOfInterest !== undefined) {
      Object.assign(this.lightData.pointOfInterest, data.pointOfInterest);
    }

    if (data.pathFollowing !== undefined) {
      Object.assign(this.lightData.pathFollowing, data.pathFollowing);
    }

    if (data.lightLinking !== undefined) {
      Object.assign(this.lightData.lightLinking, data.lightLinking);
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
    if (data.animatedColorTemperature !== undefined) {
      this.lightData.animatedColorTemperature = data.animatedColorTemperature;
    }
  }

  protected onDispose(): void {
    if ((this.light as any).dispose) {
      (this.light as any).dispose();
    }
    if (this.helper && (this.helper as any).dispose) {
      (this.helper as any).dispose();
    }
  }
}
