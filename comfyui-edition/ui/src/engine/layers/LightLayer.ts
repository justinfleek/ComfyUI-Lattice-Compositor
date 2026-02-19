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

import * as THREE from "three";
import { RectAreaLightHelper } from "three/addons/helpers/RectAreaLightHelper.js";
import { RectAreaLightUniformsLib } from "three/addons/lights/RectAreaLightUniformsLib.js";
import type { AnimatableProperty, Layer } from "@/types/project";
import { createAnimatableProperty } from "@/types/animation";
import { layerLogger } from "@/utils/logger";
import type { JSONValue } from "@/types/dataAsset";
import { BaseLayer } from "./BaseLayer";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

// Initialize RectAreaLight uniforms (required for area lights)
let rectAreaLightInitialized = false;
function initRectAreaLight() {
  if (!rectAreaLightInitialized) {
    RectAreaLightUniformsLib.init();
    rectAreaLightInitialized = true;
  }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

export type LightType = "point" | "spot" | "parallel" | "ambient" | "area";
export type FalloffType = "none" | "smooth" | "inverseSquareClamped";
export type ShadowType = "basic" | "pcf" | "pcfSoft" | "vsm";

/**
 * Type guard for objects with dispose method
 */
interface Disposable {
  dispose(): void;
}

function hasDispose(obj: RuntimeValue): obj is Disposable {
  return (
    typeof obj === "object" &&
    obj !== null &&
    "dispose" in obj &&
    typeof (obj as { dispose: JSONValue }).dispose === "function"
  );
}

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
  targetType: "position" | "layer";
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
  mode: "include" | "exclude";
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

// ════════════════════════════════════════════════════════════════════════════
//                                        // color // temperature // conversion
// ════════════════════════════════════════════════════════════════════════════

/**
 * Convert color temperature (Kelvin) to RGB
 * Based on Tanner Helland's algorithm
 */
function kelvinToRGB(kelvin: number): { r: number; g: number; b: number } {
  // Validate kelvin (NaN would produce NaN RGB values)
  const validKelvin = Number.isFinite(kelvin) ? kelvin : 6500;
  const temp = validKelvin / 100;
  let r: number, g: number, b: number;

  // Red
  if (temp <= 66) {
    r = 255;
  } else {
    r = temp - 60;
    r = 329.698727446 * r ** -0.1332047592;
    r = Math.max(0, Math.min(255, r));
  }

  // Green
  if (temp <= 66) {
    g = temp;
    g = 99.4708025861 * Math.log(g) - 161.1195681661;
  } else {
    g = temp - 60;
    g = 288.1221695283 * g ** -0.0755148492;
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

// ════════════════════════════════════════════════════════════════════════════
//                                                   // light // layer // class
// ════════════════════════════════════════════════════════════════════════════

export class LightLayer extends BaseLayer {
  private light: THREE.Light;
  private helper: THREE.Object3D | null = null;
  private lightData: LightData;

  // Point of Interest
  private poiTarget: THREE.Vector3 = new THREE.Vector3();
  private smoothedPOI: THREE.Vector3 = new THREE.Vector3();
  private lastPOIFrame: number = -1; // Track last frame for deterministic smoothing

  // Path following callback (set by LayerManager)
  private pathProvider:
    | ((
        layerId: string,
        t: number,
        frame: number,
      ) => {
        point: { x: number; y: number; z: number };
        tangent: { x: number; y: number };
      } | null)
    | null = null;

  // Layer position getter for POI layer tracking
  private layerPositionGetter:
    | ((layerId: string) => THREE.Vector3 | null)
    | null = null;

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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                        // data // extraction
  // ════════════════════════════════════════════════════════════════════════════

  private extractLightData(layerData: Layer): LightData {
    if (!layerData.data || typeof layerData.data !== "object") {
      return {
        lightType: "point",
        color: "#ffffff",
        useColorTemperature: false,
        intensity: 100,
        usePhysicalIntensity: false,
        radius: 500,
        falloff: "none",
        falloffDistance: 500,
        pointOfInterest: {
          enabled: false,
          targetType: "position",
          position: {
            id: "poi_position",
            name: "Point of Interest Position",
            type: "position",
            value: { x: 0, y: 0, z: 0 },
            animated: false,
            keyframes: [],
          },
          offset: { x: 0, y: 0, z: 0 },
          smoothing: 0.1,
        },
        pathFollowing: {
          enabled: false,
          splineLayerId: "",
          progress: {
            id: "path_progress",
            name: "Path Progress",
            type: "number",
            value: 0,
            animated: false,
            keyframes: [],
          },
          autoOrient: true,
          bankAngle: {
            id: "bank_angle",
            name: "Bank Angle",
            type: "number",
            value: 0,
            animated: false,
            keyframes: [],
          },
        },
        shadow: {
          enabled: false,
          type: "pcf",
          mapSize: 1024,
          darkness: 100,
          radius: 1,
          bias: -0.0001,
          normalBias: 0,
          cameraNear: 1,
          cameraFar: 1000,
          cameraSize: 100,
        },
        lightLinking: {
          mode: "include",
          layers: [],
        },
      };
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/null checks
    // Pattern match: data ∈ object | null → LightData (explicit defaults)
    const data = layerData.data as Partial<LightData> & { castShadows?: boolean; shadowDarkness?: number; shadowDiffusion?: number };
    
    // Pattern match: lightType ∈ string | undefined → string
    const lightTypeValue = (typeof data === "object" && data !== null && "lightType" in data && typeof data.lightType === "string")
      ? data.lightType
      : "point";
    const lightType = lightTypeValue === "point" || lightTypeValue === "spot" || lightTypeValue === "parallel" || lightTypeValue === "ambient" || lightTypeValue === "area"
      ? lightTypeValue
      : "point";
    
    // Pattern match: color ∈ string | undefined → string
    const color = (typeof data === "object" && data !== null && "color" in data && typeof data.color === "string")
      ? data.color
      : "#ffffff";
    
    // Pattern match: colorTemperature ∈ number | undefined → number | 0 (explicit default)
    const colorTemperature = (typeof data === "object" && data !== null && "colorTemperature" in data && typeof data.colorTemperature === "number")
      ? data.colorTemperature
      : 0;
    
    // Pattern match: useColorTemperature ∈ boolean | undefined → boolean
    const useColorTemperature = (typeof data === "object" && data !== null && "useColorTemperature" in data && typeof data.useColorTemperature === "boolean")
      ? data.useColorTemperature
      : false;
    
    // Pattern match: intensity ∈ number | undefined → number
    const intensity = (typeof data === "object" && data !== null && "intensity" in data && typeof data.intensity === "number")
      ? data.intensity
      : 100;
    
    // Pattern match: physicalIntensity ∈ number | undefined → number | 0 (explicit default)
    const physicalIntensity = (typeof data === "object" && data !== null && "physicalIntensity" in data && typeof data.physicalIntensity === "number")
      ? data.physicalIntensity
      : 0;
    
    // Pattern match: usePhysicalIntensity ∈ boolean | undefined → boolean
    const usePhysicalIntensity = (typeof data === "object" && data !== null && "usePhysicalIntensity" in data && typeof data.usePhysicalIntensity === "boolean")
      ? data.usePhysicalIntensity
      : false;
    
    // Pattern match: radius ∈ number | undefined → number
    const radius = (typeof data === "object" && data !== null && "radius" in data && typeof data.radius === "number")
      ? data.radius
      : 500;
    
    // Pattern match: falloff ∈ string | undefined → string
    const falloffValue = (typeof data === "object" && data !== null && "falloff" in data && typeof data.falloff === "string")
      ? data.falloff
      : "none";
    const falloff = falloffValue === "none" || falloffValue === "smooth" || falloffValue === "inverseSquareClamped"
      ? falloffValue
      : "none";
    
    // Pattern match: falloffDistance ∈ number | undefined → number
    const falloffDistance = (typeof data === "object" && data !== null && "falloffDistance" in data && typeof data.falloffDistance === "number")
      ? data.falloffDistance
      : 500;
    
    // Pattern match: coneAngle ∈ number | undefined → number
    const coneAngle = (typeof data === "object" && data !== null && "coneAngle" in data && typeof data.coneAngle === "number")
      ? data.coneAngle
      : 90;
    
    // Pattern match: coneFeather ∈ number | undefined → number
    const coneFeather = (typeof data === "object" && data !== null && "coneFeather" in data && typeof data.coneFeather === "number")
      ? data.coneFeather
      : 50;
    
    // Pattern match: areaWidth ∈ number | undefined → number
    const areaWidth = (typeof data === "object" && data !== null && "areaWidth" in data && typeof data.areaWidth === "number")
      ? data.areaWidth
      : 100;
    
    // Pattern match: areaHeight ∈ number | undefined → number
    const areaHeight = (typeof data === "object" && data !== null && "areaHeight" in data && typeof data.areaHeight === "number")
      ? data.areaHeight
      : 100;
    
    // Pattern match: pointOfInterest ∈ object | undefined → PointOfInterest
    const pointOfInterestData = (typeof data === "object" && data !== null && "pointOfInterest" in data && typeof data.pointOfInterest === "object" && data.pointOfInterest !== null)
      ? data.pointOfInterest
      : {};
    const poiEnabled = ("enabled" in pointOfInterestData && typeof pointOfInterestData.enabled === "boolean")
      ? pointOfInterestData.enabled
      : false;
    const poiTargetTypeValue = ("targetType" in pointOfInterestData && typeof pointOfInterestData.targetType === "string")
      ? pointOfInterestData.targetType
      : "position";
    const poiTargetType = poiTargetTypeValue === "position" || poiTargetTypeValue === "layer"
      ? poiTargetTypeValue
      : "position";
    // Deterministic: Create proper AnimatableProperty for poiPosition
    const poiPositionRaw = ("position" in pointOfInterestData && typeof pointOfInterestData.position === "object" && pointOfInterestData.position !== null && "type" in pointOfInterestData.position)
      ? pointOfInterestData.position
      : null;
    const poiPosition = poiPositionRaw !== null
      ? (poiPositionRaw as AnimatableProperty<{ x: number; y: number; z: number }>)
      : createAnimatableProperty("POI Position", { x: 0, y: 0, z: 0 }, "vector3");
    const poiTargetLayerId = ("targetLayerId" in pointOfInterestData && typeof pointOfInterestData.targetLayerId === "string")
      ? pointOfInterestData.targetLayerId
      : "";
    const poiOffsetRaw = ("offset" in pointOfInterestData && typeof pointOfInterestData.offset === "object" && pointOfInterestData.offset !== null && "x" in pointOfInterestData.offset && "y" in pointOfInterestData.offset && "z" in pointOfInterestData.offset)
      ? pointOfInterestData.offset
      : null;
    // Type guard: validate offset has numeric x, y, z properties
    const poiOffset: { x: number; y: number; z: number } = (poiOffsetRaw !== null &&
      typeof (poiOffsetRaw as { x?: JSONValue; y?: JSONValue; z?: JSONValue }).x === "number" &&
      typeof (poiOffsetRaw as { x?: JSONValue; y?: JSONValue; z?: JSONValue }).y === "number" &&
      typeof (poiOffsetRaw as { x?: JSONValue; y?: JSONValue; z?: JSONValue }).z === "number")
      ? {
          x: (poiOffsetRaw as { x: number; y: number; z: number }).x,
          y: (poiOffsetRaw as { x: number; y: number; z: number }).y,
          z: (poiOffsetRaw as { x: number; y: number; z: number }).z,
        }
      : { x: 0, y: 0, z: 0 };
    const poiSmoothing = ("smoothing" in pointOfInterestData && typeof pointOfInterestData.smoothing === "number")
      ? pointOfInterestData.smoothing
      : 0;
    
    // Pattern match: pathFollowing ∈ object | undefined → PathFollowing
    const pathFollowingData = (typeof data === "object" && data !== null && "pathFollowing" in data && typeof data.pathFollowing === "object" && data.pathFollowing !== null)
      ? data.pathFollowing
      : {};
    const pathEnabled = ("enabled" in pathFollowingData && typeof pathFollowingData.enabled === "boolean")
      ? pathFollowingData.enabled
      : false;
    const pathSplineLayerId = ("splineLayerId" in pathFollowingData && typeof pathFollowingData.splineLayerId === "string")
      ? pathFollowingData.splineLayerId
      : "";
    // Deterministic: Create proper AnimatableProperty for pathProgress
    const pathProgressRaw = ("progress" in pathFollowingData && typeof pathFollowingData.progress === "object" && pathFollowingData.progress !== null && "type" in pathFollowingData.progress)
      ? pathFollowingData.progress
      : null;
    const pathProgress = pathProgressRaw !== null
      ? (pathProgressRaw as AnimatableProperty<number>)
      : createAnimatableProperty("Path Progress", 0, "number");
    const pathAutoOrient = ("autoOrient" in pathFollowingData && typeof pathFollowingData.autoOrient === "boolean")
      ? pathFollowingData.autoOrient
      : true;
    // Deterministic: Create proper AnimatableProperty for pathBankAngle
    const pathBankAngleRaw = ("bankAngle" in pathFollowingData && typeof pathFollowingData.bankAngle === "object" && pathFollowingData.bankAngle !== null && "type" in pathFollowingData.bankAngle)
      ? pathFollowingData.bankAngle
      : null;
    const pathBankAngle = pathBankAngleRaw !== null
      ? (pathBankAngleRaw as AnimatableProperty<number>)
      : createAnimatableProperty("Bank Angle", 0, "number");
    
    // Pattern match: shadow ∈ object | undefined → ShadowConfig
    const shadowData = (typeof data === "object" && data !== null && "shadow" in data && typeof data.shadow === "object" && data.shadow !== null)
      ? data.shadow
      : {};
    const castShadowsValue = (typeof data === "object" && data !== null && "castShadows" in data && typeof data.castShadows === "boolean")
      ? data.castShadows
      : false;
    const shadowEnabled = ("enabled" in shadowData && typeof shadowData.enabled === "boolean")
      ? shadowData.enabled
      : castShadowsValue;
    const shadowTypeValue = ("type" in shadowData && typeof shadowData.type === "string")
      ? shadowData.type
      : "pcf";
    const shadowType = shadowTypeValue === "basic" || shadowTypeValue === "pcf" || shadowTypeValue === "pcfSoft" || shadowTypeValue === "vsm"
      ? shadowTypeValue
      : "pcf";
    const shadowMapSize = ("mapSize" in shadowData && typeof shadowData.mapSize === "number")
      ? shadowData.mapSize
      : 1024;
    const shadowDarknessValue = (typeof data === "object" && data !== null && "shadowDarkness" in data && typeof data.shadowDarkness === "number")
      ? data.shadowDarkness
      : 100;
    const shadowDarkness = ("darkness" in shadowData && typeof shadowData.darkness === "number")
      ? shadowData.darkness
      : shadowDarknessValue;
    const shadowDiffusionValue = (typeof data === "object" && data !== null && "shadowDiffusion" in data && typeof data.shadowDiffusion === "number")
      ? data.shadowDiffusion
      : 1;
    const shadowRadius = ("radius" in shadowData && typeof shadowData.radius === "number")
      ? shadowData.radius
      : shadowDiffusionValue;
    const shadowBias = ("bias" in shadowData && typeof shadowData.bias === "number")
      ? shadowData.bias
      : -0.0001;
    const shadowNormalBias = ("normalBias" in shadowData && typeof shadowData.normalBias === "number")
      ? shadowData.normalBias
      : 0;
    const shadowCameraNear = ("cameraNear" in shadowData && typeof shadowData.cameraNear === "number")
      ? shadowData.cameraNear
      : 1;
    const shadowCameraFar = ("cameraFar" in shadowData && typeof shadowData.cameraFar === "number")
      ? shadowData.cameraFar
      : 1000;
    const shadowCameraSize = ("cameraSize" in shadowData && typeof shadowData.cameraSize === "number")
      ? shadowData.cameraSize
      : 500;
    
    // Pattern match: lightLinking ∈ object | undefined → LightLinking
    const lightLinkingData = (typeof data === "object" && data !== null && "lightLinking" in data && typeof data.lightLinking === "object" && data.lightLinking !== null)
      ? data.lightLinking
      : {};
    const linkingModeValue = ("mode" in lightLinkingData && typeof lightLinkingData.mode === "string")
      ? lightLinkingData.mode
      : "include";
    const linkingMode = linkingModeValue === "include" || linkingModeValue === "exclude"
      ? linkingModeValue
      : "include";
    const linkingLayers = ("layers" in lightLinkingData && Array.isArray(lightLinkingData.layers))
      ? lightLinkingData.layers
      : [];
    
    // Deterministic: Create proper AnimatableProperty defaults instead of empty objects
    const animatedIntensity = (typeof data === "object" && data !== null && "animatedIntensity" in data && typeof data.animatedIntensity === "object" && data.animatedIntensity !== null && "type" in data.animatedIntensity)
      ? data.animatedIntensity as AnimatableProperty<number>
      : createAnimatableProperty("Intensity", intensity, "number");
    const animatedConeAngle = (typeof data === "object" && data !== null && "animatedConeAngle" in data && typeof data.animatedConeAngle === "object" && data.animatedConeAngle !== null && "type" in data.animatedConeAngle)
      ? data.animatedConeAngle as AnimatableProperty<number>
      : createAnimatableProperty("Cone Angle", coneAngle, "number");
    // Deterministic: animatedColor is AnimatableProperty<string> (hex color string)
    const animatedColorRaw = (typeof data === "object" && data !== null && "animatedColor" in data && typeof data.animatedColor === "object" && data.animatedColor !== null && "type" in data.animatedColor)
      ? data.animatedColor
      : null;
    const animatedColor = animatedColorRaw !== null
      ? (animatedColorRaw as AnimatableProperty<string>)
      : createAnimatableProperty("Color", color, "color");
    const animatedColorTemperature = (typeof data === "object" && data !== null && "animatedColorTemperature" in data && typeof data.animatedColorTemperature === "object" && data.animatedColorTemperature !== null && "type" in data.animatedColorTemperature)
      ? data.animatedColorTemperature as AnimatableProperty<number>
      : createAnimatableProperty("Color Temperature", colorTemperature, "number");

    return {
      lightType,
      color,
      colorTemperature,
      useColorTemperature,
      intensity,
      physicalIntensity,
      usePhysicalIntensity,
      radius,
      falloff,
      falloffDistance,
      coneAngle,
      coneFeather,
      areaWidth,
      areaHeight,

      pointOfInterest: {
        enabled: poiEnabled,
        targetType: poiTargetType,
        position: poiPosition,
        targetLayerId: poiTargetLayerId,
        offset: poiOffset,
        smoothing: poiSmoothing,
      },

      pathFollowing: {
        enabled: pathEnabled,
        splineLayerId: pathSplineLayerId,
        progress: pathProgress,
        autoOrient: pathAutoOrient,
        bankAngle: pathBankAngle,
      },

      shadow: {
        enabled: shadowEnabled,
        type: shadowType,
        mapSize: shadowMapSize,
        darkness: shadowDarkness,
        radius: shadowRadius,
        bias: shadowBias,
        normalBias: shadowNormalBias,
        cameraNear: shadowCameraNear,
        cameraFar: shadowCameraFar,
        cameraSize: shadowCameraSize,
      },

      lightLinking: {
        mode: linkingMode,
        layers: linkingLayers,
      },

      animatedIntensity,
      animatedConeAngle,
      animatedColor,
      animatedColorTemperature,
    };
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                         // light // creation
  // ════════════════════════════════════════════════════════════════════════════

  private createLight(): THREE.Light {
    const color = this.getEffectiveColor();
    const intensity = this.getEffectiveIntensity();

    switch (this.lightData.lightType) {
      case "point": {
        const light = new THREE.PointLight(color, intensity);
        light.distance =
          this.lightData.falloff === "none"
            ? 0
            : this.lightData.falloffDistance;
        light.decay = this.lightData.falloff === "inverseSquareClamped" ? 2 : 1;
        this.configureShadows(light);
        return light;
      }

      case "spot": {
        const light = new THREE.SpotLight(color, intensity);
        light.distance =
          this.lightData.falloff === "none"
            ? 0
            : this.lightData.falloffDistance;
        light.decay = this.lightData.falloff === "inverseSquareClamped" ? 2 : 1;
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        // Pattern match: coneAngle ∈ number | undefined → number (default 90)
        const coneAngleValue = (typeof this.lightData.coneAngle === "number" && Number.isFinite(this.lightData.coneAngle)) ? this.lightData.coneAngle : 90;
        light.angle = THREE.MathUtils.degToRad(coneAngleValue / 2);
        // Pattern match: coneFeather ∈ number | undefined → number (default 50)
        const coneFeatherValue = (typeof this.lightData.coneFeather === "number" && Number.isFinite(this.lightData.coneFeather)) ? this.lightData.coneFeather : 50;
        light.penumbra = coneFeatherValue / 100;
        this.configureShadows(light);
        return light;
      }

      case "parallel": {
        const light = new THREE.DirectionalLight(color, intensity);
        this.configureShadows(light);
        return light;
      }

      case "ambient": {
        return new THREE.AmbientLight(color, intensity);
      }

      case "area": {
        initRectAreaLight();
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        // Pattern match: areaWidth ∈ number | undefined → number (default 100)
        const areaWidthValue = (typeof this.lightData.areaWidth === "number" && Number.isFinite(this.lightData.areaWidth)) ? this.lightData.areaWidth : 100;
        // Pattern match: areaHeight ∈ number | undefined → number (default 100)
        const areaHeightValue = (typeof this.lightData.areaHeight === "number" && Number.isFinite(this.lightData.areaHeight)) ? this.lightData.areaHeight : 100;
        const light = new THREE.RectAreaLight(
          color,
          intensity,
          areaWidthValue,
          areaHeightValue,
        );
        // Area lights don't cast shadows in Three.js by default
        return light;
      }

      default:
        layerLogger.warn(
          `LightLayer: Unknown light type: ${this.lightData.lightType}, defaulting to point`,
        );
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
    if (
      this.lightData.usePhysicalIntensity &&
      this.lightData.physicalIntensity
    ) {
      // Convert lumens to Three.js intensity (approximate)
      return this.lightData.physicalIntensity / 100;
    }
    return this.lightData.intensity / 100;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                   // shadow // configuration
  // ════════════════════════════════════════════════════════════════════════════

  private configureShadows(
    light: THREE.PointLight | THREE.SpotLight | THREE.DirectionalLight,
  ): void {
    const shadowConfig = this.lightData.shadow;
    light.castShadow = shadowConfig.enabled;

    if (!light.castShadow) return;

    // Shadow map size
    light.shadow.mapSize.width = shadowConfig.mapSize;
    light.shadow.mapSize.height = shadowConfig.mapSize;

    // Shadow type
    switch (shadowConfig.type) {
      case "basic":
        // BasicShadowMap is set on renderer, not per-light
        break;
      case "pcf":
        light.shadow.radius = 1;
        break;
      case "pcfSoft":
        light.shadow.radius = shadowConfig.radius;
        break;
      case "vsm":
        //                                                                       // vsm
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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                   // helper // visualization
  // ════════════════════════════════════════════════════════════════════════════

  private createHelper(): void {
    if (this.helper) {
      this.group.remove(this.helper);
      if (hasDispose(this.helper)) {
        this.helper.dispose();
      }
    }

    switch (this.lightData.lightType) {
      case "point": {
        const helper = new THREE.PointLightHelper(
          this.light as THREE.PointLight,
          this.lightData.radius / 10,
        );
        this.helper = helper;
        this.group.add(helper);
        break;
      }

      case "spot": {
        const helper = new THREE.SpotLightHelper(this.light as THREE.SpotLight);
        this.helper = helper;
        this.group.add(helper);
        break;
      }

      case "parallel": {
        const helper = new THREE.DirectionalLightHelper(
          this.light as THREE.DirectionalLight,
          50,
        );
        this.helper = helper;
        this.group.add(helper);
        break;
      }

      case "area": {
        const helper = new RectAreaLightHelper(
          this.light as THREE.RectAreaLight,
        );
        this.helper = helper;
        this.group.add(helper);
        break;
      }

      case "ambient":
        // No helper for ambient lights
        break;
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                   // point // of // interest
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Set callback for getting layer positions (for POI layer tracking)
   */
  setLayerPositionGetter(
    getter: ((layerId: string) => THREE.Vector3 | null) | null,
  ): void {
    this.layerPositionGetter = getter;
  }

  /**
   * Update point of interest target
   */
  private updatePointOfInterest(frame: number): void {
    const poi = this.lightData.pointOfInterest;
    if (!poi.enabled) return;

    // Only spot and parallel lights can look at a target
    if (
      this.lightData.lightType !== "spot" &&
      this.lightData.lightType !== "parallel"
    ) {
      return;
    }

    // Get target position
    if (
      poi.targetType === "layer" &&
      poi.targetLayerId &&
      this.layerPositionGetter
    ) {
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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                         // path // following
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Set path provider callback (from LayerManager's spline provider)
   */
  setPathProvider(
    provider:
      | ((
          layerId: string,
          t: number,
          frame: number,
        ) => {
          point: { x: number; y: number; z: number };
          tangent: { x: number; y: number };
        } | null)
      | null,
  ): void {
    this.pathProvider = provider;
  }

  /**
   * Update position and orientation from path
   */
  private updatePathFollowing(frame: number): void {
    const path = this.lightData.pathFollowing;
    if (!path.enabled || !path.splineLayerId || !this.pathProvider) return;

    let progress = this.evaluator.evaluate(path.progress, frame);

    // Apply audio-reactive path position modifier (0-1 additive to progress)
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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                         // public // setters
  // ════════════════════════════════════════════════════════════════════════════

  setLightType(type: LightType): void {
    if (type === this.lightData.lightType) return;

    this.lightData.lightType = type;

    this.group.remove(this.light);
    if (hasDispose(this.light)) {
      this.light.dispose();
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
    // Validate intensity (NaN would corrupt light rendering)
    const validIntensity = Number.isFinite(intensity) ? intensity : 100;
    this.lightData.intensity = validIntensity;
    this.lightData.usePhysicalIntensity = false;
    this.light.intensity = validIntensity / 100;
  }

  setFalloffDistance(distance: number): void {
    // Validate distance (NaN would corrupt light falloff)
    const validDistance = Number.isFinite(distance) ? distance : 500;
    this.lightData.falloffDistance = validDistance;
    if (
      this.light instanceof THREE.PointLight ||
      this.light instanceof THREE.SpotLight
    ) {
      this.light.distance =
        this.lightData.falloff === "none" ? 0 : validDistance;
    }
  }

  setConeAngle(angle: number): void {
    if (this.light instanceof THREE.SpotLight) {
      // Validate angle (NaN would corrupt light cone)
      const validAngle = Number.isFinite(angle) ? angle : 90;
      this.lightData.coneAngle = validAngle;
      this.light.angle = THREE.MathUtils.degToRad(validAngle / 2);
      if (this.helper instanceof THREE.SpotLightHelper) {
        this.helper.update();
      }
    }
  }

  setConeFeather(feather: number): void {
    if (this.light instanceof THREE.SpotLight) {
      // Validate feather (NaN would corrupt penumbra)
      const validFeather = Number.isFinite(feather) ? feather : 50;
      this.lightData.coneFeather = validFeather;
      this.light.penumbra = validFeather / 100;
    }
  }

  setAreaSize(width: number, height: number): void {
    if (this.light instanceof THREE.RectAreaLight) {
      // Validate dimensions (NaN/0 would corrupt area light)
      const validWidth = Number.isFinite(width) && width > 0 ? width : 100;
      const validHeight = Number.isFinite(height) && height > 0 ? height : 100;
      this.lightData.areaWidth = validWidth;
      this.lightData.areaHeight = validHeight;
      this.light.width = validWidth;
      this.light.height = validHeight;
    }
  }

  setShadowEnabled(enabled: boolean): void {
    this.lightData.shadow.enabled = enabled;
    if (
      this.light instanceof THREE.PointLight ||
      this.light instanceof THREE.SpotLight ||
      this.light instanceof THREE.DirectionalLight
    ) {
      this.light.castShadow = enabled;
    }
  }

  setShadowType(type: ShadowType): void {
    this.lightData.shadow.type = type;
    if (
      this.light instanceof THREE.PointLight ||
      this.light instanceof THREE.SpotLight ||
      this.light instanceof THREE.DirectionalLight
    ) {
      this.configureShadows(this.light);
    }
  }

  setPointOfInterestEnabled(enabled: boolean): void {
    this.lightData.pointOfInterest.enabled = enabled;
  }

  setPointOfInterestTarget(layerId: string | null): void {
    if (layerId) {
      this.lightData.pointOfInterest.targetType = "layer";
      this.lightData.pointOfInterest.targetLayerId = layerId;
    } else {
      this.lightData.pointOfInterest.targetType = "position";
      this.lightData.pointOfInterest.targetLayerId = undefined;
    }
  }

  setPathFollowingEnabled(enabled: boolean): void {
    this.lightData.pathFollowing.enabled = enabled;
  }

  setPathSpline(splineLayerId: string | null): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: splineLayerId ∈ string | null → string | undefined
    this.lightData.pathFollowing.splineLayerId = (typeof splineLayerId === "string" && splineLayerId.length > 0) ? splineLayerId : undefined;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                              // driver // property // access
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Get a light property value by driver property path
   * Used by PropertyDriverSystem for property-to-property linking
   */
  getDriverPropertyValue(path: string): number | null {
    switch (path) {
      case "light.intensity":
        return this.lightData.intensity;
      case "light.color.r":
        return this.light.color.r * 255;
      case "light.color.g":
        return this.light.color.g * 255;
      case "light.color.b":
        return this.light.color.b * 255;
      case "light.colorTemperature":
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        // Pattern match: colorTemperature ∈ number | undefined → number (default 6500)
        return (typeof this.lightData.colorTemperature === "number" && Number.isFinite(this.lightData.colorTemperature)) ? this.lightData.colorTemperature : 6500;
      case "light.coneAngle":
        // Pattern match: coneAngle ∈ number | undefined → number (default 90)
        return (typeof this.lightData.coneAngle === "number" && Number.isFinite(this.lightData.coneAngle)) ? this.lightData.coneAngle : 90;
      case "light.penumbra":
        // Pattern match: coneFeather ∈ number | undefined → number (default 50)
        return (typeof this.lightData.coneFeather === "number" && Number.isFinite(this.lightData.coneFeather)) ? this.lightData.coneFeather : 50;
      case "light.falloff":
        return this.lightData.falloffDistance;
      case "light.shadow.intensity":
        return this.lightData.shadow.darkness;
      case "light.shadow.softness":
        return this.lightData.shadow.radius;
      case "light.shadow.bias":
        return this.lightData.shadow.bias * 10000; // Scale for readability
      case "light.poi.x":
        return this.poiTarget.x;
      case "light.poi.y":
        return this.poiTarget.y;
      case "light.poi.z":
        return this.poiTarget.z;
      case "light.areaSize.width":
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        // Pattern match: areaWidth ∈ number | undefined → number (default 100)
        return (typeof this.lightData.areaWidth === "number" && Number.isFinite(this.lightData.areaWidth)) ? this.lightData.areaWidth : 100;
      case "light.areaSize.height":
        // Pattern match: areaHeight ∈ number | undefined → number (default 100)
        return (typeof this.lightData.areaHeight === "number" && Number.isFinite(this.lightData.areaHeight)) ? this.lightData.areaHeight : 100;
      case "light.physicalIntensity":
        // Pattern match: physicalIntensity ∈ number | undefined → number (fallback to intensity * 100)
        return (typeof this.lightData.physicalIntensity === "number" && Number.isFinite(this.lightData.physicalIntensity)) ? this.lightData.physicalIntensity : (typeof this.lightData.intensity === "number" && Number.isFinite(this.lightData.intensity) ? this.lightData.intensity * 100 : 100);
      default:
        throw new Error(`[LightLayer] Invalid property path: "${path}". Expected one of: "light.intensity", "light.color", "light.distance", "light.decay", "light.angle", "light.penumbra", "light.shadowMapSize", "light.shadowBias", "light.shadowRadius", "light.areaWidth", "light.areaHeight", "light.physicalIntensity"`);
    }
  }

  /**
   * Set a light property value by driver property path
   * Used by PropertyDriverSystem for driven values
   */
  setDriverPropertyValue(path: string, value: number): void {
    switch (path) {
      case "light.intensity":
        this.light.intensity = value / 100;
        this.lightData.intensity = value;
        break;
      case "light.color.r":
        this.light.color.r = Math.max(0, Math.min(1, value / 255));
        break;
      case "light.color.g":
        this.light.color.g = Math.max(0, Math.min(1, value / 255));
        break;
      case "light.color.b":
        this.light.color.b = Math.max(0, Math.min(1, value / 255));
        break;
      case "light.colorTemperature":
        this.setColorTemperature(value);
        break;
      case "light.coneAngle":
        this.setConeAngle(value);
        break;
      case "light.penumbra":
        this.setConeFeather(value);
        break;
      case "light.falloff":
        this.setFalloffDistance(value);
        break;
      case "light.shadow.intensity":
        this.lightData.shadow.darkness = value;
        break;
      case "light.shadow.softness":
        this.lightData.shadow.radius = value;
        if (
          this.light instanceof THREE.PointLight ||
          this.light instanceof THREE.SpotLight ||
          this.light instanceof THREE.DirectionalLight
        ) {
          this.light.shadow.radius = value;
        }
        break;
      case "light.shadow.bias":
        this.lightData.shadow.bias = value / 10000;
        if (
          this.light instanceof THREE.PointLight ||
          this.light instanceof THREE.SpotLight ||
          this.light instanceof THREE.DirectionalLight
        ) {
          this.light.shadow.bias = value / 10000;
        }
        break;
      case "light.poi.x":
        this.poiTarget.x = value;
        this.updatePointOfInterest(0);
        break;
      case "light.poi.y":
        this.poiTarget.y = value;
        this.updatePointOfInterest(0);
        break;
      case "light.poi.z":
        this.poiTarget.z = value;
        this.updatePointOfInterest(0);
        break;
      case "light.areaSize.width":
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        // Pattern match: areaHeight ∈ number | undefined → number (default 100)
        const areaHeightForWidth = (typeof this.lightData.areaHeight === "number" && Number.isFinite(this.lightData.areaHeight)) ? this.lightData.areaHeight : 100;
        this.setAreaSize(value, areaHeightForWidth);
        break;
      case "light.areaSize.height":
        // Pattern match: areaWidth ∈ number | undefined → number (default 100)
        const areaWidthForHeight = (typeof this.lightData.areaWidth === "number" && Number.isFinite(this.lightData.areaWidth)) ? this.lightData.areaWidth : 100;
        this.setAreaSize(areaWidthForHeight, value);
        break;
      case "light.physicalIntensity":
        this.lightData.physicalIntensity = value;
        if (this.lightData.usePhysicalIntensity) {
          this.light.intensity = value / 100;
        }
        break;
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                   // getters
  // ════════════════════════════════════════════════════════════════════════════

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

    if (linking.mode === "include") {
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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // frame // evaluation
  // ════════════════════════════════════════════════════════════════════════════

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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    // Deterministic: Explicit null check before accessing animatedIntensity
    const animatedIntensity = (this.lightData != null && typeof this.lightData === "object" && "animatedIntensity" in this.lightData && this.lightData.animatedIntensity != null && typeof this.lightData.animatedIntensity === "object") ? this.lightData.animatedIntensity : undefined;
    const animatedIntensityAnimated = (animatedIntensity != null && typeof animatedIntensity === "object" && "animated" in animatedIntensity && typeof animatedIntensity.animated === "boolean" && animatedIntensity.animated) ? true : false;
    if (animatedIntensityAnimated && animatedIntensity) {
      const intensity = this.evaluator.evaluate(
        animatedIntensity,
        frame,
      );
      this.light.intensity = intensity / 100;
    }

    // Animated cone angle
    const animatedConeAngle = (this.lightData != null && typeof this.lightData === "object" && "animatedConeAngle" in this.lightData && this.lightData.animatedConeAngle != null && typeof this.lightData.animatedConeAngle === "object") ? this.lightData.animatedConeAngle : undefined;
    const animatedConeAngleAnimated = (animatedConeAngle != null && typeof animatedConeAngle === "object" && "animated" in animatedConeAngle && typeof animatedConeAngle.animated === "boolean" && animatedConeAngle.animated) ? true : false;
    if (
      animatedConeAngleAnimated &&
      animatedConeAngle &&
      this.light instanceof THREE.SpotLight
    ) {
      const angle = this.evaluator.evaluate(
        animatedConeAngle,
        frame,
      );
      this.light.angle = THREE.MathUtils.degToRad(angle / 2);
      if (this.helper instanceof THREE.SpotLightHelper) {
        this.helper.update();
      }
    }

    // Animated color
    const animatedColor = (this.lightData != null && typeof this.lightData === "object" && "animatedColor" in this.lightData && this.lightData.animatedColor != null && typeof this.lightData.animatedColor === "object") ? this.lightData.animatedColor : undefined;
    const animatedColorAnimated = (animatedColor != null && typeof animatedColor === "object" && "animated" in animatedColor && typeof animatedColor.animated === "boolean" && animatedColor.animated) ? true : false;
    if (animatedColorAnimated && animatedColor) {
      const color = this.evaluator.evaluate(
        animatedColor,
        frame,
      );
      this.light.color.set(color);
    }

    // Animated color temperature
    const animatedColorTemperature = (this.lightData != null && typeof this.lightData === "object" && "animatedColorTemperature" in this.lightData && this.lightData.animatedColorTemperature != null && typeof this.lightData.animatedColorTemperature === "object") ? this.lightData.animatedColorTemperature : undefined;
    const animatedColorTemperatureAnimated = (animatedColorTemperature != null && typeof animatedColorTemperature === "object" && "animated" in animatedColorTemperature && typeof animatedColorTemperature.animated === "boolean" && animatedColorTemperature.animated) ? true : false;
    if (
      animatedColorTemperatureAnimated &&
      animatedColorTemperature &&
      this.lightData.useColorTemperature
    ) {
      const kelvin = this.evaluator.evaluate(
        animatedColorTemperature,
        frame,
      );
      const rgb = kelvinToRGB(kelvin);
      this.light.color.setRGB(rgb.r, rgb.g, rgb.b);
    }

    // Update helpers
    if (this.helper) {
      if (
        this.helper instanceof THREE.PointLightHelper ||
        this.helper instanceof THREE.SpotLightHelper ||
        this.helper instanceof THREE.DirectionalLightHelper
      ) {
        this.helper.update();
      }
    }
  }

  protected override onApplyEvaluatedState(
    state: import("../MotionEngine").EvaluatedLayer,
  ): void {
    const props = state.properties;

    // Apply evaluated intensity
    if (props.intensity !== undefined) {
      this.light.intensity = (props.intensity as number) / 100;
    }

    // Apply evaluated cone angle
    if (
      props.coneAngle !== undefined &&
      this.light instanceof THREE.SpotLight
    ) {
      this.light.angle = THREE.MathUtils.degToRad(
        (props.coneAngle as number) / 2,
      );
      if (this.helper instanceof THREE.SpotLightHelper) {
        this.helper.update();
      }
    }

    // Apply evaluated color
    if (props.color !== undefined) {
      this.light.color.set(props.color as string);
    }

    // Apply evaluated color temperature
    if (
      props.colorTemperature !== undefined &&
      this.lightData.useColorTemperature
    ) {
      const rgb = kelvinToRGB(props.colorTemperature as number);
      this.light.color.setRGB(rgb.r, rgb.g, rgb.b);
    }

    // Apply evaluated falloff distance
    if (props.falloffDistance !== undefined) {
      if (
        this.light instanceof THREE.PointLight ||
        this.light instanceof THREE.SpotLight
      ) {
        this.light.distance =
          this.lightData.falloff === "none"
            ? 0
            : (props.falloffDistance as number);
      }
    }

    // Apply POI position
    if (
      props["poi.x"] !== undefined ||
      props["poi.y"] !== undefined ||
      props["poi.z"] !== undefined
    ) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
      // Pattern match: props["poi.x"] ∈ PropertyValue | undefined → number (fallback to poiTarget.x)
      const poiXValue = (typeof props["poi.x"] === "number" && Number.isFinite(props["poi.x"])) ? props["poi.x"] : this.poiTarget.x;
      // Pattern match: props["poi.y"] ∈ PropertyValue | undefined → number (fallback to poiTarget.y)
      const poiYValue = (typeof props["poi.y"] === "number" && Number.isFinite(props["poi.y"])) ? props["poi.y"] : this.poiTarget.y;
      // Pattern match: props["poi.z"] ∈ PropertyValue | undefined → number (fallback to poiTarget.z)
      const poiZValue = (typeof props["poi.z"] === "number" && Number.isFinite(props["poi.z"])) ? props["poi.z"] : this.poiTarget.z;
      this.poiTarget.set(poiXValue, poiYValue, poiZValue);
      this.updatePointOfInterest(0);
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<LightData> | undefined;
    if (!data) return;

    if (
      data.lightType !== undefined &&
      data.lightType !== this.lightData.lightType
    ) {
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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
      // Pattern match: areaWidth ∈ number | undefined → number (fallback chain: lightData.areaWidth → 100)
      const areaWidthUpdate = (typeof data.areaWidth === "number" && Number.isFinite(data.areaWidth)) ? data.areaWidth : ((typeof this.lightData.areaWidth === "number" && Number.isFinite(this.lightData.areaWidth)) ? this.lightData.areaWidth : 100);
      // Pattern match: areaHeight ∈ number | undefined → number (fallback chain: lightData.areaHeight → 100)
      const areaHeightUpdate = (typeof data.areaHeight === "number" && Number.isFinite(data.areaHeight)) ? data.areaHeight : ((typeof this.lightData.areaHeight === "number" && Number.isFinite(this.lightData.areaHeight)) ? this.lightData.areaHeight : 100);
      this.setAreaSize(areaWidthUpdate, areaHeightUpdate);
    }

    if (data.shadow !== undefined) {
      Object.assign(this.lightData.shadow, data.shadow);
      if (
        this.light instanceof THREE.PointLight ||
        this.light instanceof THREE.SpotLight ||
        this.light instanceof THREE.DirectionalLight
      ) {
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
    if (hasDispose(this.light)) {
      this.light.dispose();
    }
    if (this.helper && hasDispose(this.helper)) {
      this.helper.dispose();
    }
  }
}
