/**
 * Layer Defaults
 *
 * Default data configurations for each layer type.
 * Extracted from layerActions.ts createLayer() to reduce file size.
 */

import type { AnyLayerData, LayerType, SplineData } from "@/types/project";
import { createAnimatableProperty } from "@/types/project";
import {
  createDefaultFill,
  createDefaultGroup,
  createDefaultRectangle,
  createDefaultShapeLayerData,
  createDefaultStroke,
} from "@/types/shapes";

/**
 * Create default T-pose keypoints for COCO 18-point format (normalized 0-1)
 */
export function createDefaultTPoseKeypoints(): Array<{
  x: number;
  y: number;
  confidence: number;
}> {
  return [
    { x: 0.5, y: 0.1, confidence: 1 }, // 0: nose
    { x: 0.5, y: 0.2, confidence: 1 }, // 1: neck
    { x: 0.35, y: 0.2, confidence: 1 }, // 2: right_shoulder
    { x: 0.2, y: 0.2, confidence: 1 }, // 3: right_elbow
    { x: 0.1, y: 0.2, confidence: 1 }, // 4: right_wrist
    { x: 0.65, y: 0.2, confidence: 1 }, // 5: left_shoulder
    { x: 0.8, y: 0.2, confidence: 1 }, // 6: left_elbow
    { x: 0.9, y: 0.2, confidence: 1 }, // 7: left_wrist
    { x: 0.4, y: 0.45, confidence: 1 }, // 8: right_hip
    { x: 0.4, y: 0.65, confidence: 1 }, // 9: right_knee
    { x: 0.4, y: 0.85, confidence: 1 }, // 10: right_ankle
    { x: 0.6, y: 0.45, confidence: 1 }, // 11: left_hip
    { x: 0.6, y: 0.65, confidence: 1 }, // 12: left_knee
    { x: 0.6, y: 0.85, confidence: 1 }, // 13: left_ankle
    { x: 0.45, y: 0.08, confidence: 1 }, // 14: right_eye
    { x: 0.55, y: 0.08, confidence: 1 }, // 15: left_eye
    { x: 0.4, y: 0.1, confidence: 1 }, // 16: right_ear
    { x: 0.6, y: 0.1, confidence: 1 }, // 17: left_ear
  ];
}

export interface CompositionContext {
  width: number;
  height: number;
}

import type {
  TextData,
  SolidLayerData,
  NullLayerData,
  SplineData as SplineLayerData,
  PathLayerData,
  ParticleLayerData,
  DepthflowLayerData,
  LightLayerData,
  CameraLayerData,
  ImageLayerData,
  VideoData,
  NestedCompData,
  MatteLayerData,
  ModelLayerData,
  PointCloudLayerData,
  ControlLayerData,
  PoseLayerData,
  DepthLayerData,
  NormalLayerData,
  AudioLayerData,
  GeneratedMapData,
  GroupLayerData,
  LegacyParticleLayerData,
  EffectLayerData,
} from "@/types/project";

/**
 * Get default layer data for a specific layer type.
 * Returns properly typed data for each layer type.
 *
 * NOTE: The `as AnyLayerData` casts are necessary because TypeScript
 * cannot narrow union types in switch statements. Each branch returns
 * a properly structured object that satisfies the specific layer data type.
 */
export function getDefaultLayerData(
  type: LayerType,
  context: CompositionContext,
): AnyLayerData {
  switch (type) {
    case "text": {
      const data: TextData = {
        text: "Text",
        fontFamily: "Arial",
        fontSize: 72,
        fontWeight: "400",
        fontStyle: "normal",
        fill: "#ffffff",
        stroke: "",
        strokeWidth: 0,
        tracking: 0,
        letterSpacing: 0,
        lineSpacing: 1.2,
        lineAnchor: 50,
        characterOffset: 0,
        characterValue: 0,
        blur: { x: 0, y: 0 },
        lineHeight: 1.2,
        textAlign: "left",
        pathLayerId: "",
        pathReversed: false,
        pathPerpendicularToPath: true,
        pathForceAlignment: false,
        pathFirstMargin: 0,
        pathLastMargin: 0,
        pathOffset: 0,
        pathAlign: "left",
      };
      return data;
    }

    case "solid": {
      const data: SolidLayerData = {
        color: "#808080",
        width: context.width,
        height: context.height,
      };
      return data;
    }

    case "null": {
      const data: NullLayerData = { size: 40 };
      return data;
    }

    case "spline": {
      const data: SplineData = {
        pathData: "",
        controlPoints: [],
        closed: false,
        stroke: "#00ff00",
        strokeWidth: 2,
        lineCap: "round",
        lineJoin: "round",
        dashArray: [],
        dashOffset: 0,
      };
      return data;
    }

    case "path":
      return {
        pathData: "",
        controlPoints: [],
        closed: false,
        showGuide: true,
        guideColor: "#00FFFF",
        guideDashPattern: [10, 5],
      } as AnyLayerData;

    case "particles": {
      // ParticleLayerData from types/particles.ts
      const particleData: ParticleLayerData = {
        systemConfig: {
          maxParticles: 1000,
          gravity: 0,
          windStrength: 0,
          windDirection: 0,
          warmupPeriod: 0,
          respectMaskBoundary: false,
          boundaryBehavior: "kill",
          friction: 0.01,
        },
        emitters: [
          {
            id: "emitter_1",
            name: "Emitter 1",
            x: context.width / 2,
            y: context.height / 2,
            direction: 270, // Emit upward
            spread: 45,
            speed: 100,
            speedVariance: 20,
            size: 5,
            sizeVariance: 2,
            color: [255, 255, 255],
            emissionRate: 50,
            initialBurst: 0,
            particleLifetime: 2.0,
            lifetimeVariance: 0.5,
            enabled: true,
            burstOnBeat: false,
            burstCount: 0,
            shape: "point",
            shapeRadius: 0,
            shapeWidth: 100,
            shapeHeight: 100,
            shapeDepth: 0,
            shapeInnerRadius: 0,
            emitFromEdge: false,
            emitFromVolume: false,
            splinePath: null,
            sprite: {
              enabled: false,
              imageUrl: null,
              imageData: null,
              isSheet: false,
              columns: 1,
              rows: 1,
              totalFrames: 1,
              frameRate: 30,
              playMode: "loop",
              billboard: true,
              rotationEnabled: false,
              rotationSpeed: 0,
              rotationSpeedVariance: 0,
              alignToVelocity: false,
            },
          },
        ],
        gravityWells: [],
        vortices: [],
        renderOptions: {
          particleShape: "circle",
          blendMode: "normal",
          renderTrails: false,
          trailLength: 10,
          trailOpacityFalloff: 0.8,
          glowEnabled: false,
          glowRadius: 10,
          glowIntensity: 0.5,
          motionBlur: false,
          motionBlurStrength: 0.5,
          motionBlurSamples: 5,
          connections: {
            enabled: false,
            maxDistance: 100,
            maxConnections: 3,
            lineWidth: 1,
            lineOpacity: 0.5,
            fadeByDistance: true,
          },
        },
        audioMappings: [],
        exportEnabled: false,
        exportFormat: "wan-move",
      };
      return particleData;
    }

    case "depthflow":
      return {
        sourceLayerId: null,
        depthLayerId: null,
        config: {
          preset: "static",
          zoom: 1,
          offsetX: 0,
          offsetY: 0,
          rotation: 0,
          depthScale: 1,
          focusDepth: 0.5,
          dollyZoom: 0,
          orbitRadius: 0,
          orbitSpeed: 1,
          swingAmplitude: 0,
          swingFrequency: 1,
          edgeDilation: 0,
          inpaintEdges: false,
        },
      } as AnyLayerData;

    case "light":
      return {
        lightType: "point",
        color: "#ffffff",
        intensity: 100,
        radius: 500,
        falloff: "none",
        falloffDistance: 500,
        castShadows: false,
        shadowDarkness: 100,
        shadowDiffusion: 0,
      } as AnyLayerData;

    case "camera":
      return {
        cameraId: null,
        isActiveCamera: false,
      } as AnyLayerData;

    case "image":
      return {
        assetId: "",
        source: "",
        fit: "contain",
        cropEnabled: false,
        cropRect: { x: 0, y: 0, width: 0, height: 0 },
        sourceType: "file",
        segmentationMaskId: "",
      } as AnyLayerData;

    case "video":
      return {
        assetId: null,
        loop: false,
        startTime: 0,
        speed: 1.0,
      } as AnyLayerData;

    case "shape": {
      const data = createDefaultShapeLayerData();
      const defaultGroup = createDefaultGroup();
      defaultGroup.name = "Group 1";
      defaultGroup.contents = [
        createDefaultRectangle(),
        createDefaultFill(),
        createDefaultStroke(),
      ];
      data.contents = [defaultGroup];
      return data as AnyLayerData;
    }

    case "nestedComp":
      return {
        compositionId: null,
        speedMap: undefined,
        speedMapEnabled: false,
        timeRemap: undefined,
        timeRemapEnabled: false,
      } as AnyLayerData;

    case "matte":
      return {
        matteType: "luminance" as const,
        invert: false,
        threshold: 0.5,
        feather: 0,
        expansion: 0,
        sourceLayerId: null,
        previewMode: "matte" as const,
      } as AnyLayerData;

    case "model":
      return {
        assetId: "",
        format: "gltf" as const,
        scale: createAnimatableProperty("Scale", 1, "number"),
        uniformScale: true,
        castShadow: true,
        receiveShadow: true,
        frustumCulled: true,
        renderOrder: 0,
        showBoundingBox: false,
        showSkeleton: false,
        envMapIntensity: 1.0,
      } as AnyLayerData;

    case "pointcloud":
      return {
        assetId: "",
        format: "ply" as const,
        pointCount: 0,
        pointSize: createAnimatableProperty("Point Size", 2, "number"),
        sizeAttenuation: true,
        minPointSize: 1,
        maxPointSize: 64,
        colorMode: "rgb" as const,
        uniformColor: "#ffffff",
        renderMode: "points" as const,
        opacity: createAnimatableProperty("Opacity", 1, "number"),
        depthTest: true,
        depthWrite: true,
        showBoundingBox: false,
        pointBudget: 1000000,
      } as AnyLayerData;

    case "control":
      return {
        size: 50,
        showAxes: true,
        showIcon: true,
        iconShape: "crosshair" as const,
        iconColor: "#ffcc00",
      } as AnyLayerData;

    case "pose":
      return {
        poses: [
          {
            id: `pose-${Date.now()}`,
            format: "coco18" as const,
            keypoints: createDefaultTPoseKeypoints(),
          },
        ],
        format: "coco18" as const,
        normalized: true,
        boneWidth: 4,
        keypointRadius: 4,
        showKeypoints: true,
        showBones: true,
        showLabels: false,
        useDefaultColors: true,
        customBoneColor: "#FFFFFF",
        customKeypointColor: "#FF0000",
        selectedKeypoint: -1,
        selectedPose: 0,
      } as AnyLayerData;

    case "depth":
      return {
        assetId: null,
        visualizationMode: "colormap" as const,
        colorMap: "turbo" as const,
        invert: false,
        minDepth: 0,
        maxDepth: 1,
        autoNormalize: true,
        contourLevels: 10,
        contourColor: "#ffffff",
        contourWidth: 1,
        meshDisplacement: createAnimatableProperty(
          "Displacement",
          50,
          "number",
        ),
        meshResolution: 128,
        wireframe: false,
      } as AnyLayerData;

    case "normal":
      return {
        assetId: null,
        visualizationMode: "rgb" as const,
        format: "opengl" as const,
        flipX: false,
        flipY: false,
        flipZ: false,
        arrowDensity: 20,
        arrowScale: 10,
        arrowColor: "#00ff00",
        lightDirection: { x: 0.5, y: 0.5, z: 1.0 },
        lightIntensity: 1.0,
        ambientIntensity: 0.2,
      } as AnyLayerData;

    case "audio":
      return {
        assetId: null,
        level: createAnimatableProperty("Level", 0, "number"),
        muted: false,
        solo: false,
        pan: createAnimatableProperty("Pan", 0, "number"),
        startTime: 0,
        loop: false,
        speed: 1.0,
        showWaveform: true,
        waveformColor: "#4a90d9",
        exposeFeatures: true,
      } as AnyLayerData;

    case "generated":
      return {
        sourceLayerId: "", // Must be set to a valid layer ID
        mapType: "depth" as const,
        modelId: "depth-anything-v2",
        parameters: {},
      } as AnyLayerData;

    case "group":
      return {
        collapsed: false,
        color: null,
        passThrough: true,
        isolate: false,
      } as AnyLayerData;

    case "particle":
      // Legacy particle layer (backwards compatibility)
      return {
        emitterType: "point" as const,
        particleCount: 100,
        lifetime: 2.0,
        speed: 50,
        spread: 45,
        gravity: -9.8,
        color: "#ffffff",
        size: 5,
      } as AnyLayerData;

    case "adjustment":
    case "effectLayer":
      return {
        color: "#808080",
        effectLayer: true,
        adjustmentLayer: true,
      } as AnyLayerData;

    default:
      throw new Error(
        `Unknown layer type: ${type}. Cannot create default layer data.`,
      );
  }
}
