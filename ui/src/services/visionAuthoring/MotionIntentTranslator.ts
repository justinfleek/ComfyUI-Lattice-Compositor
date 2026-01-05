/**
 * Motion Intent Translator
 *
 * Converts AI-generated motion intents into deterministic keyframes
 * and configuration that can be applied to the project.
 *
 * PRINCIPLE: Translation is DETERMINISTIC.
 * Same intent + same context = same keyframes.
 */

import type {
  Keyframe,
  Layer,
  ControlPoint as ProjectControlPoint,
} from "@/types/project";
// Use the same ControlPoint type (they should be identical)
import { createLogger } from "@/utils/logger";
import type {
  CameraMotionIntent,
  ControlPoint,
  EasingType,
  KeyframeBatch,
  LayerMotionIntent,
  MotionIntensity,
  ParticleMotionIntent,
  SplineMotionIntent,
  TranslationResult,
} from "./types";

const logger = createLogger("MotionIntentTranslator");

// ============================================================================
// INTENSITY MAPPINGS
// ============================================================================

const INTENSITY_TO_DISTANCE: Record<MotionIntensity, number> = {
  very_subtle: 10,
  subtle: 30,
  medium: 80,
  strong: 200,
  dramatic: 500,
};

const INTENSITY_TO_ROTATION: Record<MotionIntensity, number> = {
  very_subtle: 2,
  subtle: 5,
  medium: 15,
  strong: 45,
  dramatic: 90,
};

const _INTENSITY_TO_SCALE: Record<MotionIntensity, number> = {
  very_subtle: 0.02,
  subtle: 0.05,
  medium: 0.1,
  strong: 0.2,
  dramatic: 0.4,
};

// ============================================================================
// EASING CONFIGURATIONS
// ============================================================================

interface BezierHandles {
  inHandle: { frame: number; value: number; enabled: boolean };
  outHandle: { frame: number; value: number; enabled: boolean };
}

function getEasingHandles(easing: EasingType, duration: number): BezierHandles {
  const third = duration / 3;

  switch (easing) {
    case "linear":
      return {
        inHandle: { frame: 0, value: 0, enabled: false },
        outHandle: { frame: 0, value: 0, enabled: false },
      };
    case "easeIn":
      return {
        inHandle: { frame: 0, value: 0, enabled: false },
        outHandle: { frame: third, value: 0, enabled: true },
      };
    case "easeOut":
      return {
        inHandle: { frame: -third, value: 0, enabled: true },
        outHandle: { frame: 0, value: 0, enabled: false },
      };
    case "easeInOut":
      return {
        inHandle: { frame: -third, value: 0, enabled: true },
        outHandle: { frame: third, value: 0, enabled: true },
      };
    case "bounce":
      // Simplified bounce - would need more keyframes for true bounce
      return {
        inHandle: { frame: -third * 0.5, value: 0, enabled: true },
        outHandle: { frame: third * 0.5, value: 0, enabled: true },
      };
    case "elastic":
      // Simplified elastic
      return {
        inHandle: { frame: -third * 0.3, value: 0, enabled: true },
        outHandle: { frame: third * 0.3, value: 0, enabled: true },
      };
    default:
      return {
        inHandle: { frame: 0, value: 0, enabled: false },
        outHandle: { frame: 0, value: 0, enabled: false },
      };
  }
}

// ============================================================================
// MOTION INTENT TRANSLATOR
// ============================================================================

export class MotionIntentTranslator {
  /**
   * Translate a camera motion intent to keyframes
   */
  translateCameraIntent(
    intent: CameraMotionIntent,
    cameraLayerId: string,
    currentPosition: { x: number; y: number; z: number },
    compositionFrameCount: number,
  ): KeyframeBatch[] {
    const duration = intent.durationFrames ?? compositionFrameCount;
    const distance = INTENSITY_TO_DISTANCE[intent.intensity];
    const rotation = INTENSITY_TO_ROTATION[intent.intensity];
    const easing = intent.suggestedEasing ?? "easeInOut";

    const batches: KeyframeBatch[] = [];

    switch (intent.type) {
      case "dolly":
        batches.push(
          this.createPositionKeyframes(
            cameraLayerId,
            "transform.position.z",
            currentPosition.z,
            currentPosition.z + (intent.axis === "z" ? distance : 0),
            0,
            duration,
            easing,
          ),
        );
        break;

      case "truck":
        batches.push(
          this.createPositionKeyframes(
            cameraLayerId,
            "transform.position.x",
            currentPosition.x,
            currentPosition.x + distance,
            0,
            duration,
            easing,
          ),
        );
        break;

      case "pedestal":
        batches.push(
          this.createPositionKeyframes(
            cameraLayerId,
            "transform.position.y",
            currentPosition.y,
            currentPosition.y + distance,
            0,
            duration,
            easing,
          ),
        );
        break;

      case "pan":
        batches.push(
          this.createRotationKeyframes(
            cameraLayerId,
            "transform.rotation.y",
            0,
            rotation,
            0,
            duration,
            easing,
          ),
        );
        break;

      case "tilt":
        batches.push(
          this.createRotationKeyframes(
            cameraLayerId,
            "transform.rotation.x",
            0,
            rotation,
            0,
            duration,
            easing,
          ),
        );
        break;

      case "roll":
        batches.push(
          this.createRotationKeyframes(
            cameraLayerId,
            "transform.rotation.z",
            0,
            rotation,
            0,
            duration,
            easing,
          ),
        );
        break;

      case "zoom":
        // Zoom via FOV change
        batches.push(
          this.createPositionKeyframes(
            cameraLayerId,
            "camera.fov",
            60,
            60 - distance * 0.5, // Narrower FOV = zoom in
            0,
            duration,
            easing,
          ),
        );
        break;

      case "drift":
        // Subtle multi-axis movement
        batches.push(
          ...this.createDriftKeyframes(
            cameraLayerId,
            currentPosition,
            duration,
            intent.intensity,
          ),
        );
        break;

      case "handheld":
        // Noisy movement simulation
        batches.push(
          ...this.createHandheldKeyframes(
            cameraLayerId,
            currentPosition,
            duration,
            intent.noiseAmount ?? 0.5,
          ),
        );
        break;

      case "orbit":
        // Orbit around a point
        if (intent.orbitCenter) {
          batches.push(
            ...this.createOrbitKeyframes(
              cameraLayerId,
              currentPosition,
              intent.orbitCenter,
              duration,
              intent.intensity,
            ),
          );
        }
        break;

      case "crane":
        // Vertical arc movement
        batches.push(
          ...this.createCraneKeyframes(
            cameraLayerId,
            currentPosition,
            duration,
            intent.intensity,
          ),
        );
        break;

      case "follow_path":
        // Path following handled separately via spline
        if (intent.suggestedPath) {
          logger.info("Camera path following requires spline layer creation");
        }
        break;
    }

    return batches;
  }

  /**
   * Translate a spline intent to a spline layer configuration
   */
  translateSplineIntent(
    intent: SplineMotionIntent,
    _compositionWidth: number,
    _compositionHeight: number,
  ): TranslationResult {
    // Convert suggested points to project control points
    const controlPoints: ProjectControlPoint[] = intent.suggestedPoints.map(
      (p, i) => ({
        id: p.id ?? `sp_${i}`,
        x: p.x,
        y: p.y,
        depth: p.depth ?? 0,
        handleIn: this.generateHandle(
          intent.suggestedPoints,
          i,
          -1,
          intent.smoothness,
        ),
        handleOut: this.generateHandle(
          intent.suggestedPoints,
          i,
          1,
          intent.smoothness,
        ),
        type: p.type ?? "smooth",
      }),
    );

    return {
      keyframeBatches: [],
      newSplines: [
        {
          name: `AI Path - ${intent.usage}`,
          points: controlPoints,
          closed: intent.closed,
        },
      ],
    };
  }

  /**
   * Translate a particle intent to emitter configuration
   */
  translateParticleIntent(
    intent: ParticleMotionIntent,
    _compositionWidth: number,
    _compositionHeight: number,
  ): TranslationResult {
    // Map behavior to particle system config
    const baseConfig: Record<string, unknown> = {
      emissionRate: intent.intensity * 20,
      particleLifetime: intent.lifetime ?? 60,
      spread: intent.spread ?? 30,
    };

    switch (intent.behavior) {
      case "snow":
        Object.assign(baseConfig, {
          direction: 270,
          speed: 50,
          speedVariance: 20,
          gravity: 0.1,
        });
        break;
      case "rain":
        Object.assign(baseConfig, {
          direction: 270,
          speed: 200,
          speedVariance: 30,
          gravity: 0.5,
        });
        break;
      case "dust":
        Object.assign(baseConfig, {
          direction: 0,
          speed: 20,
          speedVariance: 15,
          gravity: 0,
        });
        break;
      case "fireflies":
        Object.assign(baseConfig, {
          direction: 90,
          speed: 30,
          speedVariance: 20,
          gravity: -0.05,
        });
        break;
      case "explosion":
        Object.assign(baseConfig, {
          direction: 0,
          spread: 360,
          speed: 300,
          speedVariance: 100,
          initialBurst: 50,
          emissionRate: 0,
        });
        break;
      case "vortex":
        Object.assign(baseConfig, {
          direction: 0,
          spread: 360,
          speed: 100,
          // Would need vortex force field
        });
        break;
    }

    return {
      keyframeBatches: [],
      newLayers: [
        {
          type: "particles",
          name: `AI Particles - ${intent.behavior}`,
          config: baseConfig,
        },
      ],
    };
  }

  /**
   * Translate a layer motion intent to keyframes
   */
  translateLayerIntent(
    intent: LayerMotionIntent,
    layer: Layer,
    compositionFrameCount: number,
  ): KeyframeBatch[] {
    const duration = compositionFrameCount;
    const amplitude = intent.amplitude;
    const frequency = intent.frequency ?? 1;

    const batches: KeyframeBatch[] = [];

    switch (intent.motionType) {
      case "parallax":
        // Parallax based on depth would need depth info
        batches.push(
          this.createOscillatingKeyframes(
            layer.id,
            "transform.position.x",
            0,
            amplitude * 50,
            duration,
            frequency,
            intent.phase ?? 0,
          ),
        );
        break;

      case "float":
        batches.push(
          this.createOscillatingKeyframes(
            layer.id,
            "transform.position.y",
            0,
            amplitude * 30,
            duration,
            frequency,
            intent.phase ?? 0,
          ),
        );
        break;

      case "sway":
        batches.push(
          this.createOscillatingKeyframes(
            layer.id,
            "transform.position.x",
            0,
            amplitude * 40,
            duration,
            frequency,
            intent.phase ?? 0,
          ),
        );
        break;

      case "breathe":
        batches.push(
          this.createOscillatingKeyframes(
            layer.id,
            "transform.scale.x",
            100,
            100 + amplitude * 10,
            duration,
            frequency,
            intent.phase ?? 0,
          ),
          this.createOscillatingKeyframes(
            layer.id,
            "transform.scale.y",
            100,
            100 + amplitude * 10,
            duration,
            frequency,
            intent.phase ?? 0,
          ),
        );
        break;

      case "pulse":
        batches.push(
          this.createOscillatingKeyframes(
            layer.id,
            "opacity",
            100,
            100 - amplitude * 30,
            duration,
            frequency * 2,
            intent.phase ?? 0,
          ),
        );
        break;

      case "rotate":
        batches.push(
          this.createPositionKeyframes(
            layer.id,
            "transform.rotation.z",
            0,
            360 * frequency,
            0,
            duration,
            "linear",
          ),
        );
        break;
    }

    return batches;
  }

  // ============================================================================
  // KEYFRAME GENERATORS
  // ============================================================================

  private createPositionKeyframes(
    layerId: string,
    propertyPath: string,
    startValue: number,
    endValue: number,
    startFrame: number,
    endFrame: number,
    easing: EasingType,
  ): KeyframeBatch {
    const handles = getEasingHandles(easing, endFrame - startFrame);

    return {
      layerId,
      propertyPath,
      keyframes: [
        {
          id: `kf_${layerId}_${propertyPath}_0`,
          frame: startFrame,
          value: startValue,
          interpolation: easing === "linear" ? "linear" : "bezier",
          ...handles,
          controlMode: "smooth",
        },
        {
          id: `kf_${layerId}_${propertyPath}_1`,
          frame: endFrame,
          value: endValue,
          interpolation: "linear",
          inHandle: { frame: 0, value: 0, enabled: false },
          outHandle: { frame: 0, value: 0, enabled: false },
          controlMode: "smooth",
        },
      ],
    };
  }

  private createRotationKeyframes(
    layerId: string,
    propertyPath: string,
    startValue: number,
    endValue: number,
    startFrame: number,
    endFrame: number,
    easing: EasingType,
  ): KeyframeBatch {
    return this.createPositionKeyframes(
      layerId,
      propertyPath,
      startValue,
      endValue,
      startFrame,
      endFrame,
      easing,
    );
  }

  private createOscillatingKeyframes(
    layerId: string,
    propertyPath: string,
    centerValue: number,
    amplitude: number,
    duration: number,
    cycles: number,
    phase: number,
  ): KeyframeBatch {
    const keyframes: Keyframe<number>[] = [];
    const framesPerCycle = duration / cycles;
    const quarterCycle = framesPerCycle / 4;

    for (let i = 0; i <= cycles * 4; i++) {
      const frame = Math.round(i * quarterCycle);
      if (frame > duration) break;

      // Sin wave: 0 → 1 → 0 → -1 → 0
      const sinePhase = (i + phase * 4) % 4;
      let value: number;

      switch (sinePhase) {
        case 0:
          value = centerValue;
          break;
        case 1:
          value = centerValue + amplitude;
          break;
        case 2:
          value = centerValue;
          break;
        case 3:
          value = centerValue - amplitude;
          break;
        default:
          value = centerValue;
      }

      keyframes.push({
        id: `kf_${layerId}_${propertyPath}_${i}`,
        frame,
        value,
        interpolation: "bezier",
        inHandle: { frame: -quarterCycle * 0.5, value: 0, enabled: true },
        outHandle: { frame: quarterCycle * 0.5, value: 0, enabled: true },
        controlMode: "smooth",
      });
    }

    return { layerId, propertyPath, keyframes };
  }

  private createDriftKeyframes(
    layerId: string,
    startPosition: { x: number; y: number; z: number },
    duration: number,
    intensity: MotionIntensity,
  ): KeyframeBatch[] {
    const distance = INTENSITY_TO_DISTANCE[intensity] * 0.3;

    return [
      this.createOscillatingKeyframes(
        layerId,
        "transform.position.x",
        startPosition.x,
        distance,
        duration,
        0.5,
        0,
      ),
      this.createOscillatingKeyframes(
        layerId,
        "transform.position.y",
        startPosition.y,
        distance * 0.7,
        duration,
        0.3,
        0.25,
      ),
      this.createOscillatingKeyframes(
        layerId,
        "transform.position.z",
        startPosition.z,
        distance * 0.5,
        duration,
        0.4,
        0.5,
      ),
    ];
  }

  private createHandheldKeyframes(
    layerId: string,
    startPosition: { x: number; y: number; z: number },
    duration: number,
    noiseAmount: number,
  ): KeyframeBatch[] {
    // Generate pseudo-random noise keyframes
    // Using deterministic seed based on layerId
    const seed = this.hashString(layerId);
    const amplitude = noiseAmount * 5;
    const keyframes: KeyframeBatch[] = [];

    for (const axis of ["x", "y", "z"] as const) {
      const axisKeyframes: Keyframe<number>[] = [];
      const baseValue = startPosition[axis];
      const numKeyframes = Math.floor(duration / 4); // Keyframe every 4 frames

      for (let i = 0; i <= numKeyframes; i++) {
        const frame = Math.min(i * 4, duration);
        // Deterministic "random" based on seed, axis, and frame
        const noise = this.deterministicNoise(seed, axis, frame) * amplitude;

        axisKeyframes.push({
          id: `kf_${layerId}_handheld_${axis}_${i}`,
          frame,
          value: baseValue + noise,
          interpolation: "bezier",
          inHandle: { frame: -1, value: 0, enabled: true },
          outHandle: { frame: 1, value: 0, enabled: true },
          controlMode: "smooth",
        });
      }

      keyframes.push({
        layerId,
        propertyPath: `transform.position.${axis}`,
        keyframes: axisKeyframes,
      });
    }

    return keyframes;
  }

  private createOrbitKeyframes(
    layerId: string,
    startPosition: { x: number; y: number; z: number },
    center: { x: number; y: number; z: number },
    duration: number,
    intensity: MotionIntensity,
  ): KeyframeBatch[] {
    const radius =
      Math.sqrt(
        (startPosition.x - center.x) ** 2 + (startPosition.z - center.z) ** 2,
      ) || INTENSITY_TO_DISTANCE[intensity];

    const numKeyframes = 8;
    const xKeyframes: Keyframe<number>[] = [];
    const zKeyframes: Keyframe<number>[] = [];

    for (let i = 0; i <= numKeyframes; i++) {
      const frame = Math.round((i / numKeyframes) * duration);
      const angle = (i / numKeyframes) * Math.PI * 2;

      xKeyframes.push({
        id: `kf_${layerId}_orbit_x_${i}`,
        frame,
        value: center.x + Math.cos(angle) * radius,
        interpolation: "bezier",
        inHandle: {
          frame: (-duration / numKeyframes) * 0.3,
          value: 0,
          enabled: true,
        },
        outHandle: {
          frame: (duration / numKeyframes) * 0.3,
          value: 0,
          enabled: true,
        },
        controlMode: "smooth",
      });

      zKeyframes.push({
        id: `kf_${layerId}_orbit_z_${i}`,
        frame,
        value: center.z + Math.sin(angle) * radius,
        interpolation: "bezier",
        inHandle: {
          frame: (-duration / numKeyframes) * 0.3,
          value: 0,
          enabled: true,
        },
        outHandle: {
          frame: (duration / numKeyframes) * 0.3,
          value: 0,
          enabled: true,
        },
        controlMode: "smooth",
      });
    }

    return [
      { layerId, propertyPath: "transform.position.x", keyframes: xKeyframes },
      { layerId, propertyPath: "transform.position.z", keyframes: zKeyframes },
    ];
  }

  private createCraneKeyframes(
    layerId: string,
    startPosition: { x: number; y: number; z: number },
    duration: number,
    intensity: MotionIntensity,
  ): KeyframeBatch[] {
    const height = INTENSITY_TO_DISTANCE[intensity];

    // Arc: up and forward, then down
    return [
      this.createPositionKeyframes(
        layerId,
        "transform.position.y",
        startPosition.y,
        startPosition.y + height,
        0,
        duration / 2,
        "easeOut",
      ),
      this.createPositionKeyframes(
        layerId,
        "transform.position.z",
        startPosition.z,
        startPosition.z + height * 0.5,
        0,
        duration,
        "easeInOut",
      ),
    ];
  }

  // ============================================================================
  // UTILITIES
  // ============================================================================

  private generateHandle(
    points: ControlPoint[],
    index: number,
    direction: -1 | 1,
    smoothness: number,
  ): { x: number; y: number } | null {
    const prevPoint = points[index - 1];
    const nextPoint = points[index + 1];
    const currentPoint = points[index];

    if (!currentPoint) return null;

    // Calculate tangent direction
    let tangentX = 0;
    let tangentY = 0;

    if (prevPoint && nextPoint) {
      tangentX = (nextPoint.x - prevPoint.x) * 0.25 * smoothness;
      tangentY = (nextPoint.y - prevPoint.y) * 0.25 * smoothness;
    } else if (nextPoint) {
      tangentX = (nextPoint.x - currentPoint.x) * 0.25 * smoothness;
      tangentY = (nextPoint.y - currentPoint.y) * 0.25 * smoothness;
    } else if (prevPoint) {
      tangentX = (currentPoint.x - prevPoint.x) * 0.25 * smoothness;
      tangentY = (currentPoint.y - prevPoint.y) * 0.25 * smoothness;
    } else {
      return null;
    }

    return {
      x: tangentX * direction,
      y: tangentY * direction,
    };
  }

  private hashString(str: string): number {
    let hash = 0;
    for (let i = 0; i < str.length; i++) {
      const char = str.charCodeAt(i);
      hash = (hash << 5) - hash + char;
      hash = hash & hash;
    }
    return Math.abs(hash);
  }

  private deterministicNoise(
    seed: number,
    axis: string,
    frame: number,
  ): number {
    // Simple deterministic pseudo-random
    const axisOffset = axis === "x" ? 0 : axis === "y" ? 1000 : 2000;
    const combined = seed + axisOffset + frame * 13;
    const x = Math.sin(combined) * 10000;
    return x - Math.floor(x) - 0.5;
  }
}

// Singleton instance
export const motionIntentTranslator = new MotionIntentTranslator();
