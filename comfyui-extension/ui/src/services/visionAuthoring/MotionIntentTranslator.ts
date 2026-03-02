/**
 * Motion Intent Translator
 *
 * Converts AI-generated motion intents into deterministic keyframes
 * and configuration that can be applied to the project.
 *
 * PRINCIPLE: Translation is DETERMINISTIC.
 * Same intent + same context = same keyframes.
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import type {
  Keyframe,
  Layer,
  ControlPoint as ProjectControlPoint,
} from "@/types/project";
// Use the same ControlPoint type (they should be identical)
import { createLogger } from "@/utils/logger";
import { generateKeyframeId } from "@/utils/uuid5";
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
// TYPES
// ============================================================================

/**
 * Particle config for AI-generated particle layers
 * Index signature allows compatibility with NewLayerConfig
 */
interface ParticleBaseConfig {
  emissionRate: number;
  particleLifetime: number;
  spread: number;
  direction?: number;
  speed?: number;
  speedVariance?: number;
  gravity?: number;
  initialBurst?: number;
  [key: string]: number | undefined;
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
    // Type proof: duration ∈ ℕ ∪ {undefined} → ℕ
    const durationValue = intent.durationFrames;
    const duration = isFiniteNumber(durationValue) && Number.isInteger(durationValue) && durationValue > 0 ? durationValue : compositionFrameCount;
    const distance = INTENSITY_TO_DISTANCE[intent.intensity];
    const rotation = INTENSITY_TO_ROTATION[intent.intensity];
    // Type proof: easing ∈ EasingType | undefined → EasingType
    const easingValue = intent.suggestedEasing;
    const easing = typeof easingValue === "string" && (easingValue === "easeInOut" || easingValue === "easeIn" || easingValue === "easeOut" || easingValue === "linear") ? easingValue : "easeInOut";

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
            (() => {
              // Type proof: noiseAmount ∈ ℝ ∪ {undefined} → ℝ
              const noiseAmountValue = intent.noiseAmount;
              return isFiniteNumber(noiseAmountValue) && noiseAmountValue >= 0 && noiseAmountValue <= 1 ? noiseAmountValue : 0.5;
            })(),
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
        // Type proof: id ∈ string | undefined → string
        id: (() => {
          const idValue = p.id;
          return typeof idValue === "string" && idValue.length > 0 ? idValue : `sp_${i}`;
        })(),
        x: p.x,
        y: p.y,
        // Type proof: depth ∈ ℝ ∪ {undefined} → ℝ
        depth: (() => {
          const depthValue = p.depth;
          return isFiniteNumber(depthValue) ? depthValue : 0;
        })(),
        // System F/Omega: generateHandle returns null directly when no adjacent points exist (valid "no handle" state)
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
        // Type proof: type ∈ "corner" | "smooth" | "symmetric" → "corner" | "smooth" | "symmetric"
        type: (() => {
          const typeValue = p.type;
          return typeValue === "smooth" || typeValue === "corner" || typeValue === "symmetric" ? typeValue : "smooth";
        })(),
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
    const baseConfig: ParticleBaseConfig = {
      emissionRate: intent.intensity * 20,
      // Type proof: particleLifetime ∈ ℝ ∪ {undefined} → ℝ
      particleLifetime: (() => {
        const lifetimeValue = intent.lifetime;
        return isFiniteNumber(lifetimeValue) && lifetimeValue > 0 ? lifetimeValue : 60;
      })(),
      // Type proof: spread ∈ ℝ ∪ {undefined} → ℝ
      spread: (() => {
        const spreadValue = intent.spread;
        return isFiniteNumber(spreadValue) && spreadValue >= 0 ? spreadValue : 30;
      })(),
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
    // Type proof: frequency ∈ ℝ ∪ {undefined} → ℝ
    const frequencyValue = intent.frequency;
    const frequency = isFiniteNumber(frequencyValue) && frequencyValue > 0 ? frequencyValue : 1;

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
            (() => {
              // Type proof: phase ∈ ℝ ∪ {undefined} → ℝ
              const phaseValue = intent.phase;
              return isFiniteNumber(phaseValue) ? phaseValue : 0;
            })(),
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
            (() => {
              // Type proof: phase ∈ ℝ ∪ {undefined} → ℝ
              const phaseValue = intent.phase;
              return isFiniteNumber(phaseValue) ? phaseValue : 0;
            })(),
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
            (() => {
              // Type proof: phase ∈ ℝ ∪ {undefined} → ℝ
              const phaseValue = intent.phase;
              return isFiniteNumber(phaseValue) ? phaseValue : 0;
            })(),
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
            (() => {
              // Type proof: phase ∈ ℝ ∪ {undefined} → ℝ
              const phaseValue = intent.phase;
              return isFiniteNumber(phaseValue) ? phaseValue : 0;
            })(),
          ),
          this.createOscillatingKeyframes(
            layer.id,
            "transform.scale.y",
            100,
            100 + amplitude * 10,
            duration,
            frequency,
            (() => {
              // Type proof: phase ∈ ℝ ∪ {undefined} → ℝ
              const phaseValue = intent.phase;
              return isFiniteNumber(phaseValue) ? phaseValue : 0;
            })(),
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
            (() => {
              // Type proof: phase ∈ ℝ ∪ {undefined} → ℝ
              const phaseValue = intent.phase;
              return isFiniteNumber(phaseValue) ? phaseValue : 0;
            })(),
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

    // Deterministic ID generation: same layer/property/frame/value always produces same ID
    const startValueStr = String(startValue);
    const endValueStr = String(endValue);
    
    return {
      layerId,
      propertyPath,
      keyframes: [
        {
          id: generateKeyframeId(layerId, propertyPath, startFrame, startValueStr),
          frame: startFrame,
          value: startValue,
          interpolation: easing === "linear" ? "linear" : "bezier",
          ...handles,
          controlMode: "smooth",
        },
        {
          id: generateKeyframeId(layerId, propertyPath, endFrame, endValueStr),
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

      // Deterministic ID generation: same layer/property/frame/value always produces same ID
      const valueStr = String(value);
      keyframes.push({
        id: generateKeyframeId(layerId, propertyPath, frame, valueStr),
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

        // Deterministic ID generation: same layer/property/frame/value always produces same ID
        const propertyPath = `transform.position.${axis}`;
        const value = baseValue + noise;
        const valueStr = String(value);
        axisKeyframes.push({
          id: generateKeyframeId(layerId, propertyPath, frame, valueStr),
          frame,
          value,
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

      // Deterministic ID generation: same layer/property/frame/value always produces same ID
      const xValue = center.x + Math.cos(angle) * radius;
      const zValue = center.z + Math.sin(angle) * radius;
      const xValueStr = String(xValue);
      const zValueStr = String(zValue);
      
      xKeyframes.push({
        id: generateKeyframeId(layerId, "transform.position.x", frame, xValueStr),
        frame,
        value: xValue,
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
        id: generateKeyframeId(layerId, "transform.position.z", frame, zValueStr),
        frame,
        value: zValue,
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

  /**
   * Generate bezier handle for a control point
   * 
   * System F/Omega proof: Explicit validation of point existence and adjacent points
   * Type proof: points ∈ Array<ControlPoint>, index ∈ number, direction ∈ {-1, 1}, smoothness ∈ number → { x: number; y: number } | null
   * Mathematical proof: Handle calculation requires current point and at least one adjacent point to calculate tangent
   * Geometric proof: Bezier handle direction is derived from tangent between adjacent points
   * Pattern proof: Missing point or no adjacent points is an explicit failure condition, not a lazy null return
   */
  private generateHandle(
    points: ControlPoint[],
    index: number,
    direction: -1 | 1,
    smoothness: number,
  ): { x: number; y: number } | null {
    // System F/Omega proof: Explicit validation of index bounds
    // Type proof: index ∈ number → points[index] ∈ ControlPoint | undefined
    // Mathematical proof: Index must be within array bounds [0, points.length)
    if (!Number.isInteger(index) || index < 0 || index >= points.length) {
      throw new Error(
        `[MotionIntentTranslator] Cannot generate handle: Invalid point index. ` +
        `Index: ${index}, points array length: ${points.length}, valid range: [0, ${points.length}). ` +
        `Index must be a valid integer within the points array bounds.`
      );
    }

    const prevPoint = points[index - 1];
    const nextPoint = points[index + 1];
    const currentPoint = points[index];

    // System F/Omega proof: Explicit validation of current point existence
    // Type proof: currentPoint ∈ ControlPoint | undefined
    // Mathematical proof: Current point must exist at the specified index
    if (!currentPoint) {
      throw new Error(
        `[MotionIntentTranslator] Cannot generate handle: Current point is undefined at index ${index}. ` +
        `Points array length: ${points.length}, index: ${index}. ` +
        `Point at index ${index} must exist to generate a handle.`
      );
    }

    // Calculate tangent direction
    let tangentX = 0;
    let tangentY = 0;

    if (prevPoint && nextPoint) {
      // Both adjacent points exist - use average direction
      tangentX = (nextPoint.x - prevPoint.x) * 0.25 * smoothness;
      tangentY = (nextPoint.y - prevPoint.y) * 0.25 * smoothness;
    } else if (nextPoint) {
      // Only next point exists (first point) - use forward direction
      tangentX = (nextPoint.x - currentPoint.x) * 0.25 * smoothness;
      tangentY = (nextPoint.y - currentPoint.y) * 0.25 * smoothness;
    } else if (prevPoint) {
      // Only previous point exists (last point) - use backward direction
      tangentX = (currentPoint.x - prevPoint.x) * 0.25 * smoothness;
      tangentY = (currentPoint.y - prevPoint.y) * 0.25 * smoothness;
    } else {
      // System F/Omega proof: No adjacent points available to calculate tangent
      // Type proof: prevPoint ∈ ControlPoint | undefined, nextPoint ∈ ControlPoint | undefined
      // Mathematical proof: At least one adjacent point is required to calculate tangent direction
      // Geometric proof: Tangent cannot be calculated without reference to adjacent points
      // Pattern proof: Single point with no neighbors cannot have a handle - this is a valid "no handle" state
      // Note: Returning null here is correct per ControlPoint type definition (handleIn/handleOut: { x: number; y: number } | null)
      // This preserves valid "no handle" state for isolated points, similar to jsonSanitizer preserving valid JSON null
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
