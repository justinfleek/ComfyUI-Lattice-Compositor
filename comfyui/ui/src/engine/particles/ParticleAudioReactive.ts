/**
 * Particle Audio Reactive System
 *
 * Handles audio feature mapping to particle parameters,
 * audio modulation with smoothing, and beat-triggered events.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import * as THREE from "three";
import type {
  AudioBinding,
  AudioFeature,
  EmitterConfig,
  EmitterShapeConfig,
  ForceFieldConfig,
} from "./types";

// ============================================================================
// PARTICLE AUDIO REACTIVE SYSTEM CLASS
// ============================================================================

export class ParticleAudioReactive {
  private audioFeatures: Map<AudioFeature, number> = new Map();
  private smoothedAudioValues: Map<number, number> = new Map();
  private audioBindings: AudioBinding[] = [];

  /**
   * Set audio bindings configuration
   */
  setBindings(bindings: AudioBinding[]): void {
    this.audioBindings = bindings;
  }

  /**
   * Get audio bindings
   */
  getBindings(): AudioBinding[] {
    return this.audioBindings;
  }

  // ============================================================================
  // AUDIO FEATURE VALUES
  // ============================================================================

  /**
   * Set audio feature value
   */
  setFeature(feature: AudioFeature, value: number): void {
    this.audioFeatures.set(feature, value);
  }

  /**
   * Get audio feature value
   * Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
   */
  getFeature(feature: AudioFeature): number {
    const value = this.audioFeatures.get(feature);
    return (value !== null && value !== undefined && typeof value === "number" && Number.isFinite(value)) ? value : 0;
  }

  /**
   * Get all audio features as a map
   */
  getFeatures(): Map<AudioFeature, number> {
    return this.audioFeatures;
  }

  /**
   * Trigger beat event (sets onsets to 1, auto-resets next frame)
   * Note: 'onsets' is the actual audio feature for transient/beat detection
   */
  triggerBeat(): void {
    this.audioFeatures.set("onsets", 1);

    // Reset onset flag after frame
    requestAnimationFrame(() => {
      this.audioFeatures.set("onsets", 0);
    });
  }

  /**
   * Check if beat/onset is currently triggered
   */
  isBeatTriggered(): boolean {
    return this.audioFeatures.get("onsets") === 1;
  }

  // ============================================================================
  // AUDIO MODULATION
  // ============================================================================

  /**
   * Apply audio modulation to emitters and force fields
   */
  applyModulation(
    emitters: Map<
      string,
      EmitterConfig & { accumulator: number; velocity: THREE.Vector3 }
    >,
    forceFields: Map<string, ForceFieldConfig>,
  ): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    for (let i = 0; i < this.audioBindings.length; i++) {
      const binding = this.audioBindings[i];
      const featureValueRaw = this.audioFeatures.get(binding.feature);
      const featureValue = (featureValueRaw !== null && featureValueRaw !== undefined && typeof featureValueRaw === "number" && Number.isFinite(featureValueRaw)) ? featureValueRaw : 0;

      // Apply exponential moving average (EMA) smoothing
      // smoothing = 0 means no smoothing (instant response)
      // smoothing = 1 means maximum smoothing (very slow response)
      const previousSmoothedRaw = this.smoothedAudioValues.get(i);
      const previousSmoothed = (previousSmoothedRaw !== null && previousSmoothedRaw !== undefined && typeof previousSmoothedRaw === "number" && Number.isFinite(previousSmoothedRaw)) ? previousSmoothedRaw : featureValue;
      // Validate smoothing
      const safeSmoothing = Number.isFinite(binding.smoothing) ? Math.max(0, Math.min(1, binding.smoothing)) : 0;
      const alpha = 1 - safeSmoothing; // Convert smoothing to alpha
      const smoothed = alpha * featureValue + (1 - alpha) * previousSmoothed;
      this.smoothedAudioValues.set(i, smoothed);

      // Validate min/max separately to handle NaN
      const safeMin = Number.isFinite(binding.min) ? binding.min : 0;
      const safeMax = Number.isFinite(binding.max) ? binding.max : 1;
      const bindingRange = safeMax - safeMin;
      const safeRange = bindingRange !== 0 ? bindingRange : 1;
      // Map to output range
      const t = Math.max(
        0,
        Math.min(1, (smoothed - safeMin) / safeRange),
      );
      // Validate output range
      const safeOutputMin = Number.isFinite(binding.outputMin) ? binding.outputMin : 0;
      const safeOutputMax = Number.isFinite(binding.outputMax) ? binding.outputMax : 1;
      let output = safeOutputMin + t * (safeOutputMax - safeOutputMin);

      // Apply curve (using validated output range)
      if (binding.curve === "exponential") {
        output = safeOutputMin + t ** 2 * (safeOutputMax - safeOutputMin);
      } else if (binding.curve === "logarithmic") {
        output = safeOutputMin + Math.sqrt(t) * (safeOutputMax - safeOutputMin);
      } else if (binding.curve === "step") {
        // Step curve: snap to discrete steps
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        const stepCount = (typeof binding.stepCount === "number" && Number.isFinite(binding.stepCount) && binding.stepCount >= 2) ? binding.stepCount : 5;
        const steps = Math.max(2, stepCount);
        const steppedT = Math.floor(t * steps) / steps;
        output = safeOutputMin + steppedT * (safeOutputMax - safeOutputMin);
      }

      // Check trigger mode
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
      const triggerMode = (typeof binding.triggerMode === "string" && binding.triggerMode.length > 0) ? binding.triggerMode : "continuous";
      if (triggerMode === "onThreshold") {
        // Only apply when smoothed value exceeds threshold
        const rawThreshold = binding.threshold;
        const threshold = (typeof rawThreshold === 'number' && Number.isFinite(rawThreshold)) ? rawThreshold : 0.5;
        if (t < threshold) continue;
      } else if (triggerMode === "onBeat") {
        // Only apply when beat/onset is detected
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        const onsetValueRaw = this.audioFeatures.get("onsets");
        const onsetValue = (onsetValueRaw !== null && onsetValueRaw !== undefined && typeof onsetValueRaw === "number" && Number.isFinite(onsetValueRaw)) ? onsetValueRaw : 0;
        if (onsetValue < 0.5) continue;
      }
      // triggerMode === 'continuous' - always apply (default behavior)

      // Apply to target
      if (binding.target === "emitter") {
        const emitter = emitters.get(binding.targetId);
        if (emitter) {
          // Type-safe parameter assignment - explicitly handle numeric properties
          const param = binding.parameter;
          if (param === "emissionRate" || param === "emissionRateVariance" || param === "burstCount" || param === "burstInterval" ||
              param === "initialSpeed" || param === "speedVariance" || param === "inheritEmitterVelocity" ||
              param === "initialSize" || param === "sizeVariance" || param === "initialMass" || param === "massVariance" ||
              param === "lifetime" || param === "lifetimeVariance" || param === "initialRotation" || param === "rotationVariance" ||
              param === "initialAngularVelocity" || param === "angularVelocityVariance" || param === "colorVariance" ||
              param === "emissionSpread" || param === "beatEmissionMultiplier") {
            emitter[param] = output;
          }
        }
      } else if (binding.target === "forceField") {
        const field = forceFields.get(binding.targetId);
        if (field) {
          // Type-safe parameter assignment - explicitly handle numeric properties
          const param = binding.parameter;
          if (param === "strength" || param === "falloffStart" || param === "falloffEnd" ||
              param === "attractorMass" || param === "inwardForce" || param === "noiseScale" || param === "noiseSpeed" ||
              param === "noiseOctaves" || param === "noiseLacunarity" || param === "noiseGain" ||
              param === "gustStrength" || param === "gustFrequency" || param === "dragCoefficient" ||
              param === "linearDrag" || param === "quadraticDrag" || param === "bounceDamping" ||
              param === "collisionRestitution" || param === "collisionFriction" || param === "pathStrength" ||
              param === "pathRadius" || param === "lorenzSigma" || param === "lorenzRho" || param === "lorenzBeta") {
            field[param] = output;
          }
        }
      }
    }
  }

  /**
   * Get audio modulation for a specific parameter
   * 
   * System F/Omega proof: Explicit validation of audio binding existence
   * Type proof: target, targetId, parameter ∈ string → number (non-nullable)
   * Mathematical proof: Audio binding must exist for the specified target/parameter
   * Pattern proof: Missing binding is an explicit failure condition, not a lazy undefined return
   */
  getModulation(
    target: string,
    targetId: string,
    parameter: string,
  ): number {
    for (const binding of this.audioBindings) {
      if (
        binding.target === target &&
        binding.targetId === targetId &&
        binding.parameter === parameter
      ) {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        const featureValueRaw = this.audioFeatures.get(binding.feature);
        const featureValue = (featureValueRaw !== null && featureValueRaw !== undefined && typeof featureValueRaw === "number" && Number.isFinite(featureValueRaw)) ? featureValueRaw : 0;
        // Validate min/max separately to handle NaN
        const safeMin = Number.isFinite(binding.min) ? binding.min : 0;
        const safeMax = Number.isFinite(binding.max) ? binding.max : 1;
        const range = safeMax - safeMin;
        const safeRange = range !== 0 ? range : 1;
        const t = Math.max(0, Math.min(1, (featureValue - safeMin) / safeRange));
        const safeOutputMin = Number.isFinite(binding.outputMin) ? binding.outputMin : 0;
        const safeOutputMax = Number.isFinite(binding.outputMax) ? binding.outputMax : 1;
        return safeOutputMin + t * (safeOutputMax - safeOutputMin);
      }
    }
    
    // System F/Omega proof: Explicit validation of audio binding existence
    // Type proof: audioBindings is Array<AudioBinding>
    // Mathematical proof: Audio binding must exist for the specified target/parameter combination
    throw new Error(
      `[ParticleAudioReactive] Cannot get modulation: Audio binding not found. ` +
      `Target: ${target}, targetId: ${targetId}, parameter: ${parameter}, ` +
      `bindings available: ${this.audioBindings.length}. ` +
      `Audio binding must exist for the specified target/parameter. ` +
      `Wrap in try/catch if "binding not found" is an expected state.`
    );
  }

  // ============================================================================
  // CLEANUP
  // ============================================================================

  /**
   * Reset audio state
   */
  reset(): void {
    this.smoothedAudioValues.clear();
  }

  /**
   * Get smoothed audio values for cache save.
   */
  getSmoothedAudioValues(): Map<number, number> {
    return new Map(this.smoothedAudioValues);
  }

  /**
   * Set smoothed audio values from cache restore.
   */
  setSmoothedAudioValues(values: Map<number, number>): void {
    this.smoothedAudioValues = new Map(values);
  }

  /**
   * Clear all audio data
   */
  clear(): void {
    this.audioFeatures.clear();
    this.smoothedAudioValues.clear();
    this.audioBindings = [];
  }
}
