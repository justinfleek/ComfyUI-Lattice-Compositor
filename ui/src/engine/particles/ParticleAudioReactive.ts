/**
 * Particle Audio Reactive System
 *
 * Handles audio feature mapping to particle parameters,
 * audio modulation with smoothing, and beat-triggered events.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import type { AudioFeature, AudioBinding, EmitterConfig, ForceFieldConfig } from './types';

// ============================================================================
// PARTICLE AUDIO REACTIVE SYSTEM CLASS
// ============================================================================

export class ParticleAudioReactive {
  private audioFeatures: Map<AudioFeature, number> = new Map();
  private smoothedAudioValues: Map<number, number> = new Map();
  private audioBindings: AudioBinding[] = [];

  constructor() {}

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
   */
  getFeature(feature: AudioFeature): number {
    return this.audioFeatures.get(feature) ?? 0;
  }

  /**
   * Get all audio features as a map
   */
  getFeatures(): Map<AudioFeature, number> {
    return this.audioFeatures;
  }

  /**
   * Trigger beat event (sets beat to 1, auto-resets next frame)
   */
  triggerBeat(): void {
    this.audioFeatures.set('beat', 1);

    // Reset beat flag after frame
    requestAnimationFrame(() => {
      this.audioFeatures.set('beat', 0);
    });
  }

  /**
   * Check if beat is currently triggered
   */
  isBeatTriggered(): boolean {
    return this.audioFeatures.get('beat') === 1;
  }

  // ============================================================================
  // AUDIO MODULATION
  // ============================================================================

  /**
   * Apply audio modulation to emitters and force fields
   */
  applyModulation(
    emitters: Map<string, EmitterConfig & { accumulator: number; velocity: unknown }>,
    forceFields: Map<string, ForceFieldConfig>
  ): void {
    for (let i = 0; i < this.audioBindings.length; i++) {
      const binding = this.audioBindings[i];
      const featureValue = this.audioFeatures.get(binding.feature) ?? 0;

      // Apply exponential moving average (EMA) smoothing
      // smoothing = 0 means no smoothing (instant response)
      // smoothing = 1 means maximum smoothing (very slow response)
      const previousSmoothed = this.smoothedAudioValues.get(i) ?? featureValue;
      const alpha = 1 - (binding.smoothing || 0);  // Convert smoothing to alpha
      const smoothed = alpha * featureValue + (1 - alpha) * previousSmoothed;
      this.smoothedAudioValues.set(i, smoothed);

      // Map to output range
      const t = Math.max(0, Math.min(1, (smoothed - binding.min) / (binding.max - binding.min)));
      let output = binding.outputMin + t * (binding.outputMax - binding.outputMin);

      // Apply curve
      if (binding.curve === 'exponential') {
        output = binding.outputMin + Math.pow(t, 2) * (binding.outputMax - binding.outputMin);
      } else if (binding.curve === 'logarithmic') {
        output = binding.outputMin + Math.sqrt(t) * (binding.outputMax - binding.outputMin);
      }

      // Apply to target
      if (binding.target === 'emitter') {
        const emitter = emitters.get(binding.targetId);
        if (emitter) {
          (emitter as Record<string, unknown>)[binding.parameter] = output;
        }
      } else if (binding.target === 'forceField') {
        const field = forceFields.get(binding.targetId);
        if (field) {
          (field as Record<string, unknown>)[binding.parameter] = output;
        }
      }
    }
  }

  /**
   * Get audio modulation for a specific parameter
   */
  getModulation(target: string, targetId: string, parameter: string): number | undefined {
    for (const binding of this.audioBindings) {
      if (binding.target === target && binding.targetId === targetId && binding.parameter === parameter) {
        const featureValue = this.audioFeatures.get(binding.feature) ?? 0;
        const t = (featureValue - binding.min) / (binding.max - binding.min);
        return binding.outputMin + t * (binding.outputMax - binding.outputMin);
      }
    }
    return undefined;
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
   * Clear all audio data
   */
  clear(): void {
    this.audioFeatures.clear();
    this.smoothedAudioValues.clear();
    this.audioBindings = [];
  }
}
