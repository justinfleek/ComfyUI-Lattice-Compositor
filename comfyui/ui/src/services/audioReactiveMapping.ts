/**
 * Audio Reactive Mapping System
 *
 * Maps ANY audio feature to ANY animatable parameter.
 * This is the core of RyanOnTheInside's "Flex Features" system.
 */

// Import AudioFeature from canonical source (particles/types defines all features)
import type { AudioFeature } from "@/engine/particles/types";
import type { AudioAnalysis, PeakData } from "./audioFeatures";
import { getFeatureAtFrame, isPeakAtFrame } from "./audioFeatures";
import { safeNonNegativeDefault } from "@/utils/typeGuards";

// Re-export for consumers that import from this module
export type { AudioFeature };

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Types
// ═══════════════════════════════════════════════════════════════════════════

export type TargetParameter =
  // Particle parameters
  | "particle.emissionRate"
  | "particle.speed"
  | "particle.size"
  | "particle.gravity"
  | "particle.windStrength"
  | "particle.windDirection"
  // Depthflow parameters
  | "depthflow.zoom"
  | "depthflow.offsetX"
  | "depthflow.offsetY"
  | "depthflow.rotation"
  | "depthflow.depthScale"
  // Path animation
  | "path.position"
  // Generic layer properties
  | "layer.opacity"
  | "layer.scale"
  | "layer.rotation"
  | "layer.x"
  | "layer.y"
  // Extended layer properties (inspired by filliptm's ComfyUI_Fill-Nodes)
  // Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
  | "layer.scaleX"
  | "layer.scaleY" // Non-uniform scale (breathing effect)
  | "layer.brightness"
  | "layer.saturation" // Color adjustments
  | "layer.contrast"
  | "layer.hue" // More color controls
  | "layer.blur" // Blur intensity
  // Video layer properties
  | "video.playbackSpeed" // Time stretch/speed reactive
  // Effect parameters (applied as effect modifiers)
  | "effect.glowIntensity"
  | "effect.glowRadius"
  | "effect.edgeGlowIntensity" // Edge glow reactive
  | "effect.glitchAmount" // Glitch reactive
  | "effect.rgbSplitAmount" // RGB split reactive
  // Camera properties
  | "camera.fov"
  | "camera.dollyZ"
  | "camera.shake"
  // Spline control point properties (dynamic index)
  // Format: spline.controlPoint.{index}.{x|y|depth}
  | `spline.controlPoint.${number}.x`
  | `spline.controlPoint.${number}.y`
  | `spline.controlPoint.${number}.depth`;

export interface AudioMapping {
  id: string;
  feature: AudioFeature;
  target: TargetParameter;
  targetLayerId?: string; // Which layer to affect
  targetEmitterId?: string; // For particle emitter-specific mapping

  // Core mapping parameters
  sensitivity: number; // Multiplier (default 1.0)
  offset: number; // Added to result (default 0)
  min: number; // Clamp minimum
  max: number; // Clamp maximum
  smoothing: number; // 0-1 temporal smoothing
  invert: boolean; // Flip the value (1 - value)
  threshold: number; // Values below this become 0 (noise gate)
  enabled: boolean; // Toggle mapping on/off

  // ATI_AudioReactive style parameters
  amplitudeCurve: number; // Power curve (1=linear, >1=noise gate/expander, <1=compressor)
  release: number; // 0-1, return speed after peak (0=instant, 1=slow decay)

  // Beat/onset response (for flipOnBeat style effects)
  beatResponse: "none" | "flip" | "pulse" | "toggle";
  beatThreshold: number; // 0-1, sensitivity for beat detection

  // Value shaping
  curve: "linear" | "exponential" | "logarithmic" | "smoothstep" | "bounce";
}

export interface IPAdapterTransition {
  imageLayerIds: string[]; // Layer IDs of images to transition between
  peakData: PeakData; // From detectPeaks()
  blendMode: "linear" | "step" | "smooth";
  transitionLength: number; // Frames for crossfade
  minWeight: number; // Minimum IPAdapter weight (0-1)
}

export interface WeightSchedule {
  frame: number;
  weights: number[]; // Weight for each image at this frame
}

// ═══════════════════════════════════════════════════════════════════════════
// Default Values
// ═══════════════════════════════════════════════════════════════════════════

export function createDefaultAudioMapping(
  id?: string,
  feature: AudioFeature = "amplitude",
  target: TargetParameter = "particle.emissionRate",
): AudioMapping {
  return {
    id:
      id || `mapping_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    feature,
    target,
    targetLayerId: undefined,
    targetEmitterId: undefined,
    // Core
    sensitivity: 1.0,
    offset: 0,
    min: 0,
    max: 1,
    smoothing: 0.3,
    invert: false,
    threshold: 0,
    enabled: true,
    // ATI style
    amplitudeCurve: 1.0, // Linear by default
    release: 0.5, // Medium decay
    beatResponse: "none",
    beatThreshold: 0.5,
    curve: "linear",
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// Audio Reactive Mapper
// ═══════════════════════════════════════════════════════════════════════════

export class AudioReactiveMapper {
  private analysis: AudioAnalysis;
  private mappings: Map<string, AudioMapping> = new Map();
  private smoothedValues: Map<string, number> = new Map();
  private releaseEnvelopes: Map<string, number> = new Map(); // ATI-style release tracking
  private beatToggleStates: Map<string, number> = new Map(); // For beat toggle/flip
  private peakData: PeakData | null = null;

  constructor(analysis: AudioAnalysis) {
    this.analysis = analysis;
  }

  /**
   * Set peak data for peak-based features
   */
  setPeakData(peakData: PeakData): void {
    this.peakData = peakData;
  }

  /**
   * Add or update a mapping.
   * Only initializes temporal state for NEW mappings.
   * Existing mappings preserve their temporal state (smoothing, release, toggles).
   */
  addMapping(mapping: AudioMapping): void {
    const isNew = !this.mappings.has(mapping.id);
    this.mappings.set(mapping.id, mapping);
    // Only initialize temporal state for new mappings
    if (isNew) {
      this.smoothedValues.set(mapping.id, 0);
      this.releaseEnvelopes.set(mapping.id, 0);
      this.beatToggleStates.set(mapping.id, 0);
    }
  }

  /**
   * Remove a mapping
   */
  removeMapping(id: string): void {
    this.mappings.delete(id);
    this.smoothedValues.delete(id);
    this.releaseEnvelopes.delete(id);
    this.beatToggleStates.delete(id);
  }

  /**
   * Reset all temporal state (smoothing, release envelopes, beat toggles)
   * Call this when seeking non-sequentially to ensure determinism.
   * Temporal state must be reset on frame jumps.
   */
  resetTemporalState(): void {
    // Reset all smoothed values to 0
    for (const id of this.smoothedValues.keys()) {
      this.smoothedValues.set(id, 0);
    }
    // Reset all release envelopes to 0
    for (const id of this.releaseEnvelopes.keys()) {
      this.releaseEnvelopes.set(id, 0);
    }
    // Reset all beat toggle states to 0
    for (const id of this.beatToggleStates.keys()) {
      this.beatToggleStates.set(id, 0);
    }
  }

  /**
   * Update an existing mapping
   */
  updateMapping(id: string, updates: Partial<AudioMapping>): void {
    const mapping = this.mappings.get(id);
    if (mapping) {
      Object.assign(mapping, updates);
    }
  }

  /**
   * Get a specific mapping
   */
  getMapping(id: string): AudioMapping | undefined {
    return this.mappings.get(id);
  }

  /**
   * Get all mappings
   */
  getAllMappings(): AudioMapping[] {
    return Array.from(this.mappings.values());
  }

  /**
   * Get mappings for a specific layer
   */
  getMappingsForLayer(layerId: string): AudioMapping[] {
    return Array.from(this.mappings.values()).filter(
      (m) => m.targetLayerId === layerId || m.targetLayerId === undefined,
    );
  }

  /**
   * Get mappings for a specific emitter.
   * Implements targetEmitterId filtering.
   */
  getMappingsForEmitter(emitterId: string): AudioMapping[] {
    return Array.from(this.mappings.values()).filter(
      (m) => m.targetEmitterId === emitterId || m.targetEmitterId === undefined,
    );
  }

  /**
   * Get mappings for a specific layer and emitter combination.
   * Combined layer + emitter filtering for particle systems.
   */
  getMappingsForLayerEmitter(
    layerId: string,
    emitterId: string,
  ): AudioMapping[] {
    return Array.from(this.mappings.values()).filter((m) => {
      const layerMatch =
        m.targetLayerId === layerId || m.targetLayerId === undefined;
      const emitterMatch =
        m.targetEmitterId === emitterId || m.targetEmitterId === undefined;
      return layerMatch && emitterMatch;
    });
  }

  /**
   * Get mappings for a specific target parameter
   */
  getMappingsForTarget(target: TargetParameter): AudioMapping[] {
    return Array.from(this.mappings.values()).filter(
      (m) => m.target === target,
    );
  }

  /**
   * Get raw feature value at frame (before mapping transforms)
   */
  getFeatureAtFrame(feature: AudioFeature, frame: number): number {
    if (feature === "peaks") {
      if (this.peakData) {
        return isPeakAtFrame(this.peakData, frame) ? 1 : 0;
      }
      return 0;
    }

    return getFeatureAtFrame(this.analysis, feature, frame);
  }

  /**
   * Get the mapped value for a specific mapping at a frame
   */
  getValueAtFrame(mappingId: string, frame: number): number {
    const mapping = this.mappings.get(mappingId);
    if (!mapping || !mapping.enabled) return 0;

    // Get raw feature value
    let value = this.getFeatureAtFrame(mapping.feature, frame);

    // Apply threshold (noise gate)
    if (value < mapping.threshold) {
      value = 0;
    }

    // Apply amplitude curve (ATI style noise gate/expander)
    // amplitudeCurve > 1 = expander (emphasize loud, suppress quiet)
    // amplitudeCurve < 1 = compressor (boost quiet, limit loud)
    if (mapping.amplitudeCurve !== 1.0) {
      value = value ** mapping.amplitudeCurve;
    }

    // Apply release envelope (ATI style)
    // Value decays slowly after peak, creating smooth response
    // Type proof: releaseEnvelope ∈ number | undefined → number (≥ 0, envelope value)
    const releaseEnvelope = safeNonNegativeDefault(
      this.releaseEnvelopes.get(mappingId),
      0,
      "releaseEnvelopes.get(mappingId)",
    );
    if (value > releaseEnvelope) {
      // Attack: follow input immediately
      this.releaseEnvelopes.set(mappingId, value);
    } else {
      // Release: decay based on release parameter
      // release=0 means instant decay, release=1 means very slow
      const decayRate = 1 - mapping.release * 0.98;
      const newEnvelope = releaseEnvelope * decayRate;
      this.releaseEnvelopes.set(mappingId, newEnvelope);
      // Use the higher of current value or decaying envelope
      value = Math.max(value, newEnvelope);
    }

    // Apply beat response
    if (mapping.beatResponse !== "none") {
      const isBeat =
        this.analysis.onsets.includes(frame) &&
        this.getFeatureAtFrame(mapping.feature, frame) > mapping.beatThreshold;

      if (isBeat) {
        // Type proof: beatToggleState ∈ number | undefined → number (≥ 0, toggle state 0 or 1)
        const currentToggle = safeNonNegativeDefault(
          this.beatToggleStates.get(mappingId),
          0,
          "beatToggleStates.get(mappingId)",
        );

        switch (mapping.beatResponse) {
          case "flip":
            // Flip value direction on beat
            this.beatToggleStates.set(mappingId, currentToggle === 0 ? 1 : 0);
            break;
          case "pulse":
            // Spike to max on beat
            value = 1;
            break;
          case "toggle": {
            // Toggle between 0 and 1 on each beat
            const newToggle = currentToggle === 0 ? 1 : 0;
            this.beatToggleStates.set(mappingId, newToggle);
            value = newToggle;
            break;
          }
        }
      }

      // Apply flip effect if active
      if (mapping.beatResponse === "flip") {
        // Type proof: beatToggleState ∈ number | undefined → number (≥ 0, toggle state 0 or 1)
        const toggle = safeNonNegativeDefault(
          this.beatToggleStates.get(mappingId),
          0,
          "beatToggleStates.get(mappingId)",
        );
        if (toggle === 1) {
          value = 1 - value;
        }
      }
    }

    // Apply curve shaping
    value = this.applyCurve(value, mapping.curve);

    // Apply inversion
    if (mapping.invert) {
      value = 1 - value;
    }

    // Apply sensitivity (multiplier)
    value *= mapping.sensitivity;

    // Apply offset
    value += mapping.offset;

    // Clamp to min/max
    value = Math.max(mapping.min, Math.min(mapping.max, value));

    // Apply smoothing
    // Type proof: smoothedValue ∈ number | undefined → number (≥ 0, smoothed audio value)
    const prevSmoothed = safeNonNegativeDefault(
      this.smoothedValues.get(mappingId),
      0,
      "smoothedValues.get(mappingId)",
    );
    const smoothed =
      prevSmoothed * mapping.smoothing + value * (1 - mapping.smoothing);
    this.smoothedValues.set(mappingId, smoothed);

    return smoothed;
  }

  /**
   * Get ALL mapped values at a frame, organized by target
   */
  getAllValuesAtFrame(frame: number): Map<TargetParameter, number> {
    const values = new Map<TargetParameter, number>();

    for (const mapping of this.mappings.values()) {
      if (!mapping.enabled) continue;

      const value = this.getValueAtFrame(mapping.id, frame);
      const existing = values.get(mapping.target);

      if (existing !== undefined) {
        // Multiple mappings to same target - combine additively
        values.set(mapping.target, existing + value);
      } else {
        values.set(mapping.target, value);
      }
    }

    return values;
  }

  /**
   * Get mapped values for a specific layer at a frame.
   * Excludes emitter-specific mappings (those go to emitters, not layers).
   */
  getValuesForLayerAtFrame(
    layerId: string,
    frame: number,
  ): Map<TargetParameter, number> {
    const values = new Map<TargetParameter, number>();

    for (const mapping of this.mappings.values()) {
      if (!mapping.enabled) continue;
      if (mapping.targetLayerId && mapping.targetLayerId !== layerId) continue;
      // Skip emitter-specific mappings - they're collected separately via collectParticleAudioReactiveModifiers
      if (mapping.targetEmitterId) continue;

      const value = this.getValueAtFrame(mapping.id, frame);
      const existing = values.get(mapping.target);

      if (existing !== undefined) {
        values.set(mapping.target, existing + value);
      } else {
        values.set(mapping.target, value);
      }
    }

    return values;
  }

  /**
   * Get mapped values for a specific emitter at a frame.
   * Implements targetEmitterId filtering for particle systems.
   */
  getValuesForEmitterAtFrame(
    emitterId: string,
    frame: number,
  ): Map<TargetParameter, number> {
    const values = new Map<TargetParameter, number>();

    for (const mapping of this.mappings.values()) {
      if (!mapping.enabled) continue;
      if (mapping.targetEmitterId && mapping.targetEmitterId !== emitterId)
        continue;

      const value = this.getValueAtFrame(mapping.id, frame);
      const existing = values.get(mapping.target);

      if (existing !== undefined) {
        values.set(mapping.target, existing + value);
      } else {
        values.set(mapping.target, value);
      }
    }

    return values;
  }

  /**
   * Get mapped values for a specific layer and emitter at a frame.
   * Combined filtering for particle systems with multiple emitters.
   */
  getValuesForLayerEmitterAtFrame(
    layerId: string,
    emitterId: string,
    frame: number,
  ): Map<TargetParameter, number> {
    const values = new Map<TargetParameter, number>();

    for (const mapping of this.mappings.values()) {
      if (!mapping.enabled) continue;
      if (mapping.targetLayerId && mapping.targetLayerId !== layerId) continue;
      if (mapping.targetEmitterId && mapping.targetEmitterId !== emitterId)
        continue;

      const value = this.getValueAtFrame(mapping.id, frame);
      const existing = values.get(mapping.target);

      if (existing !== undefined) {
        values.set(mapping.target, existing + value);
      } else {
        values.set(mapping.target, value);
      }
    }

    return values;
  }

  /**
   * Apply curve shaping to a value
   */
  private applyCurve(value: number, curve: AudioMapping["curve"]): number {
    const clamped = Math.max(0, Math.min(1, value));

    switch (curve) {
      case "exponential":
        return clamped * clamped;

      case "logarithmic":
        return Math.sqrt(clamped);

      case "smoothstep":
        return clamped * clamped * (3 - 2 * clamped);

      case "bounce":
        // Overshoot and bounce back
        if (clamped < 0.5) {
          return 2 * clamped * clamped;
        } else {
          const t = clamped - 0.5;
          return 0.5 + 0.5 * (1 - (1 - 2 * t) ** 2);
        }
      default:
        return clamped;
    }
  }

  /**
   * Reset smoothing state
   */
  resetSmoothing(): void {
    this.smoothedValues.clear();
    this.releaseEnvelopes.clear();
    this.beatToggleStates.clear();
    for (const mapping of this.mappings.values()) {
      this.smoothedValues.set(mapping.id, 0);
      this.releaseEnvelopes.set(mapping.id, 0);
      this.beatToggleStates.set(mapping.id, 0);
    }
  }

  /**
   * Update analysis data
   */
  setAnalysis(analysis: AudioAnalysis): void {
    this.analysis = analysis;
    this.resetSmoothing();
  }

  /**
   * Clear all mappings
   */
  clear(): void {
    this.mappings.clear();
    this.smoothedValues.clear();
    this.releaseEnvelopes.clear();
    this.beatToggleStates.clear();
  }

  /**
   * Serialize mappings for storage
   */
  serialize(): AudioMapping[] {
    return Array.from(this.mappings.values());
  }

  /**
   * Load mappings from serialized data
   */
  deserialize(mappings: AudioMapping[]): void {
    this.clear();
    for (const mapping of mappings) {
      this.addMapping(mapping);
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// IPAdapter Schedule Generation (from Yvann-Nodes)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Generate IPAdapter weight schedule from peaks
 * At each peak, transition to next image in sequence
 */
export function createIPAdapterSchedule(
  transition: IPAdapterTransition,
  totalFrames: number,
): WeightSchedule[] {
  const { imageLayerIds, peakData, blendMode, transitionLength, minWeight } =
    transition;
  const numImages = imageLayerIds.length;

  if (numImages === 0) return [];

  const schedule: WeightSchedule[] = [];

  // Track current image index
  let currentImageIndex = 0;
  let transitionProgress = 0;
  let isTransitioning = false;
  let transitionStartFrame = 0;

  for (let frame = 0; frame < totalFrames; frame++) {
    const isPeak = isPeakAtFrame(peakData, frame);

    // Start transition on peak
    if (isPeak && !isTransitioning) {
      isTransitioning = true;
      transitionStartFrame = frame;
    }

    // Calculate weights
    const weights: number[] = new Array(numImages).fill(minWeight);

    if (isTransitioning) {
      transitionProgress = (frame - transitionStartFrame) / transitionLength;

      if (transitionProgress >= 1) {
        // Transition complete
        isTransitioning = false;
        currentImageIndex = (currentImageIndex + 1) % numImages;
        transitionProgress = 0;
      }

      if (isTransitioning) {
        // Calculate blend between current and next image
        const nextIndex = (currentImageIndex + 1) % numImages;
        let blend: number;

        switch (blendMode) {
          case "step":
            blend = transitionProgress >= 0.5 ? 1 : 0;
            break;
          case "smooth":
            // Smoothstep
            blend =
              transitionProgress *
              transitionProgress *
              (3 - 2 * transitionProgress);
            break;
          default:
            blend = transitionProgress;
        }

        weights[currentImageIndex] = Math.max(minWeight, 1 - blend);
        weights[nextIndex] = Math.max(minWeight, blend);
      } else {
        // Not transitioning - current image at full weight
        weights[currentImageIndex] = 1;
      }
    } else {
      // Not transitioning - current image at full weight
      weights[currentImageIndex] = 1;
    }

    schedule.push({ frame, weights });
  }

  return schedule;
}

/**
 * Get IPAdapter weights at a specific frame
 */
export function getIPAdapterWeightsAtFrame(
  schedule: WeightSchedule[],
  frame: number,
): number[] {
  const entry = schedule.find((s) => s.frame === frame);
  return entry ? entry.weights : [];
}

// ═══════════════════════════════════════════════════════════════════════════
// Utility Functions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Get human-readable name for a feature
 */
export function getFeatureDisplayName(feature: AudioFeature): string {
  // Partial because not all features need display names - fallback returns raw feature name
  const names: Partial<Record<AudioFeature, string>> = {
    // Core
    amplitude: "Amplitude",
    rms: "RMS Energy",
    spectralCentroid: "Brightness",
    // Frequency bands
    sub: "Sub Bass (20-60Hz)",
    bass: "Bass (60-250Hz)",
    lowMid: "Low Mid (250-500Hz)",
    mid: "Mid (500-2kHz)",
    highMid: "High Mid (2-4kHz)",
    high: "High (4-20kHz)",
    // Events
    onsets: "Beat Onsets",
    peaks: "Detected Peaks",
    // Enhanced features
    spectralFlux: "Spectral Flux (Transients)",
    zeroCrossingRate: "Zero Crossing (Percussive)",
    spectralRolloff: "Spectral Rolloff (High Freq)",
    spectralFlatness: "Spectral Flatness (Noise)",
    chromaEnergy: "Chroma Energy (Harmonic)",
    // Pitch classes
    chromaC: "Chroma: C",
    chromaCs: "Chroma: C#/Db",
    chromaD: "Chroma: D",
    chromaDs: "Chroma: D#/Eb",
    chromaE: "Chroma: E",
    chromaF: "Chroma: F",
    chromaFs: "Chroma: F#/Gb",
    chromaG: "Chroma: G",
    chromaGs: "Chroma: G#/Ab",
    chromaA: "Chroma: A",
    chromaAs: "Chroma: A#/Bb",
    chromaB: "Chroma: B",
  };
  return names[feature] || feature;
}

/**
 * Get human-readable name for a target parameter
 */
export function getTargetDisplayName(target: TargetParameter): string {
  // Check for spline control point targets first
  const splineMatch = target.match(
    /^spline\.controlPoint\.(\d+)\.(x|y|depth)$/,
  );
  if (splineMatch) {
    const index = splineMatch[1];
    const prop =
      splineMatch[2] === "x" ? "X" : splineMatch[2] === "y" ? "Y" : "Depth";
    return `Spline: Control Point ${index} ${prop}`;
  }

  const names: Record<string, string> = {
    "particle.emissionRate": "Particle: Emission Rate",
    "particle.speed": "Particle: Speed",
    "particle.size": "Particle: Size",
    "particle.gravity": "Particle: Gravity",
    "particle.windStrength": "Particle: Wind Strength",
    "particle.windDirection": "Particle: Wind Direction",
    "depthflow.zoom": "Depthflow: Zoom",
    "depthflow.offsetX": "Depthflow: Offset X",
    "depthflow.offsetY": "Depthflow: Offset Y",
    "depthflow.rotation": "Depthflow: Rotation",
    "depthflow.depthScale": "Depthflow: Depth Scale",
    "path.position": "Path: Position",
    "layer.opacity": "Layer: Opacity",
    "layer.scale": "Layer: Scale (Uniform)",
    "layer.scaleX": "Layer: Scale X",
    "layer.scaleY": "Layer: Scale Y",
    "layer.rotation": "Layer: Rotation",
    "layer.x": "Layer: X Position",
    "layer.y": "Layer: Y Position",
    "layer.brightness": "Layer: Brightness",
    "layer.saturation": "Layer: Saturation",
    "layer.contrast": "Layer: Contrast",
    "layer.hue": "Layer: Hue Shift",
    "layer.blur": "Layer: Blur",
    "video.playbackSpeed": "Video: Playback Speed",
    "effect.glowIntensity": "Effect: Glow Intensity",
    "effect.glowRadius": "Effect: Glow Radius",
    "effect.edgeGlowIntensity": "Effect: Edge Glow",
    "effect.glitchAmount": "Effect: Glitch Amount",
    "effect.rgbSplitAmount": "Effect: RGB Split",
    "camera.fov": "Camera: Field of View",
    "camera.dollyZ": "Camera: Dolly Z",
    "camera.shake": "Camera: Shake Intensity",
  };
  return names[target] || target;
}

/**
 * Get all available features
 */
export function getAllFeatures(): AudioFeature[] {
  return [
    // Core
    "amplitude",
    "rms",
    "spectralCentroid",
    // Frequency bands
    "sub",
    "bass",
    "lowMid",
    "mid",
    "highMid",
    "high",
    // Events
    "onsets",
    "peaks",
    // Enhanced
    "spectralFlux",
    "zeroCrossingRate",
    "spectralRolloff",
    "spectralFlatness",
    "chromaEnergy",
    // Pitch classes
    "chromaC",
    "chromaCs",
    "chromaD",
    "chromaDs",
    "chromaE",
    "chromaF",
    "chromaFs",
    "chromaG",
    "chromaGs",
    "chromaA",
    "chromaAs",
    "chromaB",
  ];
}

/**
 * Get features organized by category (for UI grouping)
 */
export function getFeaturesByCategory(): Record<string, AudioFeature[]> {
  return {
    Energy: ["amplitude", "rms"],
    "Frequency Bands": ["sub", "bass", "lowMid", "mid", "highMid", "high"],
    Spectral: [
      "spectralCentroid",
      "spectralFlux",
      "spectralRolloff",
      "spectralFlatness",
    ],
    Events: ["onsets", "peaks"],
    Harmonic: ["chromaEnergy", "zeroCrossingRate"],
    "Pitch Classes": [
      "chromaC",
      "chromaCs",
      "chromaD",
      "chromaDs",
      "chromaE",
      "chromaF",
      "chromaFs",
      "chromaG",
      "chromaGs",
      "chromaA",
      "chromaAs",
      "chromaB",
    ],
  };
}

/**
 * Get all available targets
 */
export function getAllTargets(): TargetParameter[] {
  return [
    "particle.emissionRate",
    "particle.speed",
    "particle.size",
    "particle.gravity",
    "particle.windStrength",
    "particle.windDirection",
    "depthflow.zoom",
    "depthflow.offsetX",
    "depthflow.offsetY",
    "depthflow.rotation",
    "depthflow.depthScale",
    "path.position",
    "layer.opacity",
    "layer.scale",
    "layer.scaleX",
    "layer.scaleY",
    "layer.rotation",
    "layer.x",
    "layer.y",
    "layer.brightness",
    "layer.saturation",
    "layer.contrast",
    "layer.hue",
    "layer.blur",
    "video.playbackSpeed",
    "effect.glowIntensity",
    "effect.glowRadius",
    "effect.edgeGlowIntensity",
    "effect.glitchAmount",
    "effect.rgbSplitAmount",
    "camera.fov",
    "camera.dollyZ",
    "camera.shake",
  ];
}

/**
 * Get targets filtered by category
 * Note: Spline control point targets are dynamic and generated based on the layer
 */
export function getTargetsByCategory(): Record<string, TargetParameter[]> {
  return {
    Particle: [
      "particle.emissionRate",
      "particle.speed",
      "particle.size",
      "particle.gravity",
      "particle.windStrength",
      "particle.windDirection",
    ],
    Depthflow: [
      "depthflow.zoom",
      "depthflow.offsetX",
      "depthflow.offsetY",
      "depthflow.rotation",
      "depthflow.depthScale",
    ],
    Path: ["path.position"],
    "Layer Transform": [
      "layer.opacity",
      "layer.scale",
      "layer.scaleX",
      "layer.scaleY",
      "layer.rotation",
      "layer.x",
      "layer.y",
    ],
    // Extended targets inspired by filliptm's ComfyUI_Fill-Nodes
    // Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
    "Layer Color": [
      "layer.brightness",
      "layer.saturation",
      "layer.contrast",
      "layer.hue",
    ],
    "Layer Effects": [
      "layer.blur",
      "effect.glowIntensity",
      "effect.glowRadius",
      "effect.edgeGlowIntensity",
      "effect.glitchAmount",
      "effect.rgbSplitAmount",
    ],
    Video: ["video.playbackSpeed"],
    Camera: ["camera.fov", "camera.dollyZ", "camera.shake"],
    // Note: 'Spline' targets are generated dynamically based on control point count
    // Use createSplineControlPointTargets() to get targets for a specific spline
  };
}

/**
 * Create spline control point targets for a given number of control points
 * @param controlPointCount Number of control points in the spline
 * @returns Array of TargetParameter for each control point property
 */
export function createSplineControlPointTargets(
  controlPointCount: number,
): TargetParameter[] {
  const targets: TargetParameter[] = [];
  for (let i = 0; i < controlPointCount; i++) {
    targets.push(`spline.controlPoint.${i}.x` as TargetParameter);
    targets.push(`spline.controlPoint.${i}.y` as TargetParameter);
    targets.push(`spline.controlPoint.${i}.depth` as TargetParameter);
  }
  return targets;
}

// ═══════════════════════════════════════════════════════════════════════════
// Audio Reactive Layer Application
// (Inspired by filliptm's ComfyUI_Fill-Nodes)
// Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Represents the audio-reactive modifiers for a layer
 */
export interface AudioReactiveModifiers {
  // Transform
  opacity?: number; // 0-1 additive
  scaleX?: number; // Additive to base scale
  scaleY?: number; // Additive to base scale
  scaleUniform?: number; // Additive to both X and Y
  rotation?: number; // Additive degrees
  x?: number; // Additive position
  y?: number; // Additive position

  // Color adjustments (all additive to base)
  brightness?: number; // -1 to 1
  saturation?: number; // -1 to 1
  contrast?: number; // -1 to 1
  hue?: number; // -180 to 180 degrees

  // Effects
  blur?: number; // 0-100 radius
  glowIntensity?: number; // 0-10
  glowRadius?: number; // 0-100
  glowThreshold?: number; // 0-1 (maps to luminance cutoff)
  edgeGlowIntensity?: number;
  glitchAmount?: number; // 0-10
  rgbSplitAmount?: number; // 0-50

  // Video
  playbackSpeed?: number; // Multiplier (1.0 = normal)

  // Camera
  fov?: number; // Additive FOV degrees
  dollyZ?: number; // Additive Z position
  shake?: number; // 0-1 shake intensity

  // Depthflow layer modifiers
  depthflowZoom?: number; // Additive zoom
  depthflowOffsetX?: number; // Additive offset X
  depthflowOffsetY?: number; // Additive offset Y
  depthflowRotation?: number; // Additive rotation
  depthflowDepthScale?: number; // Additive depth scale

  // Path animation modifier
  pathPosition?: number; // 0-1 position along path

  // Spline control point modifiers (dynamic key format)
  // Key format: splineControlPoint_{index}_{x|y|depth}
  [key: `splineControlPoint_${number}_${"x" | "y" | "depth"}`]:
    | number
    | undefined;
}

/**
 * Particle-specific audio reactive modifiers.
 * Separate interface for particle emitter modifiers.
 */
export interface ParticleAudioReactiveModifiers {
  emissionRate?: number;
  speed?: number;
  size?: number;
  gravity?: number;
  windStrength?: number;
  windDirection?: number;
}

/**
 * Collect particle-specific audio-reactive modifiers for a layer+emitter at a frame.
 * Uses targetEmitterId filtering for emitter-specific mappings.
 */
export function collectParticleAudioReactiveModifiers(
  mapper: AudioReactiveMapper,
  layerId: string,
  emitterId: string,
  frame: number,
): ParticleAudioReactiveModifiers {
  const values = mapper.getValuesForLayerEmitterAtFrame(
    layerId,
    emitterId,
    frame,
  );
  const modifiers: ParticleAudioReactiveModifiers = {};

  // Map particle target parameters to modifier properties
  const targetToModifier: Record<string, keyof ParticleAudioReactiveModifiers> =
    {
      "particle.emissionRate": "emissionRate",
      "particle.speed": "speed",
      "particle.size": "size",
      "particle.gravity": "gravity",
      "particle.windStrength": "windStrength",
      "particle.windDirection": "windDirection",
    };

  for (const [target, value] of values.entries()) {
    const modifierKey = targetToModifier[target];
    if (modifierKey) {
      modifiers[modifierKey] = value;
    }
  }

  return modifiers;
}

/**
 * Collect all audio-reactive modifiers for a layer at a specific frame
 */
export function collectAudioReactiveModifiers(
  mapper: AudioReactiveMapper,
  layerId: string,
  frame: number,
): AudioReactiveModifiers {
  const values = mapper.getValuesForLayerAtFrame(layerId, frame);
  const modifiers: AudioReactiveModifiers = {};

  // Map target parameters to modifier properties
  const targetToModifier: Record<string, keyof AudioReactiveModifiers> = {
    "layer.opacity": "opacity",
    "layer.scale": "scaleUniform",
    "layer.scaleX": "scaleX",
    "layer.scaleY": "scaleY",
    "layer.rotation": "rotation",
    "layer.x": "x",
    "layer.y": "y",
    "layer.brightness": "brightness",
    "layer.saturation": "saturation",
    "layer.contrast": "contrast",
    "layer.hue": "hue",
    "layer.blur": "blur",
    "video.playbackSpeed": "playbackSpeed",
    "effect.glowIntensity": "glowIntensity",
    "effect.glowRadius": "glowRadius",
    "effect.edgeGlowIntensity": "edgeGlowIntensity",
    "effect.glitchAmount": "glitchAmount",
    "effect.rgbSplitAmount": "rgbSplitAmount",
    "camera.fov": "fov",
    "camera.dollyZ": "dollyZ",
    "camera.shake": "shake",
    // Depthflow layer targets
    "depthflow.zoom": "depthflowZoom",
    "depthflow.offsetX": "depthflowOffsetX",
    "depthflow.offsetY": "depthflowOffsetY",
    "depthflow.rotation": "depthflowRotation",
    "depthflow.depthScale": "depthflowDepthScale",
    // Path position target (0-1 along path)
    "path.position": "pathPosition",
  };

  for (const [target, value] of values.entries()) {
    const modifierKey = targetToModifier[target];
    if (modifierKey) {
      modifiers[modifierKey] = value;
    }

    // Handle spline control point targets with format: spline.controlPoint.{index}.{x|y|depth}
    const splineMatch = target.match(
      /^spline\.controlPoint\.(\d+)\.(x|y|depth)$/,
    );
    if (splineMatch) {
      const index = parseInt(splineMatch[1], 10);
      const prop = splineMatch[2] as "x" | "y" | "depth";
      // Type-safe assignment using template literal type
      const key = `splineControlPoint_${index}_${prop}` as `splineControlPoint_${number}_${"x" | "y" | "depth"}`;
      // TypeScript knows this key exists in AudioReactiveModifiers via index signature
      modifiers[key] = value;
    }
  }

  return modifiers;
}

/**
 * Preset configurations for common audio-reactive effects
 * Based on filliptm's audio reactive nodes
 */
export const AUDIO_REACTIVE_PRESETS: Record<string, Partial<AudioMapping>[]> = {
  // Bass-driven breathing/pulsing effect
  "bass-pulse": [
    {
      feature: "bass",
      target: "layer.scaleX",
      sensitivity: 0.3,
      min: 0,
      max: 0.2,
      smoothing: 0.3,
      curve: "smoothstep",
    },
    {
      feature: "bass",
      target: "layer.scaleY",
      sensitivity: 0.3,
      min: 0,
      max: 0.2,
      smoothing: 0.3,
      curve: "smoothstep",
    },
  ],

  // Beat-synced brightness flash
  "beat-flash": [
    {
      feature: "onsets",
      target: "layer.brightness",
      sensitivity: 1.5,
      min: 0,
      max: 0.5,
      smoothing: 0.1,
      release: 0.8,
      curve: "exponential",
    },
  ],

  // High frequency saturation boost
  "high-saturation": [
    {
      feature: "high",
      target: "layer.saturation",
      sensitivity: 1.0,
      min: 0,
      max: 0.3,
      smoothing: 0.4,
      curve: "linear",
    },
  ],

  // Drum-driven glitch effect
  "drum-glitch": [
    {
      feature: "spectralFlux",
      target: "effect.glitchAmount",
      sensitivity: 2.0,
      min: 0,
      max: 5,
      smoothing: 0.1,
      release: 0.9,
      threshold: 0.3,
      curve: "exponential",
    },
    {
      feature: "spectralFlux",
      target: "effect.rgbSplitAmount",
      sensitivity: 15,
      min: 0,
      max: 20,
      smoothing: 0.1,
      release: 0.9,
      threshold: 0.3,
      curve: "exponential",
    },
  ],

  // Music-driven camera movement
  "audio-camera": [
    {
      feature: "bass",
      target: "camera.dollyZ",
      sensitivity: 50,
      min: 0,
      max: 30,
      smoothing: 0.5,
      curve: "smoothstep",
    },
    {
      feature: "spectralFlux",
      target: "camera.shake",
      sensitivity: 0.5,
      min: 0,
      max: 0.3,
      smoothing: 0.2,
      threshold: 0.4,
      curve: "exponential",
    },
  ],

  // Speed reactive video (slow-mo on bass drops)
  "bass-slowmo": [
    {
      feature: "bass",
      target: "video.playbackSpeed",
      sensitivity: -0.5,
      offset: 1.0,
      min: 0.3,
      max: 1.0,
      smoothing: 0.4,
      invert: false,
      curve: "smoothstep",
    },
  ],

  // Amplitude-driven glow
  "amplitude-glow": [
    {
      feature: "amplitude",
      target: "effect.glowIntensity",
      sensitivity: 3,
      min: 0,
      max: 3,
      smoothing: 0.3,
      curve: "exponential",
    },
    {
      feature: "amplitude",
      target: "effect.glowRadius",
      sensitivity: 30,
      min: 5,
      max: 40,
      smoothing: 0.3,
      curve: "exponential",
    },
  ],

  // Spectral blur effect
  "spectral-blur": [
    {
      feature: "spectralCentroid",
      target: "layer.blur",
      sensitivity: 20,
      min: 0,
      max: 15,
      smoothing: 0.4,
      invert: true, // More blur when less high frequency
      curve: "linear",
    },
  ],
};

/**
 * Apply a preset to a mapper for a specific layer
 */
export function applyAudioReactivePreset(
  mapper: AudioReactiveMapper,
  presetName: keyof typeof AUDIO_REACTIVE_PRESETS,
  layerId: string,
): string[] {
  const preset = AUDIO_REACTIVE_PRESETS[presetName];
  if (!preset) return [];

  const mappingIds: string[] = [];

  for (const config of preset) {
    const mapping = createDefaultAudioMapping(
      undefined,
      config.feature as AudioFeature,
      config.target as TargetParameter,
    );

    // Apply preset config
    Object.assign(mapping, config);
    mapping.targetLayerId = layerId;

    mapper.addMapping(mapping);
    mappingIds.push(mapping.id);
  }

  return mappingIds;
}

export default {
  AudioReactiveMapper,
  createDefaultAudioMapping,
  createIPAdapterSchedule,
  getIPAdapterWeightsAtFrame,
  getFeatureDisplayName,
  getTargetDisplayName,
  getAllFeatures,
  getFeaturesByCategory,
  getAllTargets,
  getTargetsByCategory,
  collectAudioReactiveModifiers,
  collectParticleAudioReactiveModifiers, // Collects emitter-specific modifiers for particle systems
  applyAudioReactivePreset,
  AUDIO_REACTIVE_PRESETS,
};
