/**
 * Audio Reactive Mapping System
 *
 * Maps ANY audio feature to ANY animatable parameter.
 * This is the core of RyanOnTheInside's "Flex Features" system.
 */

import type { AudioAnalysis, PeakData } from './audioFeatures';
import { getFeatureAtFrame, isPeakAtFrame } from './audioFeatures';

// ============================================================================
// Types
// ============================================================================

export type AudioFeature =
  | 'amplitude' | 'rms' | 'spectralCentroid'
  | 'sub' | 'bass' | 'lowMid' | 'mid' | 'highMid' | 'high'
  | 'onsets' | 'peaks';

export type TargetParameter =
  // Particle parameters
  | 'particle.emissionRate' | 'particle.speed' | 'particle.size'
  | 'particle.gravity' | 'particle.windStrength' | 'particle.windDirection'
  // Depthflow parameters
  | 'depthflow.zoom' | 'depthflow.offsetX' | 'depthflow.offsetY'
  | 'depthflow.rotation' | 'depthflow.depthScale'
  // Path animation
  | 'path.position'
  // Generic layer properties
  | 'layer.opacity' | 'layer.scale' | 'layer.rotation' | 'layer.x' | 'layer.y';

export interface AudioMapping {
  id: string;
  feature: AudioFeature;
  target: TargetParameter;
  targetLayerId?: string;     // Which layer to affect
  targetEmitterId?: string;   // For particle emitter-specific mapping
  // Mapping curve
  sensitivity: number;        // Multiplier (default 1.0)
  offset: number;             // Added to result (default 0)
  min: number;                // Clamp minimum
  max: number;                // Clamp maximum
  smoothing: number;          // 0-1 temporal smoothing
  invert: boolean;            // Flip the value (1 - value)
  threshold: number;          // Values below this become 0 (noise gate)
  enabled: boolean;           // Toggle mapping on/off
}

export interface IPAdapterTransition {
  imageLayerIds: string[];    // Layer IDs of images to transition between
  peakData: PeakData;         // From detectPeaks()
  blendMode: 'linear' | 'step' | 'smooth';
  transitionLength: number;   // Frames for crossfade
  minWeight: number;          // Minimum IPAdapter weight (0-1)
}

export interface WeightSchedule {
  frame: number;
  weights: number[];          // Weight for each image at this frame
}

// ============================================================================
// Default Values
// ============================================================================

export function createDefaultAudioMapping(
  id?: string,
  feature: AudioFeature = 'amplitude',
  target: TargetParameter = 'particle.emissionRate'
): AudioMapping {
  return {
    id: id || `mapping_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
    feature,
    target,
    targetLayerId: undefined,
    targetEmitterId: undefined,
    sensitivity: 1.0,
    offset: 0,
    min: 0,
    max: 1,
    smoothing: 0.3,
    invert: false,
    threshold: 0,
    enabled: true
  };
}

// ============================================================================
// Audio Reactive Mapper
// ============================================================================

export class AudioReactiveMapper {
  private analysis: AudioAnalysis;
  private mappings: Map<string, AudioMapping> = new Map();
  private smoothedValues: Map<string, number> = new Map();
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
   * Add a new mapping
   */
  addMapping(mapping: AudioMapping): void {
    this.mappings.set(mapping.id, mapping);
    this.smoothedValues.set(mapping.id, 0);
  }

  /**
   * Remove a mapping
   */
  removeMapping(id: string): void {
    this.mappings.delete(id);
    this.smoothedValues.delete(id);
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
      m => m.targetLayerId === layerId || m.targetLayerId === undefined
    );
  }

  /**
   * Get mappings for a specific target parameter
   */
  getMappingsForTarget(target: TargetParameter): AudioMapping[] {
    return Array.from(this.mappings.values()).filter(m => m.target === target);
  }

  /**
   * Get raw feature value at frame (before mapping transforms)
   */
  getFeatureAtFrame(feature: AudioFeature, frame: number): number {
    if (feature === 'peaks') {
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
    const prevSmoothed = this.smoothedValues.get(mappingId) || 0;
    const smoothed = prevSmoothed * mapping.smoothing + value * (1 - mapping.smoothing);
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
   * Get mapped values for a specific layer at a frame
   */
  getValuesForLayerAtFrame(
    layerId: string,
    frame: number
  ): Map<TargetParameter, number> {
    const values = new Map<TargetParameter, number>();

    for (const mapping of this.mappings.values()) {
      if (!mapping.enabled) continue;
      if (mapping.targetLayerId && mapping.targetLayerId !== layerId) continue;

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
   * Reset smoothing state
   */
  resetSmoothing(): void {
    this.smoothedValues.clear();
    for (const mapping of this.mappings.values()) {
      this.smoothedValues.set(mapping.id, 0);
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

// ============================================================================
// IPAdapter Schedule Generation (from Yvann-Nodes)
// ============================================================================

/**
 * Generate IPAdapter weight schedule from peaks
 * At each peak, transition to next image in sequence
 */
export function createIPAdapterSchedule(
  transition: IPAdapterTransition,
  totalFrames: number
): WeightSchedule[] {
  const { imageLayerIds, peakData, blendMode, transitionLength, minWeight } = transition;
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
          case 'step':
            blend = transitionProgress >= 0.5 ? 1 : 0;
            break;
          case 'smooth':
            // Smoothstep
            blend = transitionProgress * transitionProgress * (3 - 2 * transitionProgress);
            break;
          case 'linear':
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
  frame: number
): number[] {
  const entry = schedule.find(s => s.frame === frame);
  return entry ? entry.weights : [];
}

// ============================================================================
// Utility Functions
// ============================================================================

/**
 * Get human-readable name for a feature
 */
export function getFeatureDisplayName(feature: AudioFeature): string {
  const names: Record<AudioFeature, string> = {
    amplitude: 'Amplitude',
    rms: 'RMS Energy',
    spectralCentroid: 'Brightness',
    sub: 'Sub Bass (20-60Hz)',
    bass: 'Bass (60-250Hz)',
    lowMid: 'Low Mid (250-500Hz)',
    mid: 'Mid (500-2kHz)',
    highMid: 'High Mid (2-4kHz)',
    high: 'High (4-20kHz)',
    onsets: 'Beat Onsets',
    peaks: 'Detected Peaks'
  };
  return names[feature] || feature;
}

/**
 * Get human-readable name for a target parameter
 */
export function getTargetDisplayName(target: TargetParameter): string {
  const names: Record<TargetParameter, string> = {
    'particle.emissionRate': 'Particle: Emission Rate',
    'particle.speed': 'Particle: Speed',
    'particle.size': 'Particle: Size',
    'particle.gravity': 'Particle: Gravity',
    'particle.windStrength': 'Particle: Wind Strength',
    'particle.windDirection': 'Particle: Wind Direction',
    'depthflow.zoom': 'Depthflow: Zoom',
    'depthflow.offsetX': 'Depthflow: Offset X',
    'depthflow.offsetY': 'Depthflow: Offset Y',
    'depthflow.rotation': 'Depthflow: Rotation',
    'depthflow.depthScale': 'Depthflow: Depth Scale',
    'path.position': 'Path: Position',
    'layer.opacity': 'Layer: Opacity',
    'layer.scale': 'Layer: Scale',
    'layer.rotation': 'Layer: Rotation',
    'layer.x': 'Layer: X Position',
    'layer.y': 'Layer: Y Position'
  };
  return names[target] || target;
}

/**
 * Get all available features
 */
export function getAllFeatures(): AudioFeature[] {
  return [
    'amplitude', 'rms', 'spectralCentroid',
    'sub', 'bass', 'lowMid', 'mid', 'highMid', 'high',
    'onsets', 'peaks'
  ];
}

/**
 * Get all available targets
 */
export function getAllTargets(): TargetParameter[] {
  return [
    'particle.emissionRate', 'particle.speed', 'particle.size',
    'particle.gravity', 'particle.windStrength', 'particle.windDirection',
    'depthflow.zoom', 'depthflow.offsetX', 'depthflow.offsetY',
    'depthflow.rotation', 'depthflow.depthScale',
    'path.position',
    'layer.opacity', 'layer.scale', 'layer.rotation', 'layer.x', 'layer.y'
  ];
}

/**
 * Get targets filtered by category
 */
export function getTargetsByCategory(): Record<string, TargetParameter[]> {
  return {
    'Particle': [
      'particle.emissionRate', 'particle.speed', 'particle.size',
      'particle.gravity', 'particle.windStrength', 'particle.windDirection'
    ],
    'Depthflow': [
      'depthflow.zoom', 'depthflow.offsetX', 'depthflow.offsetY',
      'depthflow.rotation', 'depthflow.depthScale'
    ],
    'Path': ['path.position'],
    'Layer': [
      'layer.opacity', 'layer.scale', 'layer.rotation', 'layer.x', 'layer.y'
    ]
  };
}

export default {
  AudioReactiveMapper,
  createDefaultAudioMapping,
  createIPAdapterSchedule,
  getIPAdapterWeightsAtFrame,
  getFeatureDisplayName,
  getTargetDisplayName,
  getAllFeatures,
  getAllTargets,
  getTargetsByCategory
};
