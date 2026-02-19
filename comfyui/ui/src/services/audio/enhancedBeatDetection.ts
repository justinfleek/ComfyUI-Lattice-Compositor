/**
 * Enhanced Beat Detection
 *
 * Advanced beat detection with gap filling, interpolation, and confidence scoring.
 * Inspired by filliptm's ComfyUI_Fill-Nodes audio processing.
 *
 * Features:
 * - Gap filling: Detect and fill missing beats based on tempo
 * - Beat interpolation: Smooth beat positions for better sync
 * - Confidence scoring: Rate beat detection reliability
 * - Sub-beat detection: Quarter-notes, eighth-notes
 * - Beat grid alignment: Snap to musical grid
 *
 * Attribution:
 * - filliptm's ComfyUI_Fill-Nodes: https://github.com/filliptm/ComfyUI_Fill-Nodes
 *
 * @module services/audio/enhancedBeatDetection
 */

import type { AudioAnalysis } from "../audioFeatures";

// ============================================================================
// Types
// ============================================================================

/**
 * Enhanced beat information
 */
export interface EnhancedBeat {
  /** Frame number where beat occurs */
  frame: number;
  /** Beat strength (0-1) */
  strength: number;
  /** Confidence that this is a real beat (0-1) */
  confidence: number;
  /** Type of beat */
  type: "detected" | "interpolated" | "filled";
  /** Musical position (e.g., 1.1, 1.2, 1.3, 1.4 for quarter notes in measure 1) */
  musicalPosition?: number;
}

/**
 * Beat grid information
 */
export interface BeatGrid {
  /** Detected or estimated BPM */
  bpm: number;
  /** Confidence in BPM detection (0-1) */
  bpmConfidence: number;
  /** Frame of first detected beat */
  firstBeatFrame: number;
  /** Frames per beat */
  framesPerBeat: number;
  /** All beats in the grid */
  beats: EnhancedBeat[];
  /** Downbeats (first beat of each measure) */
  downbeats: number[];
  /** Time signature numerator (assumed 4 for now) */
  timeSignature: number;
}

/**
 * Beat detection configuration
 */
export interface EnhancedBeatConfig {
  /** Minimum gap (in beats) before filling */
  minGapBeats: number;
  /** Maximum gap (in beats) to fill */
  maxGapBeats: number;
  /** Tolerance for beat position matching (frames) */
  positionTolerance: number;
  /** Minimum confidence threshold */
  minConfidence: number;
  /** Enable gap filling */
  fillGaps: boolean;
  /** Enable beat interpolation */
  interpolate: boolean;
  /** Time signature (beats per measure) */
  timeSignature: number;
  /** Target BPM (0 = auto-detect) */
  targetBPM: number;
}

/**
 * Default configuration
 */
export const DEFAULT_BEAT_CONFIG: EnhancedBeatConfig = {
  minGapBeats: 1.5,
  maxGapBeats: 4,
  positionTolerance: 3,
  minConfidence: 0.3,
  fillGaps: true,
  interpolate: true,
  timeSignature: 4,
  targetBPM: 0,
};

// ============================================================================
// Main Beat Detection
// ============================================================================

/**
 * Create an enhanced beat grid from audio analysis
 *
 * @param analysis - Audio analysis from audioFeatures
 * @param fps - Frames per second
 * @param config - Beat detection configuration
 * @returns Enhanced beat grid
 */
export function createEnhancedBeatGrid(
  analysis: AudioAnalysis,
  fps: number,
  config: Partial<EnhancedBeatConfig> = {},
): BeatGrid {
  const cfg: EnhancedBeatConfig = { ...DEFAULT_BEAT_CONFIG, ...config };

  // Get initial beats and BPM
  const detectedBeats = analysis.onsets;
  const bpm = cfg.targetBPM > 0 ? cfg.targetBPM : analysis.bpm;

  // Calculate frames per beat
  const framesPerBeat = (fps * 60) / bpm;

  // Find first strong beat
  const firstBeatFrame = findFirstStrongBeat(analysis, detectedBeats, fps);

  // Convert detected beats to enhanced beats
  let beats: EnhancedBeat[] = detectedBeats.map((frame) => ({
    frame,
    strength: calculateBeatStrength(analysis, frame),
    confidence: 1.0,
    type: "detected" as const,
  }));

  // Fill gaps if enabled
  if (cfg.fillGaps) {
    beats = fillBeatGaps(beats, framesPerBeat, cfg, analysis);
  }

  // Interpolate beat positions if enabled
  if (cfg.interpolate) {
    beats = interpolateBeats(beats, framesPerBeat, cfg.positionTolerance);
  }

  // Calculate BPM confidence
  const bpmConfidence = calculateBPMConfidence(
    beats,
    framesPerBeat,
    cfg.positionTolerance,
  );

  // Assign musical positions
  beats = assignMusicalPositions(
    beats,
    firstBeatFrame,
    framesPerBeat,
    cfg.timeSignature,
  );

  // Filter out low-confidence beats to reduce false positives
  beats = beats.filter((b) => b.confidence >= cfg.minConfidence);

  // Sort by frame
  beats.sort((a, b) => a.frame - b.frame);

  // Find downbeats
  const downbeats = beats
    .filter(
      (b) => b.musicalPosition !== undefined && b.musicalPosition % 1 < 0.001,
    )
    .map((b) => b.frame);

  return {
    bpm,
    bpmConfidence,
    firstBeatFrame,
    framesPerBeat,
    beats,
    downbeats,
    timeSignature: cfg.timeSignature,
  };
}

// ============================================================================
// Gap Filling
// ============================================================================

/**
 * Fill gaps in beat detection
 *
 * When beats are missed, use the tempo to fill in missing beats.
 */
function fillBeatGaps(
  beats: EnhancedBeat[],
  framesPerBeat: number,
  config: EnhancedBeatConfig,
  analysis: AudioAnalysis,
): EnhancedBeat[] {
  if (beats.length < 2) return beats;

  const result: EnhancedBeat[] = [];
  const minGapFrames = config.minGapBeats * framesPerBeat;
  const maxGapFrames = config.maxGapBeats * framesPerBeat;

  for (let i = 0; i < beats.length; i++) {
    result.push(beats[i]);

    if (i < beats.length - 1) {
      const gap = beats[i + 1].frame - beats[i].frame;

      // Check if gap needs filling
      if (gap > minGapFrames && gap <= maxGapFrames) {
        const numMissing = Math.round(gap / framesPerBeat) - 1;

        for (let j = 1; j <= numMissing; j++) {
          const filledFrame = Math.round(beats[i].frame + j * framesPerBeat);
          const strength = calculateBeatStrength(analysis, filledFrame);

          // Only fill if there's some audio energy at this position
          if (strength > 0.1) {
            result.push({
              frame: filledFrame,
              strength: strength * 0.8, // Reduce strength for filled beats
              confidence: 0.6 - j * 0.1, // Lower confidence for later fills
              type: "filled",
            });
          }
        }
      }
    }
  }

  return result;
}

// ============================================================================
// Beat Interpolation
// ============================================================================

/**
 * Interpolate beat positions to align with a regular grid
 *
 * Slightly adjusts beat positions to create more consistent timing.
 */
function interpolateBeats(
  beats: EnhancedBeat[],
  framesPerBeat: number,
  tolerance: number,
): EnhancedBeat[] {
  if (beats.length < 4) return beats;

  // Find the best grid offset using majority voting
  const offsets = beats.map((b) => b.frame % framesPerBeat);
  const avgOffset = offsets.reduce((a, b) => a + b, 0) / offsets.length;

  return beats.map((beat) => {
    // Calculate expected grid position
    const gridPosition = Math.round((beat.frame - avgOffset) / framesPerBeat);
    const expectedFrame = gridPosition * framesPerBeat + avgOffset;
    const deviation = Math.abs(beat.frame - expectedFrame);

    // Only interpolate if within tolerance
    if (deviation <= tolerance && beat.type === "detected") {
      return {
        ...beat,
        frame: Math.round(expectedFrame),
        type: "interpolated" as const,
        confidence: beat.confidence * (1 - (deviation / tolerance) * 0.2),
      };
    }

    return beat;
  });
}

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Find the first strong beat (likely a downbeat)
 */
function findFirstStrongBeat(
  analysis: AudioAnalysis,
  beats: number[],
  fps: number,
): number {
  if (beats.length === 0) return 0;

  // Look for the strongest beat in the first few seconds
  const searchWindow = Math.min(fps * 4, beats.length);
  let strongestFrame = beats[0];
  let strongestValue = 0;

  for (let i = 0; i < searchWindow && i < beats.length; i++) {
    const strength = calculateBeatStrength(analysis, beats[i]);
    if (strength > strongestValue) {
      strongestValue = strength;
      strongestFrame = beats[i];
    }
  }

  return strongestFrame;
}

/**
 * Calculate beat strength from audio analysis
 */
function calculateBeatStrength(analysis: AudioAnalysis, frame: number): number {
  const clampedFrame = Math.max(
    0,
    Math.min(frame, analysis.amplitudeEnvelope.length - 1),
  );

  // Lean4/PureScript/Haskell: Explicit pattern matching on array access
  // Type proof: array[index] ∈ number | undefined → number (≥ 0, amplitude)
  // PureScript: case array[index] of Just x -> x; Nothing -> 0
  const amplitudeRaw = analysis.amplitudeEnvelope[clampedFrame];
  const safeAmplitude: number = amplitudeRaw !== undefined && Number.isFinite(amplitudeRaw) && amplitudeRaw >= 0
    ? amplitudeRaw
    : 0;
  
  const bassRaw = analysis.frequencyBands.bass[clampedFrame];
  const safeBass: number = bassRaw !== undefined && Number.isFinite(bassRaw) && bassRaw >= 0
    ? bassRaw
    : 0;
  
  // Type proof: spectralFlux ∈ number[] | undefined → number (≥ 0, flux)
  const fluxRaw = analysis.spectralFlux !== undefined
    ? analysis.spectralFlux[clampedFrame]
    : undefined;
  const safeFlux: number = fluxRaw !== undefined && Number.isFinite(fluxRaw) && fluxRaw >= 0
    ? fluxRaw
    : 0;

  // Weight: bass and spectral flux are most important for beats
  return safeAmplitude * 0.3 + safeBass * 0.4 + safeFlux * 0.3;
}

/**
 * Calculate confidence in BPM detection
 */
function calculateBPMConfidence(
  beats: EnhancedBeat[],
  framesPerBeat: number,
  tolerance: number,
): number {
  if (beats.length < 4) return 0.3;

  // Calculate how well beats align with expected tempo
  let alignedCount = 0;
  const detectedBeats = beats.filter((b) => b.type === "detected");

  for (let i = 1; i < detectedBeats.length; i++) {
    const interval = detectedBeats[i].frame - detectedBeats[i - 1].frame;
    const _deviation = Math.abs(interval - framesPerBeat);
    const multipleDeviation = Math.min(
      Math.abs(interval - framesPerBeat),
      Math.abs(interval - framesPerBeat * 2),
      Math.abs(interval - framesPerBeat / 2),
    );

    if (multipleDeviation <= tolerance) {
      alignedCount++;
    }
  }

  return Math.min(1, alignedCount / (detectedBeats.length - 1) + 0.2);
}

/**
 * Assign musical positions (measure.beat) to beats
 */
function assignMusicalPositions(
  beats: EnhancedBeat[],
  firstBeatFrame: number,
  framesPerBeat: number,
  timeSignature: number,
): EnhancedBeat[] {
  return beats.map((beat) => {
    const beatsFromFirst = (beat.frame - firstBeatFrame) / framesPerBeat;
    const measure = Math.floor(beatsFromFirst / timeSignature) + 1;
    const beatInMeasure = (beatsFromFirst % timeSignature) + 1;

    return {
      ...beat,
      musicalPosition: measure + (beatInMeasure - 1) / 10, // e.g., 1.1, 1.2, 1.3, 1.4
    };
  });
}

// ============================================================================
// Sub-Beat Detection
// ============================================================================

/**
 * Generate sub-beats (eighth notes, sixteenth notes, etc.)
 *
 * @param grid - Beat grid
 * @param subdivision - 2 for eighth notes, 4 for sixteenth notes
 * @returns Array of sub-beat frames
 */
export function generateSubBeats(
  grid: BeatGrid,
  subdivision: 2 | 4 | 8 = 2,
): number[] {
  const subBeats: number[] = [];
  const framesPerSubBeat = grid.framesPerBeat / subdivision;

  for (const beat of grid.beats) {
    for (let i = 0; i < subdivision; i++) {
      subBeats.push(Math.round(beat.frame + i * framesPerSubBeat));
    }
  }

  return [...new Set(subBeats)].sort((a, b) => a - b);
}

/**
 * Get the nearest beat to a given frame
 *
 * @param grid - Beat grid
 * @param frame - Target frame
 * @returns Nearest beat or null
 */
export function getNearestBeat(
  grid: BeatGrid,
  frame: number,
): EnhancedBeat {
  if (grid.beats.length === 0) {
    throw new Error(`[EnhancedBeatDetection] Cannot find nearest beat: Beat grid is empty (frame ${frame})`);
  }

  let nearest = grid.beats[0];
  let minDistance = Math.abs(frame - nearest.frame);

  for (const beat of grid.beats) {
    const distance = Math.abs(frame - beat.frame);
    if (distance < minDistance) {
      minDistance = distance;
      nearest = beat;
    }
  }

  return nearest;
}

/**
 * Check if a frame is on a beat (within tolerance)
 *
 * @param grid - Beat grid
 * @param frame - Target frame
 * @param tolerance - Frame tolerance (default: 2)
 * @returns True if frame is on a beat
 */
export function isOnBeat(
  grid: BeatGrid,
  frame: number,
  tolerance: number = 2,
): boolean {
  return grid.beats.some((b) => Math.abs(b.frame - frame) <= tolerance);
}

/**
 * Check if a frame is on a downbeat (first beat of measure)
 *
 * @param grid - Beat grid
 * @param frame - Target frame
 * @param tolerance - Frame tolerance (default: 2)
 * @returns True if frame is on a downbeat
 */
export function isOnDownbeat(
  grid: BeatGrid,
  frame: number,
  tolerance: number = 2,
): boolean {
  return grid.downbeats.some((db) => Math.abs(db - frame) <= tolerance);
}

/**
 * Get beat intensity at a given frame
 *
 * Returns a smooth intensity value that peaks on beats and
 * decays between them. Useful for audio-reactive animations.
 *
 * @param grid - Beat grid
 * @param frame - Target frame
 * @param decay - Decay rate (0-1, higher = faster decay)
 * @returns Intensity value (0-1)
 */
export function getBeatIntensity(
  grid: BeatGrid,
  frame: number,
  decay: number = 0.9,
): number {
  const nearest = getNearestBeat(grid, frame);
  if (!nearest) return 0;

  const framesSinceBeat = frame - nearest.frame;

  if (framesSinceBeat < 0) {
    // Before the beat - anticipation
    return 0;
  }

  // Exponential decay from beat
  const decayFactor = decay ** framesSinceBeat;
  return nearest.strength * decayFactor;
}

/**
 * Get pulsing intensity that smoothly interpolates between beats
 *
 * Creates a smoother animation than getBeatIntensity.
 *
 * @param grid - Beat grid
 * @param frame - Target frame
 * @returns Pulsing intensity (0-1)
 */
export function getPulseIntensity(grid: BeatGrid, frame: number): number {
  // Find position within beat cycle
  const beatPhase = (frame % grid.framesPerBeat) / grid.framesPerBeat;

  // Sine wave that peaks at beat
  return (Math.cos(beatPhase * Math.PI * 2) + 1) / 2;
}

// ============================================================================
// Presets
// ============================================================================

/**
 * Preset configurations for different music genres
 */
export const BEAT_DETECTION_PRESETS: Record<
  string,
  Partial<EnhancedBeatConfig>
> = {
  /**
   * Electronic/EDM - Strong regular beats
   */
  electronic: {
    fillGaps: true,
    interpolate: true,
    minGapBeats: 1.2,
    maxGapBeats: 2,
    positionTolerance: 2,
    timeSignature: 4,
  },

  /**
   * Rock/Pop - Variable dynamics
   */
  rock: {
    fillGaps: true,
    interpolate: true,
    minGapBeats: 1.5,
    maxGapBeats: 4,
    positionTolerance: 3,
    timeSignature: 4,
  },

  /**
   * Jazz - Swing and irregular timing
   */
  jazz: {
    fillGaps: false,
    interpolate: false,
    minGapBeats: 2,
    maxGapBeats: 8,
    positionTolerance: 5,
    timeSignature: 4,
  },

  /**
   * Classical - Variable tempo
   */
  classical: {
    fillGaps: false,
    interpolate: false,
    minGapBeats: 2,
    maxGapBeats: 16,
    positionTolerance: 6,
    timeSignature: 4,
  },

  /**
   * Hip-Hop - Strong regular beats with emphasis
   */
  hiphop: {
    fillGaps: true,
    interpolate: true,
    minGapBeats: 1.3,
    maxGapBeats: 3,
    positionTolerance: 2,
    timeSignature: 4,
  },

  /**
   * Waltz - 3/4 time
   */
  waltz: {
    fillGaps: true,
    interpolate: true,
    minGapBeats: 1.5,
    maxGapBeats: 4,
    positionTolerance: 3,
    timeSignature: 3,
  },
};

/**
 * Check if enhanced beat detection is available
 *
 * Always returns true since this is a client-side module.
 */
export function isEnhancedBeatDetectionAvailable(): boolean {
  return true;
}
