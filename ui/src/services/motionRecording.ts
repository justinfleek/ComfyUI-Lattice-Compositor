/**
 * Motion Recording Service
 *
 * Records pin motion in real-time during drag operations,
 * applies smoothing, and converts to animation keyframes.
 *
 * Features:
 * - Real-time position sampling during drag
 * - Speed parameter for slow-motion/fast-motion recording
 * - Gaussian smoothing to reduce hand jitter
 * - Keyframe simplification using Douglas-Peucker algorithm
 */

import type { Keyframe } from "@/types/project";

// ============================================================================
// TYPES
// ============================================================================

/**
 * A single position sample recorded during motion
 */
export interface MotionSample {
  /** Timestamp in milliseconds (relative to recording start) */
  time: number;
  /** X position in pixels */
  x: number;
  /** Y position in pixels */
  y: number;
}

/**
 * Recorded motion data for a single pin
 */
export interface RecordedMotion {
  /** ID of the pin being recorded */
  pinId: string;
  /** Array of position samples over time */
  samples: MotionSample[];
  /** Recording speed multiplier (0.5 = half speed playback, 2.0 = double speed) */
  recordingSpeed: number;
}

/**
 * Options for motion recording session
 */
export interface RecordingOptions {
  /** Recording speed (1.0 = realtime, 0.5 = half speed playback) */
  speed: number;
  /** Smoothing amount (0-100, higher = smoother) */
  smoothing: number;
  /** Minimum time between samples in ms (performance optimization) */
  minSampleInterval: number;
}

/**
 * Default recording options
 */
export const DEFAULT_RECORDING_OPTIONS: RecordingOptions = {
  speed: 1.0,
  smoothing: 50,
  minSampleInterval: 16, // ~60fps sampling
};

// ============================================================================
// MOTION SMOOTHING
// ============================================================================

/**
 * Apply Gaussian smoothing to recorded motion samples
 * Reduces jitter from hand movement while preserving overall motion shape
 *
 * @param motion - Recorded motion to smooth
 * @param smoothingAmount - 0-100, higher values = smoother result
 * @returns New RecordedMotion with smoothed samples
 */
export function smoothMotion(
  motion: RecordedMotion,
  smoothingAmount: number,
): RecordedMotion {
  if (motion.samples.length < 3 || smoothingAmount <= 0) {
    return { ...motion, samples: [...motion.samples] };
  }

  // Clamp smoothing to valid range
  const smoothing = Math.max(0, Math.min(100, smoothingAmount));

  // Convert smoothing amount to kernel radius (0-100 -> 1-10 samples)
  const kernelRadius = Math.max(1, Math.floor((smoothing / 100) * 10));

  // Generate Gaussian kernel
  const kernel = generateGaussianKernel(kernelRadius);

  // Apply convolution to x and y separately
  const smoothedSamples: MotionSample[] = motion.samples.map((sample, i) => {
    let smoothX = 0;
    let smoothY = 0;
    let weightSum = 0;

    for (let k = -kernelRadius; k <= kernelRadius; k++) {
      const idx = i + k;
      if (idx >= 0 && idx < motion.samples.length) {
        const weight = kernel[k + kernelRadius];
        smoothX += motion.samples[idx].x * weight;
        smoothY += motion.samples[idx].y * weight;
        weightSum += weight;
      }
    }

    // Normalize by actual weights used (handles edges)
    return {
      time: sample.time,
      x: smoothX / weightSum,
      y: smoothY / weightSum,
    };
  });

  return {
    ...motion,
    samples: smoothedSamples,
  };
}

/**
 * Generate a 1D Gaussian kernel for smoothing
 */
function generateGaussianKernel(radius: number): number[] {
  const sigma = radius / 3; // 3-sigma rule
  const kernel: number[] = [];

  for (let i = -radius; i <= radius; i++) {
    const weight = Math.exp(-(i * i) / (2 * sigma * sigma));
    kernel.push(weight);
  }

  // Normalize kernel
  const sum = kernel.reduce((a, b) => a + b, 0);
  return kernel.map((w) => w / sum);
}

/**
 * Apply moving average smoothing (simpler alternative to Gaussian)
 */
export function smoothMotionMovingAverage(
  motion: RecordedMotion,
  windowSize: number,
): RecordedMotion {
  if (motion.samples.length < windowSize || windowSize < 2) {
    return { ...motion, samples: [...motion.samples] };
  }

  const halfWindow = Math.floor(windowSize / 2);
  const smoothedSamples: MotionSample[] = motion.samples.map((sample, i) => {
    let sumX = 0;
    let sumY = 0;
    let count = 0;

    for (
      let j = Math.max(0, i - halfWindow);
      j <= Math.min(motion.samples.length - 1, i + halfWindow);
      j++
    ) {
      sumX += motion.samples[j].x;
      sumY += motion.samples[j].y;
      count++;
    }

    return {
      time: sample.time,
      x: sumX / count,
      y: sumY / count,
    };
  });

  return {
    ...motion,
    samples: smoothedSamples,
  };
}

// ============================================================================
// KEYFRAME CONVERSION
// ============================================================================

/**
 * Convert recorded motion samples to animation keyframes
 * Handles speed adjustment and aligns samples to frame boundaries
 *
 * @param motion - Recorded motion data
 * @param frameRate - Composition frame rate (e.g., 24, 30, 60)
 * @param startFrame - Frame number where animation should start
 * @returns Array of keyframes compatible with AnimatableProperty
 */
export function convertMotionToKeyframes(
  motion: RecordedMotion,
  frameRate: number,
  startFrame: number,
): Array<Keyframe<{ x: number; y: number }>> {
  if (motion.samples.length === 0) {
    return [];
  }

  const keyframes: Array<Keyframe<{ x: number; y: number }>> = [];
  const msPerFrame = 1000 / frameRate;

  // Adjust time based on recording speed
  // speed=0.5 means recorded at half speed, so playback should be at 2x the recorded time
  // speed=2.0 means recorded at double speed, so playback should be at 0.5x the recorded time
  const speedMultiplier = 1 / motion.recordingSpeed;

  // Get recording duration and calculate frame range
  const firstSample = motion.samples[0];
  const lastSample = motion.samples[motion.samples.length - 1];
  const recordedDuration = lastSample.time - firstSample.time;
  const playbackDuration = recordedDuration * speedMultiplier;
  const totalFrames = Math.ceil(playbackDuration / msPerFrame);

  // Sample at each frame boundary
  for (let f = 0; f <= totalFrames; f++) {
    const playbackTime = f * msPerFrame;
    const recordedTime = playbackTime / speedMultiplier + firstSample.time;

    // Interpolate position at this time
    const pos = interpolatePositionAtTime(motion.samples, recordedTime);

    keyframes.push({
      id: `kf_${motion.pinId}_${startFrame + f}`,
      frame: startFrame + f,
      value: { x: pos.x, y: pos.y },
      interpolation: "linear",
      inHandle: { frame: -5, value: 0, enabled: false },
      outHandle: { frame: 5, value: 0, enabled: false },
      controlMode: "smooth",
    });
  }

  return keyframes;
}

/**
 * Interpolate position at a specific time from samples
 */
function interpolatePositionAtTime(
  samples: MotionSample[],
  time: number,
): { x: number; y: number } {
  // Before first sample
  if (time <= samples[0].time) {
    return { x: samples[0].x, y: samples[0].y };
  }

  // After last sample
  if (time >= samples[samples.length - 1].time) {
    const last = samples[samples.length - 1];
    return { x: last.x, y: last.y };
  }

  // Find surrounding samples
  let prevIdx = 0;
  for (let i = 0; i < samples.length - 1; i++) {
    if (samples[i].time <= time && samples[i + 1].time > time) {
      prevIdx = i;
      break;
    }
  }

  const prev = samples[prevIdx];
  const next = samples[prevIdx + 1];

  // Linear interpolation
  const t = (time - prev.time) / (next.time - prev.time);
  return {
    x: prev.x + (next.x - prev.x) * t,
    y: prev.y + (next.y - prev.y) * t,
  };
}

// ============================================================================
// KEYFRAME SIMPLIFICATION
// ============================================================================

/**
 * Remove redundant keyframes using Douglas-Peucker algorithm
 * Reduces keyframe count while preserving motion shape
 *
 * @param keyframes - Array of position keyframes
 * @param tolerance - Maximum deviation in pixels
 * @returns Simplified keyframe array
 */
export function simplifyKeyframes(
  keyframes: Array<Keyframe<{ x: number; y: number }>>,
  tolerance: number,
): Array<Keyframe<{ x: number; y: number }>> {
  if (keyframes.length <= 2) {
    return [...keyframes];
  }

  // Convert to point array for Douglas-Peucker
  const points = keyframes.map((kf) => ({
    frame: kf.frame,
    x: kf.value.x,
    y: kf.value.y,
    keyframe: kf,
  }));

  // Run Douglas-Peucker
  const simplified = douglasPeucker(points, tolerance);

  // Return simplified keyframes
  return simplified.map((p) => p.keyframe);
}

interface DPPoint {
  frame: number;
  x: number;
  y: number;
  keyframe: Keyframe<{ x: number; y: number }>;
}

/**
 * Douglas-Peucker line simplification algorithm
 * Recursively removes points that are within tolerance of the line between endpoints
 */
function douglasPeucker(points: DPPoint[], tolerance: number): DPPoint[] {
  if (points.length <= 2) {
    return points;
  }

  // Find point with maximum distance from line between first and last
  const first = points[0];
  const last = points[points.length - 1];

  let maxDist = 0;
  let maxIdx = 0;

  for (let i = 1; i < points.length - 1; i++) {
    const dist = perpendicularDistance(points[i], first, last);
    if (dist > maxDist) {
      maxDist = dist;
      maxIdx = i;
    }
  }

  // If max distance exceeds tolerance, recursively simplify
  if (maxDist > tolerance) {
    const left = douglasPeucker(points.slice(0, maxIdx + 1), tolerance);
    const right = douglasPeucker(points.slice(maxIdx), tolerance);

    // Combine results (avoid duplicating the split point)
    return [...left.slice(0, -1), ...right];
  }

  // All points within tolerance - keep only endpoints
  return [first, last];
}

/**
 * Calculate perpendicular distance from point to line segment
 * Uses frame as x-axis and position magnitude as y-axis
 */
function perpendicularDistance(
  point: DPPoint,
  lineStart: DPPoint,
  lineEnd: DPPoint,
): number {
  // Treat frame as time axis, combine x/y into 2D position space
  // We measure distance in position space (pixels)

  const dx = lineEnd.frame - lineStart.frame;
  const dyX = lineEnd.x - lineStart.x;
  const dyY = lineEnd.y - lineStart.y;

  if (dx === 0) {
    // Vertical line - just measure position difference
    const distX = point.x - lineStart.x;
    const distY = point.y - lineStart.y;
    return Math.sqrt(distX * distX + distY * distY);
  }

  // Interpolate expected position at point's frame
  const t = (point.frame - lineStart.frame) / dx;
  const expectedX = lineStart.x + t * dyX;
  const expectedY = lineStart.y + t * dyY;

  // Distance from actual to expected position
  const distX = point.x - expectedX;
  const distY = point.y - expectedY;
  return Math.sqrt(distX * distX + distY * distY);
}

/**
 * Alternative simplification: remove keyframes with minimal change
 * Simpler than Douglas-Peucker, removes redundant "same position" keyframes
 */
export function removeRedundantKeyframes(
  keyframes: Array<Keyframe<{ x: number; y: number }>>,
  minDistance: number,
): Array<Keyframe<{ x: number; y: number }>> {
  if (keyframes.length <= 2) {
    return [...keyframes];
  }

  const result: Array<Keyframe<{ x: number; y: number }>> = [keyframes[0]];

  for (let i = 1; i < keyframes.length - 1; i++) {
    const prev = result[result.length - 1];
    const curr = keyframes[i];

    const dist = Math.sqrt(
      (curr.value.x - prev.value.x) ** 2 + (curr.value.y - prev.value.y) ** 2,
    );

    // Keep keyframe if it moved more than minDistance
    if (dist >= minDistance) {
      result.push(curr);
    }
  }

  // Always keep last keyframe
  result.push(keyframes[keyframes.length - 1]);

  return result;
}

// ============================================================================
// RECORDING SESSION MANAGEMENT
// ============================================================================

/**
 * Motion recording session manager
 * Handles sample collection during drag operations
 */
export class MotionRecorder {
  private pinId: string;
  private samples: MotionSample[] = [];
  private startTime: number = 0;
  private lastSampleTime: number = 0;
  private options: RecordingOptions;
  private isRecording: boolean = false;

  constructor(pinId: string, options: Partial<RecordingOptions> = {}) {
    this.pinId = pinId;
    this.options = { ...DEFAULT_RECORDING_OPTIONS, ...options };
  }

  /**
   * Start recording session
   */
  start(initialX: number, initialY: number): void {
    this.samples = [];
    this.startTime = performance.now();
    this.lastSampleTime = 0;
    this.isRecording = true;

    // Record initial position
    this.addSample(initialX, initialY);
  }

  /**
   * Add a sample during recording
   * Respects minimum sample interval for performance
   */
  addSample(x: number, y: number): void {
    if (!this.isRecording) return;

    const now = performance.now();
    const time = now - this.startTime;

    // Throttle samples based on minSampleInterval
    if (
      time - this.lastSampleTime < this.options.minSampleInterval &&
      this.samples.length > 0
    ) {
      return;
    }

    this.samples.push({ time, x, y });
    this.lastSampleTime = time;
  }

  /**
   * Stop recording and get recorded motion
   */
  stop(): RecordedMotion {
    this.isRecording = false;

    return {
      pinId: this.pinId,
      samples: [...this.samples],
      recordingSpeed: this.options.speed,
    };
  }

  /**
   * Check if currently recording
   */
  get recording(): boolean {
    return this.isRecording;
  }

  /**
   * Get current sample count
   */
  get sampleCount(): number {
    return this.samples.length;
  }

  /**
   * Get recording duration in ms
   */
  get duration(): number {
    if (this.samples.length < 2) return 0;
    return this.samples[this.samples.length - 1].time - this.samples[0].time;
  }
}

// ============================================================================
// CONVENIENCE FUNCTIONS
// ============================================================================

/**
 * Full pipeline: record, smooth, convert to keyframes, simplify
 * Convenience function for common use case
 */
export function processRecordedMotion(
  motion: RecordedMotion,
  frameRate: number,
  startFrame: number,
  smoothingAmount: number = 50,
  simplifyTolerance: number = 2,
): Array<Keyframe<{ x: number; y: number }>> {
  // Step 1: Smooth
  const smoothed = smoothMotion(motion, smoothingAmount);

  // Step 2: Convert to keyframes
  const keyframes = convertMotionToKeyframes(smoothed, frameRate, startFrame);

  // Step 3: Simplify
  const simplified = simplifyKeyframes(keyframes, simplifyTolerance);

  return simplified;
}

/**
 * Calculate the bounding box of recorded motion
 * Useful for UI display
 */
export function getMotionBounds(motion: RecordedMotion): {
  minX: number;
  maxX: number;
  minY: number;
  maxY: number;
  width: number;
  height: number;
} {
  if (motion.samples.length === 0) {
    return { minX: 0, maxX: 0, minY: 0, maxY: 0, width: 0, height: 0 };
  }

  let minX = Infinity;
  let maxX = -Infinity;
  let minY = Infinity;
  let maxY = -Infinity;

  for (const sample of motion.samples) {
    if (sample.x < minX) minX = sample.x;
    if (sample.x > maxX) maxX = sample.x;
    if (sample.y < minY) minY = sample.y;
    if (sample.y > maxY) maxY = sample.y;
  }

  return {
    minX,
    maxX,
    minY,
    maxY,
    width: maxX - minX,
    height: maxY - minY,
  };
}

/**
 * Calculate total path length of motion
 */
export function getMotionPathLength(motion: RecordedMotion): number {
  if (motion.samples.length < 2) return 0;

  let length = 0;
  for (let i = 1; i < motion.samples.length; i++) {
    const dx = motion.samples[i].x - motion.samples[i - 1].x;
    const dy = motion.samples[i].y - motion.samples[i - 1].y;
    length += Math.sqrt(dx * dx + dy * dy);
  }

  return length;
}

/**
 * Calculate average speed of motion in pixels per second
 */
export function getMotionAverageSpeed(motion: RecordedMotion): number {
  if (motion.samples.length < 2) return 0;

  const pathLength = getMotionPathLength(motion);
  const duration =
    motion.samples[motion.samples.length - 1].time - motion.samples[0].time;

  if (duration <= 0) return 0;

  return (pathLength / duration) * 1000; // Convert to pixels/second
}
