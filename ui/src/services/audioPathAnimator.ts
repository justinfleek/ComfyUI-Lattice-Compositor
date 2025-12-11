/**
 * Audio Path Animator
 *
 * Animates elements along spline paths based on audio features.
 * Two modes like ATI_AudioReactive:
 * - amplitude: position directly maps to volume (silence=start, loud=end)
 * - accumulate: travels forward on sound, bounces at ends
 */

export type MovementMode = 'amplitude' | 'accumulate';

export interface PathAnimatorConfig {
  movementMode: MovementMode;
  sensitivity: number;        // Range (amplitude) or Speed (accumulate)
  smoothing: number;          // 0-1, temporal smoothing
  // Amplitude mode specifics
  release: number;            // 0-1, how fast returns to start after beat (0.2=snappy, 0.8=slow)
  amplitudeCurve: number;     // 1.0=linear, >1=noise gate/expander
  // Accumulate mode specifics
  flipOnBeat: boolean;        // Reverse direction on beat detection
  beatThreshold: number;      // 0.02=sensitive, 0.1=only kicks
  // Visual
  motionBlur: boolean;        // Streak connecting previous to current frame
  motionBlurStrength: number; // 0-1
}

export interface PathAnimatorState {
  position: number;           // 0-1 along path
  direction: 1 | -1;          // For accumulate bounce/flip
  previousPosition: number;   // For motion blur
  smoothedValue: number;      // After smoothing applied
  x: number;                  // Current X position on path
  y: number;                  // Current Y position on path
  angle: number;              // Current tangent angle on path
}

interface PathSegment {
  type: 'M' | 'L' | 'C' | 'Q' | 'Z';
  points: number[];
  length: number;
  startT: number;
  endT: number;
}

const DEFAULT_CONFIG: PathAnimatorConfig = {
  movementMode: 'amplitude',
  sensitivity: 1.0,
  smoothing: 0.3,
  release: 0.5,
  amplitudeCurve: 1.0,
  flipOnBeat: true,
  beatThreshold: 0.05,
  motionBlur: false,
  motionBlurStrength: 0.5
};

export class AudioPathAnimator {
  private config: PathAnimatorConfig;
  private state: PathAnimatorState;
  private pathSegments: PathSegment[] = [];
  private totalLength: number = 0;
  private releaseState: number = 0;  // For amplitude mode release tracking

  constructor(config: Partial<PathAnimatorConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.state = {
      position: 0,
      direction: 1,
      previousPosition: 0,
      smoothedValue: 0,
      x: 0,
      y: 0,
      angle: 0
    };
  }

  /**
   * Set the SVG path data to animate along
   */
  setPath(pathData: string): void {
    this.pathSegments = this.parsePath(pathData);
    this.calculateSegmentLengths();
  }

  /**
   * Parse SVG path data into segments
   */
  private parsePath(pathData: string): PathSegment[] {
    const segments: PathSegment[] = [];
    const commands = pathData.match(/[MLCQZ][^MLCQZ]*/gi) || [];

    let currentX = 0;
    let currentY = 0;

    for (const cmd of commands) {
      const type = cmd[0].toUpperCase() as PathSegment['type'];
      const nums = cmd.slice(1).trim().split(/[\s,]+/).map(Number).filter(n => !isNaN(n));

      switch (type) {
        case 'M':
          currentX = nums[0] || 0;
          currentY = nums[1] || 0;
          segments.push({
            type: 'M',
            points: [currentX, currentY],
            length: 0,
            startT: 0,
            endT: 0
          });
          break;

        case 'L':
          segments.push({
            type: 'L',
            points: [currentX, currentY, nums[0], nums[1]],
            length: 0,
            startT: 0,
            endT: 0
          });
          currentX = nums[0];
          currentY = nums[1];
          break;

        case 'C':
          segments.push({
            type: 'C',
            points: [currentX, currentY, nums[0], nums[1], nums[2], nums[3], nums[4], nums[5]],
            length: 0,
            startT: 0,
            endT: 0
          });
          currentX = nums[4];
          currentY = nums[5];
          break;

        case 'Q':
          segments.push({
            type: 'Q',
            points: [currentX, currentY, nums[0], nums[1], nums[2], nums[3]],
            length: 0,
            startT: 0,
            endT: 0
          });
          currentX = nums[2];
          currentY = nums[3];
          break;

        case 'Z':
          // Close path - line back to start
          const firstMove = segments.find(s => s.type === 'M');
          if (firstMove) {
            segments.push({
              type: 'L',
              points: [currentX, currentY, firstMove.points[0], firstMove.points[1]],
              length: 0,
              startT: 0,
              endT: 0
            });
          }
          break;
      }
    }

    return segments;
  }

  /**
   * Calculate lengths for each segment
   */
  private calculateSegmentLengths(): void {
    let totalLength = 0;

    for (const segment of this.pathSegments) {
      switch (segment.type) {
        case 'M':
          segment.length = 0;
          break;
        case 'L':
          segment.length = this.lineLength(segment.points);
          break;
        case 'C':
          segment.length = this.bezierLength(segment.points, 3);
          break;
        case 'Q':
          segment.length = this.bezierLength(segment.points, 2);
          break;
      }

      segment.startT = totalLength;
      totalLength += segment.length;
      segment.endT = totalLength;
    }

    this.totalLength = totalLength;

    // Normalize to 0-1
    if (this.totalLength > 0) {
      for (const segment of this.pathSegments) {
        segment.startT /= this.totalLength;
        segment.endT /= this.totalLength;
      }
    }
  }

  private lineLength(points: number[]): number {
    const dx = points[2] - points[0];
    const dy = points[3] - points[1];
    return Math.sqrt(dx * dx + dy * dy);
  }

  private bezierLength(points: number[], degree: number): number {
    // Approximate bezier length using line segments
    const steps = 20;
    let length = 0;
    let prevX = points[0];
    let prevY = points[1];

    for (let i = 1; i <= steps; i++) {
      const t = i / steps;
      const { x, y } = this.getBezierPoint(points, t, degree);
      const dx = x - prevX;
      const dy = y - prevY;
      length += Math.sqrt(dx * dx + dy * dy);
      prevX = x;
      prevY = y;
    }

    return length;
  }

  private getBezierPoint(points: number[], t: number, degree: number): { x: number; y: number } {
    if (degree === 2) {
      // Quadratic bezier
      const mt = 1 - t;
      return {
        x: mt * mt * points[0] + 2 * mt * t * points[2] + t * t * points[4],
        y: mt * mt * points[1] + 2 * mt * t * points[3] + t * t * points[5]
      };
    } else {
      // Cubic bezier
      const mt = 1 - t;
      const mt2 = mt * mt;
      const t2 = t * t;
      return {
        x: mt2 * mt * points[0] + 3 * mt2 * t * points[2] + 3 * mt * t2 * points[4] + t2 * t * points[6],
        y: mt2 * mt * points[1] + 3 * mt2 * t * points[3] + 3 * mt * t2 * points[5] + t2 * t * points[7]
      };
    }
  }

  /**
   * Update position based on audio value
   */
  update(audioValue: number, isBeat: boolean): PathAnimatorState {
    this.state.previousPosition = this.state.position;

    // Apply smoothing
    const smoothedInput = this.state.smoothedValue * this.config.smoothing +
                          audioValue * (1 - this.config.smoothing);
    this.state.smoothedValue = smoothedInput;

    if (this.config.movementMode === 'amplitude') {
      this.updateAmplitudeMode(smoothedInput);
    } else {
      this.updateAccumulateMode(smoothedInput, isBeat);
    }

    // Update x, y, angle from current position on path
    const pathPoint = this.getPositionOnPath(this.state.position);
    this.state.x = pathPoint.x;
    this.state.y = pathPoint.y;
    this.state.angle = pathPoint.angle;

    return { ...this.state };
  }

  private updateAmplitudeMode(audioValue: number): void {
    // Apply amplitude curve (power function for noise gate effect)
    let processedValue = Math.pow(audioValue, this.config.amplitudeCurve);

    // Apply release envelope
    if (processedValue > this.releaseState) {
      this.releaseState = processedValue;
    } else {
      // Exponential decay based on release setting
      // Lower release = faster decay (snappier)
      const decayRate = 1 - (this.config.release * 0.95);
      this.releaseState *= decayRate;
    }

    // Final position is blend of current value and release envelope
    const finalValue = Math.max(processedValue, this.releaseState);

    // Map to position with sensitivity
    this.state.position = Math.max(0, Math.min(1, finalValue * this.config.sensitivity));
  }

  private updateAccumulateMode(audioValue: number, isBeat: boolean): void {
    // Check for beat-triggered direction flip
    if (this.config.flipOnBeat && isBeat && audioValue > this.config.beatThreshold) {
      this.state.direction *= -1;
    }

    // Accumulate position based on audio value
    const delta = audioValue * this.config.sensitivity * 0.02 * this.state.direction;
    let newPosition = this.state.position + delta;

    // Bounce at boundaries
    if (newPosition > 1) {
      newPosition = 2 - newPosition;
      this.state.direction = -1;
    } else if (newPosition < 0) {
      newPosition = -newPosition;
      this.state.direction = 1;
    }

    // Clamp just in case
    this.state.position = Math.max(0, Math.min(1, newPosition));
  }

  /**
   * Get x, y, angle at position t along path
   */
  getPositionOnPath(t: number): { x: number; y: number; angle: number } {
    t = Math.max(0, Math.min(1, t));

    if (this.pathSegments.length === 0) {
      return { x: 0, y: 0, angle: 0 };
    }

    // Find the segment containing t
    let segment = this.pathSegments[0];
    for (const seg of this.pathSegments) {
      if (seg.type !== 'M' && t >= seg.startT && t <= seg.endT) {
        segment = seg;
        break;
      }
    }

    if (segment.type === 'M') {
      return { x: segment.points[0], y: segment.points[1], angle: 0 };
    }

    // Calculate local t within segment
    const segmentT = segment.endT > segment.startT
      ? (t - segment.startT) / (segment.endT - segment.startT)
      : 0;

    let x: number, y: number;
    let tangentX: number, tangentY: number;

    switch (segment.type) {
      case 'L':
        x = segment.points[0] + (segment.points[2] - segment.points[0]) * segmentT;
        y = segment.points[1] + (segment.points[3] - segment.points[1]) * segmentT;
        tangentX = segment.points[2] - segment.points[0];
        tangentY = segment.points[3] - segment.points[1];
        break;

      case 'Q': {
        const result = this.getBezierPoint(segment.points, segmentT, 2);
        x = result.x;
        y = result.y;
        // Quadratic bezier tangent
        const mt = 1 - segmentT;
        tangentX = 2 * mt * (segment.points[2] - segment.points[0]) +
                   2 * segmentT * (segment.points[4] - segment.points[2]);
        tangentY = 2 * mt * (segment.points[3] - segment.points[1]) +
                   2 * segmentT * (segment.points[5] - segment.points[3]);
        break;
      }

      case 'C': {
        const result = this.getBezierPoint(segment.points, segmentT, 3);
        x = result.x;
        y = result.y;
        // Cubic bezier tangent
        const mt = 1 - segmentT;
        const mt2 = mt * mt;
        const t2 = segmentT * segmentT;
        tangentX = 3 * mt2 * (segment.points[2] - segment.points[0]) +
                   6 * mt * segmentT * (segment.points[4] - segment.points[2]) +
                   3 * t2 * (segment.points[6] - segment.points[4]);
        tangentY = 3 * mt2 * (segment.points[3] - segment.points[1]) +
                   6 * mt * segmentT * (segment.points[5] - segment.points[3]) +
                   3 * t2 * (segment.points[7] - segment.points[5]);
        break;
      }

      default:
        x = 0;
        y = 0;
        tangentX = 1;
        tangentY = 0;
    }

    const angle = Math.atan2(tangentY, tangentX);

    return { x, y, angle };
  }

  /**
   * Get motion blur trail points
   */
  getMotionBlurTrail(steps: number = 5): Array<{ x: number; y: number; opacity: number }> {
    if (!this.config.motionBlur) return [];

    const trail: Array<{ x: number; y: number; opacity: number }> = [];
    const startT = this.state.previousPosition;
    const endT = this.state.position;

    for (let i = 0; i <= steps; i++) {
      const t = startT + (endT - startT) * (i / steps);
      const pos = this.getPositionOnPath(t);
      const opacity = (i / steps) * this.config.motionBlurStrength;
      trail.push({ x: pos.x, y: pos.y, opacity });
    }

    return trail;
  }

  /**
   * Reset animator state
   */
  reset(): void {
    this.state = {
      position: 0,
      direction: 1,
      previousPosition: 0,
      smoothedValue: 0,
      x: 0,
      y: 0,
      angle: 0
    };
    this.releaseState = 0;
  }

  /**
   * Get current config
   */
  getConfig(): PathAnimatorConfig {
    return { ...this.config };
  }

  /**
   * Update config
   */
  setConfig(updates: Partial<PathAnimatorConfig>): void {
    Object.assign(this.config, updates);
  }

  /**
   * Get current state
   */
  getState(): PathAnimatorState {
    return { ...this.state };
  }
}

export function createDefaultPathAnimatorConfig(): PathAnimatorConfig {
  return { ...DEFAULT_CONFIG };
}
