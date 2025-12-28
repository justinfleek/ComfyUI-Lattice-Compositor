/**
 * Time Effect Renderers
 *
 * Implements time-based effects: Echo, Posterize Time, Time Warp
 * These effects manipulate temporal aspects of layers.
 *
 * Echo is the signature effect for motion trails - essential for
 * the iPod commercial / light streaks aesthetic.
 */
import {
  registerEffectRenderer,
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams
} from '../effectProcessor';

// ============================================================================
// FRAME BUFFER FOR TIME EFFECTS
// Stores previous frames for echo/trail effects
// ============================================================================

interface FrameBufferEntry {
  imageData: ImageData;
  frame: number;
  storedAtFrame: number;  // BUG-065 fix: Use frame number instead of wall-clock time for determinism
}

/**
 * Frame buffer for time-based effects
 * Maintains a ring buffer of recent frames
 */
class TimeEffectFrameBuffer {
  private buffer: FrameBufferEntry[] = [];
  private readonly maxFrames = 64;  // Max stored frames
  private readonly maxAge = 5000;   // 5 second TTL
  private layerId: string = '';

  /**
   * Set the layer this buffer is associated with
   */
  setLayer(layerId: string): void {
    if (this.layerId !== layerId) {
      this.clear();
      this.layerId = layerId;
    }
  }

  /**
   * Store a frame in the buffer
   * BUG-065 fix: Uses frame number for timestamp instead of Date.now() for determinism
   */
  store(frame: number, canvas: HTMLCanvasElement): void {
    const ctx = canvas.getContext('2d');
    if (!ctx) return;

    const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);

    // Remove existing entry for this frame
    this.buffer = this.buffer.filter(e => e.frame !== frame);

    // Add new entry - use frame number as timestamp for deterministic cleanup
    this.buffer.push({
      imageData,
      frame,
      storedAtFrame: frame  // BUG-065 fix: Frame-based timestamp
    });

    // Trim to max size (keep most recent)
    while (this.buffer.length > this.maxFrames) {
      this.buffer.shift();
    }
  }

  /**
   * Get a frame from the buffer
   * Returns null if frame not found
   */
  get(frame: number): ImageData | null {
    const entry = this.buffer.find(e => e.frame === frame);
    return entry ? entry.imageData : null;
  }

  /**
   * Get the closest frame to the target
   */
  getClosest(targetFrame: number): { imageData: ImageData; frame: number } | null {
    if (this.buffer.length === 0) return null;

    let closest = this.buffer[0];
    let minDist = Math.abs(closest.frame - targetFrame);

    for (const entry of this.buffer) {
      const dist = Math.abs(entry.frame - targetFrame);
      if (dist < minDist) {
        minDist = dist;
        closest = entry;
      }
    }

    return { imageData: closest.imageData, frame: closest.frame };
  }

  /**
   * Get multiple frames for echo effect
   * Returns frames at specified time offsets
   */
  getEchoFrames(
    currentFrame: number,
    echoTimeFrames: number,
    numEchoes: number
  ): Array<{ imageData: ImageData; frame: number; echoIndex: number }> {
    const results: Array<{ imageData: ImageData; frame: number; echoIndex: number }> = [];

    for (let i = 1; i <= numEchoes; i++) {
      const targetFrame = Math.round(currentFrame + echoTimeFrames * i);
      const entry = this.getClosest(targetFrame);
      if (entry) {
        results.push({ ...entry, echoIndex: i });
      }
    }

    return results;
  }

  /**
   * Clear the buffer
   */
  clear(): void {
    this.buffer = [];
  }

  /**
   * Remove old entries based on frame distance
   * BUG-065 fix: Uses frame-based cleanup instead of wall-clock time for determinism
   */
  cleanup(currentFrame: number): void {
    // Keep frames within maxFrames distance of current frame
    const maxFrameDistance = this.maxFrames * 2;  // Allow some buffer for echo effects
    this.buffer = this.buffer.filter(e => Math.abs(currentFrame - e.storedAtFrame) < maxFrameDistance);
  }

  /**
   * Get buffer statistics
   */
  getStats(): { frames: number; oldestFrame: number; newestFrame: number } {
    if (this.buffer.length === 0) {
      return { frames: 0, oldestFrame: -1, newestFrame: -1 };
    }
    const frames = this.buffer.map(e => e.frame);
    return {
      frames: this.buffer.length,
      oldestFrame: Math.min(...frames),
      newestFrame: Math.max(...frames)
    };
  }
}

// Global frame buffer instance (per-layer buffers managed internally)
const frameBuffers = new Map<string, TimeEffectFrameBuffer>();

/**
 * Get or create frame buffer for a layer
 */
function getFrameBuffer(layerId: string): TimeEffectFrameBuffer {
  let buffer = frameBuffers.get(layerId);
  if (!buffer) {
    buffer = new TimeEffectFrameBuffer();
    buffer.setLayer(layerId);
    frameBuffers.set(layerId, buffer);
  }
  return buffer;
}

/**
 * Clear all frame buffers (call on project change)
 */
export function clearAllFrameBuffers(): void {
  frameBuffers.clear();
}

// ============================================================================
// ECHO EFFECT
// Creates motion trails by compositing previous frames
// ============================================================================

/**
 * Echo Operator types - how echoes are composited
 */
type EchoOperator = 'add' | 'screen' | 'maximum' | 'minimum' |
                   'composite_back' | 'composite_front' | 'blend';

/**
 * Echo effect renderer
 * Creates motion trails by blending previous/future frames
 *
 * Parameters:
 * - echo_time: Time offset between echoes in seconds (negative = trail behind)
 * - number_of_echoes: How many echo copies (1-50)
 * - starting_intensity: Opacity of first echo (0-1)
 * - decay: How quickly echoes fade (0-1, higher = faster fade)
 * - echo_operator: How echoes are composited
 *
 * @param input - Current frame canvas
 * @param params - Effect parameters
 * @param frame - Current frame number (passed via extended params)
 * @param fps - Frames per second (passed via extended params)
 * @param layerId - Layer ID for frame buffer (passed via extended params)
 */
export function echoRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  // Get frame info from extended params (needed for echoTime default calculation)
  const frame = params._frame ?? 0;
  // Validate fps (nullish coalescing doesn't catch NaN)
  const fps = (Number.isFinite(params._fps) && params._fps > 0) ? params._fps : 16;

  // Extract parameters with defaults
  // Validate numeric params (NaN bypasses Math.max/min clamps)
  const rawEchoTime = params.echo_time ?? (-1 / fps);
  const echoTime = Number.isFinite(rawEchoTime) ? rawEchoTime : (-1 / fps);
  const rawNumEchoes = params.number_of_echoes ?? 8;
  const numEchoes = Number.isFinite(rawNumEchoes) ? Math.max(1, Math.min(50, rawNumEchoes)) : 8;
  const rawIntensity = params.starting_intensity ?? 1.0;
  const startingIntensity = Number.isFinite(rawIntensity) ? Math.max(0, Math.min(1, rawIntensity)) : 1.0;
  const rawDecay = params.decay ?? 0.5;
  const decay = Number.isFinite(rawDecay) ? Math.max(0, Math.min(1, rawDecay)) : 0.5;
  const operator: EchoOperator = params.echo_operator ?? 'add';
  const layerId = params._layerId ?? 'default';

  // Calculate echo time in frames
  const echoTimeFrames = echoTime * fps;

  // Get frame buffer for this layer
  const buffer = getFrameBuffer(layerId);

  // Store current frame in buffer
  buffer.store(frame, input.canvas);

  // If no echoes or intensity is 0, return input unchanged
  if (numEchoes === 0 || startingIntensity === 0) {
    return input;
  }

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);

  // Start with current frame (or empty for composite_back)
  if (operator === 'composite_back') {
    // Echoes go behind, current frame on top
    output.ctx.clearRect(0, 0, width, height);
  } else {
    output.ctx.drawImage(input.canvas, 0, 0);
  }

  // Get echo frames from buffer
  const echoFrames = buffer.getEchoFrames(frame, echoTimeFrames, numEchoes);

  // Calculate intensities for each echo
  const intensities: number[] = [];
  for (let i = 0; i < numEchoes; i++) {
    intensities.push(startingIntensity * Math.pow(1 - decay, i));
  }

  // Composite echoes based on operator
  for (const echoData of echoFrames) {
    const intensity = intensities[echoData.echoIndex - 1] ?? 0;
    if (intensity <= 0.001) continue;

    // Create temp canvas for this echo
    const tempCanvas = document.createElement('canvas');
    tempCanvas.width = width;
    tempCanvas.height = height;
    const tempCtx = tempCanvas.getContext('2d')!;
    tempCtx.putImageData(echoData.imageData, 0, 0);

    // Apply based on operator
    switch (operator) {
      case 'add':
        output.ctx.globalCompositeOperation = 'lighter';
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;

      case 'screen':
        output.ctx.globalCompositeOperation = 'screen';
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;

      case 'maximum':
        output.ctx.globalCompositeOperation = 'lighten';
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;

      case 'minimum':
        output.ctx.globalCompositeOperation = 'darken';
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;

      case 'composite_back':
        // Draw echo behind current content
        output.ctx.globalCompositeOperation = 'destination-over';
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;

      case 'composite_front':
        output.ctx.globalCompositeOperation = 'source-over';
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;

      case 'blend':
      default:
        output.ctx.globalCompositeOperation = 'source-over';
        output.ctx.globalAlpha = intensity;
        output.ctx.drawImage(tempCanvas, 0, 0);
        break;
    }
  }

  // Reset composite operation
  output.ctx.globalCompositeOperation = 'source-over';
  output.ctx.globalAlpha = 1;

  // If composite_back, draw current frame on top
  if (operator === 'composite_back') {
    output.ctx.drawImage(input.canvas, 0, 0);
  }

  return output;
}

// ============================================================================
// POSTERIZE TIME EFFECT
// Reduces temporal resolution (frame rate reduction look)
// ============================================================================

/**
 * Posterize Time effect renderer
 * Holds frames to create a lower frame rate look
 *
 * Parameters:
 * - frame_rate: Target frame rate (1-60)
 */
export function posterizeTimeRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  // Validate numeric params (NaN bypasses Math.max/min clamps)
  const rawTargetFps = params.frame_rate ?? 12;
  const targetFps = Number.isFinite(rawTargetFps) ? Math.max(1, Math.min(60, rawTargetFps)) : 12;
  const frame = params._frame ?? 0;
  // Validate fps to prevent division by NaN
  const fps = (Number.isFinite(params._fps) && params._fps > 0) ? params._fps : 16;
  const layerId = params._layerId ?? 'default';

  // Calculate which "posterized" frame this belongs to
  const frameRatio = fps / targetFps;
  const posterizedFrame = Math.floor(frame / frameRatio) * frameRatio;

  // Get frame buffer
  const buffer = getFrameBuffer(layerId);

  // Store current frame
  buffer.store(frame, input.canvas);

  // If this is a "new" posterized frame, return current
  if (Math.abs(frame - posterizedFrame) < 0.5) {
    return input;
  }

  // Otherwise, return the held frame
  const heldFrame = buffer.getClosest(posterizedFrame);
  if (heldFrame) {
    const { width, height } = input.canvas;
    const output = createMatchingCanvas(input.canvas);
    output.ctx.putImageData(heldFrame.imageData, 0, 0);
    return output;
  }

  return input;
}

// ============================================================================
// TIME DISPLACEMENT EFFECT
// Offsets different parts of the image in time
// ============================================================================

/**
 * Generate procedural time displacement map
 */
function generateTimeDisplacementMap(
  width: number,
  height: number,
  mapType: string,
  scale: number
): Float32Array {
  const map = new Float32Array(width * height);

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = y * width + x;
      let value = 0; // Neutral (no displacement)

      switch (mapType) {
        case 'gradient-h':
          value = x / width; // 0 to 1 left to right
          break;
        case 'gradient-v':
          value = y / height; // 0 to 1 top to bottom
          break;
        case 'radial':
          const cx = width / 2;
          const cy = height / 2;
          const dist = Math.sqrt((x - cx) ** 2 + (y - cy) ** 2);
          const maxDist = Math.sqrt(cx ** 2 + cy ** 2);
          value = dist / maxDist; // 0 at center, 1 at edges
          break;
        case 'sine-h':
          value = 0.5 + 0.5 * Math.sin((x / width) * Math.PI * 2 * scale);
          break;
        case 'sine-v':
          value = 0.5 + 0.5 * Math.sin((y / height) * Math.PI * 2 * scale);
          break;
        case 'diagonal':
          value = ((x / width) + (y / height)) / 2;
          break;
        case 'center-out':
          // Radial but inverted (center is most displaced)
          const cx2 = width / 2;
          const cy2 = height / 2;
          const dist2 = Math.sqrt((x - cx2) ** 2 + (y - cy2) ** 2);
          const maxDist2 = Math.sqrt(cx2 ** 2 + cy2 ** 2);
          value = 1 - (dist2 / maxDist2);
          break;
        default:
          value = 0.5;
      }

      map[i] = value;
    }
  }

  return map;
}

/**
 * Time Displacement effect renderer
 * Uses a displacement map to offset pixels in time, creating interesting
 * temporal distortion effects like ripples through time.
 *
 * Parameters:
 * - max_displacement: Maximum time offset in frames (-50 to 50)
 * - map_type: 'gradient-h' | 'gradient-v' | 'radial' | 'sine-h' | 'sine-v' | 'diagonal' | 'center-out'
 * - map_scale: Scale factor for sine patterns (1-10)
 * - time_offset_bias: Shift the neutral point (-1 to 1, 0 = centered)
 * - _frame: Current frame (passed by effect processor)
 * - _layerId: Layer ID (passed by effect processor)
 */
export function timeDisplacementRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  // Validate numeric params (NaN bypasses === 0 check)
  const rawMaxDisplacement = params.max_displacement ?? 10;
  const maxDisplacement = Number.isFinite(rawMaxDisplacement) ? rawMaxDisplacement : 10;
  const mapType = params.map_type ?? 'gradient-h';
  const rawMapScale = params.map_scale ?? 1;
  const mapScale = Number.isFinite(rawMapScale) ? rawMapScale : 1;
  const rawBias = params.time_offset_bias ?? 0;
  const bias = Number.isFinite(rawBias) ? rawBias : 0;
  const frame = params._frame ?? 0;
  const layerId = params._layerId ?? 'default';

  // No effect if max displacement is 0
  if (maxDisplacement === 0) {
    return input;
  }

  const { width, height } = input.canvas;
  const buffer = getFrameBuffer(layerId);

  // Store current frame in buffer
  buffer.store(frame, input.canvas);

  // Get input pixel data
  const inputData = input.ctx.getImageData(0, 0, width, height);

  // Generate displacement map
  const dispMap = generateTimeDisplacementMap(width, height, mapType, mapScale);

  // Create output
  const output = createMatchingCanvas(input.canvas);
  const outputData = output.ctx.createImageData(width, height);
  const dst = outputData.data;

  // Process each pixel
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = y * width + x;
      const pixelIdx = i * 4;

      // Get displacement value (0-1) and convert to frame offset
      const dispValue = dispMap[i];
      // Apply bias: shift the 0.5 neutral point
      const biasedValue = dispValue + bias;
      // Convert to frame offset: -maxDisplacement to +maxDisplacement
      const frameOffset = Math.round((biasedValue - 0.5) * 2 * maxDisplacement);
      const targetFrame = frame + frameOffset;

      // Get pixel from target frame
      const frameData = buffer.get(targetFrame);
      if (frameData) {
        dst[pixelIdx] = frameData.data[pixelIdx];
        dst[pixelIdx + 1] = frameData.data[pixelIdx + 1];
        dst[pixelIdx + 2] = frameData.data[pixelIdx + 2];
        dst[pixelIdx + 3] = frameData.data[pixelIdx + 3];
      } else {
        // Fallback to current frame if target not available
        dst[pixelIdx] = inputData.data[pixelIdx];
        dst[pixelIdx + 1] = inputData.data[pixelIdx + 1];
        dst[pixelIdx + 2] = inputData.data[pixelIdx + 2];
        dst[pixelIdx + 3] = inputData.data[pixelIdx + 3];
      }
    }
  }

  output.ctx.putImageData(outputData, 0, 0);
  return output;
}

// ============================================================================
// FREEZE FRAME EFFECT
// Freezes the layer at a specific source frame
// ============================================================================

// Store frozen frames by layer ID
const frozenFrames = new Map<string, { frame: number; imageData: ImageData }>();

/**
 * Freeze Frame effect renderer
 * Holds the layer at a specific source frame number.
 *
 * Parameters:
 * - freeze_at_frame: The source frame to freeze at (0+)
 *
 * Unlike the SpeedMap-based freeze (in layerActions.freezeFrameAtPlayhead),
 * this effect version works by capturing and holding a specific frame.
 */
export function freezeFrameRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const freezeAtFrame = Math.max(0, Math.round(params.freeze_at_frame ?? 0));
  const frame = params._frame ?? 0;
  const layerId = params._layerId ?? 'default';
  const cacheKey = `${layerId}_freeze`;

  // Get frame buffer for storing/retrieving frames
  const buffer = getFrameBuffer(layerId);

  // Store current frame in buffer
  buffer.store(frame, input.canvas);

  // Check if we have a cached frozen frame at the target
  const cached = frozenFrames.get(cacheKey);
  if (cached && cached.frame === freezeAtFrame) {
    // We already have the frozen frame cached - return it
    const { width, height } = input.canvas;
    const output = createMatchingCanvas(input.canvas);
    output.ctx.putImageData(cached.imageData, 0, 0);
    return output;
  }

  // If current frame matches freeze target, cache it and return
  if (frame === freezeAtFrame) {
    const { width, height } = input.canvas;
    const imageData = input.ctx.getImageData(0, 0, width, height);
    frozenFrames.set(cacheKey, { frame: freezeAtFrame, imageData });
    return input;
  }

  // Try to get the frozen frame from buffer
  const frozenImageData = buffer.get(freezeAtFrame);
  if (frozenImageData) {
    // Cache it for future use
    frozenFrames.set(cacheKey, { frame: freezeAtFrame, imageData: frozenImageData });

    const { width, height } = input.canvas;
    const output = createMatchingCanvas(input.canvas);
    output.ctx.putImageData(frozenImageData, 0, 0);
    return output;
  }

  // Frozen frame not available yet - return current frame
  // This happens when scrubbing directly to a frame without having
  // rendered the freeze target frame first
  return input;
}

/**
 * Clear a frozen frame cache for a layer
 */
export function clearFrozenFrame(layerId: string): void {
  frozenFrames.delete(`${layerId}_freeze`);
}

/**
 * Clear all frozen frame caches
 */
export function clearAllFrozenFrames(): void {
  frozenFrames.clear();
}

/**
 * BUG-065 fix: Clear all time effect temporal state on timeline seek
 *
 * This function MUST be called when the timeline seeks to ensure deterministic
 * playback. Time effects (Echo, Posterize Time, Time Displacement, Freeze Frame)
 * depend on accumulated frame history that becomes invalid after seeking.
 *
 * Call this from:
 * - Timeline scrubbing handler
 * - Playhead jump operations
 * - Project load/reset
 */
export function clearTimeEffectStateOnSeek(): void {
  clearAllFrameBuffers();
  clearAllFrozenFrames();
}

// ============================================================================
// TIMEWARP FRAME BLENDING
// Frame interpolation methods for Timewarp layer property
// These are called by the layer renderer when Timewarp is enabled
// ============================================================================

/**
 * Timewarp interpolation methods
 */
export type TimewarpMethod = 'whole-frames' | 'frame-mix' | 'pixel-motion';

/**
 * Apply Timewarp frame blending between two source frames
 * Called by layer renderer when timewarpEnabled is true
 *
 * @param frame1Data - ImageData of floor frame
 * @param frame2Data - ImageData of ceiling frame
 * @param blendFactor - 0-1 blend between frames
 * @param method - Interpolation method
 * @param motionBlur - Motion blur amount for pixel-motion (0-1)
 * @returns Blended ImageData
 */
export function applyTimewarpBlending(
  frame1Data: ImageData,
  frame2Data: ImageData,
  blendFactor: number,
  method: TimewarpMethod,
  motionBlur: number = 0.5
): ImageData {
  const width = frame1Data.width;
  const height = frame1Data.height;

  // No blending needed at exact frame boundaries
  if (blendFactor === 0) {
    return frame1Data;
  }
  if (blendFactor === 1) {
    return frame2Data;
  }

  switch (method) {
    case 'whole-frames': {
      // Nearest frame - no interpolation
      return blendFactor < 0.5 ? frame1Data : frame2Data;
    }

    case 'frame-mix': {
      // Simple cross-fade between frames
      const output = new ImageData(width, height);
      const dst = output.data;
      const src1 = frame1Data.data;
      const src2 = frame2Data.data;

      for (let i = 0; i < dst.length; i += 4) {
        dst[i] = src1[i] * (1 - blendFactor) + src2[i] * blendFactor;
        dst[i + 1] = src1[i + 1] * (1 - blendFactor) + src2[i + 1] * blendFactor;
        dst[i + 2] = src1[i + 2] * (1 - blendFactor) + src2[i + 2] * blendFactor;
        dst[i + 3] = src1[i + 3] * (1 - blendFactor) + src2[i + 3] * blendFactor;
      }

      return output;
    }

    case 'pixel-motion': {
      // Optical flow-based interpolation
      const output = new ImageData(width, height);
      computePixelMotionInterpolation(
        frame1Data,
        frame2Data,
        output,
        blendFactor,
        motionBlur,
        width,
        height
      );
      return output;
    }

    default:
      return frame1Data;
  }
}

/**
 * Block-based motion estimation for optical flow
 * Uses a simplified Lucas-Kanade style approach
 */
function computePixelMotionInterpolation(
  frame1: ImageData,
  frame2: ImageData,
  output: ImageData,
  blend: number,
  motionBlurAmount: number,
  width: number,
  height: number
): void {
  const blockSize = 8; // Motion estimation block size
  const searchRadius = 8; // Search radius for motion vectors

  // Compute motion vectors using block matching
  const motionVectors = computeBlockMotionVectors(
    frame1,
    frame2,
    width,
    height,
    blockSize,
    searchRadius
  );

  const dst = output.data;
  const src1 = frame1.data;
  const src2 = frame2.data;

  // Interpolate each pixel using motion vectors
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const pixelIdx = (y * width + x) * 4;

      // Get motion vector for this pixel (from block grid)
      const blockX = Math.floor(x / blockSize);
      const blockY = Math.floor(y / blockSize);
      const blocksPerRow = Math.ceil(width / blockSize);
      const blockIdx = blockY * blocksPerRow + blockX;
      const mv = motionVectors[blockIdx] || { x: 0, y: 0 };

      // Calculate source positions using motion vector
      // For forward interpolation
      const srcX1 = x + mv.x * (1 - blend);
      const srcY1 = y + mv.y * (1 - blend);
      // For backward interpolation
      const srcX2 = x - mv.x * blend;
      const srcY2 = y - mv.y * blend;

      // Sample from both frames with motion compensation
      const sample1 = samplePixelBilinear(src1, srcX1, srcY1, width, height);
      const sample2 = samplePixelBilinear(src2, srcX2, srcY2, width, height);

      // Blend samples with motion blur consideration
      const blurFactor = Math.min(1, motionBlurAmount * Math.sqrt(mv.x * mv.x + mv.y * mv.y) / 10);
      const adjustedBlend = blend * (1 - blurFactor * 0.5);

      dst[pixelIdx] = sample1.r * (1 - adjustedBlend) + sample2.r * adjustedBlend;
      dst[pixelIdx + 1] = sample1.g * (1 - adjustedBlend) + sample2.g * adjustedBlend;
      dst[pixelIdx + 2] = sample1.b * (1 - adjustedBlend) + sample2.b * adjustedBlend;
      dst[pixelIdx + 3] = sample1.a * (1 - adjustedBlend) + sample2.a * adjustedBlend;
    }
  }
}

/**
 * Compute block-based motion vectors using Sum of Absolute Differences (SAD)
 */
function computeBlockMotionVectors(
  frame1: ImageData,
  frame2: ImageData,
  width: number,
  height: number,
  blockSize: number,
  searchRadius: number
): Array<{ x: number; y: number }> {
  const blocksPerRow = Math.ceil(width / blockSize);
  const blocksPerCol = Math.ceil(height / blockSize);
  const motionVectors: Array<{ x: number; y: number }> = [];

  const src1 = frame1.data;
  const src2 = frame2.data;

  for (let by = 0; by < blocksPerCol; by++) {
    for (let bx = 0; bx < blocksPerRow; bx++) {
      const blockStartX = bx * blockSize;
      const blockStartY = by * blockSize;

      let bestDx = 0;
      let bestDy = 0;
      let bestSAD = Infinity;

      // Search within radius for best match
      for (let dy = -searchRadius; dy <= searchRadius; dy++) {
        for (let dx = -searchRadius; dx <= searchRadius; dx++) {
          let sad = 0;
          let validPixels = 0;

          // Compute SAD for this offset
          for (let py = 0; py < blockSize; py++) {
            for (let px = 0; px < blockSize; px++) {
              const x1 = blockStartX + px;
              const y1 = blockStartY + py;
              const x2 = x1 + dx;
              const y2 = y1 + dy;

              // Skip if out of bounds
              if (x1 < 0 || x1 >= width || y1 < 0 || y1 >= height) continue;
              if (x2 < 0 || x2 >= width || y2 < 0 || y2 >= height) continue;

              const idx1 = (y1 * width + x1) * 4;
              const idx2 = (y2 * width + x2) * 4;

              // Luminance-based SAD for efficiency
              const lum1 = src1[idx1] * 0.299 + src1[idx1 + 1] * 0.587 + src1[idx1 + 2] * 0.114;
              const lum2 = src2[idx2] * 0.299 + src2[idx2 + 1] * 0.587 + src2[idx2 + 2] * 0.114;

              sad += Math.abs(lum1 - lum2);
              validPixels++;
            }
          }

          // Normalize SAD
          if (validPixels > 0) {
            sad /= validPixels;
          }

          if (sad < bestSAD) {
            bestSAD = sad;
            bestDx = dx;
            bestDy = dy;
          }
        }
      }

      motionVectors.push({ x: bestDx, y: bestDy });
    }
  }

  return motionVectors;
}

/**
 * Bilinear sampling from image data
 */
function samplePixelBilinear(
  data: Uint8ClampedArray,
  x: number,
  y: number,
  width: number,
  height: number
): { r: number; g: number; b: number; a: number } {
  // Clamp coordinates
  const x0 = Math.max(0, Math.min(width - 1, Math.floor(x)));
  const y0 = Math.max(0, Math.min(height - 1, Math.floor(y)));
  const x1 = Math.min(width - 1, x0 + 1);
  const y1 = Math.min(height - 1, y0 + 1);

  const fx = x - x0;
  const fy = y - y0;

  const idx00 = (y0 * width + x0) * 4;
  const idx10 = (y0 * width + x1) * 4;
  const idx01 = (y1 * width + x0) * 4;
  const idx11 = (y1 * width + x1) * 4;

  const r = bilinearInterpolate(data[idx00], data[idx10], data[idx01], data[idx11], fx, fy);
  const g = bilinearInterpolate(data[idx00 + 1], data[idx10 + 1], data[idx01 + 1], data[idx11 + 1], fx, fy);
  const b = bilinearInterpolate(data[idx00 + 2], data[idx10 + 2], data[idx01 + 2], data[idx11 + 2], fx, fy);
  const a = bilinearInterpolate(data[idx00 + 3], data[idx10 + 3], data[idx01 + 3], data[idx11 + 3], fx, fy);

  return { r, g, b, a };
}

/**
 * Bilinear interpolation helper
 */
function bilinearInterpolate(v00: number, v10: number, v01: number, v11: number, fx: number, fy: number): number {
  const v0 = v00 * (1 - fx) + v10 * fx;
  const v1 = v01 * (1 - fx) + v11 * fx;
  return v0 * (1 - fy) + v1 * fy;
}

// ============================================================================
// PIXEL MOTION (OPTICAL FLOW) STANDALONE
// For frame blending in video layers
// ============================================================================

/**
 * Apply optical flow-based frame interpolation for video frame blending
 * This is used by the video layer's 'pixel-motion' frame blending mode
 *
 * @param frame1 - First frame (floor frame)
 * @param frame2 - Second frame (ceiling frame)
 * @param blend - Blend factor (0-1)
 * @returns Interpolated frame as ImageData
 */
export function pixelMotionBlend(
  frame1: ImageData,
  frame2: ImageData,
  blend: number
): ImageData {
  const width = frame1.width;
  const height = frame1.height;
  const output = new ImageData(width, height);

  computePixelMotionInterpolation(
    frame1,
    frame2,
    output,
    blend,
    0.5, // Default motion blur
    width,
    height
  );

  return output;
}

// ============================================================================
// REGISTRATION
// ============================================================================

/**
 * Register all time effect renderers
 * Note: Timewarp is NOT an effect - it's a layer property that modifies timing
 */
export function registerTimeEffects(): void {
  registerEffectRenderer('echo', echoRenderer);
  registerEffectRenderer('posterize-time', posterizeTimeRenderer);
  registerEffectRenderer('freeze-frame', freezeFrameRenderer);
  registerEffectRenderer('time-displacement', timeDisplacementRenderer);
}

export default {
  echoRenderer,
  posterizeTimeRenderer,
  freezeFrameRenderer,
  timeDisplacementRenderer,
  applyTimewarpBlending,
  pixelMotionBlend,
  registerTimeEffects,
  clearAllFrameBuffers,
  clearAllFrozenFrames,
  clearFrozenFrame,
  clearTimeEffectStateOnSeek,  // BUG-065 fix: Unified clear for timeline seek
  getFrameBuffer
};
