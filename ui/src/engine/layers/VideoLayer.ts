/**
 * VideoLayer - Video Playback with Time Remapping
 *
 * Full-featured video layer supporting:
 * - Video texture playback synced to composition timeline
 * - Loop, ping-pong, and speed control
 * - Time remapping (animatable)
 * - Frame blending for speed changes
 * - Audio level control
 * - Automatic composition resize on import
 */

import * as THREE from 'three';
import type { Layer, VideoData, AnimatableProperty, AssetReference } from '@/types/project';
import type { ResourceManager } from '../core/ResourceManager';
import { BaseLayer } from './BaseLayer';
import { KeyframeEvaluator } from '../animation/KeyframeEvaluator';
import { layerLogger } from '@/utils/logger';

// ============================================================================
// TYPES
// ============================================================================

export interface VideoMetadata {
  duration: number;      // Total duration in seconds
  frameCount: number;    // Total frame count
  fps: number;           // Source FPS
  width: number;
  height: number;
  hasAudio: boolean;
}

export interface VideoLayerEvents {
  'metadata-loaded': VideoMetadata;
  'playback-ended': void;
  'loop-point': number;  // Frame at which loop occurred
}

// ============================================================================
// VIDEO LAYER
// ============================================================================

export class VideoLayer extends BaseLayer {
  private readonly resources: ResourceManager;

  // Video elements
  private videoElement: HTMLVideoElement | null = null;
  private videoTexture: THREE.VideoTexture | null = null;
  private mesh: THREE.Mesh | null = null;
  private material: THREE.MeshBasicMaterial | null = null;

  // Video data
  private videoData: VideoData;
  private assetRef: AssetReference | null = null;

  // Metadata (populated after video loads)
  private metadata: VideoMetadata | null = null;

  // Animation evaluator
  private readonly videoEvaluator: KeyframeEvaluator;

  // Playback state
  private lastEvaluatedFrame: number = -1;
  private isPlaying: boolean = false;

  // Callbacks for composition auto-resize
  private onMetadataLoaded?: (metadata: VideoMetadata) => void;

  // Composition FPS for time calculation
  private compositionFPS: number = 30;

  // Canvas for effect processing
  private effectCanvas: HTMLCanvasElement | null = null;
  private effectCanvasCtx: CanvasRenderingContext2D | null = null;

  // Frame blending support
  private prevFrameCanvas: HTMLCanvasElement | null = null;
  private prevFrameCtx: CanvasRenderingContext2D | null = null;
  private blendCanvas: HTMLCanvasElement | null = null;
  private blendCtx: CanvasRenderingContext2D | null = null;
  private lastVideoTime: number = -1;
  private prevFrameTime: number = -1;

  constructor(layerData: Layer, resources: ResourceManager) {
    super(layerData);

    this.resources = resources;
    this.videoEvaluator = new KeyframeEvaluator();

    // Extract video data
    this.videoData = this.extractVideoData(layerData);

    // Create placeholder mesh (will be sized when video loads)
    this.createPlaceholderMesh();

    // Load video if asset is set
    if (this.videoData.assetId) {
      this.loadVideo(this.videoData.assetId);
    }

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  // ============================================================================
  // INITIALIZATION
  // ============================================================================

  /**
   * Extract video data with defaults
   */
  private extractVideoData(layerData: Layer): VideoData {
    const data = layerData.data as VideoData | null;

    return {
      assetId: data?.assetId ?? null,
      loop: data?.loop ?? false,
      pingPong: data?.pingPong ?? false,
      startTime: data?.startTime ?? 0,
      endTime: data?.endTime,
      speed: data?.speed ?? 1,
      // Speed map (new naming)
      speedMapEnabled: data?.speedMapEnabled ?? data?.timeRemapEnabled ?? false,
      speedMap: data?.speedMap ?? data?.timeRemap,
      // Backwards compatibility aliases
      timeRemapEnabled: data?.timeRemapEnabled ?? data?.speedMapEnabled ?? false,
      timeRemap: data?.timeRemap ?? data?.speedMap,
      frameBlending: data?.frameBlending ?? 'none',
      audioEnabled: data?.audioEnabled ?? true,
      audioLevel: data?.audioLevel ?? 100,
      posterFrame: data?.posterFrame ?? 0,
    };
  }

  /**
   * Create placeholder mesh before video loads
   */
  private createPlaceholderMesh(): void {
    // Default size (will be updated when video loads)
    const geometry = new THREE.PlaneGeometry(1, 1);
    this.material = new THREE.MeshBasicMaterial({
      color: 0x333333,
      transparent: true,
      side: THREE.DoubleSide,
    });

    this.mesh = new THREE.Mesh(geometry, this.material);
    this.mesh.name = `video_${this.id}`;
    this.group.add(this.mesh);
  }

  // ============================================================================
  // VIDEO LOADING
  // ============================================================================

  /**
   * Load video from asset
   */
  async loadVideo(assetId: string): Promise<void> {
    // Get asset reference from ResourceManager
    const asset = this.resources.getAsset(assetId);

    if (!asset || asset.type !== 'video') {
      layerLogger.warn(`VideoLayer: Asset ${assetId} not found or not a video`);
      return;
    }

    this.assetRef = asset;
    this.videoData.assetId = assetId;

    // Create video element
    this.videoElement = document.createElement('video');
    this.videoElement.crossOrigin = 'anonymous';
    this.videoElement.playsInline = true;
    this.videoElement.muted = !this.videoData.audioEnabled;
    this.videoElement.loop = false;  // We handle looping manually for precise control
    this.videoElement.preload = 'auto';

    // Set source
    if (asset.data) {
      // Base64 or blob URL
      this.videoElement.src = asset.data;
    }

    // Wait for metadata
    await this.waitForMetadata();

    // Create texture from video
    this.createVideoTexture();

    // Set initial time
    this.seekToFrame(this.videoData.posterFrame);
  }

  /**
   * Wait for video metadata to load
   */
  private waitForMetadata(): Promise<void> {
    return new Promise((resolve, reject) => {
      if (!this.videoElement) {
        reject(new Error('No video element'));
        return;
      }

      const onLoadedMetadata = () => {
        this.extractMetadata();
        cleanup();
        resolve();
      };

      const onError = (e: Event) => {
        cleanup();
        reject(new Error(`Video load error: ${e}`));
      };

      const cleanup = () => {
        this.videoElement?.removeEventListener('loadedmetadata', onLoadedMetadata);
        this.videoElement?.removeEventListener('error', onError);
      };

      this.videoElement.addEventListener('loadedmetadata', onLoadedMetadata);
      this.videoElement.addEventListener('error', onError);

      // Trigger load
      this.videoElement.load();
    });
  }

  /**
   * Extract metadata from loaded video
   */
  private extractMetadata(): void {
    if (!this.videoElement) return;

    const duration = this.videoElement.duration;
    const width = this.videoElement.videoWidth;
    const height = this.videoElement.videoHeight;

    // Estimate FPS (browser doesn't expose this directly)
    // Default to common values, or use asset metadata if available
    const fps = this.assetRef?.fps ?? 30;
    const frameCount = Math.ceil(duration * fps);

    this.metadata = {
      duration,
      frameCount,
      fps,
      width,
      height,
      hasAudio: this.hasAudioTrack(),
    };

    // Update asset reference with metadata
    if (this.assetRef) {
      this.assetRef.duration = duration;
      this.assetRef.frameCount = frameCount;
      this.assetRef.fps = fps;
      this.assetRef.hasAudio = this.metadata.hasAudio;
    }

    // Notify listeners (for composition auto-resize)
    this.onMetadataLoaded?.(this.metadata);

    layerLogger.debug(`VideoLayer: Loaded: ${width}x${height}, ${frameCount} frames @ ${fps}fps, ${duration.toFixed(2)}s`);
  }

  /**
   * Check if video has audio track
   */
  private hasAudioTrack(): boolean {
    if (!this.videoElement) return false;

    // Check for audio tracks (if available)
    const audioTracks = (this.videoElement as any).audioTracks;
    if (audioTracks) {
      return audioTracks.length > 0;
    }

    // Fallback: assume audio exists unless we can prove otherwise
    return true;
  }

  /**
   * Create Three.js texture from video element
   */
  private createVideoTexture(): void {
    if (!this.videoElement || !this.metadata) return;

    // Create texture
    this.videoTexture = new THREE.VideoTexture(this.videoElement);
    this.videoTexture.minFilter = THREE.LinearFilter;
    this.videoTexture.magFilter = THREE.LinearFilter;
    this.videoTexture.format = THREE.RGBAFormat;
    this.videoTexture.colorSpace = THREE.SRGBColorSpace;

    // Update material
    if (this.material) {
      this.material.map = this.videoTexture;
      this.material.color.setHex(0xffffff);
      this.material.needsUpdate = true;
    }

    // Resize mesh to match video aspect ratio
    this.resizeMesh(this.metadata.width, this.metadata.height);
  }

  /**
   * Resize mesh to match video dimensions
   */
  private resizeMesh(width: number, height: number): void {
    if (!this.mesh) return;

    // Dispose old geometry
    this.mesh.geometry.dispose();

    // Create new geometry with video dimensions
    this.mesh.geometry = new THREE.PlaneGeometry(width, height);
  }

  // ============================================================================
  // PLAYBACK CONTROL
  // ============================================================================

  /**
   * Seek to a specific composition frame
   */
  seekToFrame(compositionFrame: number): void {
    if (!this.videoElement || !this.metadata) return;

    // Calculate video time from composition frame
    const videoTime = this.calculateVideoTime(compositionFrame);

    // Clamp to valid range
    const clampedTime = Math.max(0, Math.min(videoTime, this.videoElement.duration));

    // Seek
    this.videoElement.currentTime = clampedTime;
  }

  /**
   * Calculate video time from composition frame
   * Handles speed, speed map (time remapping), loop, and ping-pong
   */
  private calculateVideoTime(compositionFrame: number): number {
    if (!this.metadata) return 0;

    // If speed map is enabled and animated, use that
    const speedMapEnabled = this.videoData.speedMapEnabled ?? this.videoData.timeRemapEnabled;
    const speedMapProp = this.videoData.speedMap ?? this.videoData.timeRemap;
    if (speedMapEnabled && speedMapProp?.animated) {
      return this.videoEvaluator.evaluate(speedMapProp, compositionFrame);
    }

    // Calculate based on speed and offsets
    const compFps = this.compositionFPS;
    const compTime = compositionFrame / compFps;

    // Apply speed
    let videoTime = compTime * this.videoData.speed;

    // Add start offset
    videoTime += this.videoData.startTime;

    // Get effective duration (with end time if set)
    const effectiveDuration = this.videoData.endTime
      ? this.videoData.endTime - this.videoData.startTime
      : this.metadata.duration - this.videoData.startTime;

    // Handle looping
    if (this.videoData.loop && effectiveDuration > 0) {
      if (this.videoData.pingPong) {
        // Ping-pong: 0 -> duration -> 0 -> duration...
        const cycles = Math.floor(videoTime / effectiveDuration);
        const phase = videoTime % effectiveDuration;
        videoTime = cycles % 2 === 0 ? phase : effectiveDuration - phase;
      } else {
        // Standard loop
        videoTime = videoTime % effectiveDuration;
      }
      videoTime += this.videoData.startTime;
    }

    return videoTime;
  }

  /**
   * Set audio volume
   */
  setAudioLevel(level: number): void {
    this.videoData.audioLevel = level;
    if (this.videoElement) {
      this.videoElement.volume = Math.max(0, Math.min(1, level / 100));
    }
  }

  /**
   * Enable/disable audio
   */
  setAudioEnabled(enabled: boolean): void {
    this.videoData.audioEnabled = enabled;
    if (this.videoElement) {
      this.videoElement.muted = !enabled;
    }
  }

  // ============================================================================
  // METADATA CALLBACK
  // ============================================================================

  /**
   * Set composition FPS for accurate time calculation
   */
  setFPS(fps: number): void {
    this.compositionFPS = fps;
  }

  /**
   * Register callback for when video metadata is loaded
   * Used by LayerManager to auto-resize composition
   */
  setMetadataCallback(callback: (metadata: VideoMetadata) => void): void {
    this.onMetadataLoaded = callback;

    // If metadata already loaded, call immediately
    if (this.metadata) {
      callback(this.metadata);
    }
  }

  /**
   * Get video metadata
   */
  getMetadata(): VideoMetadata | null {
    return this.metadata;
  }

  /**
   * Get video data
   */
  getVideoData(): VideoData {
    return { ...this.videoData };
  }

  // ============================================================================
  // PROPERTY UPDATES
  // ============================================================================

  setLoop(loop: boolean): void {
    this.videoData.loop = loop;
  }

  setPingPong(pingPong: boolean): void {
    this.videoData.pingPong = pingPong;
  }

  setSpeed(speed: number): void {
    this.videoData.speed = speed;
    if (this.videoElement) {
      this.videoElement.playbackRate = speed;
    }
  }

  setStartTime(time: number): void {
    this.videoData.startTime = time;
  }

  setEndTime(time: number | undefined): void {
    this.videoData.endTime = time;
  }

  setFrameBlending(mode: 'none' | 'frame-mix' | 'pixel-motion'): void {
    this.videoData.frameBlending = mode;
    // Frame blending would be implemented via shader in a full implementation
  }

  // ============================================================================
  // EFFECTS SUPPORT
  // ============================================================================

  /**
   * Get source canvas for effect processing
   * Renders the current video frame to a 2D canvas
   * Supports frame blending for smooth slow-motion
   */
  protected override getSourceCanvas(): HTMLCanvasElement | null {
    if (!this.videoElement || !this.metadata) {
      return null;
    }

    const width = this.metadata.width;
    const height = this.metadata.height;

    // Lazy create/resize canvases
    this.ensureCanvases(width, height);

    if (!this.effectCanvasCtx) {
      return null;
    }

    // Check if frame blending should be applied
    // Layer switch (frameBlending) enables blending, videoData.frameBlending specifies mode
    const shouldBlend = this.layerData.frameBlending === true &&
                        this.videoData.frameBlending !== 'none';

    if (shouldBlend && this.prevFrameCtx && this.blendCtx && this.blendCanvas) {
      return this.getBlendedFrame(width, height);
    }

    // No blending - just draw current video frame
    this.effectCanvasCtx.clearRect(0, 0, width, height);
    this.effectCanvasCtx.drawImage(this.videoElement, 0, 0, width, height);

    return this.effectCanvas;
  }

  /**
   * Ensure all canvases are created and sized correctly
   */
  private ensureCanvases(width: number, height: number): void {
    // Main effect canvas
    if (!this.effectCanvas ||
        this.effectCanvas.width !== width ||
        this.effectCanvas.height !== height) {
      this.effectCanvas = document.createElement('canvas');
      this.effectCanvas.width = width;
      this.effectCanvas.height = height;
      this.effectCanvasCtx = this.effectCanvas.getContext('2d');
    }

    // Previous frame canvas (for blending)
    if (!this.prevFrameCanvas ||
        this.prevFrameCanvas.width !== width ||
        this.prevFrameCanvas.height !== height) {
      this.prevFrameCanvas = document.createElement('canvas');
      this.prevFrameCanvas.width = width;
      this.prevFrameCanvas.height = height;
      this.prevFrameCtx = this.prevFrameCanvas.getContext('2d');
    }

    // Blend output canvas
    if (!this.blendCanvas ||
        this.blendCanvas.width !== width ||
        this.blendCanvas.height !== height) {
      this.blendCanvas = document.createElement('canvas');
      this.blendCanvas.width = width;
      this.blendCanvas.height = height;
      this.blendCtx = this.blendCanvas.getContext('2d');
    }
  }

  /**
   * Get blended frame between previous and current video frame
   * Used for smooth slow-motion playback
   */
  private getBlendedFrame(width: number, height: number): HTMLCanvasElement | null {
    if (!this.videoElement || !this.metadata || !this.blendCtx || !this.blendCanvas ||
        !this.prevFrameCtx || !this.prevFrameCanvas) {
      return null;
    }

    const currentVideoTime = this.videoElement.currentTime;
    const videoFps = this.metadata.fps || 30;
    const frameDuration = 1 / videoFps;

    // Calculate the fractional position between video frames
    const currentVideoFrame = currentVideoTime * videoFps;
    const blendFactor = currentVideoFrame - Math.floor(currentVideoFrame);

    // Check if we need to capture a new previous frame
    // We capture when we've moved to a new integer video frame
    const currentIntFrame = Math.floor(currentVideoFrame);
    const prevIntFrame = Math.floor(this.lastVideoTime * videoFps);

    if (this.lastVideoTime < 0 || currentIntFrame !== prevIntFrame) {
      // Save current frame as previous before seeking
      if (this.effectCanvasCtx && this.effectCanvas) {
        // Draw current video to effect canvas first
        this.effectCanvasCtx.clearRect(0, 0, width, height);
        this.effectCanvasCtx.drawImage(this.videoElement, 0, 0, width, height);

        // Copy to previous frame canvas
        this.prevFrameCtx.clearRect(0, 0, width, height);
        this.prevFrameCtx.drawImage(this.effectCanvas, 0, 0);

        this.prevFrameTime = this.lastVideoTime;
      }
    }

    this.lastVideoTime = currentVideoTime;

    // Draw current frame
    this.effectCanvasCtx!.clearRect(0, 0, width, height);
    this.effectCanvasCtx!.drawImage(this.videoElement, 0, 0, width, height);

    // If blend factor is very close to 0 or 1, skip blending
    if (blendFactor < 0.01 || blendFactor > 0.99) {
      return this.effectCanvas;
    }

    // Blend: composite previous frame with current frame
    this.blendCtx.clearRect(0, 0, width, height);

    // Draw previous frame (base)
    this.blendCtx.globalAlpha = 1;
    this.blendCtx.drawImage(this.prevFrameCanvas, 0, 0);

    // Draw current frame with blend factor opacity
    this.blendCtx.globalAlpha = blendFactor;
    this.blendCtx.drawImage(this.effectCanvas!, 0, 0);

    // Reset alpha
    this.blendCtx.globalAlpha = 1;

    return this.blendCanvas;
  }

  /**
   * Apply processed effects canvas back to the material
   */
  protected override applyProcessedEffects(processedCanvas: HTMLCanvasElement): void {
    if (!this.material || !this.metadata) return;

    // Create a new texture from the processed canvas
    const processedTexture = this.resources.createTextureFromCanvas(
      processedCanvas,
      `layer_${this.id}_effects`,
      {
        minFilter: THREE.LinearFilter,
        magFilter: THREE.LinearFilter,
        generateMipmaps: false,
        colorSpace: THREE.SRGBColorSpace,
      }
    );

    // Apply to material
    this.material.map = processedTexture;
    this.material.needsUpdate = true;
  }

  // ============================================================================
  // FRAME EVALUATION
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Skip if frame hasn't changed
    if (frame === this.lastEvaluatedFrame) return;
    this.lastEvaluatedFrame = frame;

    // Seek video to correct time
    this.seekToFrame(frame);

    // Update texture
    if (this.videoTexture) {
      this.videoTexture.needsUpdate = true;
    }

    // Process effects if any are enabled
    if (this.hasEnabledEffects()) {
      this.evaluateEffects(frame);
    } else if (this.material && this.videoTexture) {
      // Restore original video texture when effects are disabled
      this.material.map = this.videoTexture;
      this.material.needsUpdate = true;
    }
  }

  protected override onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    const props = state.properties;

    // Apply speed map if evaluated (direct video time in seconds)
    // Check both new 'speedMap' and legacy 'timeRemap' for backwards compatibility
    const speedMapValue = props['speedMap'] ?? props['timeRemap'];
    if (speedMapValue !== undefined && this.videoElement) {
      const targetTime = speedMapValue as number;
      const clampedTime = Math.max(0, Math.min(targetTime, this.videoElement.duration || targetTime));
      this.videoElement.currentTime = clampedTime;
    }

    // Apply speed if evaluated
    if (props['speed'] !== undefined) {
      this.videoData.speed = props['speed'] as number;
    }

    // Apply audio level if evaluated
    if (props['audioLevel'] !== undefined) {
      this.setAudioLevel(props['audioLevel'] as number);
    }

    // Apply effects
    if (state.effects.length > 0) {
      this.applyEvaluatedEffects(state.effects);
    }
  }

  // ============================================================================
  // LAYER UPDATE
  // ============================================================================

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<VideoData> | undefined;

    if (data) {
      if (data.assetId !== undefined && data.assetId !== this.videoData.assetId) {
        if (data.assetId) {
          this.loadVideo(data.assetId);
        } else {
          this.clearVideo();
        }
      }

      if (data.loop !== undefined) this.setLoop(data.loop);
      if (data.pingPong !== undefined) this.setPingPong(data.pingPong);
      if (data.speed !== undefined) this.setSpeed(data.speed);
      if (data.startTime !== undefined) this.setStartTime(data.startTime);
      if (data.endTime !== undefined) this.setEndTime(data.endTime);
      if (data.frameBlending !== undefined) this.setFrameBlending(data.frameBlending);
      if (data.audioEnabled !== undefined) this.setAudioEnabled(data.audioEnabled);
      if (data.audioLevel !== undefined) this.setAudioLevel(data.audioLevel);
    }
  }

  /**
   * Clear current video
   */
  private clearVideo(): void {
    if (this.videoElement) {
      this.videoElement.pause();
      this.videoElement.src = '';
      this.videoElement = null;
    }

    if (this.videoTexture) {
      this.videoTexture.dispose();
      this.videoTexture = null;
    }

    if (this.material) {
      this.material.map = null;
      this.material.color.setHex(0x333333);
    }

    this.metadata = null;
    this.videoData.assetId = null;

    // Clear frame blending state
    this.lastVideoTime = -1;
    this.prevFrameTime = -1;
  }

  // ============================================================================
  // DISPOSAL
  // ============================================================================

  protected onDispose(): void {
    this.clearVideo();

    // Clean up frame blending canvases
    this.prevFrameCanvas = null;
    this.prevFrameCtx = null;
    this.blendCanvas = null;
    this.blendCtx = null;
    this.effectCanvas = null;
    this.effectCanvasCtx = null;

    if (this.material) {
      this.material.dispose();
    }

    if (this.mesh) {
      this.mesh.geometry.dispose();
      this.group.remove(this.mesh);
    }
  }
}

// ============================================================================
// VIDEO METADATA EXTRACTION UTILITY
// ============================================================================

/**
 * Extract metadata from a video file
 * Can be used before creating a VideoLayer to determine composition size
 */
export async function extractVideoMetadata(
  source: string | File | Blob
): Promise<VideoMetadata> {
  return new Promise((resolve, reject) => {
    const video = document.createElement('video');
    video.crossOrigin = 'anonymous';
    video.preload = 'metadata';

    const cleanup = () => {
      video.removeEventListener('loadedmetadata', onLoad);
      video.removeEventListener('error', onError);
      URL.revokeObjectURL(video.src);
    };

    const onLoad = () => {
      const metadata: VideoMetadata = {
        duration: video.duration,
        frameCount: Math.ceil(video.duration * 30), // Estimate at 30fps
        fps: 30, // Browser doesn't expose this
        width: video.videoWidth,
        height: video.videoHeight,
        hasAudio: true, // Assume true
      };
      cleanup();
      resolve(metadata);
    };

    const onError = () => {
      cleanup();
      reject(new Error('Failed to load video metadata'));
    };

    video.addEventListener('loadedmetadata', onLoad);
    video.addEventListener('error', onError);

    // Set source
    if (typeof source === 'string') {
      video.src = source;
    } else {
      video.src = URL.createObjectURL(source);
    }
  });
}

/**
 * Calculate recommended composition settings from video metadata
 */
export function calculateCompositionFromVideo(
  metadata: VideoMetadata,
  targetFps: number = 16
): { width: number; height: number; frameCount: number } {
  // Round dimensions to nearest multiple of 8 (required for most AI models)
  const width = Math.round(metadata.width / 8) * 8;
  const height = Math.round(metadata.height / 8) * 8;

  // Calculate frame count at target FPS
  const frameCount = Math.ceil(metadata.duration * targetFps);

  return { width, height, frameCount };
}
