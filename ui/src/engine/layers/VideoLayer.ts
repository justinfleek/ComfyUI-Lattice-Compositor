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
      timeRemapEnabled: data?.timeRemapEnabled ?? false,
      timeRemap: data?.timeRemap,
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
   * Handles speed, time remapping, loop, and ping-pong
   */
  private calculateVideoTime(compositionFrame: number): number {
    if (!this.metadata) return 0;

    // If time remap is enabled and animated, use that
    if (this.videoData.timeRemapEnabled && this.videoData.timeRemap?.animated) {
      return this.videoEvaluator.evaluate(this.videoData.timeRemap, compositionFrame);
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
   */
  protected override getSourceCanvas(): HTMLCanvasElement | null {
    if (!this.videoElement || !this.metadata) {
      return null;
    }

    const width = this.metadata.width;
    const height = this.metadata.height;

    // Lazy create/resize canvas
    if (!this.effectCanvas ||
        this.effectCanvas.width !== width ||
        this.effectCanvas.height !== height) {
      this.effectCanvas = document.createElement('canvas');
      this.effectCanvas.width = width;
      this.effectCanvas.height = height;
      this.effectCanvasCtx = this.effectCanvas.getContext('2d');
    }

    if (!this.effectCanvasCtx) {
      return null;
    }

    // Draw current video frame to canvas
    this.effectCanvasCtx.clearRect(0, 0, width, height);
    this.effectCanvasCtx.drawImage(this.videoElement, 0, 0, width, height);

    return this.effectCanvas;
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
  }

  // ============================================================================
  // DISPOSAL
  // ============================================================================

  protected onDispose(): void {
    this.clearVideo();

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
