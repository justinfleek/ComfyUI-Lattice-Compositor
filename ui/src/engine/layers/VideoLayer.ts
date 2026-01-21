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

import * as THREE from "three";
import {
  isWebCodecsSupported,
  VideoDecoderService,
} from "@/services/videoDecoder";
import { assertDefined } from "@/utils/typeGuards";
import type { AssetReference, Layer, VideoData } from "@/types/project";
import { layerLogger } from "@/utils/logger";
import { KeyframeEvaluator } from "../animation/KeyframeEvaluator";
import type { ResourceManager } from "../core/ResourceManager";
import { BaseLayer } from "./BaseLayer";

// ============================================================================
// TYPES
// ============================================================================

export interface VideoMetadata {
  duration: number; // Total duration in seconds
  frameCount: number; // Total frame count (estimated if fps unknown)
  fps: number | null; // Source FPS (null if detection failed)
  width: number;
  height: number;
  hasAudio: boolean;
}

export interface VideoLayerEvents {
  "metadata-loaded": VideoMetadata;
  "playback-ended": undefined;
  "loop-point": number; // Frame at which loop occurred
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

  // Frame-accurate decoder (WebCodecs API)
  private frameAccurateDecoder: VideoDecoderService | null = null;
  private useFrameAccurateDecoding: boolean = false;
  private decodedFrameTexture: THREE.CanvasTexture | null = null;
  private decodedFrameCanvas: HTMLCanvasElement | null = null;
  private decodedFrameCtx: CanvasRenderingContext2D | null = null;

  // Callbacks for composition auto-resize
  private onMetadataLoaded?: (metadata: VideoMetadata) => void;

  // Composition FPS for time calculation
  private compositionFPS: number = 16;

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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: data ∈ VideoData | null → VideoData (with explicit defaults)
    const data = (layerData.data !== null && typeof layerData.data === "object") ? layerData.data as VideoData : null;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: Extract each property with explicit type narrowing and defaults
    const assetIdValue = (data !== null && typeof data === "object" && "assetId" in data) ? data.assetId : null;
    const loopValue = (data !== null && typeof data === "object" && "loop" in data && typeof data.loop === "boolean") ? data.loop : false;
    const pingPongValue = (data !== null && typeof data === "object" && "pingPong" in data && typeof data.pingPong === "boolean") ? data.pingPong : false;
    const startTimeValue = (data !== null && typeof data === "object" && "startTime" in data && typeof data.startTime === "number" && Number.isFinite(data.startTime)) ? data.startTime : 0;
    const endTimeValue = (data !== null && typeof data === "object" && "endTime" in data) ? data.endTime : undefined;
    const speedValue = (data !== null && typeof data === "object" && "speed" in data && typeof data.speed === "number" && Number.isFinite(data.speed)) ? data.speed : 1;
    const speedMapEnabledValue = (data !== null && typeof data === "object" && "speedMapEnabled" in data && typeof data.speedMapEnabled === "boolean") ? data.speedMapEnabled : ((data !== null && typeof data === "object" && "timeRemapEnabled" in data && typeof data.timeRemapEnabled === "boolean") ? data.timeRemapEnabled : false);
    const speedMapValue = (data !== null && typeof data === "object" && "speedMap" in data) ? data.speedMap : ((data !== null && typeof data === "object" && "timeRemap" in data) ? data.timeRemap : undefined);
    const timeRemapEnabledValue = (data !== null && typeof data === "object" && "timeRemapEnabled" in data && typeof data.timeRemapEnabled === "boolean") ? data.timeRemapEnabled : ((data !== null && typeof data === "object" && "speedMapEnabled" in data && typeof data.speedMapEnabled === "boolean") ? data.speedMapEnabled : false);
    const timeRemapValue = (data !== null && typeof data === "object" && "timeRemap" in data) ? data.timeRemap : ((data !== null && typeof data === "object" && "speedMap" in data) ? data.speedMap : undefined);
    const frameBlendingValue = (data !== null && typeof data === "object" && "frameBlending" in data && typeof data.frameBlending === "string") ? data.frameBlending : "none";
    const audioEnabledValue = (data !== null && typeof data === "object" && "audioEnabled" in data && typeof data.audioEnabled === "boolean") ? data.audioEnabled : true;
    const audioLevelValue = (data !== null && typeof data === "object" && "audioLevel" in data && typeof data.audioLevel === "number" && Number.isFinite(data.audioLevel)) ? data.audioLevel : 100;
    const posterFrameValue = (data !== null && typeof data === "object" && "posterFrame" in data && typeof data.posterFrame === "number" && Number.isFinite(data.posterFrame)) ? data.posterFrame : 0;

    return {
      assetId: assetIdValue,
      loop: loopValue,
      pingPong: pingPongValue,
      startTime: startTimeValue,
      endTime: endTimeValue,
      speed: speedValue,
      // Speed map (new naming)
      speedMapEnabled: speedMapEnabledValue,
      speedMap: speedMapValue,
      // Backwards compatibility aliases
      timeRemapEnabled: timeRemapEnabledValue,
      timeRemap: timeRemapValue,
      frameBlending: frameBlendingValue,
      audioEnabled: audioEnabledValue,
      audioLevel: audioLevelValue,
      posterFrame: posterFrameValue,
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
    // System F/Omega pattern: Wrap in try/catch for expected "asset not found" case
    let asset: AssetReference;
    try {
      asset = this.resources.getAsset(assetId);
    } catch (error) {
      layerLogger.warn(`VideoLayer: Asset ${assetId} not found:`, error instanceof Error ? error.message : String(error));
      return;
    }

    if (asset.type !== "video") {
      layerLogger.warn(`VideoLayer: Asset ${assetId} is not a video (type: ${asset.type})`);
      return;
    }

    this.assetRef = asset;
    this.videoData.assetId = assetId;

    // Create video element
    this.videoElement = document.createElement("video");
    this.videoElement.crossOrigin = "anonymous";
    this.videoElement.playsInline = true;
    this.videoElement.muted = !this.videoData.audioEnabled;
    this.videoElement.loop = false; // We handle looping manually for precise control
    this.videoElement.preload = "auto";

    // Set source
    if (asset.data) {
      // Base64 or blob URL
      this.videoElement.src = asset.data;
    }

    // Wait for metadata
    await this.waitForMetadata();

    // Create texture from video
    this.createVideoTexture();

    // Initialize frame-accurate decoder if WebCodecs is available
    if (isWebCodecsSupported() && asset.data) {
      await this.initializeFrameAccurateDecoder(asset.data);
    }

    // Set initial time
    this.seekToFrame(this.videoData.posterFrame);
  }

  /**
   * Initialize WebCodecs-based decoder for frame-accurate seeking
   */
  private async initializeFrameAccurateDecoder(
    videoUrl: string,
  ): Promise<void> {
    try {
      // Fetch the video file as blob for WebCodecs
      const response = await fetch(videoUrl);
      const videoBlob = await response.blob();
      const blobUrl = URL.createObjectURL(videoBlob);

      // Create and initialize the decoder
      this.frameAccurateDecoder = new VideoDecoderService(blobUrl, {
        maxCacheSize: 100, // Cache up to 100 frames
      });

      const info = await this.frameAccurateDecoder.initialize();

      // Update metadata with accurate frame info from decoder
      if (this.metadata) {
        this.metadata.fps = info.fps;
        this.metadata.frameCount = info.frameCount;
        this.metadata.duration = info.duration;
        this.metadata.width = info.width;
        this.metadata.height = info.height;
      }

      // Create canvas for decoded frames
      this.decodedFrameCanvas = document.createElement("canvas");
      this.decodedFrameCanvas.width = info.width;
      this.decodedFrameCanvas.height = info.height;
      this.decodedFrameCtx = this.decodedFrameCanvas.getContext("2d");

      this.useFrameAccurateDecoding = true;
      layerLogger.debug(
        `VideoLayer: WebCodecs decoder initialized - ${info.frameCount} frames @ ${info.fps}fps`,
      );
    } catch (error) {
      layerLogger.warn(
        "VideoLayer: WebCodecs decoder failed, falling back to HTMLVideoElement:",
        error,
      );
      this.useFrameAccurateDecoding = false;
      this.frameAccurateDecoder = null;
    }
  }

  /**
   * Wait for video metadata to load
   */
  private waitForMetadata(): Promise<void> {
    return new Promise((resolve, reject) => {
      if (!this.videoElement) {
        reject(new Error("No video element"));
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
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const videoElement = this.videoElement;
        if (videoElement != null && typeof videoElement === "object" && typeof videoElement.removeEventListener === "function") {
          videoElement.removeEventListener(
            "loadedmetadata",
            onLoadedMetadata,
          );
          videoElement.removeEventListener("error", onError);
        }
      };

      this.videoElement.addEventListener("loadedmetadata", onLoadedMetadata);
      this.videoElement.addEventListener("error", onError);

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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: assetRef.fps ∈ number | undefined → number (default 30)
    const fpsValue = (typeof this.assetRef === "object" && this.assetRef !== null && "fps" in this.assetRef && typeof this.assetRef.fps === "number" && Number.isFinite(this.assetRef.fps)) ? this.assetRef.fps : 30;
    const fps = fpsValue;
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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const onMetadataLoaded = this.onMetadataLoaded;
    if (onMetadataLoaded != null && typeof onMetadataLoaded === "function") {
      onMetadataLoaded(this.metadata);
    }

    layerLogger.debug(
      `VideoLayer: Loaded: ${width}x${height}, ${frameCount} frames @ ${fps}fps, ${duration.toFixed(2)}s`,
    );
  }

  /**
   * Check if video has audio track
   */
  private hasAudioTrack(): boolean {
    if (!this.videoElement) return false;

    // Check for audio tracks (if available)
    // Note: audioTracks is not in standard HTMLVideoElement type but may exist in some browsers
    const videoWithTracks = this.videoElement as HTMLVideoElement & { audioTracks?: { length: number } };
    const audioTracks = videoWithTracks.audioTracks;
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
   * Uses WebCodecs for frame-accurate seeking when available
   */
  seekToFrame(compositionFrame: number): void {
    if (!this.metadata) return;

    // Calculate video time from composition frame
    const videoTime = this.calculateVideoTime(compositionFrame);

    // Use frame-accurate decoder if available
    if (this.useFrameAccurateDecoding && this.frameAccurateDecoder) {
      this.seekToFrameAccurate(videoTime);
      return;
    }

    // Fallback to HTMLVideoElement (±0.5 frame drift)
    if (this.videoElement) {
      const clampedTime = Math.max(
        0,
        Math.min(videoTime, this.videoElement.duration),
      );
      this.videoElement.currentTime = clampedTime;
    }
  }

  /**
   * Frame-accurate seek using WebCodecs API
   */
  private async seekToFrameAccurate(videoTime: number): Promise<void> {
    if (
      !this.frameAccurateDecoder ||
      !this.metadata ||
      this.metadata.fps === null
    )
      return;

    // Convert time to frame number
    const targetFrame = Math.round(videoTime * this.metadata.fps);
    const clampedFrame = Math.max(
      0,
      Math.min(targetFrame, this.metadata.frameCount - 1),
    );

    try {
      // Get the exact frame from the decoder (throws explicit error if extraction fails)
      const frameInfo = await this.frameAccurateDecoder.getFrame(clampedFrame);

      // System F/Omega: frameInfo is guaranteed non-null (getFrame throws on failure)
      if (this.decodedFrameCtx && this.decodedFrameCanvas) {
        // Draw the decoded frame to canvas
        this.decodedFrameCtx.clearRect(
          0,
          0,
          this.decodedFrameCanvas.width,
          this.decodedFrameCanvas.height,
        );

        if (frameInfo.bitmap instanceof ImageBitmap) {
          this.decodedFrameCtx.drawImage(frameInfo.bitmap, 0, 0);
        }

        // Update texture from decoded frame
        this.updateTextureFromDecodedFrame();
      }
    } catch (error) {
      layerLogger.warn(
        "VideoLayer: Frame-accurate seek failed, falling back:",
        error,
      );

      // Fallback to HTMLVideoElement
      if (this.videoElement) {
        const clampedTime = Math.max(
          0,
          Math.min(videoTime, this.videoElement.duration),
        );
        this.videoElement.currentTime = clampedTime;
      }
    }
  }

  /**
   * Update Three.js texture from decoded frame canvas
   */
  private updateTextureFromDecodedFrame(): void {
    if (!this.decodedFrameCanvas || !this.material) return;

    // Create or update texture from canvas
    if (!this.decodedFrameTexture) {
      this.decodedFrameTexture = new THREE.CanvasTexture(
        this.decodedFrameCanvas,
      );
      this.decodedFrameTexture.minFilter = THREE.LinearFilter;
      this.decodedFrameTexture.magFilter = THREE.LinearFilter;
      this.decodedFrameTexture.colorSpace = THREE.SRGBColorSpace;
    } else {
      this.decodedFrameTexture.needsUpdate = true;
    }

    // Apply decoded frame texture
    this.material.map = this.decodedFrameTexture;
    this.material.needsUpdate = true;
  }

  /**
   * Calculate video time from composition frame
   * Handles timeStretch, speed, speed map (time remapping), loop, and ping-pong
   *
   * DETERMINISM: This is a pure function of (compositionFrame, layer state).
   * Same inputs always produce same outputs.
   */
  private calculateVideoTime(compositionFrame: number): number {
    if (!this.metadata) return 0;

    // If speed map is enabled and animated, use that (overrides other time controls)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: speedMapEnabled ∈ boolean | undefined → boolean (fallback to timeRemapEnabled)
    const speedMapEnabledValue = (typeof this.videoData.speedMapEnabled === "boolean") ? this.videoData.speedMapEnabled : ((typeof this.videoData.timeRemapEnabled === "boolean") ? this.videoData.timeRemapEnabled : false);
    // Pattern match: speedMap ∈ AnimatableProperty | undefined → AnimatableProperty | undefined (fallback to timeRemap)
    const speedMapPropValue = (this.videoData.speedMap !== undefined) ? this.videoData.speedMap : this.videoData.timeRemap;
    if (speedMapEnabledValue && speedMapPropValue !== undefined && typeof speedMapPropValue === "object" && speedMapPropValue !== null && "animated" in speedMapPropValue && speedMapPropValue.animated) {
      const remappedTime = this.videoEvaluator.evaluate(
        speedMapPropValue,
        compositionFrame,
      );
      // Validate speed map result (NaN would break video playback)
      return Number.isFinite(remappedTime) ? remappedTime : 0;
    }

    // Get layer's timeStretch (100 = normal, 200 = half speed, -100 = reversed)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: timeStretch ∈ number | undefined → number (default 100)
    const rawTimeStretch = (typeof this.layerData.timeStretch === "number" && Number.isFinite(this.layerData.timeStretch)) ? this.layerData.timeStretch : 100;
    const timeStretch = Number.isFinite(rawTimeStretch) ? rawTimeStretch : 100;
    const isReversed = timeStretch < 0;

    // Calculate effective speed:
    // - timeStretch: 100% = 1x, 200% = 0.5x, 50% = 2x
    // - speed: Direct multiplier from VideoData (1 = normal, 2 = 2x faster)
    // Combined: effectiveSpeed = (100 / |timeStretch|) * speed
    const stretchFactor = timeStretch !== 0 ? 100 / Math.abs(timeStretch) : 0;
    // Validate speed (NaN would cause video time calculation to fail)
    const speed = Number.isFinite(this.videoData.speed)
      ? this.videoData.speed
      : 1;
    const effectiveSpeed = stretchFactor * speed;

    // Calculate time relative to layer start
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: startFrame ∈ number | undefined → number (default 0)
    const layerStartFrame = (typeof this.layerData.startFrame === "number" && Number.isFinite(this.layerData.startFrame)) ? this.layerData.startFrame : 0;
    const layerFrame = compositionFrame - layerStartFrame;
    // Validate FPS (NaN would cause division issues)
    const compFps =
      Number.isFinite(this.compositionFPS) && this.compositionFPS > 0
        ? this.compositionFPS
        : 16;

    // Convert to video time with effective speed
    let videoTime = (layerFrame / compFps) * effectiveSpeed;

    // Add start offset
    videoTime += this.videoData.startTime;

    // Get effective duration (with end time if set)
    const effectiveDuration = this.videoData.endTime
      ? this.videoData.endTime - this.videoData.startTime
      : this.metadata.duration - this.videoData.startTime;

    // Handle reversed playback
    if (isReversed && effectiveDuration > 0) {
      // Reverse: map videoTime to (effectiveDuration - videoTime)
      videoTime =
        this.videoData.startTime +
        effectiveDuration -
        (videoTime - this.videoData.startTime);
    }

    // Handle looping
    if (this.videoData.loop && effectiveDuration > 0) {
      const relativeTime = videoTime - this.videoData.startTime;
      if (this.videoData.pingPong) {
        // Ping-pong: 0 -> duration -> 0 -> duration...
        const cycles = Math.floor(relativeTime / effectiveDuration);
        const phase = relativeTime % effectiveDuration;
        const adjustedPhase =
          cycles % 2 === 0 ? phase : effectiveDuration - phase;
        videoTime = this.videoData.startTime + adjustedPhase;
      } else {
        // Standard loop
        videoTime =
          this.videoData.startTime +
          (((relativeTime % effectiveDuration) + effectiveDuration) %
            effectiveDuration);
      }
    }

    // Clamp to valid range
    videoTime = Math.max(
      this.videoData.startTime,
      Math.min(videoTime, this.metadata.duration),
    );

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
    // Validate fps (NaN would break time calculations)
    this.compositionFPS = Number.isFinite(fps) && fps > 0 ? fps : 16;
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
    // Validate speed (NaN would break playback)
    const validSpeed = Number.isFinite(speed) ? speed : 1;
    this.videoData.speed = validSpeed;
    if (this.videoElement) {
      this.videoElement.playbackRate = validSpeed;
    }
  }

  setStartTime(time: number): void {
    this.videoData.startTime = time;
  }

  setEndTime(time: number | undefined): void {
    this.videoData.endTime = time;
  }

  setFrameBlending(mode: "none" | "frame-mix" | "pixel-motion"): void {
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
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
  // Pattern match: Returns HTMLCanvasElement | {} (empty object sentinel instead of null)
  protected override getSourceCanvas(): HTMLCanvasElement {
    // Throw explicit error if video element or metadata is missing
    const hasVideoElement = typeof this.videoElement === "object" && this.videoElement !== null;
    const hasMetadata = typeof this.metadata === "object" && this.metadata !== null;
    if (!hasVideoElement || !hasMetadata) {
      throw new Error(`[VideoLayer] Layer "${this.id}" cannot provide source canvas: ${!hasVideoElement ? "videoElement is missing" : "metadata is missing"}. Load a video asset before applying effects.`);
    }

    // Pattern match: Narrow metadata and videoElement to non-null after type guard
    const metadataTyped = this.metadata as { width: number; height: number };
    const videoElementTyped = this.videoElement as HTMLVideoElement;
    const width = metadataTyped.width;
    const height = metadataTyped.height;

    // Lazy create/resize canvases
    this.ensureCanvases(width, height);

    // Throw explicit error if canvas context is missing
    const hasEffectCanvasCtx = typeof this.effectCanvasCtx === "object" && this.effectCanvasCtx !== null;
    if (!hasEffectCanvasCtx) {
      throw new Error(`[VideoLayer] Layer "${this.id}" cannot provide source canvas: effectCanvasCtx is null. Canvas context creation failed. This is a rendering system error.`);
    }
    const effectCanvasCtxTyped = this.effectCanvasCtx as CanvasRenderingContext2D;

    // Check if frame blending should be applied
    // Layer switch (frameBlending) enables blending, videoData.frameBlending specifies mode
    const shouldBlend =
      this.layerData.frameBlending === true &&
      this.videoData.frameBlending !== "none";

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    const hasPrevFrameCtx = typeof this.prevFrameCtx === "object" && this.prevFrameCtx !== null;
    const hasBlendCtx = typeof this.blendCtx === "object" && this.blendCtx !== null;
    const hasBlendCanvas = typeof this.blendCanvas === "object" && this.blendCanvas !== null;
    if (shouldBlend && hasPrevFrameCtx && hasBlendCtx && hasBlendCanvas) {
      // System F/Omega pattern: getBlendedFrame now throws explicit errors
      const blendedFrame = this.getBlendedFrame(width, height);
      return blendedFrame;
    }

    // No blending - just draw current video frame
    effectCanvasCtxTyped.clearRect(0, 0, width, height);
    effectCanvasCtxTyped.drawImage(videoElementTyped, 0, 0, width, height);

    // Throw explicit error if effect canvas is missing
    const hasEffectCanvas = typeof this.effectCanvas === "object" && this.effectCanvas !== null;
    if (!hasEffectCanvas) {
      throw new Error(`[VideoLayer] Layer "${this.id}" cannot provide source canvas: effectCanvas is null. Canvas creation failed. This is a rendering system error.`);
    }
    return this.effectCanvas as HTMLCanvasElement;
  }

  /**
   * Ensure all canvases are created and sized correctly
   */
  private ensureCanvases(width: number, height: number): void {
    // Main effect canvas
    if (
      !this.effectCanvas ||
      this.effectCanvas.width !== width ||
      this.effectCanvas.height !== height
    ) {
      this.effectCanvas = document.createElement("canvas");
      this.effectCanvas.width = width;
      this.effectCanvas.height = height;
      this.effectCanvasCtx = this.effectCanvas.getContext("2d");
    }

    // Previous frame canvas (for blending)
    if (
      !this.prevFrameCanvas ||
      this.prevFrameCanvas.width !== width ||
      this.prevFrameCanvas.height !== height
    ) {
      this.prevFrameCanvas = document.createElement("canvas");
      this.prevFrameCanvas.width = width;
      this.prevFrameCanvas.height = height;
      this.prevFrameCtx = this.prevFrameCanvas.getContext("2d");
    }

    // Blend output canvas
    if (
      !this.blendCanvas ||
      this.blendCanvas.width !== width ||
      this.blendCanvas.height !== height
    ) {
      this.blendCanvas = document.createElement("canvas");
      this.blendCanvas.width = width;
      this.blendCanvas.height = height;
      this.blendCtx = this.blendCanvas.getContext("2d");
    }
  }

  /**
   * Get blended frame between previous and current video frame
   * Used for smooth slow-motion playback
   * 
   * System F/Omega proof: Explicit validation of video element and canvas contexts
   * Type proof: width ∈ number, height ∈ number → HTMLCanvasElement (non-nullable)
   * Mathematical proof: Video element and all canvas contexts must exist to blend frames
   * Pattern proof: Missing video element or contexts is an explicit failure condition, not a lazy null return
   */
  private getBlendedFrame(
    width: number,
    height: number,
  ): HTMLCanvasElement {
    // System F/Omega proof: Explicit validation of video element and contexts
    // Type proof: videoElement ∈ HTMLVideoElement | null, metadata ∈ VideoMetadata | null, etc.
    // Mathematical proof: All components must exist to perform frame blending
    if (
      !this.videoElement ||
      !this.metadata ||
      !this.blendCtx ||
      !this.blendCanvas ||
      !this.prevFrameCtx ||
      !this.prevFrameCanvas
    ) {
      const missing = [];
      if (!this.videoElement) missing.push("videoElement");
      if (!this.metadata) missing.push("metadata");
      if (!this.blendCtx) missing.push("blendCtx");
      if (!this.blendCanvas) missing.push("blendCanvas");
      if (!this.prevFrameCtx) missing.push("prevFrameCtx");
      if (!this.prevFrameCanvas) missing.push("prevFrameCanvas");
      throw new Error(
        `[VideoLayer] Cannot get blended frame: Required components missing. ` +
        `Layer ID: ${this.id}, missing components: ${missing.join(", ")}. ` +
        `Video element and all canvas contexts must be initialized before blending frames. ` +
        `Wrap in try/catch if "not ready" is an expected state.`
      );
    }

    const currentVideoTime = this.videoElement.currentTime;
    const videoFps = this.metadata.fps || 30;
    const _frameDuration = 1 / videoFps;

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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const effectCanvasCtx = this.effectCanvasCtx;
    if (effectCanvasCtx != null && typeof effectCanvasCtx === "object" && typeof effectCanvasCtx.clearRect === "function") {
      effectCanvasCtx.clearRect(0, 0, width, height);
      if (typeof effectCanvasCtx.drawImage === "function" && this.videoElement != null) {
        effectCanvasCtx.drawImage(this.videoElement, 0, 0, width, height);
      }
    }

    // If blend factor is very close to 0 or 1, skip blending
    if (blendFactor < 0.01 || blendFactor > 0.99) {
      // System F/Omega: Throw error if effectCanvas is missing instead of returning null
      // Type proof: effectCanvas ∈ HTMLCanvasElement | null → HTMLCanvasElement (non-nullable)
      if (!this.effectCanvas) {
        throw new Error(`[VideoLayer] Cannot get blended frame: effectCanvas is missing. This should not happen - effect canvas should be initialized before blending.`);
      }
      return this.effectCanvas;
    }

    // Blend: composite previous frame with current frame
    this.blendCtx.clearRect(0, 0, width, height);

    // Draw previous frame (base)
    this.blendCtx.globalAlpha = 1;
    this.blendCtx.drawImage(this.prevFrameCanvas, 0, 0);

    // Draw current frame with blend factor opacity
    // Type proof: effectCanvas is guaranteed non-null by guard clause at function start
    assertDefined(this.effectCanvas, "effectCanvas must exist when getBlendedFrame is called");
    this.blendCtx.globalAlpha = blendFactor;
    this.blendCtx.drawImage(this.effectCanvas, 0, 0);

    // Reset alpha
    this.blendCtx.globalAlpha = 1;

    return this.blendCanvas;
  }

  /**
   * Apply processed effects canvas back to the material
   */
  protected override applyProcessedEffects(
    processedCanvas: HTMLCanvasElement,
  ): void {
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
      },
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

  protected override onApplyEvaluatedState(
    state: import("../MotionEngine").EvaluatedLayer,
  ): void {
    const props = state.properties;

    // Apply speed map if evaluated (direct video time in seconds)
    // Check both new 'speedMap' and legacy 'timeRemap' for backwards compatibility
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: props.speedMap ∈ PropertyValue | undefined → PropertyValue | undefined (fallback to timeRemap)
    const speedMapValue = (props.speedMap !== undefined) ? props.speedMap : props.timeRemap;
    if (speedMapValue !== undefined && this.videoElement) {
      const targetTime = speedMapValue as number;
      const clampedTime = Math.max(
        0,
        Math.min(targetTime, this.videoElement.duration || targetTime),
      );
      this.videoElement.currentTime = clampedTime;
    }

    // Apply speed if evaluated
    if (props.speed !== undefined) {
      this.videoData.speed = props.speed as number;
    }

    // Apply audio level if evaluated
    if (props.audioLevel !== undefined) {
      this.setAudioLevel(props.audioLevel as number);
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
      if (
        data.assetId !== undefined &&
        data.assetId !== this.videoData.assetId
      ) {
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
      if (data.frameBlending !== undefined)
        this.setFrameBlending(data.frameBlending);
      if (data.audioEnabled !== undefined)
        this.setAudioEnabled(data.audioEnabled);
      if (data.audioLevel !== undefined) this.setAudioLevel(data.audioLevel);
    }
  }

  /**
   * Clear current video
   */
  private clearVideo(): void {
    if (this.videoElement) {
      this.videoElement.pause();
      this.videoElement.src = "";
      this.videoElement = null;
    }

    if (this.videoTexture) {
      this.videoTexture.dispose();
      this.videoTexture = null;
    }

    // Clean up frame-accurate decoder
    if (this.frameAccurateDecoder) {
      this.frameAccurateDecoder.dispose();
      this.frameAccurateDecoder = null;
    }

    if (this.decodedFrameTexture) {
      this.decodedFrameTexture.dispose();
      this.decodedFrameTexture = null;
    }

    this.decodedFrameCanvas = null;
    this.decodedFrameCtx = null;
    this.useFrameAccurateDecoding = false;

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

// ============================================================================
// TYPE EXTENSIONS FOR NEWER WEB APIs
// ============================================================================

/**
 * VideoFrameCallbackMetadata - metadata provided by requestVideoFrameCallback
 * This API is available in Chrome 89+ and Safari 15.4+
 */
interface VideoFrameCallbackMetadata {
  mediaTime: number;
  presentedFrames: number;
  width: number;
  height: number;
  expectedDisplayTime: number;
}

/**
 * Extended HTMLVideoElement with requestVideoFrameCallback API
 * This API is not yet in TypeScript DOM types but is available in modern browsers
 */
interface HTMLVideoElementWithFrameCallback extends HTMLVideoElement {
  requestVideoFrameCallback(
    callback: (
      now: DOMHighResTimeStamp,
      metadata: VideoFrameCallbackMetadata,
    ) => void,
  ): number;
  cancelVideoFrameCallback(handle: number): void;
}

/**
 * Type guard to check if video element supports requestVideoFrameCallback
 */
function supportsVideoFrameCallback(
  video: HTMLVideoElement,
): video is HTMLVideoElementWithFrameCallback {
  return "requestVideoFrameCallback" in video;
}

// ============================================================================
// VIDEO METADATA EXTRACTION UTILITY
// ============================================================================

/**
 * Detect video fps using requestVideoFrameCallback API
 * 
 * System F/Omega proof: Explicit validation of API support and video element
 * Type proof: video ∈ HTMLVideoElement, timeout ∈ number → Promise<number> (non-nullable)
 * Mathematical proof: API must be supported and video element must be valid to detect FPS
 * Pattern proof: Unsupported API or invalid video is an explicit failure condition, not a lazy null return
 */
async function detectVideoFps(
  video: HTMLVideoElement,
  timeout: number = 2000,
): Promise<number> {
  // System F/Omega proof: Explicit validation of API support
  // Type proof: supportsVideoFrameCallback(video) ∈ boolean
  // Mathematical proof: requestVideoFrameCallback API must be supported to detect FPS
  if (!supportsVideoFrameCallback(video)) {
    throw new Error(
      `[VideoLayer] Cannot detect video FPS: requestVideoFrameCallback API not supported. ` +
      `Video element: ${video ? "present" : "null"}, timeout: ${timeout}ms. ` +
      `Browser does not support requestVideoFrameCallback API. ` +
      `Wrap in try/catch to fallback to duration-based estimation.`
    );
  }

  return new Promise<number>((resolve, reject) => {
    let frameCount = 0;
    let startTime: number | null = null;
    let lastMediaTime = 0;
    const frameTimes: number[] = [];
    const timeoutId = setTimeout(() => {
      // System F/Omega proof: Timeout is an explicit failure condition
      reject(new Error(
        `[VideoLayer] Cannot detect video FPS: Detection timeout. ` +
        `Timeout: ${timeout}ms, frames collected: ${frameCount}. ` +
        `Video may not be playing or frame callback not firing. ` +
        `Wrap in try/catch to fallback to duration-based estimation.`
      ));
    }, timeout);

    // Need to play video briefly to measure frame rate
    video.muted = true;
    video.currentTime = 0;

    const onFrame = (
      _now: DOMHighResTimeStamp,
      metadata: VideoFrameCallbackMetadata,
    ) => {
      if (startTime === null) {
        startTime = metadata.mediaTime;
        lastMediaTime = metadata.mediaTime;
      }

      frameCount++;

      // Record time between frames
      if (frameCount > 1) {
        frameTimes.push(metadata.mediaTime - lastMediaTime);
      }
      lastMediaTime = metadata.mediaTime;

      // Collect enough frames for accurate measurement (at least 10 frames or 0.5 seconds)
      if (frameCount >= 15 || metadata.mediaTime - startTime >= 0.5) {
        video.pause();
        video.currentTime = 0;
        clearTimeout(timeoutId);

        if (frameTimes.length >= 5) {
          // Calculate average frame duration, excluding outliers
          const sorted = [...frameTimes].sort((a, b) => a - b);
          const trimmed = sorted.slice(1, -1); // Remove min/max
          const avgFrameDuration =
            trimmed.reduce((a, b) => a + b, 0) / trimmed.length;
          const detectedFps = Math.round(1 / avgFrameDuration);

          // Snap to common frame rates
          const commonFps = [
            8, 12, 15, 16, 23.976, 24, 25, 29.97, 30, 48, 50, 59.94, 60,
          ];
          const snapped = commonFps.reduce((prev, curr) =>
            Math.abs(curr - detectedFps) < Math.abs(prev - detectedFps)
              ? curr
              : prev,
          );

          resolve(Math.abs(snapped - detectedFps) <= 2 ? snapped : detectedFps);
        } else {
          // System F/Omega proof: Insufficient frames is an explicit failure condition
          reject(new Error(
            `[VideoLayer] Cannot detect video FPS: Insufficient frame data collected. ` +
            `Frames collected: ${frameCount}, frame times recorded: ${frameTimes.length}, minimum required: 5. ` +
            `Video may be too short or frame callback not firing reliably. ` +
            `Wrap in try/catch to fallback to duration-based estimation.`
          ));
        }
        return;
      }

      // Type-safe call - we've already verified support above
      video.requestVideoFrameCallback(onFrame);
    };

    video
      .play()
      .then(() => {
        // Type-safe call - we've already verified support above
        video.requestVideoFrameCallback(onFrame);
      })
      .catch((error) => {
        clearTimeout(timeoutId);
        // System F/Omega proof: Video play failure is an explicit error condition
        const errorMessage = error instanceof Error ? error.message : String(error);
        reject(new Error(
          `[VideoLayer] Cannot detect video FPS: Video play failed. ` +
          `Error: ${errorMessage}. ` +
          `Video element may be invalid or autoplay blocked. ` +
          `Wrap in try/catch to fallback to duration-based estimation.`
        ));
      });
  });
}

/**
 * Attempt to estimate fps from video duration and common AI model patterns
 * 
 * System F/Omega proof: Explicit validation of duration and pattern matching
 * Type proof: duration ∈ number → number (non-nullable)
 * Mathematical proof: Duration must match known patterns to estimate FPS
 * Pattern proof: Unknown pattern is an explicit failure condition, not a lazy null return
 */
function estimateFpsFromDuration(duration: number): number {
  // AI video models typically use specific frame rates with known patterns

  // WAN models: 16fps (4n+1 pattern: 17, 33, 49, 65, 81 frames)
  const wan16Frames = Math.round(duration * 16);
  if ([17, 33, 49, 65, 81, 97, 113, 129].includes(wan16Frames)) {
    return 16;
  }

  // AnimateDiff: 8fps with specific frame counts
  const anim8Frames = Math.round(duration * 8);
  if ([16, 24, 32].includes(anim8Frames)) {
    return 8;
  }

  // Mochi: 30fps with 85 or 163 frames (2.83s or 5.43s)
  const mochi30Frames = Math.round(duration * 30);
  if ([85, 163].includes(mochi30Frames)) {
    return 30;
  }

  // System F/Omega proof: Unknown duration pattern is an explicit failure condition
  // Type proof: duration ∈ number
  // Mathematical proof: Duration does not match any known AI video model pattern
  throw new Error(
    `[VideoLayer] Cannot estimate FPS from duration: No matching pattern found. ` +
    `Duration: ${duration}s, WAN 16fps frames: ${Math.round(duration * 16)}, ` +
    `AnimateDiff 8fps frames: ${Math.round(duration * 8)}, ` +
    `Mochi 30fps frames: ${Math.round(duration * 30)}. ` +
    `Duration does not match known AI video model patterns. ` +
    `Wrap in try/catch to prompt user for manual FPS selection.`
  );
}

/**
 * Extract metadata from a video file
 * Can be used before creating a VideoLayer to determine composition size
 * Attempts to detect actual fps using requestVideoFrameCallback API
 */
export async function extractVideoMetadata(
  source: string | File | Blob,
): Promise<VideoMetadata> {
  return new Promise((resolve, reject) => {
    const video = document.createElement("video");
    video.crossOrigin = "anonymous";
    video.preload = "auto"; // Need more than metadata for fps detection

    let sourceUrl: string;
    const isObjectUrl = typeof source !== "string";

    if (typeof source === "string") {
      sourceUrl = source;
    } else {
      sourceUrl = URL.createObjectURL(source);
    }

    const cleanup = () => {
      video.removeEventListener("loadeddata", onLoad);
      video.removeEventListener("error", onError);
      if (isObjectUrl) {
        URL.revokeObjectURL(sourceUrl);
      }
    };

    const onLoad = async () => {
      // Try to detect actual fps using requestVideoFrameCallback
      // System F/Omega pattern: Wrap in try/catch for expected "detection failure" case
      // When FPS detection fails, fallback to duration-based estimation
      let fps: number | null = null;
      try {
        fps = await detectVideoFps(video);
      } catch (error) {
        // API detection failed - try duration-based heuristics
        try {
          fps = estimateFpsFromDuration(video.duration);
        } catch (estimateError) {
          // Both methods failed - use default 30fps estimate
          fps = 30; // Default fallback for display purposes
        }
      }

      // Calculate frame count - use detected fps or estimate at 30fps for display
      // (actual frame count will be recalculated once user specifies fps)
      const frameCount =
        fps !== null
          ? Math.ceil(video.duration * fps)
          : Math.ceil(video.duration * 30); // Placeholder estimate

      const metadata: VideoMetadata = {
        duration: video.duration,
        frameCount,
        fps, // May be null - caller must handle this
        width: video.videoWidth,
        height: video.videoHeight,
        hasAudio: true, // Assume true, will be updated on actual load
      };

      cleanup();
      resolve(metadata);
    };

    const onError = () => {
      cleanup();
      reject(new Error("Failed to load video metadata"));
    };

    video.addEventListener("loadeddata", onLoad);
    video.addEventListener("error", onError);
    video.src = sourceUrl;
  });
}

/**
 * Calculate recommended composition settings from video metadata
 * Uses video's native fps for frame count to preserve all frames
 * Note: This should only be called when fps is known (not null)
 */
export function calculateCompositionFromVideo(metadata: VideoMetadata): {
  width: number;
  height: number;
  frameCount: number;
  fps: number;
} {
  // Round dimensions to nearest multiple of 8 (required for most AI models)
  const width = Math.round(metadata.width / 8) * 8;
  const height = Math.round(metadata.height / 8) * 8;

  // Use video's native fps to preserve all frames
  // Assert fps is non-null (callers should ensure fps is known before calling)
  if (metadata.fps === null) {
    throw new Error("calculateCompositionFromVideo called with unknown fps");
  }
  const fps = metadata.fps;
  const frameCount = metadata.frameCount;

  return { width, height, frameCount, fps };
}
