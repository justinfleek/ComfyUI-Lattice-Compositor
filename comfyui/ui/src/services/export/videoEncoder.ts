/**
 * Video Encoder Service
 *
 * Uses WebCodecs API to encode frame sequences into video.
 * Uses webm-muxer/mp4-muxer for proper container generation.
 * Supports H.264/AVC and VP9 codecs with configurable quality.
 */

import { Muxer as MP4Muxer, ArrayBufferTarget as MP4Target } from "mp4-muxer";
import {
  Muxer as WebMMuxer,
  ArrayBufferTarget as WebMTarget,
} from "webm-muxer";
import { exportLogger } from "@/utils/logger";

// ============================================================================
// Types
// ============================================================================

export interface VideoEncoderConfig {
  width: number;
  height: number;
  frameRate: number;
  codec: "avc" | "vp9" | "vp8";
  bitrate?: number; // bits per second
  quality?: "low" | "medium" | "high" | "lossless";
}

export interface EncodingProgress {
  framesEncoded: number;
  totalFrames: number;
  percentage: number;
  bytesWritten: number;
}

export interface EncodedVideo {
  blob: Blob;
  mimeType: string;
  duration: number;
  frameCount: number;
  size: number;
}

// ============================================================================
// WebCodecs Support Check
// ============================================================================

export function isWebCodecsSupported(): boolean {
  return (
    typeof VideoEncoder !== "undefined" && typeof VideoFrame !== "undefined"
  );
}

export async function getSupportedCodecs(): Promise<string[]> {
  if (!isWebCodecsSupported()) return [];

  const codecs: string[] = [];
  const testConfigs = [
    { codec: "avc1.42E01F", name: "avc" }, // H.264 Baseline
    { codec: "avc1.640028", name: "avc" }, // H.264 High
    { codec: "vp9", name: "vp9" },
    { codec: "vp8", name: "vp8" },
  ];

  for (const { codec, name } of testConfigs) {
    try {
      const support = await VideoEncoder.isConfigSupported({
        codec,
        width: 1920,
        height: 1080,
        bitrate: 5_000_000,
      });
      if (support.supported && !codecs.includes(name)) {
        codecs.push(name);
      }
    } catch {
      // Not supported
    }
  }

  return codecs;
}

// ============================================================================
// Video Encoder Class
// ============================================================================

export class WebCodecsVideoEncoder {
  private config: VideoEncoderConfig;
  private encoder: VideoEncoder | null = null;
  private webmMuxer: WebMMuxer<WebMTarget> | null = null;
  private mp4Muxer: MP4Muxer<MP4Target> | null = null;
  private frameCount = 0;
  private totalBytesWritten = 0;
  private onProgress?: (progress: EncodingProgress) => void;

  constructor(config: VideoEncoderConfig) {
    this.config = config;
  }

  /**
   * Initialize the encoder
   */
  async initialize(
    onProgress?: (progress: EncodingProgress) => void,
  ): Promise<void> {
    if (!isWebCodecsSupported()) {
      throw new Error("WebCodecs API is not supported in this browser");
    }

    this.onProgress = onProgress;
    this.frameCount = 0;
    this.totalBytesWritten = 0;
    this.webmMuxer = null;
    this.mp4Muxer = null;

    const codecString = this.getCodecString();
    const bitrate = this.getBitrate();

    // Check if configuration is supported
    const support = await VideoEncoder.isConfigSupported({
      codec: codecString,
      width: this.config.width,
      height: this.config.height,
      bitrate,
    });

    if (!support.supported) {
      throw new Error(`Unsupported encoder configuration: ${codecString}`);
    }

    // Initialize the appropriate muxer based on codec
    if (this.config.codec === "avc") {
      // H.264 → MP4 container
      this.mp4Muxer = new MP4Muxer({
        target: new MP4Target(),
        video: {
          codec: "avc",
          width: this.config.width,
          height: this.config.height,
        },
        fastStart: "in-memory", // Moves moov atom to beginning for streaming
      });
    } else {
      // VP8/VP9 → WebM container
      const webmCodec = this.config.codec === "vp9" ? "V_VP9" : "V_VP8";
      this.webmMuxer = new WebMMuxer({
        target: new WebMTarget(),
        video: {
          codec: webmCodec,
          width: this.config.width,
          height: this.config.height,
        },
      });
    }

    this.encoder = new VideoEncoder({
      output: (
        chunk: EncodedVideoChunk,
        metadata?: EncodedVideoChunkMetadata,
      ) => {
        this.handleChunk(chunk, metadata);
      },
      error: (error: DOMException) => {
        exportLogger.error("VideoEncoder: Encoding error:", error);
        throw error;
      },
    });

    this.encoder.configure({
      codec: codecString,
      width: this.config.width,
      height: this.config.height,
      bitrate,
      framerate: this.config.frameRate,
    });
  }

  /**
   * Encode a single frame
   */
  async encodeFrame(
    imageData: ImageData | OffscreenCanvas | HTMLCanvasElement,
    frameIndex: number,
    totalFrames: number,
    keyFrame = false,
  ): Promise<void> {
    if (!this.encoder) {
      throw new Error("Encoder not initialized");
    }

    // Create VideoFrame from image data
    let frame: VideoFrame;

    if (imageData instanceof ImageData) {
      // Convert ImageData to rgba buffer for VideoFrame
      frame = new VideoFrame(imageData.data, {
        timestamp: (frameIndex * 1_000_000) / this.config.frameRate,
        duration: 1_000_000 / this.config.frameRate,
        codedWidth: imageData.width,
        codedHeight: imageData.height,
        format: "RGBA",
      });
    } else {
      // Canvas
      frame = new VideoFrame(imageData, {
        timestamp: (frameIndex * 1_000_000) / this.config.frameRate,
        duration: 1_000_000 / this.config.frameRate,
      });
    }

    // Encode frame
    // First frame and periodic frames should be keyframes
    const isKeyFrame = keyFrame || frameIndex === 0 || frameIndex % 30 === 0;

    this.encoder.encode(frame, { keyFrame: isKeyFrame });
    frame.close();

    this.frameCount++;

    // Report progress
    if (this.onProgress) {
      this.onProgress({
        framesEncoded: this.frameCount,
        totalFrames,
        percentage: (this.frameCount / totalFrames) * 100,
        bytesWritten: this.totalBytesWritten,
      });
    }
  }

  /**
   * Finish encoding and return the video blob
   */
  async finalize(): Promise<EncodedVideo> {
    if (!this.encoder) {
      throw new Error("Encoder not initialized");
    }

    // Flush remaining frames
    await this.encoder.flush();

    // Close encoder
    this.encoder.close();
    this.encoder = null;

    // Finalize the muxer and get the video data
    let blob: Blob;
    let mimeType: string;

    if (this.mp4Muxer) {
      this.mp4Muxer.finalize();
      const buffer = this.mp4Muxer.target.buffer;
      blob = new Blob([buffer], { type: "video/mp4" });
      mimeType = "video/mp4";
      this.mp4Muxer = null;
    } else if (this.webmMuxer) {
      this.webmMuxer.finalize();
      const buffer = this.webmMuxer.target.buffer;
      blob = new Blob([buffer], { type: "video/webm" });
      mimeType = "video/webm";
      this.webmMuxer = null;
    } else {
      throw new Error("No muxer initialized");
    }

    return {
      blob,
      mimeType,
      duration: this.frameCount / this.config.frameRate,
      frameCount: this.frameCount,
      size: blob.size,
    };
  }

  /**
   * Cancel encoding
   */
  cancel(): void {
    if (this.encoder) {
      this.encoder.close();
      this.encoder = null;
    }
    this.webmMuxer = null;
    this.mp4Muxer = null;
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  private handleChunk(
    chunk: EncodedVideoChunk,
    metadata?: EncodedVideoChunkMetadata,
  ): void {
    // Pass chunk to the appropriate muxer
    if (this.mp4Muxer) {
      this.mp4Muxer.addVideoChunk(chunk, metadata);
    } else if (this.webmMuxer) {
      this.webmMuxer.addVideoChunk(chunk, metadata);
    }
    this.totalBytesWritten += chunk.byteLength;
  }

  private getCodecString(): string {
    switch (this.config.codec) {
      case "avc":
        // H.264 High Profile Level 4.0 (up to 1080p30)
        return "avc1.640028";
      case "vp9":
        return "vp09.00.10.08";
      case "vp8":
        return "vp8";
      default:
        return "avc1.640028";
    }
  }

  private getBitrate(): number {
    if (this.config.bitrate) {
      return this.config.bitrate;
    }

    // Calculate default bitrate based on resolution and quality
    const pixels = this.config.width * this.config.height;
    const baseRate = pixels * this.config.frameRate;

    switch (this.config.quality) {
      case "low":
        return Math.round(baseRate * 0.05);
      case "medium":
        return Math.round(baseRate * 0.1);
      case "high":
        return Math.round(baseRate * 0.2);
      case "lossless":
        return Math.round(baseRate * 0.5);
      default:
        return Math.round(baseRate * 0.1); // medium default
    }
  }
}

// ============================================================================
// Convenience Functions
// ============================================================================

/**
 * Encode a sequence of frames to video
 */
export async function encodeFrameSequence(
  frames: (ImageData | OffscreenCanvas | HTMLCanvasElement)[],
  config: VideoEncoderConfig,
  onProgress?: (progress: EncodingProgress) => void,
): Promise<EncodedVideo> {
  const encoder = new WebCodecsVideoEncoder(config);
  await encoder.initialize(onProgress);

  for (let i = 0; i < frames.length; i++) {
    await encoder.encodeFrame(frames[i], i, frames.length);
  }

  return encoder.finalize();
}

/**
 * Create a video from canvas frame generator
 */
export async function encodeFromGenerator(
  generator: AsyncGenerator<ImageData | OffscreenCanvas, void, unknown>,
  config: VideoEncoderConfig,
  totalFrames: number,
  onProgress?: (progress: EncodingProgress) => void,
): Promise<EncodedVideo> {
  const encoder = new WebCodecsVideoEncoder(config);
  await encoder.initialize(onProgress);

  let frameIndex = 0;
  for await (const frame of generator) {
    await encoder.encodeFrame(frame, frameIndex, totalFrames);
    frameIndex++;
  }

  return encoder.finalize();
}

/**
 * Download encoded video
 */
export function downloadVideo(video: EncodedVideo, filename: string): void {
  const extension = video.mimeType.includes("webm") ? "webm" : "mp4";
  const fullFilename = filename.includes(".")
    ? filename
    : `${filename}.${extension}`;

  const url = URL.createObjectURL(video.blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = fullFilename;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}
