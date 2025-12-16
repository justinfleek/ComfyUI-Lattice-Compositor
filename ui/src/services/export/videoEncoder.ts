/**
 * Video Encoder Service
 *
 * Uses WebCodecs API to encode frame sequences into video.
 * Supports H.264/AVC and VP9 codecs with configurable quality.
 */

import { exportLogger } from '@/utils/logger';

// ============================================================================
// Types
// ============================================================================

export interface VideoEncoderConfig {
  width: number;
  height: number;
  frameRate: number;
  codec: 'avc' | 'vp9' | 'vp8';
  bitrate?: number; // bits per second
  quality?: 'low' | 'medium' | 'high' | 'lossless';
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
  return typeof VideoEncoder !== 'undefined' &&
         typeof VideoFrame !== 'undefined';
}

export async function getSupportedCodecs(): Promise<string[]> {
  if (!isWebCodecsSupported()) return [];

  const codecs: string[] = [];
  const testConfigs = [
    { codec: 'avc1.42E01F', name: 'avc' },   // H.264 Baseline
    { codec: 'avc1.640028', name: 'avc' },   // H.264 High
    { codec: 'vp9', name: 'vp9' },
    { codec: 'vp8', name: 'vp8' },
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
  private chunks: EncodedVideoChunk[] = [];
  private frameCount = 0;
  private totalBytesWritten = 0;
  private onProgress?: (progress: EncodingProgress) => void;

  constructor(config: VideoEncoderConfig) {
    this.config = config;
  }

  /**
   * Initialize the encoder
   */
  async initialize(onProgress?: (progress: EncodingProgress) => void): Promise<void> {
    if (!isWebCodecsSupported()) {
      throw new Error('WebCodecs API is not supported in this browser');
    }

    this.onProgress = onProgress;
    this.chunks = [];
    this.frameCount = 0;
    this.totalBytesWritten = 0;

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

    this.encoder = new VideoEncoder({
      output: (chunk: EncodedVideoChunk, metadata?: EncodedVideoChunkMetadata) => {
        this.handleChunk(chunk, metadata);
      },
      error: (error: DOMException) => {
        exportLogger.error('VideoEncoder: Encoding error:', error);
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
    keyFrame = false
  ): Promise<void> {
    if (!this.encoder) {
      throw new Error('Encoder not initialized');
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
        format: 'RGBA',
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
      throw new Error('Encoder not initialized');
    }

    // Flush remaining frames
    await this.encoder.flush();

    // Close encoder
    this.encoder.close();
    this.encoder = null;

    // Create the video container
    const videoData = this.createVideoContainer();

    return {
      blob: videoData.blob,
      mimeType: videoData.mimeType,
      duration: this.frameCount / this.config.frameRate,
      frameCount: this.frameCount,
      size: videoData.blob.size,
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
    this.chunks = [];
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  private handleChunk(chunk: EncodedVideoChunk, metadata?: EncodedVideoChunkMetadata): void {
    this.chunks.push(chunk);
    this.totalBytesWritten += chunk.byteLength;
  }

  private getCodecString(): string {
    switch (this.config.codec) {
      case 'avc':
        // H.264 High Profile Level 4.0 (up to 1080p30)
        return 'avc1.640028';
      case 'vp9':
        return 'vp09.00.10.08';
      case 'vp8':
        return 'vp8';
      default:
        return 'avc1.640028';
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
      case 'low':
        return Math.round(baseRate * 0.05);
      case 'medium':
        return Math.round(baseRate * 0.1);
      case 'high':
        return Math.round(baseRate * 0.2);
      case 'lossless':
        return Math.round(baseRate * 0.5);
      default:
        return Math.round(baseRate * 0.1); // medium default
    }
  }

  private createVideoContainer(): { blob: Blob; mimeType: string } {
    // For now, just return raw chunks as WebM
    // In production, you'd use a proper muxer (mp4box.js, webm-muxer, etc.)

    // Simple approach: concatenate chunk data for WebM/VP9
    if (this.config.codec === 'vp9' || this.config.codec === 'vp8') {
      return this.createWebMContainer();
    }

    // For H.264, return as MP4 using minimal container
    return this.createMP4Container();
  }

  private createWebMContainer(): { blob: Blob; mimeType: string } {
    // WebM container creation
    // This is a simplified version - production would use webm-muxer
    const buffers: ArrayBuffer[] = [];

    for (const chunk of this.chunks) {
      const buffer = new ArrayBuffer(chunk.byteLength);
      chunk.copyTo(buffer);
      buffers.push(buffer);
    }

    const totalLength = buffers.reduce((sum, buf) => sum + buf.byteLength, 0);
    const combined = new Uint8Array(totalLength);
    let offset = 0;

    for (const buffer of buffers) {
      combined.set(new Uint8Array(buffer), offset);
      offset += buffer.byteLength;
    }

    return {
      blob: new Blob([combined], { type: 'video/webm' }),
      mimeType: 'video/webm',
    };
  }

  private createMP4Container(): { blob: Blob; mimeType: string } {
    // MP4 container creation
    // This is a simplified version - production would use mp4box.js
    const buffers: ArrayBuffer[] = [];

    for (const chunk of this.chunks) {
      const buffer = new ArrayBuffer(chunk.byteLength);
      chunk.copyTo(buffer);
      buffers.push(buffer);
    }

    const totalLength = buffers.reduce((sum, buf) => sum + buf.byteLength, 0);
    const combined = new Uint8Array(totalLength);
    let offset = 0;

    for (const buffer of buffers) {
      combined.set(new Uint8Array(buffer), offset);
      offset += buffer.byteLength;
    }

    // Return as raw H.264 stream - not a proper MP4 container
    // For proper MP4, use mp4box.js or similar
    return {
      blob: new Blob([combined], { type: 'video/mp4' }),
      mimeType: 'video/mp4',
    };
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
  onProgress?: (progress: EncodingProgress) => void
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
  onProgress?: (progress: EncodingProgress) => void
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
  const extension = video.mimeType.includes('webm') ? 'webm' : 'mp4';
  const fullFilename = filename.includes('.') ? filename : `${filename}.${extension}`;

  const url = URL.createObjectURL(video.blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = fullFilename;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}
