/**
 * Tests for ui/src/services/export/videoEncoder.ts
 * 
 * Note: WebCodecs API is browser-only. Node.js tests verify:
 * - isWebCodecsSupported() returns false in non-browser env
 * - Type structures are correct
 * 
 * Browser-dependent tests are skipped.
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import {
  isWebCodecsSupported,
  getSupportedCodecs,
  type VideoEncoderConfig,
  type EncodingProgress,
  type EncodedVideo,
} from "@/services/export/videoEncoder";

// ============================================================
// PURE FUNCTION TESTS (Node.js compatible)
// ============================================================

describe("videoEncoder: isWebCodecsSupported", () => {
  it("returns false in Node.js environment (no WebCodecs)", () => {
    // In Node.js/Vitest, VideoEncoder and VideoFrame are undefined
    const result = isWebCodecsSupported();
    expect(result).toBe(false);
  });
});

describe("videoEncoder: getSupportedCodecs", () => {
  it("returns empty array when WebCodecs not supported", async () => {
    // In Node.js, should return empty array
    const codecs = await getSupportedCodecs();
    expect(codecs).toEqual([]);
  });
});

// ============================================================
// TYPE STRUCTURE TESTS
// ============================================================

describe("videoEncoder: Type Structures", () => {
  it("VideoEncoderConfig has correct structure", () => {
    const config: VideoEncoderConfig = {
      width: 1920,
      height: 1080,
      frameRate: 30,
      codec: "avc",
      bitrate: 5_000_000,
      quality: "high",
    };
    
    expect(config.width).toBe(1920);
    expect(config.height).toBe(1080);
    expect(config.frameRate).toBe(30);
    expect(config.codec).toBe("avc");
  });

  it("EncodingProgress has correct structure", () => {
    const progress: EncodingProgress = {
      framesEncoded: 50,
      totalFrames: 100,
      percentage: 50,
      bytesWritten: 1024000,
    };
    
    expect(progress.framesEncoded).toBe(50);
    expect(progress.percentage).toBe(50);
  });

  it("EncodedVideo has correct structure", () => {
    const video: EncodedVideo = {
      blob: new Blob(["test"], { type: "video/mp4" }),
      mimeType: "video/mp4",
      duration: 10,
      frameCount: 300,
      size: 1024000,
    };
    
    expect(video.mimeType).toBe("video/mp4");
    expect(video.duration).toBe(10);
    expect(video.frameCount).toBe(300);
  });

  it("codec values are valid", () => {
    const validCodecs: VideoEncoderConfig["codec"][] = ["avc", "vp9", "vp8"];
    validCodecs.forEach(codec => {
      const config: VideoEncoderConfig = {
        width: 1920,
        height: 1080,
        frameRate: 30,
        codec,
      };
      expect(config.codec).toBe(codec);
    });
  });

  it("quality values are valid", () => {
    const validQualities: NonNullable<VideoEncoderConfig["quality"]>[] = [
      "low", "medium", "high", "lossless"
    ];
    validQualities.forEach(quality => {
      const config: VideoEncoderConfig = {
        width: 1920,
        height: 1080,
        frameRate: 30,
        codec: "avc",
        quality,
      };
      expect(config.quality).toBe(quality);
    });
  });
});

// ============================================================
// BROWSER-DEPENDENT TESTS (Skipped - require Playwright)
// ============================================================

describe.skip("videoEncoder: Browser-dependent (need Playwright)", () => {
  it("WebCodecsVideoEncoder encodes frames", () => {
    // Requires actual browser with WebCodecs support
  });

  it("encodeFrameSequence produces video", () => {
    // Requires Canvas and WebCodecs
  });

  it("downloadVideo triggers download", () => {
    // Requires DOM (document.createElement, URL.createObjectURL)
  });
});
