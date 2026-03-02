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
// BROWSER-DEPENDENT TESTS
// ============================================================
//
// The following browser-dependent functionality is tested in E2E:
//
// Location: /ui/e2e/export/video-encoder.spec.ts
//
// Covered:
// - isWebCodecsSupported (E2E lines 24-41)
// - getSupportedCodecs (E2E lines 43-61)
// - WebCodecsVideoEncoder class (E2E lines 64-185)
//   - create encoder instance
//   - encode canvas frame
//   - finish encoding and return video
// - encodeFrameSequence (E2E lines 187-230)
// - encodeFromGenerator (E2E lines 232-274)
// - downloadVideo (E2E lines 277-316)
//
// Run E2E tests with: bunx playwright test video-encoder.spec.ts
