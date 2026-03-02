/**
 * Frame Sequence Exporter Tests
 * 
 * Tests for Node.js-compatible utility functions.
 * Canvas/Blob functions are browser-only and tested in E2E.
 */

import { describe, it, expect } from "vitest";
import {
  formatFrameNumber,
  generateFilename,
  isBrowserFormat,
  getFormatInfo,
} from "@/services/export/frameSequenceExporter";

describe("formatFrameNumber", () => {
  it("pads frame number to specified digits", () => {
    expect(formatFrameNumber("frame_{frame:04d}", 5)).toBe("frame_0005");
    expect(formatFrameNumber("frame_{frame:04d}", 123)).toBe("frame_0123");
    expect(formatFrameNumber("frame_{frame:04d}", 12345)).toBe("frame_12345"); // Exceeds padding
  });

  it("handles different padding widths", () => {
    expect(formatFrameNumber("f_{frame:02d}", 5)).toBe("f_05");
    expect(formatFrameNumber("f_{frame:06d}", 5)).toBe("f_000005");
    expect(formatFrameNumber("f_{frame:08d}", 12345)).toBe("f_00012345");
  });

  it("handles zero frame number", () => {
    expect(formatFrameNumber("frame_{frame:04d}", 0)).toBe("frame_0000");
  });

  it("returns pattern unchanged if no placeholder", () => {
    expect(formatFrameNumber("static_name", 42)).toBe("static_name");
  });

  it("handles multiple placeholders", () => {
    expect(formatFrameNumber("{frame:02d}_{frame:04d}", 7)).toBe("07_0007");
  });
});

describe("generateFilename", () => {
  it("appends correct extension", () => {
    expect(generateFilename("frame_{frame:04d}", 1, "png")).toBe("frame_0001.png");
    expect(generateFilename("frame_{frame:04d}", 1, "jpeg")).toBe("frame_0001.jpeg");
    expect(generateFilename("frame_{frame:04d}", 1, "webp")).toBe("frame_0001.webp");
    expect(generateFilename("frame_{frame:04d}", 1, "exr")).toBe("frame_0001.exr");
  });

  it("works with various patterns", () => {
    expect(generateFilename("shot_A_{frame:05d}", 42, "png")).toBe("shot_A_00042.png");
    expect(generateFilename("render", 1, "png")).toBe("render.png");
  });
});

describe("isBrowserFormat", () => {
  it("returns true for browser formats", () => {
    expect(isBrowserFormat("png")).toBe(true);
    expect(isBrowserFormat("jpeg")).toBe(true);
    expect(isBrowserFormat("webp")).toBe(true);
  });

  it("returns false for backend formats", () => {
    expect(isBrowserFormat("tiff")).toBe(false);
    expect(isBrowserFormat("exr")).toBe(false);
    expect(isBrowserFormat("dpx")).toBe(false);
  });
});

describe("getFormatInfo", () => {
  it("returns correct info for PNG", () => {
    const info = getFormatInfo("png");
    expect(info.name).toBe("PNG");
    expect(info.extension).toBe("png");
    expect(info.requiresBackend).toBe(false);
    expect(info.supportsAlpha).toBe(true);
    expect(info.lossy).toBe(false);
  });

  it("returns correct info for JPEG", () => {
    const info = getFormatInfo("jpeg");
    expect(info.name).toBe("JPEG");
    expect(info.extension).toBe("jpg"); // Note: extension is jpg, not jpeg
    expect(info.requiresBackend).toBe(false);
    expect(info.supportsAlpha).toBe(false);
    expect(info.lossy).toBe(true);
  });

  it("returns correct info for EXR", () => {
    const info = getFormatInfo("exr");
    expect(info.name).toBe("OpenEXR");
    expect(info.requiresBackend).toBe(true);
    expect(info.bitDepths).toContain(16);
    expect(info.bitDepths).toContain(32);
  });

  it("returns correct info for DPX", () => {
    const info = getFormatInfo("dpx");
    expect(info.name).toBe("DPX");
    expect(info.requiresBackend).toBe(true);
    expect(info.bitDepths).toContain(10);
    expect(info.supportsAlpha).toBe(false);
  });

  it("returns correct info for all formats", () => {
    const formats = ["png", "jpeg", "webp", "tiff", "exr", "dpx"] as const;
    
    for (const format of formats) {
      const info = getFormatInfo(format);
      expect(info.name).toBeTruthy();
      expect(info.extension).toBeTruthy();
      expect(typeof info.requiresBackend).toBe("boolean");
      expect(typeof info.supportsAlpha).toBe("boolean");
      expect(typeof info.lossy).toBe("boolean");
      expect(info.bitDepths.length).toBeGreaterThan(0);
    }
  });
});
