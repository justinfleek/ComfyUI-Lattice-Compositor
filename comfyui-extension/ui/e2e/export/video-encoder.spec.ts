/**
 * Video Encoder Browser Tests
 * 
 * Tests for ACTUAL exports in videoEncoder.ts:
 * - isWebCodecsSupported
 * - getSupportedCodecs
 * - WebCodecsVideoEncoder class
 * - encodeFrameSequence
 * - encodeFromGenerator
 * - downloadVideo
 * 
 * @requires ComfyUI running at localhost:8188
 * @requires Browser with WebCodecs support (Chrome 94+)
 */

import { test, expect } from "@playwright/test";
import { openCompositor } from "../helpers/compositor";

test.describe("Video Encoder - Browser Functions", () => {
  test.beforeEach(async ({ page }) => {
    await openCompositor(page);
  });

  test.describe("isWebCodecsSupported", () => {
    test("should return boolean indicating WebCodecs support", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { isWebCodecsSupported } = await import(
          "/src/services/export/videoEncoder"
        );

        const supported = isWebCodecsSupported();

        return {
          isBoolean: typeof supported === "boolean",
          value: supported,
        };
      });

      expect(result.isBoolean).toBe(true);
    });
  });

  test.describe("getSupportedCodecs", () => {
    test("should return array of codec strings", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { getSupportedCodecs } = await import(
          "/src/services/export/videoEncoder"
        );

        const codecs = await getSupportedCodecs();

        return {
          isArray: Array.isArray(codecs),
          length: codecs.length,
          allStrings: codecs.every(c => typeof c === "string"),
        };
      });

      expect(result.isArray).toBe(true);
      expect(result.allStrings).toBe(true);
    });
  });

  test.describe("WebCodecsVideoEncoder class", () => {
    test("should create encoder instance", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { WebCodecsVideoEncoder, isWebCodecsSupported } = await import(
          "/src/services/export/videoEncoder"
        );

        if (!isWebCodecsSupported()) {
          return { skipped: true, reason: "WebCodecs not supported" };
        }

        try {
          const encoder = new WebCodecsVideoEncoder({
            width: 128,
            height: 128,
            frameRate: 30,
            bitrate: 1_000_000,
          });

          return {
            isInstance: encoder instanceof WebCodecsVideoEncoder,
            hasEncode: typeof encoder.encode === "function",
            hasFinish: typeof encoder.finish === "function",
          };
        } catch (e) {
          return { error: String(e) };
        }
      });

      if (result.skipped) {
        test.skip();
        return;
      }

      expect(result.isInstance).toBe(true);
    });

    test("should encode canvas frame", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { WebCodecsVideoEncoder, isWebCodecsSupported } = await import(
          "/src/services/export/videoEncoder"
        );

        if (!isWebCodecsSupported()) {
          return { skipped: true };
        }

        try {
          const encoder = new WebCodecsVideoEncoder({
            width: 64,
            height: 64,
            frameRate: 30,
            bitrate: 500_000,
          });

          const canvas = document.createElement("canvas");
          canvas.width = 64;
          canvas.height = 64;
          const ctx = canvas.getContext("2d")!;
          ctx.fillStyle = "#FF0000";
          ctx.fillRect(0, 0, 64, 64);

          await encoder.encode(canvas, 0);
          
          return { encoded: true };
        } catch (e) {
          return { error: String(e) };
        }
      });

      if (result.skipped) {
        test.skip();
        return;
      }

      expect(result.encoded).toBe(true);
    });

    test("should finish encoding and return video", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { WebCodecsVideoEncoder, isWebCodecsSupported } = await import(
          "/src/services/export/videoEncoder"
        );

        if (!isWebCodecsSupported()) {
          return { skipped: true };
        }

        try {
          const encoder = new WebCodecsVideoEncoder({
            width: 64,
            height: 64,
            frameRate: 30,
            bitrate: 500_000,
          });

          const canvas = document.createElement("canvas");
          canvas.width = 64;
          canvas.height = 64;

          await encoder.encode(canvas, 0);
          await encoder.encode(canvas, 1);
          
          const video = await encoder.finish();
          
          return {
            hasBlob: video.blob instanceof Blob,
            hasDuration: typeof video.duration === "number",
          };
        } catch (e) {
          return { error: String(e) };
        }
      });

      if (result.skipped) {
        test.skip();
        return;
      }

      expect(result.hasBlob).toBe(true);
    });
  });

  test.describe("encodeFrameSequence", () => {
    test("should encode array of canvases", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { encodeFrameSequence, isWebCodecsSupported } = await import(
          "/src/services/export/videoEncoder"
        );

        if (!isWebCodecsSupported()) {
          return { skipped: true };
        }

        const frames: HTMLCanvasElement[] = [];
        for (let i = 0; i < 3; i++) {
          const canvas = document.createElement("canvas");
          canvas.width = 64;
          canvas.height = 64;
          frames.push(canvas);
        }

        try {
          const video = await encodeFrameSequence(frames, {
            width: 64,
            height: 64,
            frameRate: 30,
            bitrate: 500_000,
          });

          return {
            hasBlob: video.blob instanceof Blob,
            blobSize: video.blob.size,
          };
        } catch (e) {
          return { error: String(e) };
        }
      });

      if (result.skipped) {
        test.skip();
        return;
      }

      expect(result.hasBlob).toBe(true);
    });
  });

  test.describe("encodeFromGenerator", () => {
    test("should encode frames from async generator", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { encodeFromGenerator, isWebCodecsSupported } = await import(
          "/src/services/export/videoEncoder"
        );

        if (!isWebCodecsSupported()) {
          return { skipped: true };
        }

        async function* frameGenerator() {
          for (let i = 0; i < 3; i++) {
            const canvas = document.createElement("canvas");
            canvas.width = 64;
            canvas.height = 64;
            yield canvas;
          }
        }

        try {
          const video = await encodeFromGenerator(frameGenerator(), {
            width: 64,
            height: 64,
            frameRate: 30,
            bitrate: 500_000,
          });

          return {
            hasBlob: video.blob instanceof Blob,
          };
        } catch (e) {
          return { error: String(e) };
        }
      });

      if (result.skipped) {
        test.skip();
        return;
      }

      expect(result.hasBlob).toBe(true);
    });
  });

  test.describe("downloadVideo", () => {
    test("should trigger download with correct filename", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { downloadVideo } = await import(
          "/src/services/export/videoEncoder"
        );

        let downloadTriggered = false;
        let downloadFilename = "";

        const originalCreateElement = document.createElement.bind(document);
        document.createElement = (tag: string) => {
          const el = originalCreateElement(tag);
          if (tag === "a") {
            el.click = () => {
              downloadTriggered = true;
              downloadFilename = el.getAttribute("download") || "";
            };
          }
          return el;
        };

        const fakeVideo = {
          blob: new Blob(["fake"], { type: "video/mp4" }),
          duration: 1,
          width: 64,
          height: 64,
        };

        downloadVideo(fakeVideo, "test_video.mp4");

        return {
          downloadTriggered,
          downloadFilename,
        };
      });

      expect(result.downloadTriggered).toBe(true);
      expect(result.downloadFilename).toBe("test_video.mp4");
    });
  });
});
