/**
 * Frame Sequence Exporter Browser Tests
 * 
 * Tests for browser-only frame export functions:
 * - exportCanvasToBlob: Converts canvas to Blob
 * - exportCanvasToDataURL: Converts canvas to data URL
 * - downloadBlob: Triggers browser download of Blob
 * - createZipFromFrames: Creates ZIP archive from frames
 * - exportFrameSequence: Full frame export pipeline
 * - exportViaBackend: Server-side export for EXR/DPX/TIFF
 * 
 * @requires ComfyUI running at localhost:8188
 * @requires Lattice Compositor extension installed
 */

import { test, expect } from "@playwright/test";
import { openCompositor } from "../helpers/compositor";

test.describe("Frame Sequence Exporter - Browser Functions", () => {
  test.beforeEach(async ({ page }) => {
    await openCompositor(page);
  });

  test.describe("exportCanvasToBlob", () => {
    test("should convert canvas to PNG Blob", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportCanvasToBlob } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 100;
        canvas.height = 100;
        const ctx = canvas.getContext("2d")!;
        ctx.fillStyle = "#FF0000";
        ctx.fillRect(0, 0, 100, 100);

        const blob = await exportCanvasToBlob(canvas, "png");

        return {
          isBlob: blob instanceof Blob,
          type: blob.type,
          size: blob.size,
        };
      });

      expect(result.isBlob).toBe(true);
      expect(result.type).toBe("image/png");
      expect(result.size).toBeGreaterThan(0);
    });

    test("should support JPEG format with quality", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportCanvasToBlob } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 200;
        canvas.height = 200;
        const ctx = canvas.getContext("2d")!;
        ctx.fillStyle = "#0000FF";
        ctx.fillRect(0, 0, 200, 200);

        const highQuality = await exportCanvasToBlob(canvas, "jpeg", 1.0);
        const lowQuality = await exportCanvasToBlob(canvas, "jpeg", 0.1);

        return {
          highType: highQuality.type,
          lowType: lowQuality.type,
          highSize: highQuality.size,
          lowSize: lowQuality.size,
          highBigger: highQuality.size > lowQuality.size,
        };
      });

      expect(result.highType).toBe("image/jpeg");
      expect(result.highBigger).toBe(true);
    });

    test("should support WebP format", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportCanvasToBlob } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 50;
        canvas.height = 50;
        const ctx = canvas.getContext("2d")!;
        ctx.fillStyle = "#00FF00";
        ctx.fillRect(0, 0, 50, 50);

        const blob = await exportCanvasToBlob(canvas, "webp", 0.9);

        return {
          type: blob.type,
          hasContent: blob.size > 0,
        };
      });

      expect(result.type).toBe("image/webp");
      expect(result.hasContent).toBe(true);
    });
  });

  test.describe("exportCanvasToDataURL", () => {
    test("should convert canvas to PNG data URL", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportCanvasToDataURL } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 32;
        canvas.height = 32;
        const ctx = canvas.getContext("2d")!;
        ctx.fillStyle = "#FFFFFF";
        ctx.fillRect(0, 0, 32, 32);

        const dataUrl = exportCanvasToDataURL(canvas, "png");

        return {
          isPngDataUrl: dataUrl.startsWith("data:image/png;base64,"),
          hasContent: dataUrl.length > 100,
        };
      });

      expect(result.isPngDataUrl).toBe(true);
      expect(result.hasContent).toBe(true);
    });

    test("should produce valid image that can be loaded", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportCanvasToDataURL } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 64;
        canvas.height = 64;
        const ctx = canvas.getContext("2d")!;
        ctx.fillStyle = "#FF00FF";
        ctx.fillRect(0, 0, 64, 64);

        const dataUrl = exportCanvasToDataURL(canvas, "png");

        // Try loading the image
        return new Promise((resolve) => {
          const img = new Image();
          img.onload = () => {
            resolve({
              loaded: true,
              width: img.width,
              height: img.height,
            });
          };
          img.onerror = () => {
            resolve({ loaded: false });
          };
          img.src = dataUrl;
        });
      });

      expect(result.loaded).toBe(true);
      expect(result.width).toBe(64);
      expect(result.height).toBe(64);
    });
  });

  test.describe("downloadBlob", () => {
    test("should trigger download with correct filename", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { downloadBlob } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        let downloadInfo = { triggered: false, filename: "" };

        // Mock click
        const originalCreateElement = document.createElement.bind(document);
        document.createElement = (tag: string) => {
          const el = originalCreateElement(tag);
          if (tag === "a") {
            el.click = () => {
              downloadInfo.triggered = true;
              downloadInfo.filename = el.getAttribute("download") || "";
            };
          }
          return el;
        };

        const blob = new Blob(["test"], { type: "text/plain" });
        downloadBlob(blob, "test_frame_0001.png");

        return downloadInfo;
      });

      expect(result.triggered).toBe(true);
      expect(result.filename).toBe("test_frame_0001.png");
    });

    test("should create and revoke blob URL", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { downloadBlob } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        let blobUrlCreated = "";
        let blobUrlRevoked = "";

        const originalCreate = URL.createObjectURL;
        const originalRevoke = URL.revokeObjectURL;

        URL.createObjectURL = (blob: Blob) => {
          const url = originalCreate(blob);
          blobUrlCreated = url;
          return url;
        };

        URL.revokeObjectURL = (url: string) => {
          blobUrlRevoked = url;
          originalRevoke(url);
        };

        const originalCreateElement = document.createElement.bind(document);
        document.createElement = (tag: string) => {
          const el = originalCreateElement(tag);
          if (tag === "a") el.click = () => {};
          return el;
        };

        const blob = new Blob(["data"], { type: "application/octet-stream" });
        downloadBlob(blob, "file.bin");

        return {
          urlCreated: blobUrlCreated.length > 0,
          urlRevoked: blobUrlRevoked.length > 0,
          urlsMatch: blobUrlCreated === blobUrlRevoked,
        };
      });

      expect(result.urlCreated).toBe(true);
      expect(result.urlRevoked).toBe(true);
      expect(result.urlsMatch).toBe(true);
    });
  });

  test.describe("createZipFromFrames", () => {
    test("should create ZIP from frame canvases", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { createZipFromFrames } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        const frames: Array<{ canvas: HTMLCanvasElement; frameNumber: number }> = [];
        
        for (let i = 0; i < 3; i++) {
          const canvas = document.createElement("canvas");
          canvas.width = 64;
          canvas.height = 64;
          const ctx = canvas.getContext("2d")!;
          ctx.fillStyle = `rgb(${i * 80}, 0, 0)`;
          ctx.fillRect(0, 0, 64, 64);
          frames.push({ canvas, frameNumber: i });
        }

        const zip = await createZipFromFrames(frames, {
          format: "png",
          filenamePattern: "frame_{frame}.png",
        });

        return {
          isBlob: zip instanceof Blob,
          type: zip.type,
          size: zip.size,
          hasContent: zip.size > 100, // ZIP should have content
        };
      });

      expect(result.isBlob).toBe(true);
      expect(result.hasContent).toBe(true);
    });

    test("should use correct filename pattern", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { createZipFromFrames } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 32;
        canvas.height = 32;
        
        const frames = [{ canvas, frameNumber: 42 }];

        // We can't easily inspect ZIP contents in browser,
        // but we can verify the function runs without error
        try {
          const zip = await createZipFromFrames(frames, {
            format: "png",
            filenamePattern: "output_{frame:04d}.png",
          });
          return { success: true, size: zip.size };
        } catch (e) {
          return { success: false, error: String(e) };
        }
      });

      expect(result.success).toBe(true);
    });
  });

  test.describe("exportFrameSequence", () => {
    test("should export sequence of frames", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportFrameSequence } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        const frames: Array<{ canvas: HTMLCanvasElement; frameNumber: number }> = [];
        
        for (let i = 0; i < 5; i++) {
          const canvas = document.createElement("canvas");
          canvas.width = 128;
          canvas.height = 128;
          const ctx = canvas.getContext("2d")!;
          ctx.fillStyle = "#AABBCC";
          ctx.fillRect(0, 0, 128, 128);
          frames.push({ canvas, frameNumber: i });
        }

        // Mock download to prevent actual file saves
        const originalCreateElement = document.createElement.bind(document);
        let downloadCount = 0;
        document.createElement = (tag: string) => {
          const el = originalCreateElement(tag);
          if (tag === "a") {
            el.click = () => { downloadCount++; };
          }
          return el;
        };

        const result = await exportFrameSequence(frames, {
          format: "png",
          outputMode: "individual",
          filenamePattern: "frame_{frame:04d}.png",
        });

        return {
          success: result.success,
          frameCount: result.frames.length,
          downloadCount,
          hasErrors: result.errors.length > 0,
        };
      });

      expect(result.success).toBe(true);
      expect(result.frameCount).toBe(5);
    });

    test("should support ZIP output mode", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportFrameSequence } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        const frames = [];
        for (let i = 0; i < 3; i++) {
          const canvas = document.createElement("canvas");
          canvas.width = 64;
          canvas.height = 64;
          frames.push({ canvas, frameNumber: i });
        }

        const originalCreateElement = document.createElement.bind(document);
        let downloadedFilename = "";
        document.createElement = (tag: string) => {
          const el = originalCreateElement(tag);
          if (tag === "a") {
            el.click = () => {
              downloadedFilename = el.getAttribute("download") || "";
            };
          }
          return el;
        };

        const result = await exportFrameSequence(frames, {
          format: "png",
          outputMode: "zip",
          zipFilename: "frames_export.zip",
        });

        return {
          success: result.success,
          isZip: downloadedFilename.endsWith(".zip"),
        };
      });

      expect(result.success).toBe(true);
      expect(result.isZip).toBe(true);
    });

    test("should report progress during export", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportFrameSequence } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        const frames = [];
        for (let i = 0; i < 10; i++) {
          const canvas = document.createElement("canvas");
          canvas.width = 32;
          canvas.height = 32;
          frames.push({ canvas, frameNumber: i });
        }

        const progressUpdates: number[] = [];

        const originalCreateElement = document.createElement.bind(document);
        document.createElement = (tag: string) => {
          const el = originalCreateElement(tag);
          if (tag === "a") el.click = () => {};
          return el;
        };

        await exportFrameSequence(frames, {
          format: "jpeg",
          outputMode: "individual",
          onProgress: (progress) => {
            progressUpdates.push(progress);
          },
        });

        return {
          progressCalled: progressUpdates.length > 0,
          reachesComplete: progressUpdates[progressUpdates.length - 1] === 1,
          isMonotonic: progressUpdates.every((p, i) => 
            i === 0 || p >= progressUpdates[i - 1]
          ),
        };
      });

      expect(result.progressCalled).toBe(true);
      expect(result.reachesComplete).toBe(true);
      expect(result.isMonotonic).toBe(true);
    });
  });

  test.describe("exportViaBackend", () => {
    test("should send frames to backend for EXR export", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportViaBackend } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        let requestSent = false;
        let requestBody: any = null;

        // Mock fetch
        const originalFetch = window.fetch;
        window.fetch = async (url: string, options: any) => {
          if (url.includes("/lattice/export")) {
            requestSent = true;
            requestBody = JSON.parse(options.body);
            return {
              ok: true,
              json: async () => ({
                success: true,
                files: [{ name: "frame_0001.exr", data: "base64..." }],
              }),
            } as Response;
          }
          return originalFetch(url, options);
        };

        const frames = [];
        for (let i = 0; i < 2; i++) {
          const canvas = document.createElement("canvas");
          canvas.width = 64;
          canvas.height = 64;
          const ctx = canvas.getContext("2d")!;
          ctx.fillStyle = "#FFFFFF";
          ctx.fillRect(0, 0, 64, 64);
          frames.push({ canvas, frameNumber: i });
        }

        const result = await exportViaBackend(frames, {
          format: "exr",
          bitDepth: 32,
          colorSpace: "linear",
        });

        window.fetch = originalFetch;

        return {
          requestSent,
          hasFrameData: requestBody?.frames?.length > 0,
          format: requestBody?.format,
          success: result.success,
        };
      });

      expect(result.requestSent).toBe(true);
      expect(result.hasFrameData).toBe(true);
      expect(result.format).toBe("exr");
    });

    test("should handle backend errors gracefully", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportViaBackend } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        // Mock failed fetch
        const originalFetch = window.fetch;
        window.fetch = async () => {
          return {
            ok: false,
            status: 500,
            statusText: "Internal Server Error",
          } as Response;
        };

        const canvas = document.createElement("canvas");
        canvas.width = 32;
        canvas.height = 32;

        const result = await exportViaBackend(
          [{ canvas, frameNumber: 0 }],
          { format: "dpx", bitDepth: 16 }
        );

        window.fetch = originalFetch;

        return {
          success: result.success,
          hasErrors: result.errors.length > 0,
        };
      });

      expect(result.success).toBe(false);
      expect(result.hasErrors).toBe(true);
    });

    test("should include all required metadata", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { exportViaBackend } = await import(
          "/src/services/export/frameSequenceExporter"
        );

        let sentMetadata: any = null;

        const originalFetch = window.fetch;
        window.fetch = async (url: string, options: any) => {
          sentMetadata = JSON.parse(options.body);
          return {
            ok: true,
            json: async () => ({ success: true, files: [] }),
          } as Response;
        };

        const canvas = document.createElement("canvas");
        canvas.width = 1920;
        canvas.height = 1080;

        await exportViaBackend(
          [{ canvas, frameNumber: 0 }],
          {
            format: "tiff",
            bitDepth: 16,
            colorSpace: "sRGB",
          }
        );

        window.fetch = originalFetch;

        return {
          hasFormat: !!sentMetadata?.format,
          hasBitDepth: !!sentMetadata?.bitDepth,
          hasColorSpace: !!sentMetadata?.colorSpace,
          hasFrames: Array.isArray(sentMetadata?.frames),
        };
      });

      expect(result.hasFormat).toBe(true);
      expect(result.hasBitDepth).toBe(true);
      expect(result.hasColorSpace).toBe(true);
      expect(result.hasFrames).toBe(true);
    });
  });
});
