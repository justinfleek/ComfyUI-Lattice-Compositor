/**
 * Camera Export Browser Tests
 * 
 * Tests for browser-only camera export:
 * - downloadFile: Triggers browser download
 * 
 * @requires ComfyUI running at localhost:8188
 * @requires Lattice Compositor extension installed
 */

import { test, expect } from "@playwright/test";
import { openCompositor } from "../helpers/compositor";

test.describe("Camera Export - Browser Functions", () => {
  test.beforeEach(async ({ page }) => {
    await openCompositor(page);
  });

  test.describe("downloadFile", () => {
    test("should create download link with correct attributes", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { downloadFile } = await import(
          "/src/services/export/cameraExport"
        );

        // Mock the click to prevent actual download
        let downloadTriggered = false;
        let downloadFilename = "";
        let downloadHref = "";

        const originalCreateElement = document.createElement.bind(document);
        document.createElement = (tagName: string) => {
          const el = originalCreateElement(tagName);
          if (tagName === "a") {
            el.click = () => {
              downloadTriggered = true;
              downloadFilename = el.getAttribute("download") || "";
              downloadHref = el.getAttribute("href") || "";
            };
          }
          return el;
        };

        const jsonData = JSON.stringify({ test: "data" });
        downloadFile(jsonData, "camera_export.json", "application/json");

        return {
          downloadTriggered,
          downloadFilename,
          hasHref: downloadHref.length > 0,
        };
      });

      expect(result.downloadTriggered).toBe(true);
      expect(result.downloadFilename).toBe("camera_export.json");
      expect(result.hasHref).toBe(true);
    });

    test("should create blob URL for content", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { downloadFile } = await import(
          "/src/services/export/cameraExport"
        );

        let blobUrl = "";
        const originalCreateObjectURL = URL.createObjectURL;
        URL.createObjectURL = (blob: Blob) => {
          blobUrl = originalCreateObjectURL(blob);
          return blobUrl;
        };

        const originalCreateElement = document.createElement.bind(document);
        document.createElement = (tagName: string) => {
          const el = originalCreateElement(tagName);
          if (tagName === "a") {
            el.click = () => {}; // Prevent actual download
          }
          return el;
        };

        downloadFile("test content", "test.txt", "text/plain");

        return {
          hasBlobUrl: blobUrl.startsWith("blob:"),
        };
      });

      expect(result.hasBlobUrl).toBe(true);
    });

    test("should handle different content types", async ({ page }) => {
      const contentTypes = [
        { content: '{"key": "value"}', filename: "data.json", type: "application/json" },
        { content: "plain text", filename: "data.txt", type: "text/plain" },
        { content: "<script>code</script>", filename: "script.jsx", type: "text/javascript" },
      ];

      for (const { content, filename, type } of contentTypes) {
        const result = await page.evaluate(async ({ content, filename, type }) => {
          const { downloadFile } = await import(
            "/src/services/export/cameraExport"
          );

          let usedType = "";
          const originalBlob = window.Blob;
          window.Blob = class extends originalBlob {
            constructor(parts: BlobPart[], options?: BlobPropertyBag) {
              super(parts, options);
              usedType = options?.type || "";
            }
          } as any;

          const originalCreateElement = document.createElement.bind(document);
          document.createElement = (tagName: string) => {
            const el = originalCreateElement(tagName);
            if (tagName === "a") el.click = () => {};
            return el;
          };

          downloadFile(content, filename, type);
          window.Blob = originalBlob;

          return { usedType };
        }, { content, filename, type });

        expect(result.usedType).toBe(type);
      }
    });

    test("should revoke blob URL after download", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { downloadFile } = await import(
          "/src/services/export/cameraExport"
        );

        let revokedUrl = "";
        const originalRevokeObjectURL = URL.revokeObjectURL;
        URL.revokeObjectURL = (url: string) => {
          revokedUrl = url;
          originalRevokeObjectURL(url);
        };

        const originalCreateElement = document.createElement.bind(document);
        document.createElement = (tagName: string) => {
          const el = originalCreateElement(tagName);
          if (tagName === "a") el.click = () => {};
          return el;
        };

        downloadFile("test", "test.txt", "text/plain");

        return { wasRevoked: revokedUrl.length > 0 };
      });

      expect(result.wasRevoked).toBe(true);
    });
  });
});
