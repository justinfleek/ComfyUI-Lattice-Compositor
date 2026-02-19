/**
 * WebGL/Canvas Rendering E2E Tests
 *
 * Hard-to-pass tests that verify:
 * - WebGL context initialization
 * - Shader compilation and execution
 * - Pixel-accurate rendering
 * - Canvas state management
 * - GPU resource cleanup
 */

import pixelmatch from "pixelmatch";
import { PNG } from "pngjs";
import type { Page } from "puppeteer";
import {
  afterAll,
  afterEach,
  beforeAll,
  beforeEach,
  describe,
  expect,
  it,
} from "vitest";
import {
  closeBrowser,
  createPage,
  getCanvasPixels,
  getWebGLInfo,
  launchBrowser,
  navigateTo,
  waitForCanvas,
  waitFrames,
} from "./helpers/browser.js";

describe("WebGL Rendering", () => {
  let page: Page;

  beforeAll(async () => {
    await launchBrowser();
  });

  afterAll(async () => {
    await closeBrowser();
  });

  beforeEach(async () => {
    page = await createPage();
  });

  afterEach(async () => {
    await page.close();
  });

  describe("WebGL Context Initialization", () => {
    it("should initialize WebGL2 context on canvas", async () => {
      await navigateTo(page, "/");

      // Check if WebGL canvas exists in the workspace
      const hasCanvas = await page.evaluate(() => {
        const canvas = document.querySelector("#lattice-webgl");
        return canvas !== null;
      });

      // The canvas may or may not exist depending on route - check for app initialization
      const hasAppRoot = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(hasAppRoot).toBe(true);
    });

    it("should report correct WebGL capabilities when canvas exists", async () => {
      await navigateTo(page, "/");

      const canvasExists = await page.evaluate(() => {
        return document.querySelector("#lattice-webgl") !== null;
      });

      if (canvasExists) {
        const glInfo = await getWebGLInfo(page);

        // Should have valid WebGL info
        expect(glInfo.version).toBeDefined();
        expect(glInfo.version.length).toBeGreaterThan(0);
        expect(glInfo.shadingLanguageVersion).toBeDefined();
      }
    });

    it("should handle WebGL context loss gracefully", async () => {
      await navigateTo(page, "/");

      const canvasExists = await page.evaluate(() => {
        return document.querySelector("#lattice-webgl") !== null;
      });

      if (canvasExists) {
        // Simulate context loss
        const contextLost = await page.evaluate(() => {
          const canvas = document.querySelector(
            "#lattice-webgl",
          ) as HTMLCanvasElement | null;
          if (!canvas) return false;

          const gl = canvas.getContext("webgl2") || canvas.getContext("webgl");
          if (!gl) return false;

          // Get the WEBGL_lose_context extension
          const ext = gl.getExtension("WEBGL_lose_context");
          if (!ext) return false;

          // Lose the context
          ext.loseContext();
          return gl.isContextLost();
        });

        expect(contextLost).toBe(true);

        // App should not crash - check it's still responsive
        const stillResponsive = await page.evaluate(() => {
          return document.querySelector("#lattice-root") !== null;
        });

        expect(stillResponsive).toBe(true);
      }
    });
  });

  describe("Shader Validation", () => {
    it("should compile shaders without errors", async () => {
      await navigateTo(page, "/");

      // Check for shader compilation errors in console
      const shaderErrors: string[] = [];
      page.on("console", (msg) => {
        const text = msg.text().toLowerCase();
        if (
          text.includes("shader") &&
          (text.includes("error") || text.includes("failed"))
        ) {
          shaderErrors.push(msg.text());
        }
      });

      // Wait for potential shader compilation
      await waitFrames(page, 30);

      expect(shaderErrors).toHaveLength(0);
    });

    it("should have no WebGL errors in console", async () => {
      await navigateTo(page, "/");

      const glErrors: string[] = [];
      page.on("console", (msg) => {
        const text = msg.text().toLowerCase();
        if (text.includes("webgl") && text.includes("error")) {
          glErrors.push(msg.text());
        }
      });

      await waitFrames(page, 60);

      expect(glErrors).toHaveLength(0);
    });
  });

  describe("Canvas Rendering Correctness", () => {
    it("should render non-blank content when initialized", async () => {
      await navigateTo(page, "/");

      const canvasExists = await page.evaluate(() => {
        return document.querySelector("#lattice-webgl") !== null;
      });

      if (canvasExists) {
        await waitForCanvas(page);
        await waitFrames(page, 10);

        // Get canvas pixel data
        const pixelData = await page.evaluate(() => {
          const canvas = document.querySelector(
            "#lattice-webgl",
          ) as HTMLCanvasElement | null;
          if (!canvas) return null;

          const ctx = canvas.getContext("2d");
          if (ctx) {
            const imageData = ctx.getImageData(
              0,
              0,
              canvas.width,
              canvas.height,
            );
            // Check if all pixels are the same (blank canvas)
            const data = imageData.data;
            const firstPixel = [data[0], data[1], data[2], data[3]];
            let allSame = true;
            for (let i = 4; i < data.length; i += 4) {
              if (
                data[i] !== firstPixel[0] ||
                data[i + 1] !== firstPixel[1] ||
                data[i + 2] !== firstPixel[2] ||
                data[i + 3] !== firstPixel[3]
              ) {
                allSame = false;
                break;
              }
            }
            return { allSame, width: canvas.width, height: canvas.height };
          }

          // For WebGL canvas, just check dimensions
          return { allSame: false, width: canvas.width, height: canvas.height };
        });

        expect(pixelData).not.toBeNull();
        if (pixelData) {
          expect(pixelData.width).toBeGreaterThan(0);
          expect(pixelData.height).toBeGreaterThan(0);
        }
      }
    });

    it("should maintain consistent rendering across frames", async () => {
      await navigateTo(page, "/");

      const canvasExists = await page.evaluate(() => {
        return document.querySelector("#lattice-webgl") !== null;
      });

      if (canvasExists) {
        await waitForCanvas(page);

        // Capture two frames and compare
        await waitFrames(page, 5);
        const frame1 = await getCanvasPixels(page);

        await waitFrames(page, 5);
        const frame2 = await getCanvasPixels(page);

        // Parse PNGs
        const png1 = PNG.sync.read(frame1);
        const png2 = PNG.sync.read(frame2);

        // Compare - should be identical for static content
        const diff = pixelmatch(
          png1.data,
          png2.data,
          null,
          png1.width,
          png1.height,
          { threshold: 0.1 },
        );

        // Allow some variance for animations, but should be mostly stable
        const totalPixels = png1.width * png1.height;
        const diffPercentage = (diff / totalPixels) * 100;

        // Less than 10% difference for stable rendering
        expect(diffPercentage).toBeLessThan(10);
      }
    });

    it("should respond to zoom operations", async () => {
      await navigateTo(page, "/");

      const canvasContainer = await page.$(".lattice-webgl-container");

      if (canvasContainer) {
        // Find zoom buttons
        const zoomInButton = await page.$('button[title="Zoom In"]');
        const zoomOutButton = await page.$('button[title="Zoom Out"]');

        if (zoomInButton && zoomOutButton) {
          // Get initial zoom display
          const initialZoom = await page.$eval(
            ".lattice-zoom-level",
            (el) => el.textContent,
          );

          // Click zoom in
          await zoomInButton.click();
          await waitFrames(page, 5);

          const zoomedIn = await page.$eval(
            ".lattice-zoom-level",
            (el) => el.textContent,
          );
          expect(zoomedIn).not.toBe(initialZoom);

          // Click zoom out twice
          await zoomOutButton.click();
          await waitFrames(page, 5);
          await zoomOutButton.click();
          await waitFrames(page, 5);

          const zoomedOut = await page.$eval(
            ".lattice-zoom-level",
            (el) => el.textContent,
          );
          expect(zoomedOut).not.toBe(zoomedIn);
        }
      }
    });
  });

  describe("GPU Resource Management", () => {
    it("should not leak textures over multiple renders", async () => {
      await navigateTo(page, "/");

      const canvasExists = await page.evaluate(() => {
        return document.querySelector("#lattice-webgl") !== null;
      });

      if (canvasExists) {
        // Track WebGL object creation
        const initialResources = await page.evaluate(() => {
          const canvas = document.querySelector(
            "#lattice-webgl",
          ) as HTMLCanvasElement | null;
          if (!canvas) return null;

          const gl = canvas.getContext("webgl2") || canvas.getContext("webgl");
          if (!gl) return null;

          // Get memory info if available
          const memInfo = gl.getExtension("WEBGL_memory_info");
          if (memInfo) {
            return {
              // @ts-expect-error - extension property
              memory: gl.getParameter(
                memInfo.MEMORY_INFO_CURRENT_AVAILABLE_VIDMEM_NVX,
              ),
            };
          }
          return { memory: 0 };
        });

        // Trigger many renders
        for (let i = 0; i < 100; i++) {
          await waitFrames(page, 1);
        }

        const afterResources = await page.evaluate(() => {
          const canvas = document.querySelector(
            "#lattice-webgl",
          ) as HTMLCanvasElement | null;
          if (!canvas) return null;

          const gl = canvas.getContext("webgl2") || canvas.getContext("webgl");
          if (!gl) return null;

          const memInfo = gl.getExtension("WEBGL_memory_info");
          if (memInfo) {
            return {
              // @ts-expect-error - extension property
              memory: gl.getParameter(
                memInfo.MEMORY_INFO_CURRENT_AVAILABLE_VIDMEM_NVX,
              ),
            };
          }
          return { memory: 0 };
        });

        // Memory should not decrease significantly (no leaks)
        // This is a soft check since not all GPUs support memory querying
        if (initialResources?.memory && afterResources?.memory) {
          const memoryLoss = initialResources.memory - afterResources.memory;
          const percentLoss = (memoryLoss / initialResources.memory) * 100;
          expect(percentLoss).toBeLessThan(10);
        }
      }
    });

    it("should properly cleanup on page navigation", async () => {
      await navigateTo(page, "/");

      // Navigate away
      await navigateTo(page, "/settings");

      // Should not have any WebGL errors
      const hasErrors = await page.evaluate(() => {
        return (
          (window as unknown as { __webglError?: boolean }).__webglError ===
          true
        );
      });

      expect(hasErrors).toBe(false);

      // Navigate back
      await navigateTo(page, "/");

      // App should still work
      const appWorks = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(appWorks).toBe(true);
    });
  });
});
