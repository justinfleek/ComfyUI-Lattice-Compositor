/**
 * VACE Control Export Browser Tests
 * 
 * Tests for browser-only VACE rendering:
 * - VACEControlExporter: Renders animated shapes following paths
 * 
 * @requires ComfyUI running at localhost:8188
 * @requires Lattice Compositor extension installed
 */

import { test, expect } from "@playwright/test";
import { openCompositor } from "../helpers/compositor";

test.describe("VACE Control Export - Browser Functions", () => {
  test.beforeEach(async ({ page }) => {
    await openCompositor(page);
  });

  test.describe("VACEControlExporter", () => {
    test("should render path follower on canvas", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { VACEControlExporter, createPathFollower, createVACEExportConfig } = await import(
          "/src/services/export/vaceControlExport"
        );

        const pathFollower = createPathFollower("test", [
          { x: 100, y: 100 },
          { x: 200, y: 100 },
          { x: 200, y: 200 },
          { x: 100, y: 200 },
        ], {
          closed: true,
          shape: "circle",
          size: [30, 30],
          fillColor: "#FF0000",
          duration: 60,
        });

        const config = createVACEExportConfig([pathFollower], {
          width: 256,
          height: 256,
          startFrame: 0,
          endFrame: 60,
        });

        const exporter = new VACEControlExporter(config);
        const frame = await exporter.renderFrame(30); // Middle frame

        const ctx = frame.getContext("2d");
        const imageData = ctx!.getImageData(0, 0, 256, 256);
        
        // Check for red pixels (our shape color)
        let hasRed = false;
        for (let i = 0; i < imageData.data.length; i += 4) {
          if (imageData.data[i] > 200 && imageData.data[i + 1] < 50 && imageData.data[i + 2] < 50) {
            hasRed = true;
            break;
          }
        }

        return { hasRed, width: frame.width, height: frame.height };
      });

      expect(result.hasRed).toBe(true);
      expect(result.width).toBe(256);
      expect(result.height).toBe(256);
    });

    test("should animate shape along path", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { VACEControlExporter, createPathFollower, createVACEExportConfig } = await import(
          "/src/services/export/vaceControlExport"
        );

        const pathFollower = createPathFollower("moving", [
          { x: 50, y: 128 },  // Start left
          { x: 206, y: 128 }, // End right
        ], {
          shape: "circle",
          size: [20, 20],
          fillColor: "#FFFFFF",
          duration: 30,
        });

        const config = createVACEExportConfig([pathFollower], {
          width: 256,
          height: 256,
          startFrame: 0,
          endFrame: 30,
        });

        const exporter = new VACEControlExporter(config);
        
        const frame0 = await exporter.renderFrame(0);
        const frame29 = await exporter.renderFrame(29);

        const getCenterOfMass = (canvas: HTMLCanvasElement) => {
          const ctx = canvas.getContext("2d")!;
          const data = ctx.getImageData(0, 0, 256, 256).data;
          let sumX = 0, sumY = 0, count = 0;
          
          for (let y = 0; y < 256; y++) {
            for (let x = 0; x < 256; x++) {
              const i = (y * 256 + x) * 4;
              if (data[i] > 128) { // White pixel
                sumX += x;
                sumY += y;
                count++;
              }
            }
          }
          
          return count > 0 ? { x: sumX / count, y: sumY / count } : null;
        };

        const center0 = getCenterOfMass(frame0);
        const center29 = getCenterOfMass(frame29);

        return {
          startX: center0?.x,
          endX: center29?.x,
          movedRight: center29!.x > center0!.x + 100,
        };
      });

      expect(result.movedRight).toBe(true);
    });

    test("should render multiple shapes", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { VACEControlExporter, createPathFollower, createVACEExportConfig } = await import(
          "/src/services/export/vaceControlExport"
        );

        const followers = [
          createPathFollower("shape1", [{ x: 50, y: 50 }, { x: 100, y: 50 }], {
            shape: "circle",
            size: [20, 20],
            fillColor: "#FF0000",
            duration: 10,
          }),
          createPathFollower("shape2", [{ x: 200, y: 200 }, { x: 150, y: 200 }], {
            shape: "rectangle",
            size: [30, 30],
            fillColor: "#00FF00",
            duration: 10,
          }),
        ];

        const config = createVACEExportConfig(followers, {
          width: 256,
          height: 256,
          startFrame: 0,
          endFrame: 10,
        });

        const exporter = new VACEControlExporter(config);
        const frame = await exporter.renderFrame(5);

        const ctx = frame.getContext("2d")!;
        const data = ctx.getImageData(0, 0, 256, 256).data;
        
        let hasRed = false, hasGreen = false;
        for (let i = 0; i < data.length; i += 4) {
          if (data[i] > 200 && data[i + 1] < 50) hasRed = true;
          if (data[i + 1] > 200 && data[i] < 50) hasGreen = true;
        }

        return { hasRed, hasGreen, hasBoth: hasRed && hasGreen };
      });

      expect(result.hasBoth).toBe(true);
    });

    test("should export full sequence", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { VACEControlExporter, createPathFollower, createVACEExportConfig } = await import(
          "/src/services/export/vaceControlExport"
        );

        const pathFollower = createPathFollower("test", [
          { x: 50, y: 50 },
          { x: 200, y: 200 },
        ], {
          shape: "circle",
          size: [15, 15],
          fillColor: "#FFFFFF",
          duration: 5,
        });

        const config = createVACEExportConfig([pathFollower], {
          width: 128,
          height: 128,
          startFrame: 0,
          endFrame: 5,
        });

        const exporter = new VACEControlExporter(config);
        const sequence = await exporter.exportSequence();

        return {
          frameCount: sequence.frames.length,
          hasMetadata: !!sequence.metadata,
          allCanvases: sequence.frames.every(f => f instanceof HTMLCanvasElement),
        };
      });

      expect(result.frameCount).toBe(5);
      expect(result.hasMetadata).toBe(true);
      expect(result.allCanvases).toBe(true);
    });

    test("should support different shapes", async ({ page }) => {
      const shapes = ["circle", "rectangle", "triangle", "star"];

      for (const shape of shapes) {
        const result = await page.evaluate(async (shapeType) => {
          const { VACEControlExporter, createPathFollower, createVACEExportConfig } = await import(
            "/src/services/export/vaceControlExport"
          );

          const pathFollower = createPathFollower("test", [{ x: 64, y: 64 }], {
            shape: shapeType as any,
            size: [40, 40],
            fillColor: "#FFFFFF",
            duration: 1,
          });

          const config = createVACEExportConfig([pathFollower], {
            width: 128,
            height: 128,
            startFrame: 0,
            endFrame: 1,
          });

          const exporter = new VACEControlExporter(config);
          const frame = await exporter.renderFrame(0);

          const ctx = frame.getContext("2d")!;
          const data = ctx.getImageData(0, 0, 128, 128).data;
          
          let pixelCount = 0;
          for (let i = 0; i < data.length; i += 4) {
            if (data[i] > 128) pixelCount++;
          }

          return { shape: shapeType, hasPixels: pixelCount > 0, pixelCount };
        }, shape);

        expect(result.hasPixels).toBe(true);
      }
    });

    test("should handle easing functions", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { VACEControlExporter, createPathFollower, createVACEExportConfig } = await import(
          "/src/services/export/vaceControlExport"
        );

        const linearFollower = createPathFollower("linear", [
          { x: 0, y: 64 },
          { x: 128, y: 64 },
        ], {
          shape: "circle",
          size: [10, 10],
          fillColor: "#FFFFFF",
          duration: 10,
          easing: "linear",
        });

        const easeFollower = createPathFollower("ease", [
          { x: 0, y: 64 },
          { x: 128, y: 64 },
        ], {
          shape: "circle",
          size: [10, 10],
          fillColor: "#FFFFFF",
          duration: 10,
          easing: "ease-in-out",
        });

        const linearConfig = createVACEExportConfig([linearFollower], {
          width: 128,
          height: 128,
          startFrame: 0,
          endFrame: 10,
        });

        const easeConfig = createVACEExportConfig([easeFollower], {
          width: 128,
          height: 128,
          startFrame: 0,
          endFrame: 10,
        });

        const linearExporter = new VACEControlExporter(linearConfig);
        const easeExporter = new VACEControlExporter(easeConfig);

        // At frame 5 (midpoint), ease-in-out should be at different position than linear
        const linearFrame = await linearExporter.renderFrame(2); // Early frame
        const easeFrame = await easeExporter.renderFrame(2);

        const getCenterX = (canvas: HTMLCanvasElement) => {
          const ctx = canvas.getContext("2d")!;
          const data = ctx.getImageData(0, 0, 128, 128).data;
          let sumX = 0, count = 0;
          for (let x = 0; x < 128; x++) {
            for (let y = 0; y < 128; y++) {
              const i = (y * 128 + x) * 4;
              if (data[i] > 128) { sumX += x; count++; }
            }
          }
          return count > 0 ? sumX / count : 0;
        };

        const linearX = getCenterX(linearFrame);
        const easeX = getCenterX(easeFrame);

        return {
          linearX,
          easeX,
          areDifferent: Math.abs(linearX - easeX) > 1,
        };
      });

      // Easing should produce different positions at early frames
      expect(result.areDifferent).toBe(true);
    });
  });
});
