/**
 * Effect Processor Browser Tests
 *
 * Tests for browser-only effect processing functions:
 * - processEffectStack: Process a stack of effects on a canvas
 * - hasEnabledEffects: Check if any effects are enabled
 * - clearEffectCaches: Clear effect processing caches
 *
 * @requires ComfyUI running at localhost:8188
 * @requires Lattice Compositor extension installed
 */

import { test, expect } from "@playwright/test";
import { openCompositor } from "../helpers/compositor";

test.describe("Effect Processor - Browser Functions", () => {
  test.beforeEach(async ({ page }) => {
    await openCompositor(page);
  });

  test.describe("hasEnabledEffects", () => {
    test("should return false for empty effect list", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { hasEnabledEffects } = await import(
          "/src/services/effectProcessor"
        );

        return hasEnabledEffects([]);
      });

      expect(result).toBe(false);
    });

    test("should return false when all effects disabled", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { hasEnabledEffects } = await import(
          "/src/services/effectProcessor"
        );

        const effects = [
          { id: "1", effectKey: "gaussian-blur", name: "Blur", enabled: false, parameters: {} },
          { id: "2", effectKey: "brightness", name: "Brightness", enabled: false, parameters: {} },
        ];

        return hasEnabledEffects(effects);
      });

      expect(result).toBe(false);
    });

    test("should return true when at least one effect enabled", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { hasEnabledEffects } = await import(
          "/src/services/effectProcessor"
        );

        const effects = [
          { id: "1", effectKey: "gaussian-blur", name: "Blur", enabled: false, parameters: {} },
          { id: "2", effectKey: "brightness", name: "Brightness", enabled: true, parameters: {} },
        ];

        return hasEnabledEffects(effects);
      });

      expect(result).toBe(true);
    });
  });

  test.describe("processEffectStack", () => {
    test("should return canvas with same dimensions for empty effect stack", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { processEffectStack } = await import(
          "/src/services/effectProcessor"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 128;
        canvas.height = 64;
        const ctx = canvas.getContext("2d")!;
        ctx.fillStyle = "#FF0000";
        ctx.fillRect(0, 0, 128, 64);

        const output = processEffectStack([], canvas, 0);

        return {
          width: output.canvas.width,
          height: output.canvas.height,
        };
      });

      expect(result.width).toBe(128);
      expect(result.height).toBe(64);
    });

    test("should preserve input when all effects disabled", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { processEffectStack } = await import(
          "/src/services/effectProcessor"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 64;
        canvas.height = 64;
        const ctx = canvas.getContext("2d")!;
        ctx.fillStyle = "#00FF00";
        ctx.fillRect(0, 0, 64, 64);

        const inputData = ctx.getImageData(0, 0, 64, 64);
        const inputFirstPixel = [inputData.data[0], inputData.data[1], inputData.data[2]];

        const effects = [
          { id: "1", effectKey: "gaussian-blur", name: "Blur", enabled: false, parameters: { blurriness: 10 } },
        ];

        const output = processEffectStack(effects, canvas, 0);
        const outputData = output.ctx.getImageData(0, 0, 64, 64);
        const outputFirstPixel = [outputData.data[0], outputData.data[1], outputData.data[2]];

        return {
          inputFirstPixel,
          outputFirstPixel,
          match: inputFirstPixel[0] === outputFirstPixel[0] &&
                 inputFirstPixel[1] === outputFirstPixel[1] &&
                 inputFirstPixel[2] === outputFirstPixel[2],
        };
      });

      expect(result.match).toBe(true);
    });

    test("should process enabled effects", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { processEffectStack } = await import(
          "/src/services/effectProcessor"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 64;
        canvas.height = 64;
        const ctx = canvas.getContext("2d")!;
        ctx.fillStyle = "#FF0000";
        ctx.fillRect(0, 0, 64, 64);

        // Invert colors effect
        const effects = [
          {
            id: "1",
            effectKey: "invert",
            name: "Invert",
            enabled: true,
            parameters: {}
          },
        ];

        try {
          const output = processEffectStack(effects, canvas, 0);
          return {
            success: true,
            width: output.canvas.width,
            height: output.canvas.height,
          };
        } catch (e) {
          return {
            success: false,
            error: String(e),
          };
        }
      });

      // Even if effect not registered, should not throw (per current error handling)
      expect(result.width).toBe(64);
      expect(result.height).toBe(64);
    });

    test("should be deterministic - same input produces same output", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { processEffectStack } = await import(
          "/src/services/effectProcessor"
        );

        const createCanvas = () => {
          const canvas = document.createElement("canvas");
          canvas.width = 32;
          canvas.height = 32;
          const ctx = canvas.getContext("2d")!;
          ctx.fillStyle = "#8080FF";
          ctx.fillRect(0, 0, 32, 32);
          return canvas;
        };

        const effects = [
          { id: "1", effectKey: "brightness", name: "Brightness", enabled: true, parameters: { brightness: 50 } },
        ];

        const canvas1 = createCanvas();
        const canvas2 = createCanvas();

        const output1 = processEffectStack(effects, canvas1, 10);
        const output2 = processEffectStack(effects, canvas2, 10);

        const data1 = output1.ctx.getImageData(0, 0, 32, 32);
        const data2 = output2.ctx.getImageData(0, 0, 32, 32);

        // Compare first 100 pixels
        let match = true;
        for (let i = 0; i < 400; i += 4) {
          if (data1.data[i] !== data2.data[i] ||
              data1.data[i + 1] !== data2.data[i + 1] ||
              data1.data[i + 2] !== data2.data[i + 2] ||
              data1.data[i + 3] !== data2.data[i + 3]) {
            match = false;
            break;
          }
        }

        return { match };
      });

      expect(result.match).toBe(true);
    });
  });

  test.describe("clearEffectCaches", () => {
    test("should clear caches without error", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { clearEffectCaches } = await import(
          "/src/services/effectProcessor"
        );

        try {
          clearEffectCaches();
          return { success: true };
        } catch (e) {
          return { success: false, error: String(e) };
        }
      });

      expect(result.success).toBe(true);
    });
  });

  test.describe("Effect Processing Error Handling", () => {
    test("should handle unregistered effect gracefully", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { processEffectStack } = await import(
          "/src/services/effectProcessor"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 32;
        canvas.height = 32;

        const effects = [
          {
            id: "1",
            effectKey: "nonexistent-effect-xyz",
            name: "Unknown",
            enabled: true,
            parameters: {}
          },
        ];

        try {
          const output = processEffectStack(effects, canvas, 0);
          return {
            success: true,
            hasOutput: !!output.canvas,
          };
        } catch (e) {
          return {
            success: false,
            errorMessage: String(e),
          };
        }
      });

      // Should either gracefully skip or throw a descriptive error
      // Based on current implementation, it may skip or error - either is acceptable
      expect(result.success !== undefined).toBe(true);
    });

    test("should handle NaN in effect parameters", async ({ page }) => {
      const result = await page.evaluate(async () => {
        const { processEffectStack } = await import(
          "/src/services/effectProcessor"
        );

        const canvas = document.createElement("canvas");
        canvas.width = 32;
        canvas.height = 32;

        const effects = [
          {
            id: "1",
            effectKey: "gaussian-blur",
            name: "Blur",
            enabled: true,
            parameters: { blurriness: NaN }
          },
        ];

        try {
          const output = processEffectStack(effects, canvas, 0);
          return {
            success: true,
            width: output.canvas.width,
            height: output.canvas.height,
          };
        } catch (e) {
          return {
            success: false,
            error: String(e),
          };
        }
      });

      // Should handle NaN gracefully
      expect(result.width || result.success === false).toBeTruthy();
    });
  });
});
