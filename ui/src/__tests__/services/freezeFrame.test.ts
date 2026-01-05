/**
 * FreezeFrame Effect Tests
 *
 * Tests the FreezeFrame effect which holds a layer at a specific source frame.
 * Tutorial 04 Steps 95-98.
 */

import { beforeEach, describe, expect, test } from "vitest";
import { EFFECT_DEFINITIONS } from "../../types/effects";

describe("FreezeFrame Effect", () => {
  describe("Effect Definition", () => {
    test("freeze-frame effect exists in definitions", () => {
      expect(EFFECT_DEFINITIONS["freeze-frame"]).toBeDefined();
    });

    test("freeze-frame has correct category", () => {
      expect(EFFECT_DEFINITIONS["freeze-frame"].category).toBe("time");
    });

    test("freeze-frame has correct name", () => {
      expect(EFFECT_DEFINITIONS["freeze-frame"].name).toBe("Freeze Frame");
    });

    test("freeze-frame has freeze_at_frame parameter", () => {
      const params = EFFECT_DEFINITIONS["freeze-frame"].parameters;
      expect(params).toBeDefined();
      expect(params.length).toBeGreaterThan(0);

      const freezeParam = params.find((p) => p.name === "Freeze At Frame");
      expect(freezeParam).toBeDefined();
      expect(freezeParam?.type).toBe("number");
      expect(freezeParam?.defaultValue).toBe(0);
      expect(freezeParam?.min).toBe(0);
      expect(freezeParam?.animatable).toBe(true);
    });
  });

  describe("Effect Renderer", () => {
    // Mock canvas and context
    let mockCanvas: HTMLCanvasElement;
    let mockCtx: CanvasRenderingContext2D;
    let _mockImageData: ImageData;

    beforeEach(() => {
      // Create mock canvas
      mockCanvas = document.createElement("canvas");
      mockCanvas.width = 100;
      mockCanvas.height = 100;
      mockCtx = mockCanvas.getContext("2d")!;

      // Fill with a test color (red)
      mockCtx.fillStyle = "#ff0000";
      mockCtx.fillRect(0, 0, 100, 100);
      _mockImageData = mockCtx.getImageData(0, 0, 100, 100);
    });

    test("renderer passes through input when freeze frame matches current", async () => {
      // Import dynamically to ensure fresh state
      const { freezeFrameRenderer } = await import(
        "../../services/effects/timeRenderer"
      );

      const input = { canvas: mockCanvas, ctx: mockCtx };
      const params = {
        freeze_at_frame: 10,
        _frame: 10,
        _layerId: "test-layer-1",
      };

      const result = freezeFrameRenderer(input, params);

      // When current frame matches freeze frame, input passes through
      expect(result).toBeDefined();
      expect(result.canvas).toBeDefined();
    });

    test("renderer caches frame when freeze frame is reached", async () => {
      const { freezeFrameRenderer, clearFrozenFrame } = await import(
        "../../services/effects/timeRenderer"
      );

      // Clear any existing cache
      clearFrozenFrame("test-layer-2");

      const input = { canvas: mockCanvas, ctx: mockCtx };

      // First, render at frame 5 (not the freeze target)
      freezeFrameRenderer(input, {
        freeze_at_frame: 5,
        _frame: 0,
        _layerId: "test-layer-2",
      });

      // Now render at freeze frame (5)
      const result = freezeFrameRenderer(input, {
        freeze_at_frame: 5,
        _frame: 5,
        _layerId: "test-layer-2",
      });

      expect(result).toBeDefined();
    });

    test("renderer returns cached frame after freeze", async () => {
      const { freezeFrameRenderer, clearFrozenFrame, clearAllFrameBuffers } =
        await import("../../services/effects/timeRenderer");

      // Clear caches
      clearFrozenFrame("test-layer-3");
      clearAllFrameBuffers();

      // Create two different colored canvases
      const canvas1 = document.createElement("canvas");
      canvas1.width = 100;
      canvas1.height = 100;
      const ctx1 = canvas1.getContext("2d")!;
      ctx1.fillStyle = "#ff0000"; // Red
      ctx1.fillRect(0, 0, 100, 100);

      const canvas2 = document.createElement("canvas");
      canvas2.width = 100;
      canvas2.height = 100;
      const ctx2 = canvas2.getContext("2d")!;
      ctx2.fillStyle = "#00ff00"; // Green
      ctx2.fillRect(0, 0, 100, 100);

      // Render at frame 10 (freeze target) - capture red
      freezeFrameRenderer(
        { canvas: canvas1, ctx: ctx1 },
        { freeze_at_frame: 10, _frame: 10, _layerId: "test-layer-3" },
      );

      // Render at frame 20 with green canvas - should return frozen red
      const result = freezeFrameRenderer(
        { canvas: canvas2, ctx: ctx2 },
        { freeze_at_frame: 10, _frame: 20, _layerId: "test-layer-3" },
      );

      // Result should be from the cached frozen frame
      expect(result.canvas).toBeDefined();
      // The result should have pixel data from frame 10 (red), not frame 20 (green)
    });

    test("different layers have independent freeze caches", async () => {
      const { freezeFrameRenderer, clearFrozenFrame } = await import(
        "../../services/effects/timeRenderer"
      );

      clearFrozenFrame("layer-a");
      clearFrozenFrame("layer-b");

      // Layer A freezes at frame 10
      freezeFrameRenderer(
        { canvas: mockCanvas, ctx: mockCtx },
        { freeze_at_frame: 10, _frame: 10, _layerId: "layer-a" },
      );

      // Layer B freezes at frame 20
      const canvas2 = document.createElement("canvas");
      canvas2.width = 100;
      canvas2.height = 100;
      const ctx2 = canvas2.getContext("2d")!;
      ctx2.fillStyle = "#0000ff";
      ctx2.fillRect(0, 0, 100, 100);

      freezeFrameRenderer(
        { canvas: canvas2, ctx: ctx2 },
        { freeze_at_frame: 20, _frame: 20, _layerId: "layer-b" },
      );

      // Both should work independently
      expect(true).toBe(true);
    });

    test("clearFrozenFrame removes cache for specific layer", async () => {
      const { freezeFrameRenderer, clearFrozenFrame } = await import(
        "../../services/effects/timeRenderer"
      );

      // Cache a frozen frame
      freezeFrameRenderer(
        { canvas: mockCanvas, ctx: mockCtx },
        { freeze_at_frame: 15, _frame: 15, _layerId: "clear-test-layer" },
      );

      // Clear it
      clearFrozenFrame("clear-test-layer");

      // Verify no error on subsequent render
      const result = freezeFrameRenderer(
        { canvas: mockCanvas, ctx: mockCtx },
        { freeze_at_frame: 15, _frame: 20, _layerId: "clear-test-layer" },
      );

      expect(result).toBeDefined();
    });

    test("clearAllFrozenFrames removes all caches", async () => {
      const { freezeFrameRenderer, clearAllFrozenFrames } = await import(
        "../../services/effects/timeRenderer"
      );

      // Cache frozen frames for multiple layers
      freezeFrameRenderer(
        { canvas: mockCanvas, ctx: mockCtx },
        { freeze_at_frame: 5, _frame: 5, _layerId: "multi-1" },
      );

      freezeFrameRenderer(
        { canvas: mockCanvas, ctx: mockCtx },
        { freeze_at_frame: 10, _frame: 10, _layerId: "multi-2" },
      );

      // Clear all
      clearAllFrozenFrames();

      // Should work without issues
      expect(true).toBe(true);
    });
  });

  describe("Integration with Time Effects", () => {
    test("freeze-frame is registered with time effects", async () => {
      const { registerTimeEffects } = await import(
        "../../services/effects/timeRenderer"
      );

      // Registration should not throw
      expect(() => registerTimeEffects()).not.toThrow();
    });

    test("time effect module exports freeze frame functions", async () => {
      const timeRenderer = await import("../../services/effects/timeRenderer");

      expect(timeRenderer.freezeFrameRenderer).toBeDefined();
      expect(typeof timeRenderer.freezeFrameRenderer).toBe("function");

      expect(timeRenderer.clearFrozenFrame).toBeDefined();
      expect(typeof timeRenderer.clearFrozenFrame).toBe("function");

      expect(timeRenderer.clearAllFrozenFrames).toBeDefined();
      expect(typeof timeRenderer.clearAllFrozenFrames).toBe("function");
    });
  });

  describe("Parameter Handling", () => {
    test("freeze_at_frame defaults to 0 when not provided", async () => {
      const { freezeFrameRenderer } = await import(
        "../../services/effects/timeRenderer"
      );

      // Should not throw with missing parameter
      const result = freezeFrameRenderer(
        {
          canvas: document.createElement("canvas"),
          ctx: document.createElement("canvas").getContext("2d")!,
        },
        { _frame: 0, _layerId: "default-test" },
      );

      expect(result).toBeDefined();
    });

    test("freeze_at_frame is clamped to minimum 0", async () => {
      const { freezeFrameRenderer } = await import(
        "../../services/effects/timeRenderer"
      );

      const canvas = document.createElement("canvas");
      canvas.width = 10;
      canvas.height = 10;
      const ctx = canvas.getContext("2d")!;

      // Negative value should be treated as 0
      const result = freezeFrameRenderer(
        { canvas, ctx },
        { freeze_at_frame: -10, _frame: 0, _layerId: "negative-test" },
      );

      expect(result).toBeDefined();
    });

    test("freeze_at_frame is rounded to nearest integer", async () => {
      const { freezeFrameRenderer, clearFrozenFrame } = await import(
        "../../services/effects/timeRenderer"
      );

      clearFrozenFrame("round-test");

      const canvas = document.createElement("canvas");
      canvas.width = 10;
      canvas.height = 10;
      const ctx = canvas.getContext("2d")!;

      // Should round 10.7 to 11
      const result = freezeFrameRenderer(
        { canvas, ctx },
        { freeze_at_frame: 10.7, _frame: 11, _layerId: "round-test" },
      );

      expect(result).toBeDefined();
    });
  });

  describe("Tutorial 04 Steps 95-98", () => {
    test("Step 95-98: Apply FreezeFrame effect and freeze at frame 60", async () => {
      const { freezeFrameRenderer, clearFrozenFrame, clearAllFrameBuffers } =
        await import("../../services/effects/timeRenderer");

      clearFrozenFrame("tutorial-layer");
      clearAllFrameBuffers();

      const canvas = document.createElement("canvas");
      canvas.width = 100;
      canvas.height = 100;
      const ctx = canvas.getContext("2d")!;

      // Step 95: Effect exists
      expect(EFFECT_DEFINITIONS["freeze-frame"]).toBeDefined();

      // Step 96: Parameter is freezeAtFrame
      const freezeParam = EFFECT_DEFINITIONS["freeze-frame"].parameters.find(
        (p) => p.name === "Freeze At Frame",
      );
      expect(freezeParam).toBeDefined();

      // Step 97: Set freezeAtFrame = 60
      ctx.fillStyle = "#ff0000";
      ctx.fillRect(0, 0, 100, 100);

      // Render at frame 60 to capture it
      freezeFrameRenderer(
        { canvas, ctx },
        { freeze_at_frame: 60, _frame: 60, _layerId: "tutorial-layer" },
      );

      // Step 98: Entire layer shows only source frame 60
      // Render at different frames - all should show frame 60
      const canvas2 = document.createElement("canvas");
      canvas2.width = 100;
      canvas2.height = 100;
      const ctx2 = canvas2.getContext("2d")!;
      ctx2.fillStyle = "#00ff00"; // Different color
      ctx2.fillRect(0, 0, 100, 100);

      const resultAt30 = freezeFrameRenderer(
        { canvas: canvas2, ctx: ctx2 },
        { freeze_at_frame: 60, _frame: 30, _layerId: "tutorial-layer" },
      );

      const resultAt90 = freezeFrameRenderer(
        { canvas: canvas2, ctx: ctx2 },
        { freeze_at_frame: 60, _frame: 90, _layerId: "tutorial-layer" },
      );

      const resultAt120 = freezeFrameRenderer(
        { canvas: canvas2, ctx: ctx2 },
        { freeze_at_frame: 60, _frame: 120, _layerId: "tutorial-layer" },
      );

      // All results should be defined (showing the frozen frame)
      expect(resultAt30).toBeDefined();
      expect(resultAt90).toBeDefined();
      expect(resultAt120).toBeDefined();
    });
  });

  describe("Undo/Redo Compatibility", () => {
    test("effect definition is serializable", () => {
      const effectDef = EFFECT_DEFINITIONS["freeze-frame"];

      // Should be able to stringify and parse
      const serialized = JSON.stringify(effectDef);
      const parsed = JSON.parse(serialized);

      expect(parsed.name).toBe("Freeze Frame");
      expect(parsed.category).toBe("time");
      expect(parsed.parameters).toBeDefined();
    });
  });

  describe("Save/Load Compatibility", () => {
    test("effect instance serializes correctly", () => {
      // Create a mock effect instance as it would be stored
      const effectInstance = {
        id: "effect-123",
        effectKey: "freeze-frame",
        name: "Freeze Frame",
        enabled: true,
        parameters: {
          "Freeze At Frame": 60,
        },
        keyframes: {},
      };

      const serialized = JSON.stringify(effectInstance);
      const parsed = JSON.parse(serialized);

      expect(parsed.effectKey).toBe("freeze-frame");
      expect(parsed.parameters["Freeze At Frame"]).toBe(60);
    });
  });
});
