import { test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 02: Neon Motion Trails - Phases 4-5 (Steps 41-82)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Test", 1920, 1080, 30, 10);
    await h.newShapeLayer("Light_Streak_01");
  });

  test("Phase 4: Stroke Properties (Steps 41-60)", async ({ page }) => {
    // Step 43-45: Stroke color
    await h.setStrokeColor(0, "#FFFFFF");

    // Step 46-48: Stroke width
    await h.setStrokeWidth(0, 15);
    await h.setStrokeWidth(0, 5);
    await h.setStrokeWidth(0, 30);
    await h.setStrokeWidth(0, 15); // Reset

    // Step 49-52: Line cap
    await h.setStrokeLineCap(0, "butt");
    await h.setStrokeLineCap(0, "round");
    await h.setStrokeLineCap(0, "square");
    await h.setStrokeLineCap(0, "round"); // Final choice

    // Step 53-56: Line join
    await h.setStrokeLineJoin(0, "miter");
    await h.setStrokeLineJoin(0, "round");
    await h.setStrokeLineJoin(0, "bevel");
    await h.setStrokeLineJoin(0, "round"); // Final choice

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });

  test("Phase 5: Trim Paths Animator (Steps 61-82)", async ({ page }) => {
    // Step 61-63: Add trim paths
    await h.addTrimPaths(0);

    // Step 64-67: Test end property
    await h.setTrimPathsEnd(0, 100);
    await h.setTrimPathsEnd(0, 50);
    await h.setTrimPathsEnd(0, 0);
    await h.setTrimPathsEnd(0, 100); // Reset

    // Step 68-71: Test start property
    await h.setTrimPathsStart(0, 0);
    await h.setTrimPathsStart(0, 50);
    await h.setTrimPathsStart(0, 100);
    await h.setTrimPathsStart(0, 0); // Reset

    // Step 72-74: Combined (light segment)
    await h.setTrimPathsStart(0, 0);
    await h.setTrimPathsEnd(0, 20);

    // Step 75-78: Test offset
    await h.setTrimPathsOffset(0, 0);
    await h.setTrimPathsOffset(0, 180);
    await h.setTrimPathsOffset(0, 360);
    await h.setTrimPathsOffset(0, 0); // Reset

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });
});
