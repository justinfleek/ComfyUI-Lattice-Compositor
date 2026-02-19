import { expect, test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 02: Neon Motion Trails - Phases 1-3 (Steps 1-42)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
  });

  test("Phase 1: Project Setup & Background (Steps 1-12)", async ({ page }) => {
    // Step 1-3: Create and rename composition
    await h.newProject();
    await h.newComposition("Neon_Trails_Main", 1920, 1080, 30, 10);

    // Step 4: Create gradient background solid
    await h.newSolid("BG_Gradient");

    // Step 5-6: Add and configure Gradient Ramp
    await h.addGradientRamp(0);
    await h.configureGradientRamp({
      startX: 960,
      startY: 0,
      endX: 960,
      endY: 1080,
      startColor: "#FF00FF",
      endColor: "#330033",
      shape: "linear",
    });

    // Step 7-11: Test radial variant
    await h.duplicateLayer();
    await h.configureGradientRamp({
      startX: 960,
      startY: 540,
      endX: 960,
      endY: 1080,
      shape: "radial",
    });
    await h.toggleLayerVisibility(0);
    await h.toggleLayerVisibility(0);
    await h.deleteLayer();

    // Step 12: Lock background
    await h.toggleLayerLock();

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });

  test("Phase 2: Creating Silhouette (Steps 13-26)", async ({ page }) => {
    await h.newProject();
    await h.newComposition("Neon_Trails_Main", 1920, 1080, 30, 10);

    // Step 13-15: Create placeholder for silhouette
    await h.newSolid("Silhouette_Source");

    // Step 16-18: Add Fill effect for silhouette
    await h.addFillEffect(0, "#000000");

    // Step 19-23: Alternative Tint method
    await h.undo();
    await h.addTintEffect(0, "#000000", "#000000", 100);

    // Step 24-26: Position silhouette
    await h.selectLayer(0);
    await h.isolatePosition();
    await h.setPropertyValue("position", "960, 810");
    await h.isolateScale();
    await h.setPropertyValue("scale", "70");

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });

  test("Phase 3: Shape Layer Basics (Steps 27-42)", async ({ page }) => {
    await h.newProject();
    await h.newComposition("Test", 1920, 1080, 30, 10);

    // Step 27-29: Create shape layer
    await h.newShapeLayer("Light_Streak_01");
    await h.expectLayerCount(1);

    // Step 30-31: Verify shape structure
    await h.expandShapeContents(0);
    await expect(
      page.locator('[data-testid="layer-0-contents"]'),
    ).toBeVisible();

    // Step 35-36: Remove fill
    await h.removeShapeFill(0);

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });
});
