import { expect, test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 04: Time Remapping - Phases 5-6 (Steps 83-135)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Time_Test", 1920, 1080, 24, 10);
    await h.newSolid("Footage");
    await h.setLayerEndFrame(0, 240);
    await h.enableSpeedMap(0);
  });

  test("Phase 5: Freeze Frames (Steps 83-102)", async ({ page }) => {
    // Step 83-90: Freeze via speedMap
    await h.goToStart();
    await h.setSpeedMapValue(0, 0);

    await h.goToFrame(60);
    await h.setSpeedMapValue(0, 60); // Normal playback to here

    // Freeze section
    await h.goToFrame(84);
    await h.setSpeedMapValue(0, 60); // Same value = frozen

    // Verify frames 60-84 show source frame 60
    await h.goToFrame(72);
    const frozenValue = await h.getSpeedMapValue(0);
    expect(frozenValue).toBe(60);

    // Step 91-94: Hold keyframe for freeze
    await h.setKeyframeInterpolation("speedmap", "hold");

    // Step 95-98: Freeze Frame effect alternative
    await h.addFreezeFrameEffect(0);
    await h.setFreezeAtFrame(0, 60);

    // Remove effect for further tests
    await h.undo();

    // Step 99-102: Freeze in speed ramp
    await h.goToFrame(120);
    await h.setSpeedMapValue(0, 60); // Resume from frozen value
    await h.goToFrame(180);
    await h.setSpeedMapValue(0, 120); // Continue playback

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });

  test("Phase 6: Speed Ramps (Steps 103-135)", async ({ page }) => {
    // Step 103-105: Setup for speed ramp
    // Plan: normal → slow → fast → normal

    // Step 106-109: Create slow motion section
    await h.goToStart();
    await h.setSpeedMapValue(0, 0);

    await h.goToFrame(48);
    await h.setSpeedMapValue(0, 48); // Normal speed so far

    await h.goToFrame(96);
    await h.setSpeedMapValue(0, 72); // Slow: 24 source in 48 comp = 50%

    // Step 110-111: Fast motion section
    await h.goToFrame(120);
    await h.setSpeedMapValue(0, 120); // Fast: 48 source in 24 comp = 200%

    // Step 112-113: Return to normal
    await h.goToFrame(168);
    await h.setSpeedMapValue(0, 168);

    // Step 114-116: Apply easing
    await h.smoothEase();

    // Step 117-122: Graph Editor - Value Graph
    await h.openGraphEditor(0, "speedmap");
    await h.setGraphType("value");
    // Y-axis = source frame, X-axis = comp frame
    // Slope = playback speed

    // Step 123-128: Speed Graph
    await h.setGraphType("speed");
    // Y-axis = playback speed percentage
    // 100% = normal, 50% = half, 200% = double

    // Close graph editor
    await h.toggleCurveEditor();

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });
});
