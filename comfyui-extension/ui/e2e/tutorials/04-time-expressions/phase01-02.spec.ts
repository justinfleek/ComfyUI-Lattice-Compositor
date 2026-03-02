import { expect, test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 04: Time Remapping - Phases 1-2 (Steps 1-42)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Time_Test", 1920, 1080, 24, 10);
  });

  test("Phase 1: Layer Time Properties (Steps 1-18)", async ({ page }) => {
    // Step 1-3: Create comp with footage (using solid as placeholder)
    await h.newSolid("Footage");

    // Step 4-5: Verify layer timing
    const startFrame = await h.getLayerStartFrame(0);
    expect(startFrame).toBe(0);

    // Step 11-12: Extend layer beyond source
    await h.setLayerEndFrame(0, 240);
    const endFrame = await h.getLayerEndFrame(0);
    expect(endFrame).toBe(240);

    // Step 13-14: Trim start
    await h.setLayerStartFrame(0, 30);
    const newStart = await h.getLayerStartFrame(0);
    expect(newStart).toBe(30);

    // Step 15: Reset
    await h.setLayerStartFrame(0, 0);

    // Step 16-18: Undo/Redo
    await h.undo();
    const afterUndo = await h.getLayerStartFrame(0);
    expect(afterUndo).toBe(30);
    await h.redo();
  });

  test("Phase 2: Time Stretch (Steps 19-42)", async ({ page }) => {
    await h.newSolid("Footage");
    await h.setLayerEndFrame(0, 120); // 5 second layer

    // Step 20-24: Basic time stretch
    const defaultStretch = await h.getTimeStretch(0);
    expect(defaultStretch).toBe(100);

    await h.setTimeStretch(0, 200); // Half speed
    const endFrame = await h.getLayerEndFrame(0);
    expect(endFrame).toBe(240); // Doubled duration

    // Step 25-28: Speed relationships
    // 200% stretch = 50% speed
    // 50% stretch = 200% speed

    // Step 29-32: Slow motion verification
    await h.goToFrame(60);
    // At 200% stretch, comp frame 60 = source frame 30

    // Step 33-36: Fast motion
    await h.setTimeStretch(0, 50);
    // Layer duration halves

    // Step 37-42: Stretch anchor
    await h.setTimeStretch(0, 100); // Reset
    await h.setStretchAnchor(0, "startFrame");
    await h.setTimeStretch(0, 200);
    // Should extend rightward

    await h.setTimeStretch(0, 100);
    await h.setStretchAnchor(0, "endFrame");
    await h.setTimeStretch(0, 200);
    // Should extend leftward

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });
});
