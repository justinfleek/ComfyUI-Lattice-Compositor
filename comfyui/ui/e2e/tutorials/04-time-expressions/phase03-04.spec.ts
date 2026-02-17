import { expect, test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 04: Time Remapping - Phases 3-4 (Steps 43-82)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Time_Test", 1920, 1080, 24, 10);
    await h.newSolid("Footage");
    await h.setLayerEndFrame(0, 120);
  });

  test("Phase 3: Time Reverse (Steps 43-58)", async ({ page }) => {
    // Step 43-47: Reverse playback
    await h.setTimeReverse(0, true);
    // At comp frame 0, sourceTime should be at end
    // At comp frame 120, sourceTime should be 0

    // Step 48-51: Verify negative stretch
    const stretch = await h.getTimeStretch(0);
    expect(stretch).toBe(-100);

    await h.setTimeReverse(0, false);
    const normalStretch = await h.getTimeStretch(0);
    expect(normalStretch).toBe(100);

    // Step 52-56: Combine reverse with stretch
    await h.setTimeStretch(0, -200); // Reversed AND half speed
    await h.setTimeStretch(0, -50); // Reversed AND double speed

    // Step 57-58: Undo
    await h.undo();
    await h.redo();
  });

  test("Phase 4: Enable SpeedMap (Steps 59-82)", async ({ page }) => {
    // Step 59-62: Enable speedMap
    await h.enableSpeedMap(0);
    const enabled = await h.isSpeedMapEnabled(0);
    expect(enabled).toBe(true);

    // Step 63-66: Initial keyframes auto-created
    await h.goToStart();
    const startValue = await h.getSpeedMapValue(0);
    expect(startValue).toBe(0);

    await h.goToFrame(120);
    const endValue = await h.getSpeedMapValue(0);
    expect(endValue).toBe(120);

    // Step 70-72: Extend layer for speedMap control
    await h.setLayerEndFrame(0, 240);

    // Step 73-78: SpeedMap slow motion
    // Delete end keyframe, create new one
    await h.goToStart();
    await h.setSpeedMapValue(0, 0);
    await h.goToFrame(240);
    await h.setSpeedMapValue(0, 120);
    // 240 comp frames show 120 source frames = 50% speed

    // Step 79-82: SpeedMap fast motion
    await h.goToStart();
    await h.setSpeedMapValue(0, 0);
    await h.goToFrame(60);
    await h.setSpeedMapValue(0, 120);
    // 60 comp frames show 120 source frames = 200% speed

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });
});
