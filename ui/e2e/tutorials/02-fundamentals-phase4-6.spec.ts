import { test } from "@playwright/test";
import { CompositorHelper } from "../helpers/compositor";

test.describe("Tutorial 01: Fundamentals - Phases 4-6", () => {
  let helper: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    helper = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await helper.newProject();
    await helper.newComposition("Test_Comp");
    await helper.newSolid("Layer1");
  });

  test("Phase 4: Timeline Navigation (Steps 61-85)", async ({ page }) => {
    // Step 61-63: Playback
    await helper.play();
    await page.waitForTimeout(500);
    await helper.stop();

    // Step 64-65: Home/End
    await helper.goToStart();
    await helper.goToEnd();

    // Step 66-69: Frame stepping
    await helper.goToStart();
    await page.keyboard.press("PageDown"); // Forward 1
    await page.keyboard.press("PageUp"); // Back 1
    await page.keyboard.press("Shift+PageDown"); // Forward 10
    await page.keyboard.press("Shift+PageUp"); // Back 10

    // Step 73-75: Timeline zoom
    await page.keyboard.press("Equal"); // Zoom in
    await page.keyboard.press("Minus"); // Zoom out
    await page.keyboard.press("Semicolon"); // Fit to view
  });

  test("Phase 5: Layer Timing (Steps 86-110)", async ({ page }) => {
    await helper.selectLayer(0);

    // Step 87-88: Navigate to layer bounds
    await page.keyboard.press("i"); // Go to in point
    await page.keyboard.press("o"); // Go to out point

    // Step 92-93: Move layer
    await helper.goToFrame(10);
    await page.keyboard.press("BracketLeft"); // Move start to playhead
    await page.keyboard.press("BracketRight"); // Move end to playhead

    // Step 97-100: Trim layer
    await helper.goToFrame(5);
    await page.keyboard.press("Alt+BracketLeft"); // Trim start
    await helper.goToFrame(70);
    await page.keyboard.press("Alt+BracketRight"); // Trim end

    // Step 102-107: Split layer
    await helper.goToFrame(40);
    await page.keyboard.press("Control+Shift+d");
    await helper.expectLayerCount(2);
  });

  test("Phase 6: Layer Switches (Steps 111-135)", async ({ page }) => {
    await helper.selectLayer(0);

    // Step 113-114: Visibility toggle
    await page.click('[data-testid="layer-0-visibility"]');
    await page.click('[data-testid="layer-0-visibility"]');

    // Step 116-120: Isolate toggle
    await page.click('[data-testid="layer-0-isolate"]');
    await page.click('[data-testid="layer-0-isolate"]');

    // Step 121-125: Lock toggle
    await page.keyboard.press("Control+l");
    await page.keyboard.press("Control+l");

    // Step 126-131: Shy toggle
    await page.click('[data-testid="layer-0-shy"]');
  });
});
