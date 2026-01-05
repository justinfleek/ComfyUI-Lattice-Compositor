import { expect, test } from "@playwright/test";
import { CompositorHelper } from "../helpers/compositor";

test.describe("Tutorial 01: Fundamentals - Phases 7-9", () => {
  let helper: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    helper = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await helper.newProject();
    await helper.newComposition("Test_Comp");
    await helper.newSolid("Layer1");
  });

  test("Phase 7: Transform Properties (Steps 136-175)", async ({ page }) => {
    await helper.selectLayer(0);

    // Step 137-142: Property isolation
    await helper.isolatePosition();
    await helper.isolateScale();
    await helper.isolateRotation();
    await helper.isolateOpacity();

    // Step 143-148: Multi-property reveal
    await page.keyboard.press("p");
    await page.keyboard.press("Shift+s");
    await page.keyboard.press("Shift+r");

    // Verify properties visible
    await expect(
      page.locator('[data-testid="property-position"]'),
    ).toBeVisible();
    await expect(page.locator('[data-testid="property-scale"]')).toBeVisible();
    await expect(
      page.locator('[data-testid="property-rotation"]'),
    ).toBeVisible();
  });

  test("Phase 8: Property Reveal Shortcuts (Steps 176-195)", async ({
    page,
  }) => {
    await helper.selectLayer(0);

    // Need keyframes first for U shortcut
    await helper.isolatePosition();
    await helper.toggleStopwatch("position");
    await helper.goToFrame(30);
    // Change position value...

    // Step 177-180: Reveal animated
    await helper.revealAnimated();

    // Step 182-184: Reveal modified (UU)
    await page.keyboard.press("u");
    await page.keyboard.press("u");
  });

  test("Phase 9: Keyframe Animation (Steps 196-240)", async ({ page }) => {
    await helper.selectLayer(0);

    // Step 196-206: Create position keyframes
    await helper.goToStart();
    await helper.isolatePosition();
    await helper.toggleStopwatch("position");
    // First keyframe created at frame 0

    await helper.goToFrame(16); // 1 second at 16fps
    // Change position - auto keyframe

    // Step 214-218: Keyframe navigation
    await page.keyboard.press("j"); // Previous keyframe
    await page.keyboard.press("k"); // Next keyframe

    // Step 231-235: Hold keyframes
    await page.keyboard.press("Control+Alt+h");

    // Step 241-246: Smooth ease
    await helper.smoothEase();
  });
});
