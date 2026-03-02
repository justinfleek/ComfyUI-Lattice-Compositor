import { expect, test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 02: Neon Motion Trails - Phases 8-9 (Steps 136-178)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Test", 1920, 1080, 30, 10);
    await h.newShapeLayer("Light_Streak_01");
    await h.setStrokeColor(0, "#FFFFFF");
    await h.setStrokeWidth(0, 15);
  });

  test("Phase 8: Glow Effect (Steps 136-158)", async ({ page }) => {
    // Step 136-141: Add base glow
    await h.selectLayer(0);
    await h.searchEffects("Glow");
    await h.applyEffect("glow");
    await h.configureGlow(0, {
      threshold: 60,
      radius: 30,
      intensity: 1.5,
    });

    // Step 145-148: Glow colors
    await h.configureGlow(0, {
      colorA: "#FFFFFF",
      colorB: "#FFFFFF",
    });

    // Step 153-158: Copy glow to multiple layers
    await h.duplicateLayer();
    await h.duplicateLayer();
    await h.duplicateLayer();
    await h.duplicateLayer();

    // Copy effects from layer 0 to others
    await h.selectLayer(0);
    await h.copy();
    await h.selectLayer(1);
    await h.paste();
    await h.selectLayer(2);
    await h.paste();
    await h.selectLayer(3);
    await h.paste();
    await h.selectLayer(4);
    await h.paste();

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });

  test("Phase 9: Stacking Glow Effects (Steps 159-178)", async ({ page }) => {
    // Step 159-161: Add second glow
    await h.selectLayer(0);
    await h.searchEffects("Glow");
    await h.applyEffect("glow");
    await h.applyEffect("glow"); // Second glow

    // Step 162-164: Configure second glow (atmosphere)
    await h.configureGlow(1, {
      radius: 100,
      intensity: 0.5,
    });

    // Step 165-168: Add third glow (bloom)
    await h.applyEffect("glow"); // Third glow
    await h.configureGlow(2, {
      radius: 200,
      intensity: 0.3,
    });

    // Verify 3 stacked glows
    await expect(page.locator('[data-testid="effect-0-glow"]')).toBeVisible();
    await expect(page.locator('[data-testid="effect-1-glow"]')).toBeVisible();
    await expect(page.locator('[data-testid="effect-2-glow"]')).toBeVisible();

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });
});
