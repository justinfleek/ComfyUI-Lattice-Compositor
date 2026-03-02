import { test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 02: Neon Motion Trails - Phases 10-11 (Steps 179-225)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Test", 1920, 1080, 30, 10);
    // Create 5 shape layers
    for (let i = 1; i <= 5; i++) {
      await h.newShapeLayer(`Light_Streak_0${i}`);
    }
  });

  test("Phase 10: Echo Effect / Motion Trails (Steps 179-205)", async ({
    page,
  }) => {
    // Step 179-182: Pre-compose streaks
    await h.selectAllLayers();
    await h.createNestedComp("Streaks_Precomp");
    await h.expectLayerCount(1);

    // Step 183-188: Add Echo effect
    await h.addEchoEffect(0);
    await h.configureEcho({
      echoTime: -0.03,
      numberOfEchoes: 8,
      startingIntensity: 1.0,
      decay: 0.5,
    });

    // Step 189-194: Test operator modes
    await h.configureEcho({ operator: "add" });
    await h.configureEcho({ operator: "maximum" });
    await h.configureEcho({ operator: "screen" });
    await h.configureEcho({ operator: "composite_back" });
    await h.configureEcho({ operator: "composite_front" });
    await h.configureEcho({ operator: "add" }); // Final choice

    // Step 195-203: Fine-tune echo
    await h.configureEcho({ echoTime: -0.02 });
    await h.configureEcho({ echoTime: -0.05 });
    await h.configureEcho({ echoTime: -0.03 }); // Reset
    await h.configureEcho({ decay: 0.7 });
    await h.configureEcho({ decay: 0.3 });
    await h.configureEcho({ decay: 0.5 }); // Reset
    await h.configureEcho({ numberOfEchoes: 12 });
    await h.configureEcho({ numberOfEchoes: 5 });
    await h.configureEcho({ numberOfEchoes: 8 }); // Reset

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });

  test("Phase 11: Motion Blur (Steps 206-225)", async ({ page }) => {
    // Pre-compose first
    await h.selectAllLayers();
    await h.createNestedComp("Streaks_Precomp");

    // Step 206-210: Enable layer motion blur in precomp
    await page.dblclick('[data-testid="layer-0"]'); // Enter precomp
    for (let i = 0; i < 5; i++) {
      await h.enableLayerMotionBlur(i);
    }
    // Return to main
    await page.click('[data-testid="comp-tab-Test"]');

    // Step 211-212: Enable master motion blur
    await h.enableCompMotionBlur();

    // Step 213-216: Configure motion blur
    await h.configureMotionBlur(180, -90, 16);

    // Step 217-221: Test shutter angles
    await h.configureMotionBlur(90, -90, 16);
    await h.configureMotionBlur(270, -90, 16);
    await h.configureMotionBlur(360, -90, 16);
    await h.configureMotionBlur(180, -90, 16); // Standard

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });
});
