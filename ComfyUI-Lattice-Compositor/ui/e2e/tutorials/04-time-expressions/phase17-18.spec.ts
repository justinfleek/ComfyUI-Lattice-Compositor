import { expect, test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 04: Expressions - Phases 17-18 (Steps 386-425)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Determinism_Test", 1920, 1080, 24, 10);
  });

  test("Phase 17: Save/Load Verification (Steps 386-404)", async ({ page }) => {
    // Step 386-389: Create complex project state
    await h.newSolid("SpeedMapLayer");
    await h.setLayerEndFrame(0, 240);
    await h.enableSpeedMap(0);
    await h.goToStart();
    await h.setSpeedMapValue(0, 0);
    await h.goToFrame(120);
    await h.setSpeedMapValue(0, 60);
    await h.goToFrame(240);
    await h.setSpeedMapValue(0, 120);
    await h.setFrameBlending(0, "mix");

    await h.newSolid("ExpressionLayer");
    await h.isolatePosition();
    await h.enablePropertyExpression(1, "position");
    await h.setExpressionText(1, "position", "wiggle(2, 100)");

    await h.addSliderControl(1, "Speed");
    await h.setSliderValue(0, 75);

    // Step 390: Save
    await h.saveProject();

    // Step 391-398: Reload and verify
    await page.reload();
    await page.waitForSelector('[data-testid="app-ready"]');

    // Verify speedMap
    const enabled = await h.isSpeedMapEnabled(0);
    expect(enabled).toBe(true);

    await h.goToFrame(120);
    const speedMapVal = await h.getSpeedMapValue(0);
    expect(speedMapVal).toBe(60);

    // Verify expression
    const exprText = await h.getExpressionText(1, "position");
    expect(exprText).toContain("wiggle");

    // Verify expression control
    const sliderVal = await h.getSliderValue(0);
    expect(sliderVal).toBe(75);

    // Step 399-404: Determinism after load
    await h.goToFrame(50);
    const beforeSave = await h.getExpressionResult(1, "position");

    await h.saveProject();
    await page.reload();
    await page.waitForSelector('[data-testid="app-ready"]');

    await h.goToFrame(50);
    const afterLoad = await h.getExpressionResult(1, "position");
    expect(afterLoad).toBe(beforeSave);
  });

  test("Phase 18: Final Determinism Verification (Steps 405-425)", async ({
    page,
  }) => {
    // Step 405-409: SpeedMap determinism
    await h.newSolid("SpeedMapTest");
    await h.setLayerEndFrame(0, 200);
    await h.enableSpeedMap(0);

    // Create complex speed ramp
    await h.goToStart();
    await h.setSpeedMapValue(0, 0);
    await h.goToFrame(50);
    await h.setSpeedMapValue(0, 30);
    await h.goToFrame(100);
    await h.setSpeedMapValue(0, 80);
    await h.goToFrame(150);
    await h.setSpeedMapValue(0, 100);

    await h.verifySpeedMapDeterminism(0, 75);

    // Step 410-415: Expression determinism
    await h.newSolid("ExpressionTest");
    await h.isolatePosition();
    await h.enablePropertyExpression(1, "position");
    await h.setExpressionText(
      1,
      "position",
      `
      seedRandom(index, false);
      var base = wiggle(3, 50);
      base + [time * 10, Math.sin(time) * 30]
    `,
    );

    await h.verifyExpressionDeterminism(1, "position", 100);

    // Step 416-421: Frame blending determinism
    await h.selectLayer(0);
    await h.setTimeStretch(0, 200);
    await h.setFrameBlending(0, "mix");
    await h.enableCompFrameBlending();

    await h.verifyFrameDeterminism(45);

    // Step 422-425: Combined system determinism
    // Layer with speedMap + expression + frame blending
    await h.newSolid("CombinedTest");
    await h.setLayerEndFrame(2, 200);
    await h.enableSpeedMap(2);
    await h.setTimeStretch(2, 150);
    await h.setFrameBlending(2, "motion");

    await h.isolateOpacity();
    await h.enablePropertyExpression(2, "opacity");
    await h.setExpressionText(2, "opacity", "linear(time, 0, 5, 0, 100)");

    // Full determinism check
    await h.goToFrame(60);
    const pixels1 = await h.captureFramePixels();
    const expr1 = await h.getExpressionResult(2, "opacity");
    const speed1 = await h.getSpeedMapValue(2);

    await h.goToFrame(0);
    await h.goToFrame(120);
    await h.goToFrame(60);

    const pixels2 = await h.captureFramePixels();
    const expr2 = await h.getExpressionResult(2, "opacity");
    const speed2 = await h.getSpeedMapValue(2);

    expect(pixels2).toBe(pixels1);
    expect(expr2).toBe(expr1);
    expect(speed2).toBe(speed1);
  });

  test("COMPLETE DETERMINISM SUITE", async ({ page }) => {
    // This test runs comprehensive determinism verification
    // across all time-related features

    await h.newSolid("Layer1");
    await h.newSolid("Layer2");
    await h.newSolid("Layer3");

    // Layer 1: Time stretch
    await h.setTimeStretch(0, 200);
    await h.setFrameBlending(0, "mix");

    // Layer 2: SpeedMap
    await h.enableSpeedMap(1);
    await h.goToStart();
    await h.setSpeedMapValue(1, 0);
    await h.goToFrame(120);
    await h.setSpeedMapValue(1, 80);

    // Layer 3: Expression with wiggle
    await h.selectLayer(2);
    await h.isolatePosition();
    await h.enablePropertyExpression(2, "position");
    await h.setExpressionText(2, "position", "wiggle(5, 100)");

    // Enable composition frame blending
    await h.enableCompFrameBlending();

    // Verify at multiple frames
    for (const frame of [25, 50, 75, 100]) {
      await h.verifyFrameDeterminism(frame);
    }
  });
});
