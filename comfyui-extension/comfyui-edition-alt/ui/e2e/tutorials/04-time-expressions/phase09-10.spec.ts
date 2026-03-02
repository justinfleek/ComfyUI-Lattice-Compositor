import { expect, test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 04: Expressions - Phases 9-10 (Steps 181-248)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Expression_Test", 1920, 1080, 24, 10);
    await h.newSolid("ExpressionLayer");
  });

  test("Phase 9: Expression Fundamentals (Steps 181-215)", async ({ page }) => {
    // Step 181-185: Enable expression
    await h.selectLayer(0);
    await h.isolatePosition();
    await h.enablePropertyExpression(0, "position");

    // Step 186-188: Static value expression
    await h.setExpressionText(0, "position", "[960, 540]");
    const result = await h.getExpressionResult(0, "position");
    expect(result).toContain("960");

    // Step 194-197: Expression errors
    await h.setExpressionText(0, "position", "[960,"); // Invalid
    const hasError = await h.hasExpressionError(0, "position");
    expect(hasError).toBe(true);

    // Fix error
    await h.setExpressionText(0, "position", "[960, 540]");
    const noError = await h.hasExpressionError(0, "position");
    expect(noError).toBe(false);

    // Step 198-201: Variables and arithmetic
    await h.setExpressionText(
      0,
      "position",
      `
      var x = 500;
      var y = 300;
      [x, y]
    `,
    );

    await h.setExpressionText(
      0,
      "position",
      `
      var base = 100;
      [base * 2, base + 50]
    `,
    );

    // Step 202-207: Time variable
    await h.setExpressionText(
      0,
      "position",
      `
      var x = time * 100;
      var y = 540;
      [x, y]
    `,
    );

    // Verify movement over time
    await h.goToStart();
    await h.goToFrame(24); // 1 second
    // x should be ~100

    // Step 208-209: Time-based rotation
    await h.isolateRotation();
    await h.enablePropertyExpression(0, "rotation");
    await h.setExpressionText(0, "rotation", "time * 90");
    // Rotates 90deg per second

    // Step 210-213: Value variable
    await h.isolatePosition();
    // Create keyframe animation first
    await h.goToStart();
    await h.setPropertyValue("position", "100, 540");
    await h.goToFrame(60);
    await h.setPropertyValue("position", "1820, 540");

    await h.enablePropertyExpression(0, "position");
    await h.setExpressionText(0, "position", "value + [0, -50]");
    // Animation plays, offset 50px up

    // Step 214-215: Determinism test
    await h.verifyExpressionDeterminism(0, "position", 50);

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });

  test("Phase 10: Math Functions (Steps 216-248)", async ({ page }) => {
    await h.selectLayer(0);
    await h.isolatePosition();
    await h.enablePropertyExpression(0, "position");

    // Step 216-217: Sin/Cos oscillation
    await h.setExpressionText(
      0,
      "position",
      `
      var amplitude = 100;
      var frequency = 2;
      var y = Math.sin(time * frequency) * amplitude;
      [960, 540 + y]
    `,
    );

    // Step 218-219: Circular motion
    await h.setExpressionText(
      0,
      "position",
      `
      var radius = 200;
      var speed = 1;
      var x = 960 + Math.cos(time * speed) * radius;
      var y = 540 + Math.sin(time * speed) * radius;
      [x, y]
    `,
    );

    // Step 220-221: Math.abs
    await h.isolateOpacity();
    await h.enablePropertyExpression(0, "opacity");
    await h.setExpressionText(
      0,
      "opacity",
      `
      var wave = Math.sin(time * 3);
      var bounce = Math.abs(wave);
      bounce * 100
    `,
    );

    // Step 226-227: Clamping
    await h.setExpressionText(
      0,
      "opacity",
      `
      var raw = time * 50;
      Math.max(Math.min(raw, 100), 0)
    `,
    );

    // Step 228-231: Pow and Sqrt
    await h.setExpressionText(0, "opacity", "Math.pow(time, 2) * 10");
    await h.setExpressionText(0, "opacity", "Math.sqrt(time) * 100");

    // Step 234-238: seedRandom (deterministic)
    await h.isolatePosition();
    await h.setExpressionText(
      0,
      "position",
      `
      seedRandom(1, true);
      var x = Math.random() * 1920;
      var y = Math.random() * 1080;
      [x, y]
    `,
    );

    // Same value every frame with timeless=true
    await h.goToFrame(0);
    const val0 = await h.getExpressionResult(0, "position");
    await h.goToFrame(50);
    const val50 = await h.getExpressionResult(0, "position");
    expect(val50).toBe(val0);

    // Step 239-246: seedRandom per-frame determinism
    await h.setExpressionText(
      0,
      "position",
      `
      seedRandom(index, false);
      var x = Math.random() * 1920;
      var y = Math.random() * 1080;
      [x, y]
    `,
    );

    // Verify determinism
    await h.verifyExpressionDeterminism(0, "position", 30);

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });
});
