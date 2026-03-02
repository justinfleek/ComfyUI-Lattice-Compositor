import { test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 04: Expressions - Phases 11-12 (Steps 249-295)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Expression_Test", 1920, 1080, 24, 10);
    await h.newSolid("ExpressionLayer");
  });

  test("Phase 11: Conditionals (Steps 249-265)", async ({ page }) => {
    await h.selectLayer(0);
    await h.isolatePosition();
    await h.enablePropertyExpression(0, "position");

    // Step 249-250: Basic if/else
    await h.setExpressionText(
      0,
      "position",
      `
      if (time < 2) {
        [0, 540];
      } else {
        [960, 540];
      }
    `,
    );

    await h.goToFrame(24); // 1 second
    // Should be at [0, 540]
    await h.goToFrame(72); // 3 seconds
    // Should be at [960, 540]

    // Step 251-252: if/else if/else
    await h.setExpressionText(
      0,
      "position",
      `
      if (time < 1) {
        [200, 540];
      } else if (time < 2) {
        [960, 540];
      } else {
        [1720, 540];
      }
    `,
    );

    // Step 259-260: Ternary operator
    await h.isolateOpacity();
    await h.enablePropertyExpression(0, "opacity");
    await h.setExpressionText(0, "opacity", "time < 2 ? 0 : 100");

    // Step 261-262: Nested ternary
    await h.setExpressionText(
      0,
      "opacity",
      "time < 1 ? 0 : (time < 2 ? 50 : 100)",
    );

    // Step 263-265: Conditional with animation
    await h.isolatePosition();
    // Create keyframe animation first
    await h.goToStart();
    await h.setPropertyValue("position", "100, 540");
    await h.goToFrame(60);
    await h.setPropertyValue("position", "1820, 540");

    await h.enablePropertyExpression(0, "position");
    await h.setExpressionText(
      0,
      "position",
      `
      if (time < 2) {
        value;
      } else {
        value + [100, 0];
      }
    `,
    );

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });

  test("Phase 12: Loops and Functions (Steps 266-295)", async ({ page }) => {
    await h.selectLayer(0);
    await h.isolateOpacity();
    await h.enablePropertyExpression(0, "opacity");

    // Step 266-267: For loop
    await h.setExpressionText(
      0,
      "opacity",
      `
      var sum = 0;
      for (var i = 0; i < 5; i++) {
        sum += i;
      }
      sum
    `,
    );
    // Returns 10

    // Step 270-271: Custom function
    await h.setExpressionText(
      0,
      "opacity",
      `
      function double(x) {
        return x * 2;
      }
      double(50)
    `,
    );
    // Returns 100

    // Step 272-273: Function with multiple parameters
    await h.setExpressionText(
      0,
      "opacity",
      `
      function clamp(val, min, max) {
        return Math.max(min, Math.min(max, val));
      }
      clamp(150, 0, 100)
    `,
    );
    // Returns 100 (clamped)

    // Step 274-275: Easing function
    await h.setExpressionText(
      0,
      "opacity",
      `
      function easeOutCubic(t) {
        return 1 - Math.pow(1 - t, 3);
      }
      var t = Math.min(time / 2, 1);
      easeOutCubic(t) * 100
    `,
    );
    // Eased animation 0-100 over 2 seconds

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });
});
