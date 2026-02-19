import { test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 04: Expressions - Phases 13-14 (Steps 276-355)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Expression_Test", 1920, 1080, 24, 10);
    await h.newSolid("ExpressionLayer");
  });

  test("Phase 13: Built-in Expression Functions (Steps 276-312)", async ({
    page,
  }) => {
    await h.selectLayer(0);
    await h.isolateOpacity();
    await h.enablePropertyExpression(0, "opacity");

    // Step 276-278: linear()
    await h.setExpressionText(0, "opacity", "linear(time, 0, 2, 0, 100)");
    // As time goes 0-2, value goes 0-100

    // Step 279-280: ease()
    await h.setExpressionText(0, "opacity", "ease(time, 0, 2, 0, 100)");
    // Smooth eased version

    // Step 284-285: clamp()
    await h.setExpressionText(0, "opacity", "clamp(time * 50, 0, 100)");

    // Step 286-291: wiggle()
    await h.isolatePosition();
    await h.enablePropertyExpression(0, "position");
    await h.setExpressionText(0, "position", "wiggle(3, 50)");
    // Random oscillation, 3 times/sec, 50px range

    // Verify determinism
    await h.verifyExpressionDeterminism(0, "position", 45);

    // Step 289-290: wiggle with octaves
    await h.setExpressionText(0, "position", "wiggle(3, 50, 2, 0.5)");

    // Step 292-299: loopOut()
    // Create keyframe animation first
    await h.goToStart();
    await h.setPropertyValue("position", "100, 540");
    await h.goToFrame(60);
    await h.setPropertyValue("position", "1820, 540");

    await h.enablePropertyExpression(0, "position");
    await h.setExpressionText(0, "position", 'loopOut("cycle")');

    // Test different loop types
    await h.setExpressionText(0, "position", 'loopOut("pingpong")');
    await h.setExpressionText(0, "position", 'loopOut("offset")');
    await h.setExpressionText(0, "position", 'loopOut("continue")');

    // Step 304-306: valueAtTime()
    await h.setExpressionText(0, "position", "valueAtTime(time - 0.5)");
    // Returns value from 0.5 seconds ago

    // Step 311-312: posterizeTime()
    await h.isolateOpacity();
    await h.setExpressionText(
      0,
      "opacity",
      `
      posterizeTime(1);
      time * 100
    `,
    );
    // Updates once per second

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });

  test("Phase 14: Layer and Property References (Steps 313-355)", async ({
    page,
  }) => {
    // Create second layer for reference
    await h.newSolid("Leader");
    await h.selectLayer(1); // Original layer
    await h.isolatePosition();

    // Step 313-316: thisLayer
    await h.enablePropertyExpression(1, "position");
    await h.setExpressionText(1, "position", "thisLayer.position");

    // Step 317-321: thisComp
    await h.setExpressionText(
      1,
      "position",
      "[thisComp.width/2, thisComp.height/2]",
    );
    // Centers in composition

    // Step 322-324: Reference another layer
    await h.setExpressionText(
      1,
      "position",
      'thisComp.layer("Leader").position',
    );
    // Follows Leader exactly

    // Step 325-326: Follow with offset
    await h.setExpressionText(
      1,
      "position",
      'thisComp.layer("Leader").position + [100, 0]',
    );
    // Follows 100px to the right

    // Step 327-328: Follow with delay
    await h.setExpressionText(
      1,
      "position",
      `
      var delay = 0.2;
      thisComp.layer("Leader").position.valueAtTime(time - delay)
    `,
    );

    // Step 329-333: Layer index
    await h.isolateOpacity();
    await h.enablePropertyExpression(1, "opacity");
    await h.setExpressionText(
      1,
      "opacity",
      `
      var delay = index * 0.2;
      var t = Math.max(time - delay, 0);
      linear(t, 0, 0.5, 0, 100)
    `,
    );

    // Step 334-337: inPoint and outPoint
    await h.setExpressionText(
      1,
      "opacity",
      "linear(time - inPoint, 0, 1, 0, 100)",
    );
    // Fades in over 1 second from layer start

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });
});
