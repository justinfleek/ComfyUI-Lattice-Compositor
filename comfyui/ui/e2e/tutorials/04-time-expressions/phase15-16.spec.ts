import { expect, test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 04: Expressions - Phases 15-16 (Steps 338-385)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Expression_Test", 1920, 1080, 24, 10);
    await h.newSolid("ControlledLayer");
  });

  test("Phase 15: Expression Controls (Steps 338-365)", async ({ page }) => {
    // Step 338-345: Slider Control
    await h.addSliderControl(0, "Size");
    await h.setSliderValue(0, 50);

    await h.isolateScale();
    await h.enablePropertyExpression(0, "scale");
    await h.setExpressionText(
      0,
      "scale",
      `
      var s = effect("Size")("Slider");
      [s, s]
    `,
    );

    // Step 346-350: Checkbox Control
    await h.addCheckboxControl(0, "Show");
    await h.setCheckboxValue(1, true);

    await h.isolateOpacity();
    await h.enablePropertyExpression(0, "opacity");
    await h.setExpressionText(0, "opacity", 'effect("Show")("Checkbox") * 100');
    // Opacity 0 or 100

    // Step 351-353: Color Control
    await h.addColorControl(0, "Fill Color");
    await h.setColorControlValue(2, "#FF0000");
    // Expression: effect("Fill Color")("Color")

    // Step 354-357: Point Control
    await h.addPointControl(0, "Target");
    await h.setPointControlValue(3, 960, 540);

    await h.isolatePosition();
    await h.enablePropertyExpression(0, "position");
    await h.setExpressionText(0, "position", 'effect("Target")("Point")');

    // Step 358-361: Dropdown Control
    await h.addDropdownControl(0, "Position Preset");
    await h.setExpressionText(
      0,
      "position",
      `
      var menu = effect("Position Preset")("Menu").value;
      if (menu == 1) { [100, 540]; }
      else if (menu == 2) { [960, 540]; }
      else { [1820, 540]; }
    `,
    );

    await h.setDropdownValue(4, 1);
    await h.setDropdownValue(4, 2);

    // Step 362-365: Layer Control
    await h.newSolid("TargetLayer");
    await h.selectLayer(0);
    await h.addLayerControl(0, "Follow Layer");
    await h.setLayerControlTarget(5, 1);

    await h.setExpressionText(
      0,
      "position",
      `
      var target = effect("Follow Layer")("Layer");
      target.position
    `,
    );

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });

  test("Phase 16: Undo/Redo Verification (Steps 366-385)", async ({ page }) => {
    await h.newSolid("TimeLayer");
    await h.setLayerEndFrame(0, 120);

    // Step 366-371: SpeedMap undo
    await h.enableSpeedMap(0);
    await h.goToFrame(60);
    await h.addSpeedMapKeyframe(0, 30);

    await h.undo();
    // Keyframe removed
    await h.redo();
    // Keyframe restored

    // Step 372-377: Expression undo
    await h.selectLayer(1);
    await h.isolatePosition();
    await h.enablePropertyExpression(1, "position");
    await h.setExpressionText(1, "position", "[500, 500]");

    await h.undo();
    // Expression reverted
    await h.undo();
    // Expression disabled

    await h.redo();
    await h.redo();

    // Step 378-380: Time stretch undo
    await h.selectLayer(0);
    await h.setTimeStretch(0, 200);
    await h.undo();
    const stretch = await h.getTimeStretch(0);
    expect(stretch).toBe(100);

    // Step 381-383: Frame blending undo
    await h.setFrameBlending(0, "motion");
    await h.undo();
    // Should be 'none'

    // Step 384-385: Multiple undo
    await h.setTimeStretch(0, 150);
    await h.setTimeStretch(0, 200);
    await h.setTimeStretch(0, 250);
    await h.setTimeStretch(0, 300);
    await h.setTimeStretch(0, 350);

    await h.undo();
    await h.undo();
    await h.undo();
    await h.undo();
    await h.undo();

    await h.redo();
    await h.redo();
    await h.redo();
    await h.redo();
    await h.redo();
  });
});
