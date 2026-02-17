import { expect, test } from "@playwright/test";
import { CompositorHelper } from "../helpers/compositor";

test.describe("Tutorial 01: Phases 10-13 (Steps 241-355)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Test", 1920, 1080, 16, 5);
    await h.newSolid("Layer1");
  });

  test("Phase 10: Easing & CurveEditor (Steps 241-275)", async ({ page }) => {
    await h.selectLayer(0);
    await h.isolatePosition();
    await h.toggleStopwatch("position");
    await h.goToFrame(16);
    // Change position to create animation

    // Step 242: F9 Smooth Ease
    await h.smoothEase();

    // Step 247-250: CurveEditor
    await h.toggleCurveEditor();
    await expect(page.locator('[data-testid="curve-editor"]')).toBeVisible();

    // Step 261-265: Graph types
    await h.setCurveEditorGraphType("value");
    await h.setCurveEditorGraphType("speed");

    // Step 266-270: Separate dimensions
    await h.separateDimensions("position");

    await h.toggleCurveEditor();

    // UNDO TEST
    await h.undo();
    await h.redo();
  });

  test("Phase 11: Fading Elements (Steps 276-295)", async ({ page }) => {
    await h.selectLayer(0);

    // Step 280-286: Fade in
    await h.isolateOpacity();
    await h.goToStart();
    await h.toggleStopwatch("opacity");
    await h.setPropertyValue("opacity", "0");
    await h.goToFrame(15);
    await h.setPropertyValue("opacity", "100");

    // Step 287-291: Fade out
    await h.goToFrame(65);
    // Add keyframe at current value
    await h.goToFrame(80);
    await h.setPropertyValue("opacity", "0");

    // Step 292-295: Apply easing
    await h.smoothEase();

    // UNDO TEST
    await h.undo();
    await h.redo();
  });

  test("Phase 12: Text Layers (Steps 296-325)", async ({ page }) => {
    // Step 296-300: Create text
    await h.newTextLayer("LATTICE COMPOSITOR");
    await h.expectLayerCount(2);

    // Step 301-307: Character Panel
    await h.openCharacterPanel();
    await expect(page.locator('[data-testid="character-panel"]')).toBeVisible();

    // Step 308-310: Paragraph Panel
    await h.openParagraphPanel();
    await expect(page.locator('[data-testid="paragraph-panel"]')).toBeVisible();

    // Step 311-318: Animate text
    await h.selectLayer(0);
    await h.isolatePosition();
    await h.toggleStopwatch("position");

    // UNDO TEST
    await h.undo();
    await h.redo();
  });

  test("Phase 13: Align Panel & Snapping (Steps 326-355)", async ({ page }) => {
    // Step 326-333: Align Panel
    await h.openAlignPanel();
    await h.selectLayer(0);
    await h.alignHorizontalCenter();
    await h.alignVerticalCenter();

    // Step 339-342: Grid
    await h.toggleGrid();
    await h.toggleGrid();

    // Step 343-347: Rulers
    await h.toggleRulers();
    await h.toggleRulers();

    // Step 349: Center layer
    await h.centerLayerInComp();

    // UNDO TEST
    await h.undo();
    await h.redo();
  });
});
