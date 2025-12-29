import { test, expect } from '@playwright/test';
import { CompositorHelper } from '../../helpers/compositor';

test.describe('Tutorial 02: Neon Motion Trails - Phases 6-7 (Steps 83-135)', () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto('/');
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition('Test', 1920, 1080, 30, 10);
    await h.newShapeLayer('Light_Streak_01');
    await h.addTrimPaths(0);
  });

  test('Phase 6: Animating Light Streak - Draw On (Steps 83-99)', async ({ page }) => {
    // Step 83-87: Setup at frame 0
    await h.goToStart();
    await h.setTrimPathsStart(0, 0);
    await h.setTrimPathsEnd(0, 0);
    await h.enableTrimPathsKeyframes(0, 'start');
    await h.enableTrimPathsKeyframes(0, 'end');

    // Step 88-91: Frame 15 - partial draw
    await h.goToFrame(15);
    await h.setTrimPathsEnd(0, 20);

    // Step 92-95: Frame 30 - complete
    await h.goToFrame(30);
    await h.setTrimPathsStart(0, 80);
    await h.setTrimPathsEnd(0, 100);

    // Step 96-99: Apply easing
    await h.selectAllLayers();
    await h.smoothEase();

    // Preview
    await h.goToStart();
    await h.play();
    await page.waitForTimeout(2000);
    await h.stop();

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });

  test('Phase 6: Animating Light Streak - Offset Loop (Steps 100-112)', async ({ page }) => {
    // Step 100-101: Static trim values
    await h.setTrimPathsStart(0, 0);
    await h.setTrimPathsEnd(0, 15);

    // Step 102-105: Animate offset
    await h.goToStart();
    await h.enableTrimPathsKeyframes(0, 'offset');
    await h.setTrimPathsOffset(0, 0);
    await h.goToFrame(60);
    await h.setTrimPathsOffset(0, 360);

    // Preview continuous loop
    await h.goToStart();
    await h.play();
    await page.waitForTimeout(2000);
    await h.stop();

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });

  test('Phase 7: Multiple Streaks (Steps 113-135)', async ({ page }) => {
    // Setup initial animation
    await h.setTrimPathsStart(0, 0);
    await h.setTrimPathsEnd(0, 15);
    await h.goToStart();
    await h.enableTrimPathsKeyframes(0, 'offset');
    await h.setTrimPathsOffset(0, 0);
    await h.goToFrame(60);
    await h.setTrimPathsOffset(0, 360);

    // Step 113-118: Duplicate and stagger
    await h.selectLayer(0);
    await h.duplicateLayer();
    await h.renameLayer('Light_Streak_02');

    // Step 120-125: Create more streaks
    await h.duplicateLayer();
    await h.renameLayer('Light_Streak_03');
    await h.duplicateLayer();
    await h.renameLayer('Light_Streak_04');
    await h.duplicateLayer();
    await h.renameLayer('Light_Streak_05');

    await h.expectLayerCount(5);

    // Step 126-129: Vary stroke widths
    await h.selectLayer(1);
    await h.setStrokeWidth(1, 8);
    await h.selectLayer(2);
    await h.setStrokeWidth(2, 25);
    await h.selectLayer(3);
    await h.setStrokeWidth(3, 5);
    await h.selectLayer(4);
    await h.setStrokeWidth(4, 20);

    // Step 130-132: Color variations
    await h.setStrokeColor(1, '#00FFFF');
    await h.setStrokeColor(3, '#FFFF00');

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });
});
