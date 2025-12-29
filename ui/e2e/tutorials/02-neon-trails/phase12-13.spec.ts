import { test, expect } from '@playwright/test';
import { CompositorHelper } from '../../helpers/compositor';

test.describe('Tutorial 02: Neon Motion Trails - Phases 12-13 (Steps 226-272)', () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto('/');
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition('Test', 1920, 1080, 30, 10);
  });

  test('Phase 12: Path-Based Position Animation (Steps 226-248)', async ({ page }) => {
    // Step 226-228: Create motion path layer
    await h.newShapeLayer('Motion_Path');

    // Step 229-232: Create object to animate
    await h.newShapeLayer('Traveling_Orb');
    await h.selectLayer(0);
    await h.searchEffects('Glow');
    await h.applyEffect('glow');

    // Step 233-238: Copy path to position
    await h.copyPathToPosition(1, 0);

    // Step 239-242: Adjust animation
    await h.selectLayer(0);
    await h.isolatePosition();
    await h.smoothEase();

    // Step 243-246: Auto-orient along path
    await h.enableAutoOrient(0, 'alongPath');

    // Step 247: Hide motion path
    await h.toggleLayerVisibility(1);

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });

  test('Phase 13: Gradient Strokes (Steps 249-272)', async ({ page }) => {
    await h.newShapeLayer('Light_Streak_01');

    // Step 249-252: Add gradient stroke
    await h.removeShapeFill(0);
    await h.addGradientStroke(0);

    // Step 253-256: Configure gradient type
    await h.configureGradientStroke(0, { type: 'linear' });

    // Step 265-270: Animate gradient
    await h.goToStart();
    await h.goToFrame(30);

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });
});
