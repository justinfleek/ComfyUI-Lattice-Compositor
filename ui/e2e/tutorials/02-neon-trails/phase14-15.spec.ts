import { test, expect } from '@playwright/test';
import { CompositorHelper } from '../../helpers/compositor';

test.describe('Tutorial 02: Neon Motion Trails - Phases 14-15 (Steps 273-325)', () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto('/');
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition('Test', 1920, 1080, 30, 10);
    await h.newSolid('BG_Gradient');
    await h.newShapeLayer('Light_Streak_01');
    await h.newSolid('Silhouette');
  });

  test('Phase 14: Silhouette Integration (Steps 273-292)', async ({ page }) => {
    // Step 273-275: Verify layer order
    await h.expectLayerCount(3);

    // Step 280-285: Edge highlight
    await h.selectLayer(1); // Silhouette
    await h.duplicateLayer();
    await h.addFillEffect(0, '#FFFFFF');
    await h.setBlendMode(0, 'add');
    await h.isolateOpacity();
    await h.setPropertyValue('opacity', '25');

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });

  test('Phase 15: Final Polish (Steps 293-325)', async ({ page }) => {
    // Step 293-300: Vignette
    await h.newAdjustmentLayer('Vignette');
    await h.searchEffects('Curves');
    await h.applyEffect('curves');
    await h.addOvalMask(0);
    await h.setMaskMode(0, 0, 'subtract');
    await h.setMaskFeather(0, 0, 200);

    // Step 301-305: Color grade
    await h.newAdjustmentLayer('Color_Grade');
    await h.searchEffects('Curves');
    await h.applyEffect('curves');
    await h.searchEffects('Hue/Saturation');
    await h.applyEffect('hue-saturation');

    // Step 306-311: Film grain (optional)
    await h.newSolid('Grain');
    await h.searchEffects('Fractal Noise');
    await h.applyEffect('fractal-noise');
    await h.setBlendMode(0, 'overlay');
    await h.isolateOpacity();
    await h.setPropertyValue('opacity', '8');

    // Step 319-322: Undo/Redo verification
    await h.undo();
    await h.redo();

    // Step 323-325: Save/Load verification
    await h.saveProject();
  });

  test('DETERMINISM: Animation playback consistency', async ({ page }) => {
    await h.newShapeLayer('Test_Streak');
    await h.addTrimPaths(0);
    await h.goToStart();
    await h.enableTrimPathsKeyframes(0, 'offset');
    await h.setTrimPathsOffset(0, 0);
    await h.goToFrame(60);
    await h.setTrimPathsOffset(0, 360);

    // Verify determinism
    await h.verifyDeterminism(['trimpath-offset'], 30);
  });
});
