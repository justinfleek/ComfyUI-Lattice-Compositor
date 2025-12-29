import { test, expect } from '@playwright/test';
import { CompositorHelper } from '../helpers/compositor';

test.describe('Tutorial 01: Phases 14-16 (Steps 356-455)', () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto('/');
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition('Test', 1920, 1080, 16, 5);
    await h.newSolid('Layer1');
  });

  test('Phase 14: Effects (Steps 356-390)', async ({ page }) => {
    // Step 356-358: Effects Panel
    await h.openEffectsPanel();
    await expect(page.locator('[data-testid="effects-panel"]')).toBeVisible();

    // Step 359-363: Apply Glow
    await h.selectLayer(0);
    await h.searchEffects('Glow');
    await h.applyEffect('glow');

    // Step 368-371: Apply Drop Shadow
    await h.searchEffects('Drop Shadow');
    await h.applyEffect('drop-shadow');

    // Step 380-381: Toggle effect
    await h.toggleEffectEnabled(0);
    await h.toggleEffectEnabled(0);

    // Step 383-387: EffectLayer
    await h.newEffectLayer();
    await h.expectLayerCount(2);

    // UNDO TEST
    await h.undo();
    await h.redo();
  });

  test('Phase 15: Parenting (Steps 391-420)', async ({ page }) => {
    await h.newSolid('Child1');
    await h.newSolid('Child2');
    await h.newControlLayer();

    // Step 397-400: PropertyLink parenting
    await h.setParent(0, 2); // Parent Child1 to Control
    await h.setParent(1, 2); // Parent Child2 to Control

    // Step 404: Remove parent
    await h.setParent(0, null);

    // UNDO TEST
    await h.undo();
    await h.redo();
  });

  test('Phase 16: Expressions (Steps 421-455)', async ({ page }) => {
    await h.selectLayer(0);

    // Step 424-428: Enable expression
    await h.isolatePosition();
    await h.enableExpression('position');

    // Step 434-438: Wiggle
    await h.setExpression('position', 'wiggle(2, 50)');

    // Step 444-448: Time expression on rotation
    await h.isolateRotation();
    await h.enableExpression('rotation');
    await h.setExpression('rotation', 'time * 90');

    // DETERMINISM TEST for expressions
    await h.verifyDeterminism(['position', 'rotation'], 40);

    // UNDO TEST
    await h.undo();
    await h.redo();
  });
});
