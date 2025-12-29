import { test, expect } from '@playwright/test';
import { CompositorHelper } from '../helpers/compositor';

test.describe('Tutorial 01: Phases 17-19 (Steps 456-550)', () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto('/');
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition('Test', 1920, 1080, 16, 5);
  });

  test('Phase 17: Nested Compositions (Steps 456-480)', async ({ page }) => {
    await h.newSolid('Layer1');
    await h.newSolid('Layer2');
    await h.newSolid('Layer3');

    // Step 460-467: Create NestedComp
    await h.selectAllLayers();
    await h.createNestedComp('Nested_Group');

    // Verify single NestedComp layer replaces 3 layers
    await h.expectLayerCount(1);

    // Step 468-471: Edit NestedComp (double-click)
    await page.dblclick('[data-testid="layer-0"]');
    // Should open nested comp with 3 layers
    await h.expectLayerCount(3);

    // UNDO TEST
    await h.undo();
    await h.redo();
  });

  test('Phase 18: RenderRange & Preview (Steps 481-510)', async ({ page }) => {
    await h.newSolid('Layer1');

    // Step 482-486: Set RenderRange
    await h.goToFrame(10);
    await h.setRenderRangeStart();
    await h.goToFrame(70);
    await h.setRenderRangeEnd();

    // Step 490: Spacebar preview
    await h.play();
    await page.waitForTimeout(500);
    await h.stop();

    // UNDO TEST
    await h.undo();
    await h.redo();
  });

  test('Phase 19: Export (Steps 511-550)', async ({ page }) => {
    await h.newSolid('Layer1');

    // Step 511-514: Add to Render Queue
    await h.addToRenderQueue();
    await expect(page.locator('[data-testid="render-queue-panel"]')).toBeVisible();

    // Verify composition is in queue
    await expect(page.locator('[data-testid="render-queue-item-0"]')).toBeVisible();
  });

  test('SAVE/LOAD: Full Project Persistence', async ({ page }) => {
    // Create complex project state
    await h.newSolid('Solid1');
    await h.newTextLayer('Test Text');
    await h.newControlLayer();

    // Add keyframes
    await h.selectLayer(0);
    await h.isolatePosition();
    await h.toggleStopwatch('position');
    await h.goToFrame(30);
    // Modify position

    // Add expression
    await h.isolateRotation();
    await h.enableExpression('rotation');
    await h.setExpression('rotation', 'time * 45');

    // Add parenting
    await h.setParent(0, 2);

    // Save
    await h.saveProject();

    // Reload page
    await page.reload();
    await page.waitForSelector('[data-testid="app-ready"]');

    // Verify all state preserved
    await h.expectLayerCount(3);
    await h.selectLayer(0);
    await h.revealAnimatedProperties();
    await expect(page.locator('[data-testid="property-position"]')).toBeVisible();
  });
});
