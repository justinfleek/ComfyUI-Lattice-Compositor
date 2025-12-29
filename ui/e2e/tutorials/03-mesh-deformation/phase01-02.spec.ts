import { test, expect } from '@playwright/test';
import { CompositorHelper } from '../../helpers/compositor';

test.describe('Tutorial 03: Mesh Deformation - Phases 1-2 (Steps 1-22)', () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto('/');
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
  });

  test('Phase 1: Artwork Preparation (Steps 1-9)', async ({ page }) => {
    // Step 1-3: Create composition for character
    await h.newComposition('Character_Comp', 1920, 1080, 30, 10);
    await h.newSolid('Character_Art');

    // Step 4-6: Verify composition settings
    await h.openCompositionSettings();
    await expect(page.locator('[data-testid="comp-fps"]')).toHaveValue('30');
    await page.keyboard.press('Escape');

    // Step 7-9: Layer setup
    await h.selectLayer(0);
    await h.expectLayerCount(1);

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });

  test('Phase 2: Mesh Deformation Effect (Steps 10-22)', async ({ page }) => {
    await h.newComposition('Test', 1920, 1080, 30, 10);
    await h.newSolid('Character');

    // Step 10-15: Apply mesh deformation via pin tool
    await h.selectDeformPinTool();
    await h.placePinAtPosition(960, 540);

    // Verify mesh deformation auto-applied
    await h.expectMeshDeformationEffect(0);
    await h.expectMeshGenerated(0);

    // Step 16-18: Mesh configuration
    await h.setMeshTriangleCount(0, 100);
    await h.setMeshTriangleCount(0, 400);
    await h.setMeshTriangleCount(0, 50);

    await h.setMeshExpansion(0, 5);
    await h.setMeshExpansion(0, 8);
    await h.setMeshExpansion(0, 3);

    // Step 19-22: Mesh visualization
    await h.toggleMeshVisibility(0);
    await expect(page.locator('[data-testid="layer-0-mesh-overlay"]')).toBeVisible();
    await h.toggleMeshVisibility(0);
    await expect(page.locator('[data-testid="layer-0-mesh-overlay"]')).not.toBeVisible();

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });
});
