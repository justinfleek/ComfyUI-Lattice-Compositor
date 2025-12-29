import { test, expect } from '@playwright/test';
import { CompositorHelper } from '../helpers/compositor';

test.describe('Tutorial 01: Fundamentals - Phases 1-3', () => {
  let helper: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    helper = new CompositorHelper(page);
    await page.goto('/');
    await page.waitForSelector('[data-testid="app-ready"]');
  });

  test('Phase 1: Project Setup (Steps 1-15)', async ({ page }) => {
    // Step 2: Create New Project
    await helper.newProject();
    await expect(page.locator('[data-testid="project-panel"]')).toBeVisible();

    // Step 4: Create folders
    await page.click('[data-testid="project-panel"]', { button: 'right' });
    await page.click('text=New Folder');
    await page.fill('[data-testid="folder-name-input"]', 'Assets');
    await page.keyboard.press('Enter');

    // Step 15: Save project
    await helper.saveProject();
  });

  test('Phase 2: Composition Creation (Steps 16-30)', async ({ page }) => {
    await helper.newProject();

    // Step 16-18: Create composition
    await helper.newComposition('Main_Comp', 1920, 1080, 16, 5);

    // Verify composition created
    await expect(page.locator('[data-testid="composition-panel"]')).toBeVisible();
    await expect(page.locator('[data-testid="timeline-panel"]')).toBeVisible();

    // Step 23: Create second composition
    await helper.newComposition('Test_Comp', 1920, 1080, 16, 5);

    // Verify tabs
    await expect(page.locator('[data-testid="comp-tab-Main_Comp"]')).toBeVisible();
    await expect(page.locator('[data-testid="comp-tab-Test_Comp"]')).toBeVisible();
  });

  test('Phase 3: Adding Layers (Steps 31-60)', async ({ page }) => {
    await helper.newProject();
    await helper.newComposition('Main_Comp');

    // Step 42: Create Solid layer
    await helper.newSolid('Background');
    await helper.expectLayerCount(1);

    // Step 45: Create EffectLayer
    await helper.newEffectLayer();
    await helper.expectLayerCount(2);

    // Step 46: Create Control layer
    await helper.newControlLayer();
    await helper.expectLayerCount(3);

    // Step 51: Duplicate layer
    await helper.selectLayer(0);
    await helper.duplicateLayer();
    await helper.expectLayerCount(4);

    // Step 53-54: Delete and undo
    await helper.deleteLayer();
    await helper.expectLayerCount(3);
    await helper.undo();
    await helper.expectLayerCount(4);

    // Step 55-60: Layer selection
    await page.keyboard.press('Control+a'); // Select all
  });
});
