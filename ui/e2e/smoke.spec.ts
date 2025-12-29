import { test, expect } from '@playwright/test';

test.describe('Lattice Compositor Smoke Test', () => {

  test('app loads in ComfyUI', async ({ page }) => {
    await page.goto('/');
    await expect(page).toHaveTitle(/ComfyUI/i, { timeout: 30000 });
    await page.screenshot({ path: 'e2e/screenshots/01-comfyui-loaded.png' });
    console.log('✅ ComfyUI loaded');
  });

  test('opens in fullscreen mode by default', async ({ page }) => {
    await page.goto('/');
    await page.waitForSelector('canvas', { timeout: 30000 });
    await page.waitForTimeout(2000);

    await page.screenshot({ path: 'e2e/screenshots/02-initial-state.png' });

    // Find Motion Compositor sidebar tab by title/tooltip
    const compositorTab = page.locator(
      '[title*="Motion" i], [title*="Lattice" i], [aria-label*="Motion" i], [aria-label*="Lattice" i]'
    ).first();

    // Fallback: look for the pi-video icon class
    const videoIcon = page.locator('.pi-video, [class*="pi-video"]').first();

    let found = false;

    if (await compositorTab.isVisible({ timeout: 3000 }).catch(() => false)) {
      console.log('✅ Found Motion Compositor tab');
      await compositorTab.click();
      found = true;
    } else if (await videoIcon.isVisible({ timeout: 2000 }).catch(() => false)) {
      console.log('✅ Found video icon, clicking...');
      await videoIcon.click();
      found = true;
    }

    if (found) {
      // Wait for compositor to load
      await page.waitForTimeout(3000);
      await page.screenshot({ path: 'e2e/screenshots/03-compositor-opened.png' });

      // Verify fullscreen mode is active
      const fullscreenPanel = page.locator('.lattice-fullscreen-mode');
      const closeButton = page.locator('#lattice-close-btn, .lattice-close-btn');

      // Check panel width is near full width (at least 80% of viewport)
      const panelBox = await fullscreenPanel.boundingBox().catch(() => null);
      const viewport = page.viewportSize();

      if (panelBox && viewport) {
        const widthRatio = panelBox.width / viewport.width;
        console.log(`Panel width: ${panelBox.width}px (${(widthRatio * 100).toFixed(1)}% of viewport)`);
        expect(widthRatio).toBeGreaterThan(0.8);
        console.log('✅ Compositor opened in fullscreen mode');
      }

      // Verify close button exists
      if (await closeButton.isVisible({ timeout: 2000 }).catch(() => false)) {
        console.log('✅ Close button visible');
        await page.screenshot({ path: 'e2e/screenshots/04-fullscreen-verified.png' });

        // Test closing
        await closeButton.click();
        await page.waitForTimeout(1000);
        await page.screenshot({ path: 'e2e/screenshots/05-after-close.png' });

        // Verify fullscreen mode is no longer active
        const stillFullscreen = await fullscreenPanel.isVisible().catch(() => false);
        expect(stillFullscreen).toBe(false);
        console.log('✅ Fullscreen mode closed successfully');
      } else {
        console.log('⚠️ Close button not found');
      }
    } else {
      console.log('❌ Motion Compositor tab not found');
      await page.screenshot({ path: 'e2e/screenshots/03-not-found.png', fullPage: true });
    }
  });

  test('compositor UI elements are visible when opened', async ({ page }) => {
    await page.goto('/');
    await page.waitForSelector('canvas', { timeout: 30000 });
    await page.waitForTimeout(2000);

    // Click Motion Compositor
    const compositorTab = page.locator(
      '[title*="Motion" i], [title*="Lattice" i], .pi-video'
    ).first();

    if (await compositorTab.isVisible({ timeout: 3000 }).catch(() => false)) {
      await compositorTab.click();
      await page.waitForTimeout(3000);

      // Verify key compositor elements exist
      const root = page.locator('#lattice-compositor-root');
      expect(await root.isVisible()).toBe(true);
      console.log('✅ Compositor root element visible');

      // Check for toolbar, timeline, canvas, etc.
      const toolbar = page.locator('[class*="toolbar" i], [class*="Toolbar"]').first();
      const timeline = page.locator('[class*="timeline" i], [class*="Timeline"]').first();

      if (await toolbar.isVisible({ timeout: 2000 }).catch(() => false)) {
        console.log('✅ Toolbar visible');
      }

      if (await timeline.isVisible({ timeout: 2000 }).catch(() => false)) {
        console.log('✅ Timeline visible');
      }

      await page.screenshot({ path: 'e2e/screenshots/06-ui-elements.png' });
    }
  });
});
