import { test, expect } from '@playwright/test';

/**
 * Infrastructure Tests
 * 
 * Verify that browser testing infrastructure is working:
 * - Canvas 2D available
 * - WebGL available
 * - WebGL2 available
 * - Web Audio available
 */

test.describe('Browser Test Infrastructure', () => {
  test('Canvas 2D is available', async ({ page }) => {
    const hasCanvas = await page.evaluate(() => {
      const canvas = document.createElement('canvas');
      const ctx = canvas.getContext('2d');
      return ctx !== null;
    });
    expect(hasCanvas).toBe(true);
  });

  test('WebGL is available', async ({ page }) => {
    const hasWebGL = await page.evaluate(() => {
      const canvas = document.createElement('canvas');
      const gl = canvas.getContext('webgl');
      return gl !== null;
    });
    expect(hasWebGL).toBe(true);
  });

  test('WebGL2 is available', async ({ page }) => {
    const hasWebGL2 = await page.evaluate(() => {
      const canvas = document.createElement('canvas');
      const gl = canvas.getContext('webgl2');
      return gl !== null;
    });
    expect(hasWebGL2).toBe(true);
  });

  test('Web Audio is available', async ({ page }) => {
    const hasAudio = await page.evaluate(() => {
      try {
        const ctx = new AudioContext();
        ctx.close();
        return true;
      } catch {
        return false;
      }
    });
    expect(hasAudio).toBe(true);
  });

  test('OffscreenCanvas is available', async ({ page }) => {
    const hasOffscreen = await page.evaluate(() => {
      try {
        const canvas = new OffscreenCanvas(100, 100);
        return canvas !== null;
      } catch {
        return false;
      }
    });
    expect(hasOffscreen).toBe(true);
  });

  test('ImageData can be created and manipulated', async ({ page }) => {
    const result = await page.evaluate(() => {
      const canvas = document.createElement('canvas');
      canvas.width = 10;
      canvas.height = 10;
      const ctx = canvas.getContext('2d');
      if (!ctx) return null;
      
      // Draw red rectangle
      ctx.fillStyle = '#ff0000';
      ctx.fillRect(0, 0, 10, 10);
      
      // Read pixel
      const data = ctx.getImageData(5, 5, 1, 1).data;
      return { r: data[0], g: data[1], b: data[2], a: data[3] };
    });
    
    expect(result).not.toBeNull();
    expect(result?.r).toBe(255);
    expect(result?.g).toBe(0);
    expect(result?.b).toBe(0);
    expect(result?.a).toBe(255);
  });
});
