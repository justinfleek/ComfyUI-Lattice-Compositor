import { defineConfig, devices } from '@playwright/test';

/**
 * Playwright configuration for Lattice Compositor E2E tests
 * 
 * PREREQUISITES:
 * 1. ComfyUI must be running: python main.py --port 8188
 * 2. Lattice Compositor extension installed in ComfyUI/custom_nodes
 * 3. Open browser to localhost:8188, click "Motion Compositor" in left sidebar
 * 
 * Tests Canvas, WebGL, WebGPU, Web Audio, and DOM operations
 * in a real Chromium browser environment connected to ComfyUI.
 */

// Fix terminal size for proper test output formatting (WSL issue)
if (process.env.COLUMNS && parseInt(process.env.COLUMNS) > 1000) {
  process.env.COLUMNS = '120';
}
if (process.env.LINES && parseInt(process.env.LINES) < 2) {
  process.env.LINES = '30';
}

export default defineConfig({
  testDir: './e2e',
  fullyParallel: false,  // Sequential for UI testing
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 2 : 0,
  workers: parseInt(process.env.PLAYWRIGHT_WORKERS || '1'),  // Single worker for ComfyUI testing
  reporter: process.env.CI ? [['html'], ['json', { outputFile: 'test-results/results.json' }]] : 'html',
  timeout: parseInt(process.env.PLAYWRIGHT_TIMEOUT || '60000'),  // 60s per test
  
  use: {
    baseURL: process.env.COMFYUI_URL || 'http://localhost:8188',  // ComfyUI default port
    trace: 'on-first-retry',
    screenshot: process.env.SCREENSHOT_ON_FAILURE !== 'false' ? 'on' : 'off',
  },
  
  // Output directory for test artifacts
  outputDir: './test-results',

  projects: [
    {
      name: 'chromium',
      use: { 
        ...devices['Desktop Chrome'],
        // Enable WebGL and WebGPU
        launchOptions: {
          args: [
            '--enable-webgpu',
            '--enable-unsafe-webgpu',
            '--use-gl=angle',
            '--use-angle=gl',
          ],
        },
      },
    },
  ],

  //                                                                 // important
  // Start ComfyUI manually: cd /path/to/ComfyUI && python main.py --port 8188
  // The Lattice Compositor extension opens from left menu bar under "Motion Compositor"
  // 
  // webServer is disabled because ComfyUI is an external dependency
  // that must be started manually with the extension installed
});
