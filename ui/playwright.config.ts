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
export default defineConfig({
  testDir: './e2e',
  fullyParallel: false,  // Sequential for UI testing
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 2 : 0,
  workers: 1,  // Single worker for ComfyUI testing
  reporter: 'html',
  timeout: 60000,  // 60s per test
  
  use: {
    baseURL: 'http://localhost:8188',  // ComfyUI default port
    trace: 'on-first-retry',
    screenshot: 'on',
  },

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

  // IMPORTANT: ComfyUI must be running BEFORE tests
  // Start ComfyUI manually: cd /path/to/ComfyUI && python main.py --port 8188
  // The Lattice Compositor extension opens from left menu bar under "Motion Compositor"
  // 
  // webServer is disabled because ComfyUI is an external dependency
  // that must be started manually with the extension installed
});
