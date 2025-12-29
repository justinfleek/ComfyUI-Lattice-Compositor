import { defineConfig, devices } from '@playwright/test';

export default defineConfig({
  testDir: './e2e',
  fullyParallel: false, // Run tests sequentially for UI testing
  forbidOnly: !!process.env.CI,
  retries: 0,
  workers: 1,
  reporter: [
    ['html', { open: 'never' }],
    ['list']
  ],
  timeout: 60000, // 60s per test
  
  use: {
    // ComfyUI serves Lattice UI
    baseURL: 'http://localhost:8188',
    
    // Record everything for debugging
    trace: 'on',
    screenshot: 'on',
    video: 'on',
    
    // Slow down for visibility
    launchOptions: {
      slowMo: 100,
    },
  },

  projects: [
    {
      name: 'chromium',
      use: { 
        ...devices['Desktop Chrome'],
        // For WSL: use Windows Chrome
        channel: 'chrome',
      },
    },
  ],
});
