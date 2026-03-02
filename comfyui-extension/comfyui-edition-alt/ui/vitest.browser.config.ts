/**
 * Vitest Browser Mode Configuration
 *
 * Runs integration tests in a REAL Chromium browser with WebGL support.
 * Use this for testing LatticeEngine, Three.js rendering, and WebGL operations.
 */

import { fileURLToPath } from "node:url";
import vue from "@vitejs/plugin-vue";
import { playwright } from "@vitest/browser-playwright";
import { defineConfig } from "vitest/config";

export default defineConfig({
  plugins: [vue()],
  resolve: {
    alias: {
      "@": fileURLToPath(new URL("./src", import.meta.url)),
    },
  },
  test: {
    globals: true,
    include: ["src/__tests__/browser/**/*.{test,spec}.{js,ts}"],
    browser: {
      enabled: true,
      provider: playwright({
        launch: {
          args: ["--use-gl=angle"], // Enable WebGL in headless mode
        },
      }),
      instances: [{ browser: "chromium" }],
      headless: true,
    },
    // Longer timeout for browser tests
    testTimeout: 30000,
  },
});
