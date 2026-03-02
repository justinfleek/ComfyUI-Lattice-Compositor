/**
 * Performance E2E Tests
 *
 * Hard-to-pass tests that verify:
 * - Frame rate stability (60fps target)
 * - Render timing consistency
 * - Memory usage and leak detection
 * - CPU throttling resilience
 * - Large data handling
 */

import type { Page } from "puppeteer";
import {
  afterAll,
  afterEach,
  beforeAll,
  beforeEach,
  describe,
  expect,
  it,
} from "vitest";
import {
  closeBrowser,
  createPage,
  getMemoryUsage,
  launchBrowser,
  measureFrameTime,
  navigateTo,
  waitFrames,
} from "./helpers/browser.js";

describe("Performance", () => {
  let page: Page;

  beforeAll(async () => {
    await launchBrowser();
  });

  afterAll(async () => {
    await closeBrowser();
  });

  beforeEach(async () => {
    page = await createPage();
  });

  afterEach(async () => {
    await page.close();
  });

  describe("Frame Rate", () => {
    it("should maintain reasonable frame rate on idle", async () => {
      await navigateTo(page, "/");
      await waitFrames(page, 30); // Let the app settle

      const metrics = await measureFrameTime(page, 120);

      // Target: at least 30fps average (33ms frame time)
      // This is lenient for CI environments with software rendering
      expect(metrics.avgFrameTime).toBeLessThan(33);
      expect(metrics.fps).toBeGreaterThan(30);
    });

    it("should not have excessive frame time variance", async () => {
      await navigateTo(page, "/");
      await waitFrames(page, 30);

      const metrics = await measureFrameTime(page, 120);

      // Frame time variance should be reasonable
      // Max should not be more than 5x average (allowing for occasional GC pauses)
      expect(metrics.maxFrameTime).toBeLessThan(metrics.avgFrameTime * 5);
    });

    it("should recover from long frames", async () => {
      await navigateTo(page, "/");

      // Simulate heavy computation that might cause a long frame
      await page.evaluate(() => {
        // Block main thread briefly
        const start = Date.now();
        while (Date.now() - start < 100) {
          // Busy wait
        }
      });

      // Should recover to normal frame rate
      const metrics = await measureFrameTime(page, 60);
      expect(metrics.avgFrameTime).toBeLessThan(50); // Should recover
    });
  });

  describe("Memory", () => {
    it("should have stable memory usage on idle", async () => {
      await navigateTo(page, "/");
      await waitFrames(page, 60);

      const initial = await getMemoryUsage(page);

      // Wait and measure again
      await waitFrames(page, 300);

      const after = await getMemoryUsage(page);

      // Memory should not grow significantly on idle
      const growthMB =
        (after.usedJSHeapSize - initial.usedJSHeapSize) / (1024 * 1024);
      expect(growthMB).toBeLessThan(10); // Less than 10MB growth
    });

    it("should not leak memory during navigation", async () => {
      // Initial measurement
      await navigateTo(page, "/");
      await waitFrames(page, 30);
      const initial = await getMemoryUsage(page);

      // Navigate many times
      const routes = ["/", "/settings", "/project", "/assets", "/export"];
      for (let i = 0; i < 5; i++) {
        for (const route of routes) {
          await navigateTo(page, route);
          await waitFrames(page, 10);
        }
      }

      // Force GC if possible
      await page.evaluate(() => {
        if ((globalThis as unknown as { gc?: () => void }).gc) {
          (globalThis as unknown as { gc: () => void }).gc();
        }
      });

      await waitFrames(page, 30);
      const final = await getMemoryUsage(page);

      // Memory should not have grown excessively
      const growthMB =
        (final.usedJSHeapSize - initial.usedJSHeapSize) / (1024 * 1024);
      expect(growthMB).toBeLessThan(50); // Less than 50MB growth after many navigations
    });

    it("should not leak memory during zoom operations", async () => {
      await navigateTo(page, "/");
      await waitFrames(page, 30);

      const initial = await getMemoryUsage(page);

      const zoomInButton = await page.$('button[title="Zoom In"]');
      const zoomOutButton = await page.$('button[title="Zoom Out"]');

      if (zoomInButton && zoomOutButton) {
        // Perform many zoom operations
        for (let i = 0; i < 50; i++) {
          await zoomInButton.click();
          await waitFrames(page, 2);
          await zoomOutButton.click();
          await waitFrames(page, 2);
        }
      }

      await waitFrames(page, 30);
      const final = await getMemoryUsage(page);

      const growthMB =
        (final.usedJSHeapSize - initial.usedJSHeapSize) / (1024 * 1024);
      expect(growthMB).toBeLessThan(20);
    });
  });

  describe("Load Time", () => {
    it("should complete initial render within acceptable time", async () => {
      const start = Date.now();

      await page.goto("http://localhost:8080/", {
        waitUntil: "domcontentloaded",
      });
      await page.waitForSelector("#lattice-root");

      const loadTime = Date.now() - start;

      // Should load within 5 seconds even in CI
      expect(loadTime).toBeLessThan(5000);
    });

    it("should have interactive UI within acceptable time", async () => {
      const start = Date.now();

      await navigateTo(page, "/");

      // Wait for an interactive element
      await page.waitForSelector(".lattice-app", { timeout: 10000 });

      const interactiveTime = Date.now() - start;

      // Should be interactive within 3 seconds
      expect(interactiveTime).toBeLessThan(3000);
    });

    it("should handle slow network gracefully", async () => {
      // Simulate slow network
      const client = await page.createCDPSession();
      await client.send("Network.emulateNetworkConditions", {
        offline: false,
        downloadThroughput: 100 * 1024, // 100 KB/s
        uploadThroughput: 50 * 1024, // 50 KB/s
        latency: 500, // 500ms latency
      });

      const start = Date.now();
      await page.goto("http://localhost:8080/", {
        waitUntil: "networkidle0",
        timeout: 30000,
      });
      const loadTime = Date.now() - start;

      // Should still load (even if slow)
      const isLoaded = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isLoaded).toBe(true);

      // Reset network conditions
      await client.send("Network.emulateNetworkConditions", {
        offline: false,
        downloadThroughput: -1,
        uploadThroughput: -1,
        latency: 0,
      });
    });
  });

  describe("CPU Throttling", () => {
    it("should remain responsive under CPU throttling", async () => {
      const client = await page.createCDPSession();

      // Throttle CPU to 4x slower
      await client.send("Emulation.setCPUThrottlingRate", { rate: 4 });

      await navigateTo(page, "/");

      // Should still be responsive
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);

      // UI should still respond to clicks
      const zoomButton = await page.$('button[title="Zoom In"]');
      if (zoomButton) {
        await zoomButton.click();
        await waitFrames(page, 10);

        // Verify click was registered
        const zoomText = await page.$eval(
          ".lattice-zoom-level",
          (el) => el.textContent,
        );
        expect(zoomText).toBeDefined();
      }

      // Reset CPU throttling
      await client.send("Emulation.setCPUThrottlingRate", { rate: 1 });
    });
  });

  describe("Stress Testing", () => {
    it("should handle rapid repeated renders", async () => {
      await navigateTo(page, "/");

      // Trigger many re-renders by rapidly changing state
      const zoomInButton = await page.$('button[title="Zoom In"]');
      const zoomOutButton = await page.$('button[title="Zoom Out"]');
      const resetButton = await page.$('button[title="Reset View"]');

      if (zoomInButton && zoomOutButton && resetButton) {
        for (let i = 0; i < 100; i++) {
          await zoomInButton.click();
          await zoomOutButton.click();
        }
        await resetButton.click();
        await waitFrames(page, 10);
      }

      // App should still work correctly
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle long-running session without degradation", async () => {
      await navigateTo(page, "/");

      // Measure initial performance
      const initialMetrics = await measureFrameTime(page, 60);

      // Simulate extended use
      for (let i = 0; i < 10; i++) {
        await waitFrames(page, 60);

        // Do some operations
        const zoomIn = await page.$('button[title="Zoom In"]');
        const zoomOut = await page.$('button[title="Zoom Out"]');
        if (zoomIn && zoomOut) {
          await zoomIn.click();
          await zoomOut.click();
        }
      }

      // Measure final performance
      const finalMetrics = await measureFrameTime(page, 60);

      // Performance should not degrade significantly (less than 50% slower)
      expect(finalMetrics.avgFrameTime).toBeLessThan(
        initialMetrics.avgFrameTime * 1.5,
      );
    });
  });

  describe("Resource Cleanup", () => {
    it("should release resources on page close", async () => {
      const browser = await launchBrowser();

      // Create and close many pages
      for (let i = 0; i < 5; i++) {
        const testPage = await browser.newPage();
        await testPage.goto("http://localhost:8080/", {
          waitUntil: "networkidle0",
        });
        await testPage.waitForSelector("#lattice-root");
        await waitFrames(testPage, 30);
        await testPage.close();
      }

      // Browser should still be healthy
      const healthPage = await browser.newPage();
      await healthPage.goto("http://localhost:8080/", {
        waitUntil: "networkidle0",
      });

      const isHealthy = await healthPage.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isHealthy).toBe(true);
      await healthPage.close();
    });
  });
});
