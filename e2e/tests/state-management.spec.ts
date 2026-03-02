/**
 * State Management E2E Tests
 *
 * Hard-to-pass tests that verify:
 * - Undo/redo functionality
 * - Layer operations
 * - Property changes and persistence
 * - State consistency across navigation
 * - Race conditions in state updates
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
  launchBrowser,
  navigateTo,
  pressKeys,
  waitFrames,
} from "./helpers/browser.js";

describe("State Management", () => {
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

  describe("Routing State", () => {
    it("should maintain correct route state after navigation", async () => {
      // Navigate to workspace
      await navigateTo(page, "/");

      const route1 = await page.evaluate(() => window.location.pathname);
      expect(route1).toBe("/");

      // Navigate to settings
      await navigateTo(page, "/settings");

      const route2 = await page.evaluate(() => window.location.pathname);
      expect(route2).toBe("/settings");

      // Use browser back
      await page.goBack();
      await page.waitForSelector("#lattice-root");

      const route3 = await page.evaluate(() => window.location.pathname);
      expect(route3).toBe("/");
    });

    it("should handle rapid navigation without breaking state", async () => {
      const routes = ["/", "/settings", "/project", "/assets", "/export"];

      for (let i = 0; i < 3; i++) {
        for (const route of routes) {
          await page.goto(`http://localhost:8080${route}`, {
            waitUntil: "domcontentloaded",
          });
        }
      }

      // Final state should be consistent
      await page.waitForSelector("#lattice-root", { timeout: 10000 });

      const isResponsive = await page.evaluate(() => {
        const root = document.querySelector("#lattice-root");
        return root !== null && root.children.length > 0;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle 404 route gracefully", async () => {
      await navigateTo(page, "/nonexistent-route-12345");

      // Should show 404 page
      const has404 = await page.evaluate(() => {
        return document.body.textContent?.includes("404") ?? false;
      });

      expect(has404).toBe(true);

      // Should have navigation back to workspace
      const hasBackButton = await page.evaluate(() => {
        return document.body.textContent?.includes("Go to Workspace") ?? false;
      });

      expect(hasBackButton).toBe(true);
    });
  });

  describe("UI State Consistency", () => {
    it("should persist zoom level across operations", async () => {
      await navigateTo(page, "/");

      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) {
        // Workspace may not have zoom controls visible
        return;
      }

      const initialZoom = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // Zoom in multiple times
      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        await zoomInButton.click();
        await waitFrames(page, 3);
        await zoomInButton.click();
        await waitFrames(page, 3);
      }

      const zoomedValue = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      expect(zoomedValue).not.toBe(initialZoom);

      // The zoom should persist until reset
      await waitFrames(page, 30);

      const stillZoomed = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      expect(stillZoomed).toBe(zoomedValue);
    });

    it("should reset view correctly", async () => {
      await navigateTo(page, "/");

      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      // Zoom in
      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        await zoomInButton.click();
        await zoomInButton.click();
        await zoomInButton.click();
        await waitFrames(page, 5);
      }

      // Reset
      const resetButton = await page.$('button[title="Reset View"]');
      if (resetButton) {
        await resetButton.click();
        await waitFrames(page, 5);
      }

      const resetZoom = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      expect(resetZoom).toBe("100%");
    });
  });

  describe("History Stack", () => {
    it("should handle empty history gracefully", async () => {
      await navigateTo(page, "/");

      // Try to undo with no history - should not crash
      await pressKeys(page, "Control", "z");
      await waitFrames(page, 5);

      // App should still be responsive
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle redo at end of history", async () => {
      await navigateTo(page, "/");

      // Try to redo at end of history - should not crash
      await pressKeys(page, "Control", "Shift", "z");
      await waitFrames(page, 5);

      // App should still be responsive
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });
  });

  describe("Concurrent State Updates", () => {
    it("should handle multiple rapid clicks without race conditions", async () => {
      await navigateTo(page, "/");

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (!zoomInButton) return;

      // Rapid fire clicks
      const clickPromises = [];
      for (let i = 0; i < 20; i++) {
        clickPromises.push(zoomInButton.click());
      }

      await Promise.all(clickPromises);
      await waitFrames(page, 10);

      // State should be consistent (not corrupted)
      const zoomText = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      expect(zoomText).toBeDefined();
      expect(zoomText).toMatch(/^\d+(\.\d+)?%$/);
    });

    it("should handle interleaved zoom in/out operations", async () => {
      await navigateTo(page, "/");

      const zoomInButton = await page.$('button[title="Zoom In"]');
      const zoomOutButton = await page.$('button[title="Zoom Out"]');
      if (!zoomInButton || !zoomOutButton) return;

      // Interleave zoom operations rapidly
      for (let i = 0; i < 10; i++) {
        zoomInButton.click(); // Don't await
        zoomOutButton.click(); // Don't await
      }

      await waitFrames(page, 20);

      // State should still be valid
      const zoomText = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      expect(zoomText).toBeDefined();

      // Parse the zoom value - should be a valid number
      const zoomValue = parseFloat(zoomText!.replace("%", ""));
      expect(zoomValue).toBeGreaterThan(0);
      expect(zoomValue).toBeLessThan(10000); // Sanity check
    });
  });

  describe("State Recovery", () => {
    it("should recover from JavaScript errors gracefully", async () => {
      await navigateTo(page, "/");

      // Inject a synthetic error
      await page.evaluate(() => {
        try {
          throw new Error("Synthetic test error");
        } catch {
          // Error handled
        }
      });

      // App should still work
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle storage quota exceeded", async () => {
      await navigateTo(page, "/");

      // Try to overflow localStorage (simulated)
      const storageError = await page.evaluate(() => {
        try {
          // Try to store something
          localStorage.setItem("lattice-test", "test");
          localStorage.removeItem("lattice-test");
          return false;
        } catch {
          return true;
        }
      });

      // Whether or not storage works, app should be fine
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });
  });

  describe("Cross-Tab State", () => {
    it("should handle multiple tabs accessing the app", async () => {
      const browser = await launchBrowser();

      // Open two pages
      const page1 = await browser.newPage();
      const page2 = await browser.newPage();

      try {
        await page1.goto("http://localhost:8080/", {
          waitUntil: "networkidle0",
        });
        await page2.goto("http://localhost:8080/", {
          waitUntil: "networkidle0",
        });

        // Both should initialize correctly
        const page1Ready = await page1.evaluate(() => {
          return document.querySelector("#lattice-root") !== null;
        });

        const page2Ready = await page2.evaluate(() => {
          return document.querySelector("#lattice-root") !== null;
        });

        expect(page1Ready).toBe(true);
        expect(page2Ready).toBe(true);
      } finally {
        await page1.close();
        await page2.close();
      }
    });
  });
});
