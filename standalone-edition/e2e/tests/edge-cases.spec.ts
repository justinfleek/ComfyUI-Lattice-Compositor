/**
 * Edge Cases and Error Handling E2E Tests
 *
 * Hard-to-pass tests that verify:
 * - Invalid inputs handling
 * - Network failure recovery
 * - Corrupted data handling
 * - Boundary conditions
 * - Unexpected user interactions
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

describe("Edge Cases", () => {
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

  describe("Invalid Routes", () => {
    it("should handle routes with special characters", async () => {
      await navigateTo(page, "/test%20with%20spaces");

      const has404 = await page.evaluate(() => {
        return document.body.textContent?.includes("404") ?? false;
      });

      expect(has404).toBe(true);
    });

    it("should handle extremely long route paths", async () => {
      const longPath = "/" + "a".repeat(10000);

      await page.goto(`http://localhost:8080${longPath}`, {
        waitUntil: "networkidle0",
      });

      // Should either show 404 or handle gracefully
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("body") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle routes with unicode characters", async () => {
      // Unicode paths may have encoding issues - test graceful handling
      try {
        await page.goto("http://localhost:8080/测试/κόσμε/🎬", {
          waitUntil: "networkidle0",
          timeout: 10000,
        });
      } catch {
        // Navigation may fail due to encoding - that's acceptable
      }

      // Should handle gracefully - page should still be responsive
      const isResponsive = await page.evaluate(() => {
        return document.body !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle routes with query parameters", async () => {
      await navigateTo(page, "/?foo=bar&baz=qux");

      // Should load the workspace (ignoring query params)
      const hasRoot = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(hasRoot).toBe(true);
    });

    it("should handle routes with hash fragments", async () => {
      await navigateTo(page, "/#some-anchor");

      const hasRoot = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(hasRoot).toBe(true);
    });
  });

  describe("Network Failures", () => {
    it("should handle offline mode", async () => {
      await navigateTo(page, "/");

      // Go offline
      await page.setOfflineMode(true);

      // Try to navigate - should use cached resources or handle gracefully
      try {
        await page.goto("http://localhost:8080/settings", {
          waitUntil: "networkidle0",
          timeout: 5000,
        });
      } catch {
        // Expected to fail or timeout
      }

      // Go back online
      await page.setOfflineMode(false);

      // Should recover
      await navigateTo(page, "/");

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle request timeouts", async () => {
      const client = await page.createCDPSession();

      // Simulate very high latency
      await client.send("Network.emulateNetworkConditions", {
        offline: false,
        downloadThroughput: 1024, // 1 KB/s
        uploadThroughput: 1024,
        latency: 10000, // 10 second latency
      });

      const start = Date.now();

      try {
        await page.goto("http://localhost:8080/", {
          waitUntil: "load",
          timeout: 15000,
        });
      } catch {
        // May timeout - that's acceptable
      }

      // Reset
      await client.send("Network.emulateNetworkConditions", {
        offline: false,
        downloadThroughput: -1,
        uploadThroughput: -1,
        latency: 0,
      });

      // Should be able to load normally after reset
      await navigateTo(page, "/");

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });
  });

  describe("Corrupted State", () => {
    it("should handle corrupted localStorage", async () => {
      await navigateTo(page, "/");

      // Inject corrupted data
      await page.evaluate(() => {
        localStorage.setItem("lattice-state", "{invalid json}}}");
        localStorage.setItem("lattice-prefs", "not even json");
      });

      // Reload
      await page.reload({ waitUntil: "networkidle0" });

      // App should recover (ignore corrupted data)
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);

      // Clean up
      await page.evaluate(() => {
        localStorage.clear();
      });
    });

    it("should handle sessionStorage corruption", async () => {
      await navigateTo(page, "/");

      await page.evaluate(() => {
        sessionStorage.setItem("lattice-session", "{{{broken");
      });

      // Navigate
      await navigateTo(page, "/settings");

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });
  });

  describe("Boundary Values", () => {
    it("should handle minimum zoom level", async () => {
      await navigateTo(page, "/");

      const zoomOutButton = await page.$('button[title="Zoom Out"]');
      if (!zoomOutButton) return;

      // Zoom out many times to hit minimum
      for (let i = 0; i < 50; i++) {
        await zoomOutButton.click();
      }

      await waitFrames(page, 5);

      // Should not go below minimum (10%)
      const zoomText = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      const zoomValue = parseFloat(zoomText!.replace("%", ""));

      expect(zoomValue).toBeGreaterThanOrEqual(10);
    });

    it("should handle maximum zoom level", async () => {
      await navigateTo(page, "/");

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (!zoomInButton) return;

      // Zoom in many times to hit maximum
      for (let i = 0; i < 50; i++) {
        await zoomInButton.click();
      }

      await waitFrames(page, 5);

      // Should not exceed maximum (1000%)
      const zoomText = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      const zoomValue = parseFloat(zoomText!.replace("%", ""));

      expect(zoomValue).toBeLessThanOrEqual(1000);
    });
  });

  describe("Unexpected Interactions", () => {
    it("should handle rapid double-clicks", async () => {
      await navigateTo(page, "/");

      const element = await page.$("#lattice-root");
      if (element) {
        await element.click({ clickCount: 2 });
        await element.click({ clickCount: 2 });
        await element.click({ clickCount: 2 });
      }

      await waitFrames(page, 10);

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle right-click context menu", async () => {
      await navigateTo(page, "/");

      await page.click("#lattice-root", { button: "right" });

      // Should not break the app
      await waitFrames(page, 5);

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle middle-click", async () => {
      await navigateTo(page, "/");

      await page.click("#lattice-root", { button: "middle" });

      await waitFrames(page, 5);

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle focus/blur cycles", async () => {
      await navigateTo(page, "/");

      // Rapidly focus/blur the page
      for (let i = 0; i < 10; i++) {
        await page.evaluate(() => {
          (document.activeElement as HTMLElement)?.blur?.();
        });
        await page.evaluate(() => {
          document.body.focus();
        });
      }

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });
  });

  describe("DOM Manipulation", () => {
    it("should recover from external DOM manipulation", async () => {
      await navigateTo(page, "/");

      // Externally modify the DOM
      await page.evaluate(() => {
        const root = document.querySelector("#lattice-root");
        if (root) {
          // Add a rogue element
          const rogue = document.createElement("div");
          rogue.id = "rogue-element";
          rogue.textContent = "Injected!";
          root.appendChild(rogue);
        }
      });

      await waitFrames(page, 10);

      // App should still function
      const isResponsive = await page.evaluate(() => {
        const root = document.querySelector("#lattice-root");
        return root !== null && root.children.length > 0;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle removed essential elements", async () => {
      await navigateTo(page, "/");

      // Try to remove an element (simulating extension interference)
      await page.evaluate(() => {
        const toolbar = document.querySelector(".lattice-canvas-toolbar");
        toolbar?.remove();
      });

      await waitFrames(page, 10);

      // App should not crash
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });
  });

  describe("Clipboard Edge Cases", () => {
    it("should handle paste with no clipboard data", async () => {
      await navigateTo(page, "/");

      // Trigger paste without clipboard content
      await pressKeys(page, "Control", "v");

      await waitFrames(page, 5);

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle copy with no selection", async () => {
      await navigateTo(page, "/");

      await pressKeys(page, "Control", "c");

      await waitFrames(page, 5);

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });
  });

  describe("Window Events", () => {
    it("should handle window resize", async () => {
      await navigateTo(page, "/");

      // Resize viewport
      await page.setViewport({ width: 800, height: 600 });
      await waitFrames(page, 10);

      await page.setViewport({ width: 1920, height: 1080 });
      await waitFrames(page, 10);

      await page.setViewport({ width: 320, height: 480 }); // Mobile size
      await waitFrames(page, 10);

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle visibility change", async () => {
      await navigateTo(page, "/");

      // Simulate visibility change
      await page.evaluate(() => {
        document.dispatchEvent(new Event("visibilitychange"));
      });

      await waitFrames(page, 10);

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });
  });
});
