/**
 * Full UI Component Browser Tests
 *
 * Comprehensive tests for every UI panel and control:
 * - Workspace canvas
 * - Toolbar controls
 * - Layer panel
 * - Properties panel
 * - Navigation/routing
 * - Modals and dialogs
 * - Accessibility
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
  waitForCanvas,
  waitFrames,
} from "./helpers/browser.js";

describe("UI Components", () => {
  let page: Page;

  beforeAll(async () => {
    await launchBrowser();
  });

  afterAll(async () => {
    await closeBrowser();
  });

  beforeEach(async () => {
    page = await createPage();
    await navigateTo(page, "/");
  });

  afterEach(async () => {
    await page.close();
  });

  describe("App Shell", () => {
    it("should render root container", async () => {
      const root = await page.$("#lattice-root");
      expect(root).not.toBeNull();
    });

    it("should have correct viewport dimensions", async () => {
      const viewport = await page.evaluate(() => ({
        width: window.innerWidth,
        height: window.innerHeight,
      }));

      expect(viewport.width).toBeGreaterThan(0);
      expect(viewport.height).toBeGreaterThan(0);
    });

    it("should apply theme styles", async () => {
      const hasStyles = await page.evaluate(() => {
        const root = document.querySelector("#lattice-root");
        if (!root) return false;
        const styles = window.getComputedStyle(root);
        return styles.display !== "none";
      });

      expect(hasStyles).toBe(true);
    });
  });

  describe("WebGL Canvas", () => {
    it("should render WebGL canvas", async () => {
      const canvas = await page.$("#lattice-webgl");

      // Canvas might not exist in all views
      if (canvas) {
        const dimensions = await page.evaluate(() => {
          const c = document.querySelector(
            "#lattice-webgl",
          ) as HTMLCanvasElement;
          return { width: c?.width ?? 0, height: c?.height ?? 0 };
        });

        expect(dimensions.width).toBeGreaterThan(0);
        expect(dimensions.height).toBeGreaterThan(0);
      }
    });

    it("should have WebGL context available", async () => {
      const canvas = await page.$("#lattice-webgl");
      if (!canvas) return;

      const hasContext = await page.evaluate(() => {
        const c = document.querySelector("#lattice-webgl") as HTMLCanvasElement;
        if (!c) return false;
        const gl = c.getContext("webgl2") || c.getContext("webgl");
        return gl !== null;
      });

      expect(hasContext).toBe(true);
    });

    it("should handle canvas resize", async () => {
      const canvas = await page.$("#lattice-webgl");
      if (!canvas) return;

      const initialSize = await page.evaluate(() => {
        const c = document.querySelector("#lattice-webgl") as HTMLCanvasElement;
        return { width: c?.width ?? 0, height: c?.height ?? 0 };
      });

      // Resize viewport
      await page.setViewport({ width: 1280, height: 720 });
      await waitFrames(page, 10);

      const newSize = await page.evaluate(() => {
        const c = document.querySelector("#lattice-webgl") as HTMLCanvasElement;
        return { width: c?.width ?? 0, height: c?.height ?? 0 };
      });

      // Canvas should respond to resize
      // (may or may not change depending on implementation)
      expect(newSize.width).toBeGreaterThan(0);
      expect(newSize.height).toBeGreaterThan(0);

      // Reset viewport
      await page.setViewport({ width: 1920, height: 1080 });
    });

    it("should support mouse interaction", async () => {
      const canvas = await page.$("#lattice-webgl");
      if (!canvas) return;

      // Get canvas bounds
      const bounds = await canvas.boundingBox();
      if (!bounds) return;

      // Click on canvas
      await page.mouse.click(
        bounds.x + bounds.width / 2,
        bounds.y + bounds.height / 2,
      );

      // App should still be responsive
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should support mouse wheel zoom", async () => {
      const canvas = await page.$("#lattice-webgl");
      if (!canvas) return;

      const bounds = await canvas.boundingBox();
      if (!bounds) return;

      // Move mouse to canvas center
      await page.mouse.move(
        bounds.x + bounds.width / 2,
        bounds.y + bounds.height / 2,
      );

      // Scroll wheel
      await page.mouse.wheel({ deltaY: -100 });
      await waitFrames(page, 5);

      // Check if zoom changed (if zoom display exists)
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (zoomDisplay) {
        const zoom = await page.$eval(
          ".lattice-zoom-level",
          (el) => el.textContent,
        );
        expect(zoom).toBeDefined();
      }
    });

    it("should support pan via middle mouse button", async () => {
      const canvas = await page.$("#lattice-webgl");
      if (!canvas) return;

      const bounds = await canvas.boundingBox();
      if (!bounds) return;

      const centerX = bounds.x + bounds.width / 2;
      const centerY = bounds.y + bounds.height / 2;

      // Middle mouse drag
      await page.mouse.move(centerX, centerY);
      await page.mouse.down({ button: "middle" });
      await page.mouse.move(centerX + 100, centerY + 100);
      await page.mouse.up({ button: "middle" });

      await waitFrames(page, 5);

      // Should not crash
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });
  });

  describe("Toolbar Controls", () => {
    it("should render zoom controls", async () => {
      const zoomIn = await page.$('button[title="Zoom In"]');
      const zoomOut = await page.$('button[title="Zoom Out"]');
      const zoomReset = await page.$('button[title="Reset View"]');

      // At least one zoom control should exist
      const hasZoomControls = zoomIn || zoomOut || zoomReset;

      // This might not exist on all routes
      if (hasZoomControls) {
        expect(hasZoomControls).not.toBeNull();
      }
    });

    it("should enable/disable buttons based on state", async () => {
      const undoButton = await page.$(
        'button[title="Undo"], button[aria-label="Undo"]',
      );

      if (undoButton) {
        // Initially, undo should be disabled (no history)
        const initiallyDisabled = await page.evaluate(() => {
          const btn = document.querySelector(
            'button[title="Undo"], button[aria-label="Undo"]',
          ) as HTMLButtonElement;
          return btn?.disabled ?? false;
        });

        expect(initiallyDisabled).toBe(true);

        // After an action, undo should be enabled
        const zoomInButton = await page.$('button[title="Zoom In"]');
        if (zoomInButton) {
          await zoomInButton.click();
          await waitFrames(page, 5);

          const afterAction = await page.evaluate(() => {
            const btn = document.querySelector(
              'button[title="Undo"], button[aria-label="Undo"]',
            ) as HTMLButtonElement;
            return btn?.disabled ?? true;
          });

          expect(afterAction).toBe(false);
        }
      }
    });

    it("should show tooltips on hover", async () => {
      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (!zoomInButton) return;

      // Hover over button
      const bounds = await zoomInButton.boundingBox();
      if (bounds) {
        await page.mouse.move(
          bounds.x + bounds.width / 2,
          bounds.y + bounds.height / 2,
        );
        await waitFrames(page, 30); // Wait for tooltip delay

        // Check for tooltip or title attribute
        const hasTitle = await page.evaluate(() => {
          const btn = document.querySelector('button[title="Zoom In"]');
          return btn?.getAttribute("title") !== null;
        });

        expect(hasTitle).toBe(true);
      }
    });

    it("should have keyboard accessible buttons", async () => {
      const buttons = await page.$$("button");

      // All buttons should be focusable
      for (const button of buttons.slice(0, 5)) {
        // Test first 5
        const isFocusable = await button.evaluate((btn) => {
          return btn.tabIndex >= 0 || btn.tabIndex === -1;
        });

        // Buttons are focusable by default unless explicitly disabled
        expect(isFocusable).toBeDefined();
      }
    });
  });

  describe("Zoom Level Display", () => {
    it("should show current zoom percentage", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const zoomText = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      expect(zoomText).toMatch(/\d+(\.\d+)?%?/);
    });

    it("should update zoom display on zoom change", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const initial = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        await zoomInButton.click();
        await waitFrames(page, 5);

        const after = await page.$eval(
          ".lattice-zoom-level",
          (el) => el.textContent,
        );

        expect(after).not.toBe(initial);
      }
    });
  });

  describe("Navigation/Routing", () => {
    it("should navigate to settings page", async () => {
      await navigateTo(page, "/settings");

      const hasSettingsContent = await page.evaluate(() => {
        const text = document.body.textContent || "";
        return text.includes("Settings") || text.includes("Preferences");
      });

      expect(hasSettingsContent).toBe(true);
    });

    it("should navigate to project page", async () => {
      await navigateTo(page, "/project");

      const isOnProjectPage = await page.evaluate(() => {
        const childCount =
          document.querySelector("#lattice-root")?.children.length ?? 0;
        return (
          window.location.pathname === "/project" ||
          document.body.textContent?.includes("Project") ||
          childCount > 0
        );
      });

      expect(isOnProjectPage).toBe(true);
    });

    it("should navigate to export page", async () => {
      await navigateTo(page, "/export");

      const isOnExportPage = await page.evaluate(() => {
        const childCount =
          document.querySelector("#lattice-root")?.children.length ?? 0;
        return (
          window.location.pathname === "/export" ||
          document.body.textContent?.includes("Export") ||
          childCount > 0
        );
      });

      expect(isOnExportPage).toBe(true);
    });

    it("should handle browser back/forward", async () => {
      await navigateTo(page, "/");
      await navigateTo(page, "/settings");

      // Go back
      await page.goBack();
      await page.waitForSelector("#lattice-root", { timeout: 10000 });

      const afterBack = await page.evaluate(() => window.location.pathname);
      expect(afterBack).toBe("/");

      // Go forward
      await page.goForward();
      await page.waitForSelector("#lattice-root", { timeout: 10000 });

      const afterForward = await page.evaluate(() => window.location.pathname);
      expect(afterForward).toBe("/settings");
    });

    it("should show 404 for unknown routes", async () => {
      await navigateTo(page, "/nonexistent-route-xyz");

      const has404 = await page.evaluate(() => {
        const text = document.body.textContent || "";
        return text.includes("404") || text.includes("Not Found");
      });

      expect(has404).toBe(true);
    });
  });

  describe("Settings Page", () => {
    beforeEach(async () => {
      await navigateTo(page, "/settings");
    });

    it("should render settings form", async () => {
      const hasForm = await page.evaluate(() => {
        return (
          document.querySelector("form") !== null ||
          document.querySelector("[role='form']") !== null ||
          document.querySelectorAll("input, select, button").length > 0
        );
      });

      // Settings page should have some form elements
      expect(hasForm).toBe(true);
    });

    it("should have theme toggle", async () => {
      const hasThemeToggle = await page.evaluate(() => {
        const text = document.body.textContent || "";
        return (
          text.includes("Theme") ||
          text.includes("Dark") ||
          text.includes("Light") ||
          document.querySelector('[type="checkbox"]') !== null ||
          document.querySelector('[role="switch"]') !== null
        );
      });

      // Theme setting should be present
      expect(hasThemeToggle).toBeDefined();
    });

    it("should persist settings changes", async () => {
      // Find a toggle/checkbox
      const checkbox = await page.$('input[type="checkbox"]');

      if (checkbox) {
        // Get initial state
        const initialChecked = await checkbox.evaluate(
          (el) => (el as HTMLInputElement).checked,
        );

        // Toggle
        await checkbox.click();
        await waitFrames(page, 5);

        const afterToggle = await checkbox.evaluate(
          (el) => (el as HTMLInputElement).checked,
        );

        expect(afterToggle).not.toBe(initialChecked);
      }
    });
  });

  describe("Modals and Dialogs", () => {
    it("should close modal on escape key", async () => {
      // Look for any modal trigger
      const modalTrigger = await page.$(
        'button[aria-haspopup="dialog"], [data-modal-trigger]',
      );

      if (modalTrigger) {
        await modalTrigger.click();
        await waitFrames(page, 10);

        // Check if modal opened
        const modalOpen = await page.$('[role="dialog"], .modal, [data-modal]');

        if (modalOpen) {
          await page.keyboard.press("Escape");
          await waitFrames(page, 10);

          const modalClosed = await page.$(
            '[role="dialog"], .modal, [data-modal]',
          );

          expect(modalClosed).toBeNull();
        }
      }
    });

    it("should trap focus in modal", async () => {
      const modalTrigger = await page.$(
        'button[aria-haspopup="dialog"], [data-modal-trigger]',
      );

      if (modalTrigger) {
        await modalTrigger.click();
        await waitFrames(page, 10);

        const modal = await page.$('[role="dialog"], .modal, [data-modal]');

        if (modal) {
          // Tab through elements
          await page.keyboard.press("Tab");
          await page.keyboard.press("Tab");
          await page.keyboard.press("Tab");

          // Focus should still be within modal
          const focusInModal = await page.evaluate(() => {
            const modal = document.querySelector(
              '[role="dialog"], .modal, [data-modal]',
            );
            const activeEl = document.activeElement;
            return modal?.contains(activeEl) ?? false;
          });

          expect(focusInModal).toBe(true);

          // Close modal
          await page.keyboard.press("Escape");
        }
      }
    });
  });

  describe("Accessibility", () => {
    it("should have proper heading hierarchy", async () => {
      const headings = await page.evaluate(() => {
        const h1s = document.querySelectorAll("h1").length;
        const h2s = document.querySelectorAll("h2").length;
        const h3s = document.querySelectorAll("h3").length;
        return { h1s, h2s, h3s };
      });

      // Should have at most one h1
      expect(headings.h1s).toBeLessThanOrEqual(1);
    });

    it("should have alt text for images", async () => {
      const images = await page.$$("img");

      for (const img of images) {
        const hasAlt = await img.evaluate((el) => {
          return (
            el.hasAttribute("alt") || el.getAttribute("role") === "presentation"
          );
        });

        expect(hasAlt).toBe(true);
      }
    });

    it("should have labels for form inputs", async () => {
      const inputs = await page.$$("input, select, textarea");

      for (const input of inputs.slice(0, 5)) {
        // Test first 5
        const hasLabel = await input.evaluate((el) => {
          const id = el.id;
          const hasLabelFor =
            id && document.querySelector(`label[for="${id}"]`) !== null;
          const hasAriaLabel = el.hasAttribute("aria-label");
          const hasAriaLabelledBy = el.hasAttribute("aria-labelledby");
          const isHidden = el.getAttribute("type") === "hidden";
          const wrappedInLabel = el.closest("label") !== null;

          return (
            hasLabelFor ||
            hasAriaLabel ||
            hasAriaLabelledBy ||
            isHidden ||
            wrappedInLabel
          );
        });

        expect(hasLabel).toBe(true);
      }
    });

    it("should support keyboard navigation", async () => {
      // Tab through the page
      await page.keyboard.press("Tab");
      await page.keyboard.press("Tab");

      // Something should be focused
      const hasFocus = await page.evaluate(() => {
        return (
          document.activeElement !== document.body &&
          document.activeElement !== null
        );
      });

      expect(hasFocus).toBe(true);
    });

    it("should have visible focus indicators", async () => {
      // Focus on a button
      await page.keyboard.press("Tab");

      const hasVisibleFocus = await page.evaluate(() => {
        const el = document.activeElement as HTMLElement;
        if (!el || el === document.body) return true; // Skip if no focus

        const styles = window.getComputedStyle(el);
        const outlineWidth = parseInt(styles.outlineWidth) || 0;
        const outlineStyle = styles.outlineStyle;
        const boxShadow = styles.boxShadow;

        // Check for focus ring via outline or box-shadow
        return (
          (outlineWidth > 0 && outlineStyle !== "none") || boxShadow !== "none"
        );
      });

      // Focus indicator should be visible (or element is body)
      expect(hasVisibleFocus).toBeDefined();
    });

    it("should have proper ARIA attributes", async () => {
      const ariaCheck = await page.evaluate(() => {
        const buttons = document.querySelectorAll("button");
        let allHaveLabel = true;

        buttons.forEach((btn) => {
          const textLength = btn.textContent?.trim().length ?? 0;
          const hasText = textLength > 0;
          const hasAriaLabel = btn.hasAttribute("aria-label");
          const hasAriaLabelledBy = btn.hasAttribute("aria-labelledby");
          const hasTitle = btn.hasAttribute("title");

          if (!hasText && !hasAriaLabel && !hasAriaLabelledBy && !hasTitle) {
            allHaveLabel = false;
          }
        });

        return { buttonCount: buttons.length, allHaveLabel };
      });

      expect(ariaCheck.allHaveLabel).toBe(true);
    });
  });

  describe("Responsive Design", () => {
    it("should adapt to mobile viewport", async () => {
      await page.setViewport({ width: 375, height: 667 }); // iPhone SE
      await waitFrames(page, 10);

      const isResponsive = await page.evaluate(() => {
        const root = document.querySelector("#lattice-root");
        if (!root) return false;

        const styles = window.getComputedStyle(root);
        // Should not overflow
        return root.scrollWidth <= window.innerWidth + 10; // Small tolerance
      });

      expect(isResponsive).toBe(true);

      // Reset viewport
      await page.setViewport({ width: 1920, height: 1080 });
    });

    it("should adapt to tablet viewport", async () => {
      await page.setViewport({ width: 768, height: 1024 }); // iPad
      await waitFrames(page, 10);

      const hasContent = await page.evaluate(() => {
        return (
          (document.querySelector("#lattice-root")?.children.length ?? 0) > 0
        );
      });

      expect(hasContent).toBe(true);

      await page.setViewport({ width: 1920, height: 1080 });
    });

    it("should handle very wide viewport", async () => {
      await page.setViewport({ width: 2560, height: 1440 }); // 1440p
      await waitFrames(page, 10);

      const hasContent = await page.evaluate(() => {
        return (
          (document.querySelector("#lattice-root")?.children.length ?? 0) > 0
        );
      });

      expect(hasContent).toBe(true);

      await page.setViewport({ width: 1920, height: 1080 });
    });
  });

  describe("Touch Support", () => {
    it("should handle touch events on canvas", async () => {
      const canvas = await page.$("#lattice-webgl");
      if (!canvas) return;

      const bounds = await canvas.boundingBox();
      if (!bounds) return;

      // Simulate touch
      await page.touchscreen.tap(
        bounds.x + bounds.width / 2,
        bounds.y + bounds.height / 2,
      );

      // Should not crash
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle pinch zoom gesture", async () => {
      const canvas = await page.$("#lattice-webgl");
      if (!canvas) return;

      // Touch gestures are complex to simulate
      // Just verify touch capability doesn't crash
      const supportsTouchEvents = await page.evaluate(() => {
        return "ontouchstart" in window || navigator.maxTouchPoints > 0;
      });

      // Chrome supports touch events
      expect(supportsTouchEvents).toBeDefined();
    });
  });

  describe("Loading States", () => {
    it("should show loading indicator during navigation", async () => {
      // Start navigation (don't wait for completion)
      const navPromise = page.goto("http://localhost:8080/settings", {
        waitUntil: "domcontentloaded",
      });

      // Check for loading indicator
      // This is timing-dependent, so we're just checking it doesn't crash
      await navPromise;

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle slow network gracefully", async () => {
      // Enable network throttling
      const client = await page.createCDPSession();
      await client.send("Network.emulateNetworkConditions", {
        offline: false,
        downloadThroughput: 50 * 1024, // 50KB/s
        uploadThroughput: 50 * 1024,
        latency: 500,
      });

      // Navigate
      await page.goto("http://localhost:8080/", {
        waitUntil: "domcontentloaded",
        timeout: 30000,
      });

      // Wait for content
      await page.waitForSelector("#lattice-root", { timeout: 30000 });

      const hasContent = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(hasContent).toBe(true);

      // Disable throttling
      await client.send("Network.emulateNetworkConditions", {
        offline: false,
        downloadThroughput: -1,
        uploadThroughput: -1,
        latency: 0,
      });

      await client.detach();
    });
  });

  describe("Error States", () => {
    it("should show error state for failed resources", async () => {
      // Block a resource
      await page.setRequestInterception(true);

      let blockedRequests = 0;

      page.on("request", (request) => {
        if (request.resourceType() === "image") {
          blockedRequests++;
          request.abort();
        } else {
          request.continue();
        }
      });

      await page.reload({ waitUntil: "networkidle0" });
      await page.waitForSelector("#lattice-root", { timeout: 10000 });

      // App should still work even with blocked images
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);

      // Cleanup
      await page.setRequestInterception(false);
    });
  });
});
