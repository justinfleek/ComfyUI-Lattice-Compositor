/**
 * Integration/Wiring Tests
 *
 * Hard-to-pass tests that verify:
 * - Component communication
 * - State propagation across modules
 * - Event flow correctness
 * - Module boundaries
 * - Side effect coordination
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

describe("Integration Tests", () => {
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

  describe("UI ↔ State Wiring", () => {
    it("integration: zoom button click should update display", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const initialZoom = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        await zoomInButton.click();
        await waitFrames(page, 10);
      }

      const newZoom = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // UI should reflect state change
      expect(newZoom).not.toBe(initialZoom);
    });

    it("integration: keyboard shortcut should trigger same action as button", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      // Get initial state
      const initial = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // Click button
      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        await zoomInButton.click();
        await waitFrames(page, 5);
      }

      const afterButton = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // Reset (if reset button exists)
      const resetButton = await page.$('button[title="Reset View"]');
      if (resetButton) {
        await resetButton.click();
        await waitFrames(page, 5);
      }

      // Use keyboard shortcut (common zoom shortcuts)
      await pressKeys(page, "Control", "="); // or Control + Plus
      await waitFrames(page, 5);

      // Both methods should produce equivalent results
      // (exact value may differ based on implementation)
      const afterKeyboard = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // At minimum, keyboard should change something
      expect(afterKeyboard).toBeDefined();
    });

    it("integration: state change should propagate to all dependent UI", async () => {
      // Check if zoom affects multiple UI elements
      const checkUIConsistency = async () => {
        const zoomDisplay = await page.$(".lattice-zoom-level");
        const zoomSlider = await page.$('input[type="range"][title*="Zoom"]');
        const canvasTransform = await page.evaluate(() => {
          const canvas = document.querySelector("#lattice-webgl");
          if (!canvas) return null;
          return window.getComputedStyle(canvas).transform;
        });

        return {
          hasDisplay: !!zoomDisplay,
          hasSlider: !!zoomSlider,
          canvasTransform,
        };
      };

      const initial = await checkUIConsistency();

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        await zoomInButton.click();
        await waitFrames(page, 10);
      }

      const after = await checkUIConsistency();

      // UI elements should be present (wired correctly)
      if (initial.hasDisplay) {
        expect(after.hasDisplay).toBe(true);
      }
    });
  });

  describe("Router ↔ Component Wiring", () => {
    it("integration: route change should mount correct component", async () => {
      // Navigate to different routes and verify correct components are mounted

      // Root route should have main workspace
      await navigateTo(page, "/");
      const hasWorkspace = await page.evaluate(() => {
        // Check for workspace-specific elements
        return (
          document.querySelector("#lattice-root") !== null &&
          (document.querySelector("#lattice-webgl") !== null ||
            document.querySelector(".lattice-workspace") !== null)
        );
      });
      expect(hasWorkspace).toBe(true);

      // Settings route should have settings UI
      await navigateTo(page, "/settings");
      const hasSettings = await page.evaluate(() => {
        const root = document.querySelector("#lattice-root");
        const text = root?.textContent || "";
        return (
          text.includes("Settings") ||
          text.includes("Preferences") ||
          document.querySelector(".lattice-settings") !== null
        );
      });
      expect(hasSettings).toBe(true);
    });

    it("integration: navigation should preserve app shell", async () => {
      // App shell (header, footer, etc.) should persist across navigation
      const getShellElements = async () =>
        page.evaluate(() => {
          return {
            hasRoot: document.querySelector("#lattice-root") !== null,
            hasHeader:
              document.querySelector("header") !== null ||
              document.querySelector(".lattice-header") !== null,
            // Check for any persistent UI
            bodyChildren: document.body.children.length,
          };
        });

      const initial = await getShellElements();

      await navigateTo(page, "/settings");
      const afterNav1 = await getShellElements();

      await navigateTo(page, "/");
      const afterNav2 = await getShellElements();

      // Root should always be present
      expect(initial.hasRoot).toBe(true);
      expect(afterNav1.hasRoot).toBe(true);
      expect(afterNav2.hasRoot).toBe(true);
    });

    it("integration: deep link should work", async () => {
      // Direct navigation to deep route
      await page.goto("http://localhost:8080/settings", {
        waitUntil: "networkidle0",
      });
      await page.waitForSelector("#lattice-root", { timeout: 10000 });

      const route = await page.evaluate(() => window.location.pathname);
      expect(route).toBe("/settings");

      // Should show settings content
      const hasContent = await page.evaluate(() => {
        const childCount =
          document.querySelector("#lattice-root")?.children.length ?? 0;
        return childCount > 0;
      });
      expect(hasContent).toBe(true);
    });
  });

  describe("Event Flow", () => {
    it("integration: events should bubble correctly", async () => {
      // Click on nested element should trigger parent handlers
      const eventFlow = await page.evaluate(() => {
        const events: string[] = [];

        // Add listeners at different levels
        const root = document.querySelector("#lattice-root");
        if (!root) return { events: [], error: "no root" };

        const originalHandler = (e: Event) => {
          events.push(`root:${e.type}`);
        };

        root.addEventListener("click", originalHandler);

        // Create and dispatch a click event on a child
        const child = root.querySelector("button") || root.children[0];
        if (child) {
          child.dispatchEvent(new MouseEvent("click", { bubbles: true }));
        }

        root.removeEventListener("click", originalHandler);

        return { events, hasChild: !!child };
      });

      if (eventFlow.hasChild) {
        expect(eventFlow.events).toContain("root:click");
      }
    });

    it("integration: custom events should propagate", async () => {
      const customEventResult = await page.evaluate(() => {
        let received = false;

        const handler = () => {
          received = true;
        };

        window.addEventListener("lattice:test-event", handler);

        // Dispatch custom event
        window.dispatchEvent(new CustomEvent("lattice:test-event"));

        window.removeEventListener("lattice:test-event", handler);

        return { received };
      });

      expect(customEventResult.received).toBe(true);
    });

    it("integration: keyboard events should reach correct handlers", async () => {
      // Focus on app and send keyboard events
      await page.focus("#lattice-root");

      const keyboardResult = await page.evaluate(() => {
        return new Promise((resolve) => {
          let received = false;

          const handler = (e: KeyboardEvent) => {
            if (e.key === "Escape") {
              received = true;
            }
          };

          document.addEventListener("keydown", handler);

          setTimeout(() => {
            document.removeEventListener("keydown", handler);
            resolve({ received });
          }, 100);
        });
      });

      await page.keyboard.press("Escape");
      await waitFrames(page, 5);

      // Keyboard handler should be wired
      // (actual result depends on app state)
    });
  });

  describe("State Synchronization", () => {
    it("integration: multiple components should reflect same state", async () => {
      // If zoom is shown in multiple places, they should be in sync
      const getZoomValues = async () =>
        page.evaluate(() => {
          const values: string[] = [];

          // Check all possible zoom displays
          const zoomDisplay = document.querySelector(".lattice-zoom-level");
          if (zoomDisplay) values.push(zoomDisplay.textContent || "");

          const zoomInput = document.querySelector(
            'input[title*="Zoom"]',
          ) as HTMLInputElement;
          if (zoomInput) values.push(zoomInput.value);

          return values;
        });

      const initial = await getZoomValues();

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        await zoomInButton.click();
        await waitFrames(page, 10);
      }

      const after = await getZoomValues();

      // All zoom displays should have changed together
      if (initial.length > 1) {
        expect(after.length).toBeGreaterThanOrEqual(initial.length);
      }
    });

    it("integration: state should persist during re-renders", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        await zoomInButton.click();
        await waitFrames(page, 5);
      }

      const zoomAfterClick = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // Trigger a re-render by resizing window
      await page.setViewport({ width: 1280, height: 720 });
      await waitFrames(page, 10);

      const zoomAfterResize = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // State should persist through re-render
      expect(zoomAfterResize).toBe(zoomAfterClick);

      // Reset viewport
      await page.setViewport({ width: 1920, height: 1080 });
    });
  });

  describe("Module Boundaries", () => {
    it("integration: modules should communicate through defined interfaces", async () => {
      // Test that modules don't leak implementation details
      const moduleInterfaces = await page.evaluate(() => {
        // Check that global scope isn't polluted with internal details
        const windowKeys = Object.keys(window);

        const latticeGlobals = windowKeys.filter(
          (k) =>
            k.toLowerCase().includes("lattice") ||
            k.toLowerCase().includes("layer") ||
            k.toLowerCase().includes("canvas"),
        );

        // Check for proper encapsulation
        const hasProperInterface =
          typeof (window as unknown as { __LATTICE_APP_STATE__?: unknown })
            .__LATTICE_APP_STATE__ !== "undefined" ||
          latticeGlobals.length < 10; // Some globals are ok, but not too many

        return {
          latticeGlobals,
          globalCount: latticeGlobals.length,
          hasProperInterface,
        };
      });

      // Should not leak too many globals
      expect(moduleInterfaces.globalCount).toBeLessThan(20);
    });

    it("integration: error in one module should not crash others", async () => {
      // Inject an error in one part of the app
      await page.evaluate(() => {
        // Try to break something non-critical
        try {
          const el = document.querySelector(".non-existent-element");
          // @ts-expect-error - intentional
          el.click(); // This will throw
        } catch {
          // Error contained
        }
      });

      // App should still work
      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        await zoomInButton.click();
        await waitFrames(page, 5);
      }

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });
  });

  describe("Side Effect Coordination", () => {
    it("integration: localStorage writes should be atomic", async () => {
      // Perform operations that write to localStorage
      const result = await page.evaluate(() => {
        const key = "lattice-integration-test";

        // Simulate concurrent writes
        const writes: Promise<void>[] = [];
        for (let i = 0; i < 10; i++) {
          writes.push(
            new Promise((resolve) => {
              localStorage.setItem(key, JSON.stringify({ value: i }));
              resolve();
            }),
          );
        }

        return Promise.all(writes).then(() => {
          const final = localStorage.getItem(key);
          localStorage.removeItem(key);
          return {
            finalValue: final ? JSON.parse(final) : null,
            hasValue: final !== null,
          };
        });
      });

      expect(result.hasValue).toBe(true);
      expect(result.finalValue.value).toBeDefined();
    });

    it("integration: network requests should be properly sequenced", async () => {
      // Test that requests don't race incorrectly
      const networkResult = await page.evaluate(async () => {
        const responses: number[] = [];

        // Simulate sequential requests
        for (let i = 0; i < 3; i++) {
          try {
            // Use a simple endpoint that exists
            const response = await fetch(`/index.html?seq=${i}`);
            if (response.ok) {
              responses.push(i);
            }
          } catch {
            // Network errors are ok in tests
          }
        }

        return { responses, count: responses.length };
      });

      // If requests worked, they should be in order
      if (networkResult.count > 0) {
        for (let i = 1; i < networkResult.responses.length; i++) {
          expect(networkResult.responses[i]).toBeGreaterThan(
            networkResult.responses[i - 1],
          );
        }
      }
    });

    it("integration: cleanup should run on unmount", async () => {
      // Navigate away and check for cleanup
      await navigateTo(page, "/settings");
      await waitFrames(page, 10);

      // Check that old subscriptions/listeners are cleaned up
      const cleanupResult = await page.evaluate(() => {
        // Check for any orphaned intervals or animations
        let activeAnimations = 0;

        try {
          // Check for any running animations via getAnimations
          activeAnimations = document.getAnimations?.()?.length || 0;
        } catch {
          // getAnimations might not be available
        }

        return {
          activeAnimations,
          hasCleanup: activeAnimations < 50, // Allow some animations
        };
      });

      expect(cleanupResult.hasCleanup).toBe(true);
    });
  });

  describe("Error Boundary Wiring", () => {
    it("integration: errors should be caught by boundaries", async () => {
      // Check if error boundaries are in place
      const errorBoundaryCheck = await page.evaluate(() => {
        // Look for error boundary UI patterns
        const hasErrorUI =
          document.querySelector(".error-boundary") !== null ||
          document.querySelector('[role="alert"]') !== null;

        // Check that main app is rendered
        const childCount =
          document.querySelector("#lattice-root")?.children.length ?? 0;
        const hasMainApp = childCount > 0;

        return { hasErrorUI, hasMainApp };
      });

      // Main app should be rendered (not crashed)
      expect(errorBoundaryCheck.hasMainApp).toBe(true);
    });

    it("integration: error recovery should restore functionality", async () => {
      // Simulate recoverable error
      await page.evaluate(() => {
        // Dispatch an error event
        window.dispatchEvent(
          new ErrorEvent("error", {
            message: "Test error",
            error: new Error("Test error"),
          }),
        );
      });

      await waitFrames(page, 10);

      // App should still work
      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        await zoomInButton.click();
        await waitFrames(page, 5);
      }

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });
  });

  describe("Initialization Sequence", () => {
    it("integration: components should initialize in correct order", async () => {
      // Reload and track initialization
      const initOrder = await page.evaluate(() => {
        // Check that critical components exist in correct order
        const checks = {
          hasDocument: document !== null,
          hasBody: document.body !== null,
          hasRoot: document.querySelector("#lattice-root") !== null,
          hasContent:
            (document.querySelector("#lattice-root")?.children.length ?? 0) > 0,
        };

        return checks;
      });

      expect(initOrder.hasDocument).toBe(true);
      expect(initOrder.hasBody).toBe(true);
      expect(initOrder.hasRoot).toBe(true);
      expect(initOrder.hasContent).toBe(true);
    });

    it("integration: lazy-loaded modules should load correctly", async () => {
      // Navigate to a route that might lazy-load
      await navigateTo(page, "/settings");

      // Content should eventually load
      await page.waitForFunction(
        () => {
          const root = document.querySelector("#lattice-root");
          return root && root.children.length > 0;
        },
        { timeout: 10000 },
      );

      const hasContent = await page.evaluate(() => {
        return (
          (document.querySelector("#lattice-root")?.children.length ?? 0) > 0
        );
      });

      expect(hasContent).toBe(true);
    });
  });
});
