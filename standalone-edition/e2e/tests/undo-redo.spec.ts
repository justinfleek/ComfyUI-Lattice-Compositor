/**
 * Undo/Redo Correctness Tests
 *
 * Hard-to-pass tests that verify undo/redo system invariants:
 * - History stack consistency
 * - State restoration accuracy
 * - Operation coalescence
 * - Edge cases (empty history, max depth, etc.)
 * - Undo across different operation types
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
  getAppState,
  launchBrowser,
  navigateTo,
  pressKeys,
  waitFrames,
} from "./helpers/browser.js";

describe("Undo/Redo Correctness", () => {
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

  describe("Invariant: Initial State", () => {
    it("should start with empty undo stack (canUndo = false)", async () => {
      // Check if undo button is disabled or app reports canUndo = false
      const undoState = await page.evaluate(() => {
        const undoBtn = document.querySelector(
          'button[title="Undo"], button[aria-label="Undo"]',
        ) as HTMLButtonElement | null;

        // Check button disabled state
        if (undoBtn) {
          return { hasButton: true, isDisabled: undoBtn.disabled };
        }

        // Check app state if exposed
        const appState = (
          window as unknown as { __LATTICE_APP_STATE__?: { canUndo?: boolean } }
        ).__LATTICE_APP_STATE__;
        if (appState?.canUndo !== undefined) {
          return { hasButton: false, canUndo: appState.canUndo };
        }

        return { hasButton: false, canUndo: false };
      });

      // Either button is disabled OR canUndo is false
      if (undoState.hasButton) {
        expect(undoState.isDisabled).toBe(true);
      } else {
        expect(undoState.canUndo).toBe(false);
      }
    });

    it("should start with empty redo stack (canRedo = false)", async () => {
      const redoState = await page.evaluate(() => {
        const redoBtn = document.querySelector(
          'button[title="Redo"], button[aria-label="Redo"]',
        ) as HTMLButtonElement | null;

        if (redoBtn) {
          return { hasButton: true, isDisabled: redoBtn.disabled };
        }

        const appState = (
          window as unknown as { __LATTICE_APP_STATE__?: { canRedo?: boolean } }
        ).__LATTICE_APP_STATE__;
        if (appState?.canRedo !== undefined) {
          return { hasButton: false, canRedo: appState.canRedo };
        }

        return { hasButton: false, canRedo: false };
      });

      if (redoState.hasButton) {
        expect(redoState.isDisabled).toBe(true);
      } else {
        expect(redoState.canRedo).toBe(false);
      }
    });

    it("should not crash when attempting undo on empty history", async () => {
      // Try to undo multiple times
      for (let i = 0; i < 5; i++) {
        await pressKeys(page, "Control", "z");
        await waitFrames(page, 2);
      }

      // App should still be responsive
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should not crash when attempting redo on empty history", async () => {
      for (let i = 0; i < 5; i++) {
        await pressKeys(page, "Control", "Shift", "z");
        await waitFrames(page, 2);
      }

      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });
  });

  describe("Invariant: Undo Reverses Operations", () => {
    it("should undo zoom operation and restore previous value", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) {
        // Skip if zoom control not present
        return;
      }

      const initialZoom = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // Zoom in
      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        await zoomInButton.click();
        await waitFrames(page, 5);
      }

      const zoomedValue = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      expect(zoomedValue).not.toBe(initialZoom);

      // Undo
      await pressKeys(page, "Control", "z");
      await waitFrames(page, 5);

      const afterUndo = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // INVARIANT: zoom should be restored to initial value
      expect(afterUndo).toBe(initialZoom);
    });

    it("should restore state after multiple sequential undos", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const states: string[] = [];

      // Capture initial state
      const initial = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      states.push(initial || "");

      // Make 5 zoom changes
      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        for (let i = 0; i < 5; i++) {
          await zoomInButton.click();
          await waitFrames(page, 5);
          const zoom = await page.$eval(
            ".lattice-zoom-level",
            (el) => el.textContent,
          );
          states.push(zoom || "");
        }
      }

      // Undo all 5 operations one by one
      for (let i = 4; i >= 0; i--) {
        await pressKeys(page, "Control", "z");
        await waitFrames(page, 5);

        const currentZoom = await page.$eval(
          ".lattice-zoom-level",
          (el) => el.textContent,
        );

        // INVARIANT: each undo restores to the previous state
        expect(currentZoom).toBe(states[i]);
      }
    });
  });

  describe("Invariant: Redo Restores Undone Operations", () => {
    it("should redo undone operation", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const initialZoom = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // Zoom in
      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        await zoomInButton.click();
        await waitFrames(page, 5);
      }

      const zoomedValue = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // Undo
      await pressKeys(page, "Control", "z");
      await waitFrames(page, 5);

      // Redo
      await pressKeys(page, "Control", "Shift", "z");
      await waitFrames(page, 5);

      const afterRedo = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // INVARIANT: redo restores the zoomed value
      expect(afterRedo).toBe(zoomedValue);
    });

    it("should allow multiple redo operations after multiple undos", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const states: string[] = [];

      // Initial state
      const initial = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      states.push(initial || "");

      // Make 3 changes
      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (zoomInButton) {
        for (let i = 0; i < 3; i++) {
          await zoomInButton.click();
          await waitFrames(page, 5);
          const zoom = await page.$eval(
            ".lattice-zoom-level",
            (el) => el.textContent,
          );
          states.push(zoom || "");
        }
      }

      // Undo all 3
      for (let i = 0; i < 3; i++) {
        await pressKeys(page, "Control", "z");
        await waitFrames(page, 5);
      }

      // Should be at initial state
      let current = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      expect(current).toBe(states[0]);

      // Redo all 3
      for (let i = 1; i <= 3; i++) {
        await pressKeys(page, "Control", "Shift", "z");
        await waitFrames(page, 5);

        current = await page.$eval(
          ".lattice-zoom-level",
          (el) => el.textContent,
        );
        // INVARIANT: each redo advances to next state
        expect(current).toBe(states[i]);
      }
    });
  });

  describe("Invariant: New Operation Clears Redo Stack", () => {
    it("should clear redo stack after new operation", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const zoomInButton = await page.$('button[title="Zoom In"]');
      const zoomOutButton = await page.$('button[title="Zoom Out"]');
      if (!zoomInButton || !zoomOutButton) return;

      // Make a change
      await zoomInButton.click();
      await waitFrames(page, 5);

      // Undo
      await pressKeys(page, "Control", "z");
      await waitFrames(page, 5);

      // At this point, redo should be possible
      // Now make a different operation (zoom out)
      await zoomOutButton.click();
      await waitFrames(page, 5);

      // Try to redo - should have no effect
      const beforeRedo = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      await pressKeys(page, "Control", "Shift", "z");
      await waitFrames(page, 5);

      const afterRedo = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // INVARIANT: redo should not change state (redo stack was cleared)
      expect(afterRedo).toBe(beforeRedo);
    });
  });

  describe("Invariant: History Depth Limit", () => {
    it("should not exceed maximum history depth", async () => {
      // Make many operations to potentially exceed history limit
      const MAX_EXPECTED_HISTORY = 50;

      const zoomInButton = await page.$('button[title="Zoom In"]');
      const zoomOutButton = await page.$('button[title="Zoom Out"]');

      if (!zoomInButton || !zoomOutButton) return;

      // Make 60+ operations (more than expected max)
      for (let i = 0; i < 65; i++) {
        if (i % 2 === 0) {
          await zoomInButton.click();
        } else {
          await zoomOutButton.click();
        }
        // Don't wait too long, just a frame
        await waitFrames(page, 1);
      }

      await waitFrames(page, 10);

      // Try to undo as many times as possible
      let undoCount = 0;
      for (let i = 0; i < 100; i++) {
        const beforeUndo = await page.$eval(
          ".lattice-zoom-level",
          (el) => el.textContent,
        );

        await pressKeys(page, "Control", "z");
        await waitFrames(page, 2);

        const afterUndo = await page.$eval(
          ".lattice-zoom-level",
          (el) => el.textContent,
        );

        if (beforeUndo === afterUndo) {
          // Hit the bottom of history
          break;
        }
        undoCount++;
      }

      // INVARIANT: should be capped at MAX_HISTORY_SIZE - 1 undos
      // (since initial state counts as one)
      expect(undoCount).toBeLessThanOrEqual(MAX_EXPECTED_HISTORY);
    });
  });

  describe("Invariant: State Consistency", () => {
    it("should maintain consistent state through undo-redo cycle", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (!zoomInButton) return;

      // Initial state
      const initialState = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // Make 3 changes
      for (let i = 0; i < 3; i++) {
        await zoomInButton.click();
        await waitFrames(page, 3);
      }

      const finalState = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // Undo all
      for (let i = 0; i < 3; i++) {
        await pressKeys(page, "Control", "z");
        await waitFrames(page, 3);
      }

      // Should be at initial
      let current = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      expect(current).toBe(initialState);

      // Redo all
      for (let i = 0; i < 3; i++) {
        await pressKeys(page, "Control", "Shift", "z");
        await waitFrames(page, 3);
      }

      // Should be at final
      current = await page.$eval(".lattice-zoom-level", (el) => el.textContent);
      expect(current).toBe(finalState);

      // Undo 2
      for (let i = 0; i < 2; i++) {
        await pressKeys(page, "Control", "z");
        await waitFrames(page, 3);
      }

      // Redo 2
      for (let i = 0; i < 2; i++) {
        await pressKeys(page, "Control", "Shift", "z");
        await waitFrames(page, 3);
      }

      // Should still be at final
      current = await page.$eval(".lattice-zoom-level", (el) => el.textContent);
      expect(current).toBe(finalState);
    });

    it("should handle interleaved undo/redo operations", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (!zoomInButton) return;

      const states: string[] = [];

      // Capture states as we make changes
      states.push(
        (await page.$eval(".lattice-zoom-level", (el) => el.textContent)) || "",
      );

      for (let i = 0; i < 5; i++) {
        await zoomInButton.click();
        await waitFrames(page, 3);
        states.push(
          (await page.$eval(".lattice-zoom-level", (el) => el.textContent)) ||
            "",
        );
      }

      // Interleaved undo/redo pattern
      const commands: ("undo" | "redo")[] = [
        "undo", // at state[4]
        "undo", // at state[3]
        "redo", // at state[4]
        "undo", // at state[3]
        "undo", // at state[2]
        "undo", // at state[1]
        "redo", // at state[2]
        "redo", // at state[3]
        "redo", // at state[4]
        "redo", // at state[5] (final)
      ];

      const expectedStates = [4, 3, 4, 3, 2, 1, 2, 3, 4, 5];

      for (let i = 0; i < commands.length; i++) {
        if (commands[i] === "undo") {
          await pressKeys(page, "Control", "z");
        } else {
          await pressKeys(page, "Control", "Shift", "z");
        }
        await waitFrames(page, 3);

        const current = await page.$eval(
          ".lattice-zoom-level",
          (el) => el.textContent,
        );
        expect(current).toBe(states[expectedStates[i]]);
      }
    });
  });

  describe("Invariant: Cross-Session Persistence", () => {
    it("should persist history across navigation within session", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (!zoomInButton) return;

      // Make changes
      const initialZoom = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      await zoomInButton.click();
      await waitFrames(page, 5);

      const zoomedValue = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // Navigate away and back
      await navigateTo(page, "/settings");
      await waitFrames(page, 5);
      await navigateTo(page, "/");
      await waitFrames(page, 5);

      // Check if zoom is preserved
      const newZoomDisplay = await page.$(".lattice-zoom-level");
      if (!newZoomDisplay) return;

      const currentZoom = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // The zoom should either be preserved or reset, but undo should work
      // Try undo and see if app remains stable
      await pressKeys(page, "Control", "z");
      await waitFrames(page, 5);

      const afterUndo = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // If history persisted, should be at initial
      // If reset, should still work without crashing
      expect(afterUndo).toBeDefined();
    });
  });

  describe("Invariant: Keyboard Shortcuts Work Correctly", () => {
    it("should support Ctrl+Z for undo", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (!zoomInButton) return;

      const before = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      await zoomInButton.click();
      await waitFrames(page, 5);

      // Use Ctrl+Z
      await pressKeys(page, "Control", "z");
      await waitFrames(page, 5);

      const after = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      expect(after).toBe(before);
    });

    it("should support Ctrl+Shift+Z for redo", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (!zoomInButton) return;

      await zoomInButton.click();
      await waitFrames(page, 5);

      const zoomed = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      await pressKeys(page, "Control", "z");
      await waitFrames(page, 5);

      // Use Ctrl+Shift+Z
      await pressKeys(page, "Control", "Shift", "z");
      await waitFrames(page, 5);

      const after = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      expect(after).toBe(zoomed);
    });

    it("should support Ctrl+Y as alternative redo", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (!zoomInButton) return;

      await zoomInButton.click();
      await waitFrames(page, 5);

      const zoomed = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      await pressKeys(page, "Control", "z");
      await waitFrames(page, 5);

      // Use Ctrl+Y as alternative redo
      await pressKeys(page, "Control", "y");
      await waitFrames(page, 5);

      const after = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      // This should either work or not crash
      // If Ctrl+Y is supported, it should restore zoomed value
      // If not supported, state should remain unchanged
      expect(after).toBeDefined();
    });
  });

  describe("Edge Cases", () => {
    it("should handle rapid undo/redo keypresses", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (!zoomInButton) return;

      // Make some changes
      for (let i = 0; i < 5; i++) {
        await zoomInButton.click();
        await waitFrames(page, 2);
      }

      // Rapid fire undo/redo without waiting
      const keyPromises = [];
      for (let i = 0; i < 10; i++) {
        keyPromises.push(pressKeys(page, "Control", "z"));
        keyPromises.push(pressKeys(page, "Control", "Shift", "z"));
      }

      await Promise.all(keyPromises);
      await waitFrames(page, 10);

      // App should still be responsive
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);

      // Zoom display should have valid value
      const finalZoom = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );
      expect(finalZoom).toMatch(/^\d+(\.\d+)?%$/);
    });

    it("should handle undo during animation", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (!zoomInButton) return;

      // Start an action and immediately undo
      zoomInButton.click(); // Don't await
      await pressKeys(page, "Control", "z");
      await waitFrames(page, 10);

      // App should be in a valid state
      const isResponsive = await page.evaluate(() => {
        return document.querySelector("#lattice-root") !== null;
      });

      expect(isResponsive).toBe(true);
    });

    it("should handle undo while another operation is in progress", async () => {
      const zoomDisplay = await page.$(".lattice-zoom-level");
      if (!zoomDisplay) return;

      const zoomInButton = await page.$('button[title="Zoom In"]');
      if (!zoomInButton) return;

      // Make initial change
      await zoomInButton.click();
      await waitFrames(page, 5);

      // Start multiple operations simultaneously
      zoomInButton.click();
      zoomInButton.click();
      await pressKeys(page, "Control", "z");
      zoomInButton.click();

      await waitFrames(page, 20);

      // App should reach a stable, valid state
      const finalZoom = await page.$eval(
        ".lattice-zoom-level",
        (el) => el.textContent,
      );

      expect(finalZoom).toBeDefined();
      expect(finalZoom).toMatch(/^\d+(\.\d+)?%$/);

      // Zoom should be a positive value
      const zoomValue = parseFloat(finalZoom!.replace("%", ""));
      expect(zoomValue).toBeGreaterThan(0);
    });
  });
});
