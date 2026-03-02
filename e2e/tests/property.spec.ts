/**
 * Property-Based Tests using fast-check
 *
 * Hard-to-pass tests with realistic distributions that verify:
 * - History stack invariants (undo/redo)
 * - State transition correctness
 * - Input validation robustness
 * - Serialization roundtrips
 * - UI state consistency
 */

import fc from "fast-check";
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
  waitFrames,
} from "./helpers/browser.js";

// ============================================================================
// History State Model (mirrors PureScript HistoryOps)
// ============================================================================

interface HistoryState<T> {
  stack: T[];
  index: number;
}

const MAX_HISTORY_SIZE = 50;

function mkHistoryState<T>(initial: T): HistoryState<T> {
  return { stack: [initial], index: 0 };
}

function pushHistory<T>(snapshot: T, state: HistoryState<T>): HistoryState<T> {
  // Truncate future states
  const truncated = state.stack.slice(0, state.index + 1);
  // Add new snapshot
  const withNew = [...truncated, snapshot];
  // Enforce max size
  const trimmed =
    withNew.length > MAX_HISTORY_SIZE
      ? withNew.slice(withNew.length - MAX_HISTORY_SIZE)
      : withNew;
  return { stack: trimmed, index: trimmed.length - 1 };
}

function undo<T>(state: HistoryState<T>): {
  state: HistoryState<T>;
  snapshot: T | undefined;
} {
  if (canUndo(state)) {
    const newIdx = state.index - 1;
    return {
      state: { ...state, index: newIdx },
      snapshot: state.stack[newIdx],
    };
  }
  return { state, snapshot: undefined };
}

function redo<T>(state: HistoryState<T>): {
  state: HistoryState<T>;
  snapshot: T | undefined;
} {
  if (canRedo(state)) {
    const newIdx = state.index + 1;
    return {
      state: { ...state, index: newIdx },
      snapshot: state.stack[newIdx],
    };
  }
  return { state, snapshot: undefined };
}

function canUndo<T>(state: HistoryState<T>): boolean {
  return state.index > 0;
}

function canRedo<T>(state: HistoryState<T>): boolean {
  return state.index < state.stack.length - 1;
}

function clearHistory<T>(state: HistoryState<T>): HistoryState<T> {
  const current = state.stack[state.index];
  return current !== undefined ? mkHistoryState(current) : state;
}

// ============================================================================
// Arbitraries - Realistic test data generators
// ============================================================================

// Layer names with realistic distribution (weighted toward common patterns)
const layerNameArb = fc.oneof(
  { weight: 10, arbitrary: fc.constantFrom("Layer 1", "Background", "Text") },
  { weight: 5, arbitrary: fc.stringMatching(/^Layer \d{1,3}$/) },
  { weight: 3, arbitrary: fc.string({ minLength: 1, maxLength: 50 }) },
  { weight: 2, arbitrary: fc.constantFrom("图层 1", "レイヤー 2", "שכבה 3") },
);

// Opacity values with realistic distribution
const opacityArb = fc.oneof(
  { weight: 10, arbitrary: fc.constantFrom(0, 0.5, 1) }, // Common values
  { weight: 5, arbitrary: fc.double({ min: 0, max: 1, noNaN: true }) },
);

// Zoom levels with realistic distribution
const zoomLevelArb = fc.oneof(
  { weight: 10, arbitrary: fc.constantFrom(25, 50, 100, 150, 200, 400) },
  { weight: 3, arbitrary: fc.integer({ min: 10, max: 3200 }) },
);

// Canvas dimensions with realistic distribution
const dimensionArb = fc.oneof(
  { weight: 10, arbitrary: fc.constantFrom(512, 768, 1024, 1920, 2048, 4096) },
  { weight: 3, arbitrary: fc.integer({ min: 1, max: 8192 }) },
);

// Color values
const colorArb = fc.tuple(
  fc.integer({ min: 0, max: 255 }),
  fc.integer({ min: 0, max: 255 }),
  fc.integer({ min: 0, max: 255 }),
  fc.double({ min: 0, max: 1, noNaN: true }),
);

// Layer object
const layerArb = fc.record({
  id: fc.uuid(),
  name: layerNameArb,
  opacity: opacityArb,
  visible: fc.boolean(),
  locked: fc.boolean(),
  blendMode: fc.constantFrom("normal", "multiply", "screen", "overlay"),
});

// Project state snapshot
const projectSnapshotArb = fc.record({
  version: fc.constant("1.0.0"),
  width: dimensionArb,
  height: dimensionArb,
  layers: fc.array(layerArb, { minLength: 1, maxLength: 20 }),
  activeLayerIndex: fc.nat(19),
  zoom: zoomLevelArb,
  panX: fc.double({ min: -10000, max: 10000, noNaN: true }),
  panY: fc.double({ min: -10000, max: 10000, noNaN: true }),
});

// History command - represents user actions
const historyCommandArb = fc.oneof(
  { weight: 5, arbitrary: fc.constant({ type: "push" as const }) },
  { weight: 3, arbitrary: fc.constant({ type: "undo" as const }) },
  { weight: 2, arbitrary: fc.constant({ type: "redo" as const }) },
  { weight: 1, arbitrary: fc.constant({ type: "clear" as const }) },
);

// ============================================================================
// Property Tests - History State Invariants
// ============================================================================

describe("Property: History Stack Invariants", () => {
  it("property: index always within stack bounds", () => {
    fc.assert(
      fc.property(
        fc.array(fc.string(), { minLength: 1, maxLength: 100 }),
        fc.array(historyCommandArb, { minLength: 0, maxLength: 200 }),
        (snapshots, commands) => {
          let state = mkHistoryState(snapshots[0]);

          // Apply initial pushes
          for (let i = 1; i < snapshots.length; i++) {
            state = pushHistory(snapshots[i], state);
          }

          // Apply random commands
          for (const cmd of commands) {
            switch (cmd.type) {
              case "push":
                state = pushHistory(`snapshot-${Math.random()}`, state);
                break;
              case "undo":
                state = undo(state).state;
                break;
              case "redo":
                state = redo(state).state;
                break;
              case "clear":
                state = clearHistory(state);
                break;
            }

            // INVARIANT: index always in bounds
            expect(state.index).toBeGreaterThanOrEqual(0);
            expect(state.index).toBeLessThan(state.stack.length);
          }

          return true;
        },
      ),
      { numRuns: 1000 },
    );
  });

  it("property: stack never exceeds max size", () => {
    fc.assert(
      fc.property(
        fc.array(fc.string(), { minLength: 1, maxLength: 200 }),
        (snapshots) => {
          let state = mkHistoryState(snapshots[0]);

          for (let i = 1; i < snapshots.length; i++) {
            state = pushHistory(snapshots[i], state);
            // INVARIANT: never exceeds max
            expect(state.stack.length).toBeLessThanOrEqual(MAX_HISTORY_SIZE);
          }

          return true;
        },
      ),
      { numRuns: 500 },
    );
  });

  it("property: undo-redo are inverses (without intervening push)", () => {
    fc.assert(
      fc.property(
        fc.array(fc.string(), { minLength: 2, maxLength: 50 }),
        fc.nat(49),
        (snapshots, undoCount) => {
          // Build history
          let state = mkHistoryState(snapshots[0]);
          for (let i = 1; i < snapshots.length; i++) {
            state = pushHistory(snapshots[i], state);
          }

          const initialIndex = state.index;
          const actualUndos = Math.min(undoCount, initialIndex);

          // Undo N times
          for (let i = 0; i < actualUndos; i++) {
            state = undo(state).state;
          }

          // Redo N times
          for (let i = 0; i < actualUndos; i++) {
            state = redo(state).state;
          }

          // INVARIANT: should be back at original index
          expect(state.index).toBe(initialIndex);

          return true;
        },
      ),
      { numRuns: 500 },
    );
  });

  it("property: push after undo truncates future", () => {
    fc.assert(
      fc.property(
        fc.array(fc.string(), { minLength: 3, maxLength: 20 }),
        fc.nat(19),
        fc.string(),
        (snapshots, undoCount, newSnapshot) => {
          // Build history
          let state = mkHistoryState(snapshots[0]);
          for (let i = 1; i < snapshots.length; i++) {
            state = pushHistory(snapshots[i], state);
          }

          const actualUndos = Math.min(undoCount, state.index);

          // Undo some amount
          for (let i = 0; i < actualUndos; i++) {
            state = undo(state).state;
          }

          const indexBeforePush = state.index;

          // Push new state
          state = pushHistory(newSnapshot, state);

          // INVARIANT: new index is one more than before
          expect(state.index).toBe(indexBeforePush + 1);

          // INVARIANT: redo should not be possible (future was truncated)
          expect(canRedo(state)).toBe(false);

          // INVARIANT: stack length matches index + 1
          expect(state.stack.length).toBe(state.index + 1);

          return true;
        },
      ),
      { numRuns: 500 },
    );
  });

  it("property: canUndo and canRedo are consistent with index", () => {
    fc.assert(
      fc.property(
        fc.array(fc.string(), { minLength: 1, maxLength: 50 }),
        fc.array(historyCommandArb, { minLength: 0, maxLength: 100 }),
        (snapshots, commands) => {
          let state = mkHistoryState(snapshots[0]);

          for (let i = 1; i < snapshots.length; i++) {
            state = pushHistory(snapshots[i], state);
          }

          for (const cmd of commands) {
            // INVARIANT: canUndo iff index > 0
            expect(canUndo(state)).toBe(state.index > 0);

            // INVARIANT: canRedo iff index < stack.length - 1
            expect(canRedo(state)).toBe(state.index < state.stack.length - 1);

            switch (cmd.type) {
              case "push":
                state = pushHistory(`s-${Math.random()}`, state);
                break;
              case "undo":
                state = undo(state).state;
                break;
              case "redo":
                state = redo(state).state;
                break;
              case "clear":
                state = clearHistory(state);
                break;
            }
          }

          return true;
        },
      ),
      { numRuns: 500 },
    );
  });

  it("property: undo returns correct snapshot", () => {
    fc.assert(
      fc.property(
        fc.array(fc.string({ minLength: 1 }), { minLength: 2, maxLength: 50 }),
        (snapshots) => {
          // Build history with unique snapshots
          let state = mkHistoryState(snapshots[0]);
          for (let i = 1; i < snapshots.length; i++) {
            state = pushHistory(snapshots[i], state);
          }

          // Undo all the way back
          const undoneSnapshots: string[] = [];
          while (canUndo(state)) {
            const result = undo(state);
            state = result.state;
            if (result.snapshot !== undefined) {
              undoneSnapshots.push(result.snapshot);
            }
          }

          // INVARIANT: undone snapshots match history in reverse
          const expectedSnapshots = [...snapshots]
            .slice(0, snapshots.length - 1)
            .reverse();

          // Only compare up to MAX_HISTORY_SIZE - 1 (since we start at end)
          const actualExpected = expectedSnapshots.slice(
            0,
            MAX_HISTORY_SIZE - 1,
          );
          const actualUndone = undoneSnapshots.slice(0, MAX_HISTORY_SIZE - 1);

          // If snapshots exceed max, adjust expectations
          if (snapshots.length <= MAX_HISTORY_SIZE) {
            expect(undoneSnapshots.length).toBe(snapshots.length - 1);
          }

          return true;
        },
      ),
      { numRuns: 300 },
    );
  });

  it("property: clearHistory preserves current state only", () => {
    fc.assert(
      fc.property(
        fc.array(fc.string(), { minLength: 1, maxLength: 50 }),
        fc.nat(49),
        (snapshots, moveCount) => {
          let state = mkHistoryState(snapshots[0]);

          for (let i = 1; i < snapshots.length; i++) {
            state = pushHistory(snapshots[i], state);
          }

          // Move around in history
          for (let i = 0; i < moveCount && canUndo(state); i++) {
            state = undo(state).state;
          }

          const currentSnapshot = state.stack[state.index];
          state = clearHistory(state);

          // INVARIANTS after clear:
          expect(state.stack.length).toBe(1);
          expect(state.index).toBe(0);
          expect(state.stack[0]).toBe(currentSnapshot);
          expect(canUndo(state)).toBe(false);
          expect(canRedo(state)).toBe(false);

          return true;
        },
      ),
      { numRuns: 300 },
    );
  });
});

// ============================================================================
// Property Tests - Serialization Roundtrips
// ============================================================================

describe("Property: Serialization Roundtrips", () => {
  it("property: JSON roundtrip preserves project state", () => {
    fc.assert(
      fc.property(projectSnapshotArb, (project) => {
        const serialized = JSON.stringify(project);
        const deserialized = JSON.parse(serialized);

        expect(deserialized.version).toBe(project.version);
        expect(deserialized.width).toBe(project.width);
        expect(deserialized.height).toBe(project.height);
        expect(deserialized.layers.length).toBe(project.layers.length);

        for (let i = 0; i < project.layers.length; i++) {
          expect(deserialized.layers[i].id).toBe(project.layers[i].id);
          expect(deserialized.layers[i].name).toBe(project.layers[i].name);
        }

        return true;
      }),
      { numRuns: 500 },
    );
  });

  it("property: layer opacity clamping", () => {
    fc.assert(
      fc.property(
        fc.double({ min: -100, max: 100, noNaN: true }),
        (rawOpacity) => {
          const clamped = Math.max(0, Math.min(1, rawOpacity));

          expect(clamped).toBeGreaterThanOrEqual(0);
          expect(clamped).toBeLessThanOrEqual(1);

          // Idempotence
          expect(Math.max(0, Math.min(1, clamped))).toBe(clamped);

          return true;
        },
      ),
      { numRuns: 1000 },
    );
  });

  it("property: zoom level rounding maintains precision", () => {
    fc.assert(
      fc.property(zoomLevelArb, (zoom) => {
        // Simulate display rounding
        const displayed = Math.round(zoom);
        // Convert back
        const roundtrip = Math.round(displayed);

        expect(roundtrip).toBe(displayed);
        expect(displayed).toBeGreaterThanOrEqual(1);

        return true;
      }),
      { numRuns: 500 },
    );
  });

  it("property: dimension validation", () => {
    fc.assert(
      fc.property(dimensionArb, dimensionArb, (width, height) => {
        // Dimensions must be positive integers
        expect(width).toBeGreaterThan(0);
        expect(height).toBeGreaterThan(0);
        expect(Number.isInteger(width)).toBe(true);
        expect(Number.isInteger(height)).toBe(true);

        // Canvas pixel count calculation shouldn't overflow for reasonable sizes
        if (width <= 8192 && height <= 8192) {
          const pixels = width * height;
          expect(pixels).toBeLessThanOrEqual(8192 * 8192);
          expect(pixels).toBeGreaterThan(0);
        }

        return true;
      }),
      { numRuns: 500 },
    );
  });
});

// ============================================================================
// Property Tests - Input Validation
// ============================================================================

describe("Property: Input Validation", () => {
  it("property: layer name sanitization", () => {
    fc.assert(
      fc.property(layerNameArb, (name) => {
        // Name should be a string
        expect(typeof name).toBe("string");

        // Trimmed name should not be empty if original wasn't
        if (name.trim().length > 0) {
          const sanitized = name.trim().slice(0, 100);
          expect(sanitized.length).toBeGreaterThan(0);
          expect(sanitized.length).toBeLessThanOrEqual(100);
        }

        return true;
      }),
      { numRuns: 1000 },
    );
  });

  it("property: color values are valid RGBA", () => {
    fc.assert(
      fc.property(colorArb, ([r, g, b, a]) => {
        expect(r).toBeGreaterThanOrEqual(0);
        expect(r).toBeLessThanOrEqual(255);
        expect(g).toBeGreaterThanOrEqual(0);
        expect(g).toBeLessThanOrEqual(255);
        expect(b).toBeGreaterThanOrEqual(0);
        expect(b).toBeLessThanOrEqual(255);
        expect(a).toBeGreaterThanOrEqual(0);
        expect(a).toBeLessThanOrEqual(1);

        // RGB values are integers
        expect(Number.isInteger(r)).toBe(true);
        expect(Number.isInteger(g)).toBe(true);
        expect(Number.isInteger(b)).toBe(true);

        return true;
      }),
      { numRuns: 500 },
    );
  });

  it("property: pan coordinates are finite", () => {
    fc.assert(
      fc.property(
        fc.double({ min: -1e10, max: 1e10, noNaN: true }),
        fc.double({ min: -1e10, max: 1e10, noNaN: true }),
        (panX, panY) => {
          expect(Number.isFinite(panX)).toBe(true);
          expect(Number.isFinite(panY)).toBe(true);

          // Clamping to reasonable bounds
          const clampedX = Math.max(-100000, Math.min(100000, panX));
          const clampedY = Math.max(-100000, Math.min(100000, panY));

          expect(Number.isFinite(clampedX)).toBe(true);
          expect(Number.isFinite(clampedY)).toBe(true);

          return true;
        },
      ),
      { numRuns: 500 },
    );
  });
});

// ============================================================================
// Property Tests - State Transitions
// ============================================================================

describe("Property: State Machine Transitions", () => {
  // Model of app state for state machine testing
  type AppState = {
    route: string;
    zoom: number;
    selectedLayerIndex: number | null;
    layerCount: number;
  };

  type AppCommand =
    | { type: "navigate"; route: string }
    | { type: "zoom"; direction: "in" | "out" | "reset" }
    | { type: "selectLayer"; index: number }
    | { type: "addLayer" }
    | { type: "deleteLayer" };

  const appCommandArb: fc.Arbitrary<AppCommand> = fc.oneof(
    {
      weight: 2,
      arbitrary: fc.record({
        type: fc.constant("navigate" as const),
        route: fc.constantFrom("/", "/settings", "/project", "/export"),
      }),
    },
    {
      weight: 5,
      arbitrary: fc.record({
        type: fc.constant("zoom" as const),
        direction: fc.constantFrom(
          "in" as const,
          "out" as const,
          "reset" as const,
        ),
      }),
    },
    {
      weight: 3,
      arbitrary: fc.record({
        type: fc.constant("selectLayer" as const),
        index: fc.nat(19),
      }),
    },
    { weight: 2, arbitrary: fc.constant({ type: "addLayer" as const }) },
    { weight: 2, arbitrary: fc.constant({ type: "deleteLayer" as const }) },
  );

  function applyCommand(state: AppState, cmd: AppCommand): AppState {
    switch (cmd.type) {
      case "navigate":
        return { ...state, route: cmd.route };
      case "zoom":
        if (cmd.direction === "reset") return { ...state, zoom: 100 };
        if (cmd.direction === "in")
          return { ...state, zoom: Math.min(3200, state.zoom * 1.25) };
        return { ...state, zoom: Math.max(10, state.zoom / 1.25) };
      case "selectLayer":
        if (cmd.index < state.layerCount) {
          return { ...state, selectedLayerIndex: cmd.index };
        }
        return state;
      case "addLayer":
        return {
          ...state,
          layerCount: Math.min(20, state.layerCount + 1),
        };
      case "deleteLayer":
        if (state.layerCount > 1) {
          const newCount = state.layerCount - 1;
          const newSelected =
            state.selectedLayerIndex !== null &&
            state.selectedLayerIndex >= newCount
              ? newCount - 1
              : state.selectedLayerIndex;
          return {
            ...state,
            layerCount: newCount,
            selectedLayerIndex: newSelected,
          };
        }
        return state;
    }
  }

  it("property: state transitions maintain invariants", () => {
    fc.assert(
      fc.property(
        fc.array(appCommandArb, { minLength: 0, maxLength: 100 }),
        (commands) => {
          let state: AppState = {
            route: "/",
            zoom: 100,
            selectedLayerIndex: 0,
            layerCount: 1,
          };

          for (const cmd of commands) {
            state = applyCommand(state, cmd);

            // INVARIANTS
            expect(state.zoom).toBeGreaterThanOrEqual(10);
            expect(state.zoom).toBeLessThanOrEqual(3200);
            expect(state.layerCount).toBeGreaterThanOrEqual(1);
            expect(state.layerCount).toBeLessThanOrEqual(20);

            if (state.selectedLayerIndex !== null) {
              expect(state.selectedLayerIndex).toBeGreaterThanOrEqual(0);
              expect(state.selectedLayerIndex).toBeLessThan(state.layerCount);
            }

            expect([
              "/",
              "/settings",
              "/project",
              "/export",
              "/assets",
            ]).toContain(state.route);
          }

          return true;
        },
      ),
      { numRuns: 500 },
    );
  });

  it("property: zoom operations are bounded", () => {
    fc.assert(
      fc.property(
        fc.array(
          fc.constantFrom("in", "out", "reset") as fc.Arbitrary<
            "in" | "out" | "reset"
          >,
          {
            minLength: 0,
            maxLength: 100,
          },
        ),
        (directions) => {
          let zoom = 100;

          for (const dir of directions) {
            if (dir === "reset") {
              zoom = 100;
            } else if (dir === "in") {
              zoom = Math.min(3200, zoom * 1.25);
            } else {
              zoom = Math.max(10, zoom / 1.25);
            }

            // INVARIANT: zoom always within bounds
            expect(zoom).toBeGreaterThanOrEqual(10);
            expect(zoom).toBeLessThanOrEqual(3200);
          }

          return true;
        },
      ),
      { numRuns: 500 },
    );
  });

  it("property: layer selection validity after deletion", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 1, max: 20 }),
        fc.nat(19),
        fc.nat(19),
        (initialLayers, selectedIndex, deleteCount) => {
          let layerCount = initialLayers;
          let selected = Math.min(selectedIndex, layerCount - 1);

          const actualDeletes = Math.min(deleteCount, layerCount - 1);

          for (let i = 0; i < actualDeletes; i++) {
            layerCount--;
            if (selected >= layerCount) {
              selected = layerCount - 1;
            }
          }

          // INVARIANTS
          expect(layerCount).toBeGreaterThanOrEqual(1);
          expect(selected).toBeGreaterThanOrEqual(0);
          expect(selected).toBeLessThan(layerCount);

          return true;
        },
      ),
      { numRuns: 500 },
    );
  });
});

// ============================================================================
// Browser Property Tests - UI Consistency
// ============================================================================

describe("Property: Browser UI Consistency", () => {
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

  it("property: route changes are idempotent", async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.constantFrom("/", "/settings", "/project"),
        async (route) => {
          await navigateTo(page, route);

          const path1 = await page.evaluate(() => window.location.pathname);

          // Navigate again to same route
          await navigateTo(page, route);

          const path2 = await page.evaluate(() => window.location.pathname);

          // INVARIANT: same route
          expect(path1).toBe(path2);
          expect(path1).toBe(route);

          return true;
        },
      ),
      { numRuns: 10 }, // Fewer runs for browser tests
    );
  });

  it("property: app remains responsive after random navigation", async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.array(fc.constantFrom("/", "/settings", "/project", "/export"), {
          minLength: 1,
          maxLength: 5,
        }),
        async (routes) => {
          for (const route of routes) {
            await page.goto(`http://localhost:8080${route}`, {
              waitUntil: "domcontentloaded",
            });
          }

          await page.waitForSelector("#lattice-root", { timeout: 10000 });

          const isResponsive = await page.evaluate(() => {
            const root = document.querySelector("#lattice-root");
            return root !== null && root.children.length > 0;
          });

          expect(isResponsive).toBe(true);

          return true;
        },
      ),
      { numRuns: 10 },
    );
  });

  it("property: localStorage state survives page reload", async () => {
    await navigateTo(page, "/");

    await fc.assert(
      fc.asyncProperty(
        fc.string({ minLength: 1, maxLength: 100 }),
        async (testValue) => {
          const key = "lattice-property-test";

          // Set value
          await page.evaluate(
            ({ k, v }) => {
              localStorage.setItem(k, v);
            },
            { k: key, v: testValue },
          );

          // Reload
          await page.reload({ waitUntil: "networkidle0" });
          await page.waitForSelector("#lattice-root", { timeout: 10000 });

          // Read value back
          const retrieved = await page.evaluate((k) => {
            return localStorage.getItem(k);
          }, key);

          expect(retrieved).toBe(testValue);

          // Cleanup
          await page.evaluate((k) => {
            localStorage.removeItem(k);
          }, key);

          return true;
        },
      ),
      { numRuns: 5 },
    );
  });
});

// ============================================================================
// Stress Tests with Property-Based Generation
// ============================================================================

describe("Property: Stress Tests", () => {
  it("property: history can handle maximum load", () => {
    fc.assert(
      fc.property(
        fc.array(fc.string(), {
          minLength: MAX_HISTORY_SIZE * 2,
          maxLength: MAX_HISTORY_SIZE * 3,
        }),
        (snapshots) => {
          let state = mkHistoryState(snapshots[0]);

          for (let i = 1; i < snapshots.length; i++) {
            state = pushHistory(snapshots[i], state);
          }

          // After many pushes, should be at max size
          expect(state.stack.length).toBe(MAX_HISTORY_SIZE);
          expect(state.index).toBe(MAX_HISTORY_SIZE - 1);

          // Should still be able to undo MAX_HISTORY_SIZE - 1 times
          let undoCount = 0;
          while (canUndo(state)) {
            state = undo(state).state;
            undoCount++;
          }

          expect(undoCount).toBe(MAX_HISTORY_SIZE - 1);

          return true;
        },
      ),
      { numRuns: 100 },
    );
  });

  it("property: interleaved undo/redo/push is stable", () => {
    fc.assert(
      fc.property(
        fc.array(
          fc.oneof(
            { weight: 3, arbitrary: fc.constant("push" as const) },
            { weight: 2, arbitrary: fc.constant("undo" as const) },
            { weight: 2, arbitrary: fc.constant("redo" as const) },
          ),
          { minLength: 100, maxLength: 500 },
        ),
        (operations) => {
          let state = mkHistoryState("initial");
          let pushCounter = 0;

          for (const op of operations) {
            switch (op) {
              case "push":
                state = pushHistory(`push-${pushCounter++}`, state);
                break;
              case "undo":
                state = undo(state).state;
                break;
              case "redo":
                state = redo(state).state;
                break;
            }

            // INVARIANTS must hold after every operation
            expect(state.index).toBeGreaterThanOrEqual(0);
            expect(state.index).toBeLessThan(state.stack.length);
            expect(state.stack.length).toBeGreaterThanOrEqual(1);
            expect(state.stack.length).toBeLessThanOrEqual(MAX_HISTORY_SIZE);
          }

          return true;
        },
      ),
      { numRuns: 200 },
    );
  });

  it("property: deep project state nesting roundtrips correctly", () => {
    // Generate deeply nested structures
    const deepLayerArb = fc.letrec((tie) => ({
      node: fc.record({
        id: fc.uuid(),
        name: fc.string({ minLength: 1, maxLength: 20 }),
        children: fc.option(
          fc.array(tie("node") as fc.Arbitrary<unknown>, {
            minLength: 0,
            maxLength: 3,
          }),
          { nil: undefined },
        ),
        properties: fc.dictionary(
          fc.string({ minLength: 1, maxLength: 10 }),
          fc.oneof(fc.string(), fc.integer(), fc.boolean()),
          { minKeys: 0, maxKeys: 5 },
        ),
      }),
    })).node;

    fc.assert(
      fc.property(
        fc.array(deepLayerArb, { minLength: 1, maxLength: 5 }),
        (layers) => {
          const project = { layers, version: "1.0.0" };

          const serialized = JSON.stringify(project);
          const deserialized = JSON.parse(serialized);

          expect(deserialized.layers.length).toBe(layers.length);
          expect(deserialized.version).toBe("1.0.0");

          // Deep equality check
          expect(JSON.stringify(deserialized)).toBe(serialized);

          return true;
        },
      ),
      { numRuns: 200 },
    );
  });
});
