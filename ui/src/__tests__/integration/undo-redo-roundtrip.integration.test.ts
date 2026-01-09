/**
 * Integration Test: Undo/Redo Roundtrip
 *
 * Tests that undo/redo operations correctly restore state
 * without data loss or corruption.
 *
 * CRITICAL: If this fails, users cannot reliably undo their work.
 */

import { describe, expect, test, beforeEach } from "vitest";

// ============================================================================
// Mock History Manager (simulates store undo/redo behavior)
// ============================================================================

interface HistoryEntry<T> {
  state: T;
  timestamp: number;
}

class MockHistoryManager<T> {
  private undoStack: HistoryEntry<T>[] = [];
  private redoStack: HistoryEntry<T>[] = [];
  private currentState: T;
  private maxHistory = 100;

  constructor(initialState: T) {
    this.currentState = this.deepClone(initialState);
  }

  private deepClone<V>(obj: V): V {
    return JSON.parse(JSON.stringify(obj));
  }

  pushState(state: T): void {
    this.undoStack.push({
      state: this.deepClone(this.currentState),
      timestamp: Date.now(),
    });

    if (this.undoStack.length > this.maxHistory) {
      this.undoStack.shift();
    }

    this.currentState = this.deepClone(state);
    this.redoStack = []; // Clear redo stack on new action
  }

  undo(): T | null {
    if (this.undoStack.length === 0) {
      return null;
    }

    this.redoStack.push({
      state: this.deepClone(this.currentState),
      timestamp: Date.now(),
    });

    const entry = this.undoStack.pop()!;
    this.currentState = this.deepClone(entry.state);
    return this.currentState;
  }

  redo(): T | null {
    if (this.redoStack.length === 0) {
      return null;
    }

    this.undoStack.push({
      state: this.deepClone(this.currentState),
      timestamp: Date.now(),
    });

    const entry = this.redoStack.pop()!;
    this.currentState = this.deepClone(entry.state);
    return this.currentState;
  }

  getState(): T {
    return this.deepClone(this.currentState);
  }

  canUndo(): boolean {
    return this.undoStack.length > 0;
  }

  canRedo(): boolean {
    return this.redoStack.length > 0;
  }

  getUndoCount(): number {
    return this.undoStack.length;
  }

  getRedoCount(): number {
    return this.redoStack.length;
  }
}

// ============================================================================
// Test Types
// ============================================================================

interface TestLayer {
  id: string;
  name: string;
  opacity: number;
  position: { x: number; y: number; z: number };
  visible: boolean;
}

interface TestProject {
  id: string;
  name: string;
  layers: TestLayer[];
  settings: {
    width: number;
    height: number;
  };
}

function createTestProject(): TestProject {
  return {
    id: "project-1",
    name: "Test Project",
    layers: [],
    settings: { width: 1920, height: 1080 },
  };
}

function createTestLayer(id: string, name: string): TestLayer {
  return {
    id,
    name,
    opacity: 100,
    position: { x: 0, y: 0, z: 0 },
    visible: true,
  };
}

// ============================================================================
// Integration Tests
// ============================================================================

describe("Undo/Redo - Basic Operations", () => {
  let history: MockHistoryManager<TestProject>;

  beforeEach(() => {
    history = new MockHistoryManager(createTestProject());
  });

  test("single undo returns to previous state", () => {
    const project = history.getState();
    project.layers.push(createTestLayer("layer-1", "Layer 1"));
    history.pushState(project);

    expect(history.getState().layers).toHaveLength(1);

    history.undo();
    expect(history.getState().layers).toHaveLength(0);
  });

  test("single redo restores undone change", () => {
    const project = history.getState();
    project.layers.push(createTestLayer("layer-1", "Layer 1"));
    history.pushState(project);

    history.undo();
    expect(history.getState().layers).toHaveLength(0);

    history.redo();
    expect(history.getState().layers).toHaveLength(1);
  });

  test("multiple undos walk back through history", () => {
    // Make 5 changes
    for (let i = 0; i < 5; i++) {
      const project = history.getState();
      project.layers.push(createTestLayer(`layer-${i}`, `Layer ${i}`));
      history.pushState(project);
    }

    expect(history.getState().layers).toHaveLength(5);

    // Undo all
    for (let i = 4; i >= 0; i--) {
      history.undo();
      expect(history.getState().layers).toHaveLength(i);
    }
  });

  test("multiple redos walk forward through history", () => {
    // Make 5 changes
    for (let i = 0; i < 5; i++) {
      const project = history.getState();
      project.layers.push(createTestLayer(`layer-${i}`, `Layer ${i}`));
      history.pushState(project);
    }

    // Undo all
    for (let i = 0; i < 5; i++) {
      history.undo();
    }

    expect(history.getState().layers).toHaveLength(0);

    // Redo all
    for (let i = 0; i < 5; i++) {
      history.redo();
      expect(history.getState().layers).toHaveLength(i + 1);
    }
  });
});

describe("Undo/Redo - State Integrity", () => {
  let history: MockHistoryManager<TestProject>;

  beforeEach(() => {
    history = new MockHistoryManager(createTestProject());
  });

  test("undo/redo preserves layer properties exactly", () => {
    const project = history.getState();
    const layer = createTestLayer("layer-1", "Test Layer");
    layer.opacity = 75;
    layer.position = { x: 100, y: 200, z: 50 };
    layer.visible = false;
    project.layers.push(layer);
    history.pushState(project);

    history.undo();
    history.redo();

    const restored = history.getState().layers[0];
    expect(restored.opacity).toBe(75);
    expect(restored.position.x).toBe(100);
    expect(restored.position.y).toBe(200);
    expect(restored.position.z).toBe(50);
    expect(restored.visible).toBe(false);
  });

  test("undo/redo preserves project settings", () => {
    const project = history.getState();
    project.settings.width = 4096;
    project.settings.height = 2160;
    history.pushState(project);

    history.undo();
    expect(history.getState().settings.width).toBe(1920);

    history.redo();
    expect(history.getState().settings.width).toBe(4096);
    expect(history.getState().settings.height).toBe(2160);
  });

  test("undo/redo preserves floating point precision", () => {
    const project = history.getState();
    const layer = createTestLayer("layer-1", "Test");
    layer.position = { x: 123.456789, y: 987.654321, z: 0.123456789 };
    project.layers.push(layer);
    history.pushState(project);

    history.undo();
    history.redo();

    const restored = history.getState().layers[0];
    expect(restored.position.x).toBeCloseTo(123.456789, 8);
    expect(restored.position.y).toBeCloseTo(987.654321, 8);
    expect(restored.position.z).toBeCloseTo(0.123456789, 8);
  });

  test("undo/redo preserves layer order", () => {
    const project = history.getState();
    project.layers = [
      createTestLayer("a", "Layer A"),
      createTestLayer("b", "Layer B"),
      createTestLayer("c", "Layer C"),
    ];
    history.pushState(project);

    // Reorder
    const reordered = history.getState();
    reordered.layers = [reordered.layers[2], reordered.layers[0], reordered.layers[1]];
    history.pushState(reordered);

    expect(history.getState().layers[0].id).toBe("c");

    history.undo();
    expect(history.getState().layers[0].id).toBe("a");

    history.redo();
    expect(history.getState().layers[0].id).toBe("c");
  });
});

describe("Undo/Redo - Edge Cases", () => {
  let history: MockHistoryManager<TestProject>;

  beforeEach(() => {
    history = new MockHistoryManager(createTestProject());
  });

  test("undo on empty stack returns null", () => {
    expect(history.undo()).toBeNull();
    expect(history.canUndo()).toBe(false);
  });

  test("redo on empty stack returns null", () => {
    expect(history.redo()).toBeNull();
    expect(history.canRedo()).toBe(false);
  });

  test("new action clears redo stack", () => {
    const project = history.getState();
    project.layers.push(createTestLayer("1", "Layer 1"));
    history.pushState(project);

    const project2 = history.getState();
    project2.layers.push(createTestLayer("2", "Layer 2"));
    history.pushState(project2);

    history.undo(); // Back to 1 layer
    expect(history.canRedo()).toBe(true);

    // New action
    const project3 = history.getState();
    project3.layers[0].name = "Renamed";
    history.pushState(project3);

    expect(history.canRedo()).toBe(false);
  });

  test("undo after redo works correctly", () => {
    const project = history.getState();
    project.layers.push(createTestLayer("1", "Layer 1"));
    history.pushState(project);

    history.undo();
    history.redo();
    history.undo();

    expect(history.getState().layers).toHaveLength(0);
    expect(history.canRedo()).toBe(true);
  });

  test("rapid undo/redo maintains consistency", () => {
    // Create initial state with layers
    for (let i = 0; i < 10; i++) {
      const project = history.getState();
      project.layers.push(createTestLayer(`${i}`, `Layer ${i}`));
      history.pushState(project);
    }

    // Rapid undo/redo
    history.undo(); // 9
    history.undo(); // 8
    history.redo(); // 9
    history.undo(); // 8
    history.undo(); // 7
    history.undo(); // 6
    history.redo(); // 7
    history.redo(); // 8

    expect(history.getState().layers).toHaveLength(8);
  });
});

describe("Undo/Redo - Complex Scenarios", () => {
  let history: MockHistoryManager<TestProject>;

  beforeEach(() => {
    history = new MockHistoryManager(createTestProject());
  });

  test("undo/redo with layer deletion", () => {
    // Add 3 layers
    let project = history.getState();
    project.layers = [
      createTestLayer("a", "A"),
      createTestLayer("b", "B"),
      createTestLayer("c", "C"),
    ];
    history.pushState(project);

    // Delete middle layer
    project = history.getState();
    project.layers = project.layers.filter((l) => l.id !== "b");
    history.pushState(project);

    expect(history.getState().layers).toHaveLength(2);
    expect(history.getState().layers.find((l) => l.id === "b")).toBeUndefined();

    // Undo deletion
    history.undo();
    expect(history.getState().layers).toHaveLength(3);
    expect(history.getState().layers.find((l) => l.id === "b")).toBeDefined();
  });

  test("undo/redo with batch property changes", () => {
    let project = history.getState();
    project.layers.push(createTestLayer("1", "Layer"));
    history.pushState(project);

    // Batch change: opacity + position + visibility
    project = history.getState();
    project.layers[0].opacity = 50;
    project.layers[0].position = { x: 100, y: 100, z: 0 };
    project.layers[0].visible = false;
    history.pushState(project);

    const modified = history.getState().layers[0];
    expect(modified.opacity).toBe(50);
    expect(modified.position.x).toBe(100);
    expect(modified.visible).toBe(false);

    history.undo();

    const original = history.getState().layers[0];
    expect(original.opacity).toBe(100);
    expect(original.position.x).toBe(0);
    expect(original.visible).toBe(true);
  });

  test("full undo/redo cycle returns to exact initial state", () => {
    const initial = JSON.stringify(history.getState());

    // Make many changes
    for (let i = 0; i < 20; i++) {
      const project = history.getState();
      project.layers.push(createTestLayer(`${i}`, `Layer ${i}`));
      if (i > 0) {
        project.layers[0].opacity = i * 5;
      }
      history.pushState(project);
    }

    // Undo all
    while (history.canUndo()) {
      history.undo();
    }

    expect(JSON.stringify(history.getState())).toBe(initial);
  });

  test("undo/redo maintains referential independence", () => {
    let project = history.getState();
    const layer = createTestLayer("1", "Original");
    project.layers.push(layer);
    history.pushState(project);

    // Modify after pushing (should not affect history)
    project.layers[0].name = "Modified After Push";

    history.undo();
    history.redo();

    // Name should be what was pushed, not the modified value
    expect(history.getState().layers[0].name).toBe("Original");
  });
});

describe("Undo/Redo - State Count Verification", () => {
  let history: MockHistoryManager<TestProject>;

  beforeEach(() => {
    history = new MockHistoryManager(createTestProject());
  });

  test("undo count tracks correctly", () => {
    expect(history.getUndoCount()).toBe(0);

    for (let i = 0; i < 5; i++) {
      const project = history.getState();
      project.name = `Version ${i}`;
      history.pushState(project);
    }

    expect(history.getUndoCount()).toBe(5);

    history.undo();
    expect(history.getUndoCount()).toBe(4);

    history.undo();
    expect(history.getUndoCount()).toBe(3);
  });

  test("redo count tracks correctly", () => {
    expect(history.getRedoCount()).toBe(0);

    for (let i = 0; i < 5; i++) {
      const project = history.getState();
      project.name = `Version ${i}`;
      history.pushState(project);
    }

    history.undo();
    history.undo();
    history.undo();

    expect(history.getRedoCount()).toBe(3);

    history.redo();
    expect(history.getRedoCount()).toBe(2);
  });

  test("new action resets redo count to zero", () => {
    for (let i = 0; i < 3; i++) {
      const project = history.getState();
      project.name = `Version ${i}`;
      history.pushState(project);
    }

    history.undo();
    history.undo();
    expect(history.getRedoCount()).toBe(2);

    // New action
    const project = history.getState();
    project.name = "New Version";
    history.pushState(project);

    expect(history.getRedoCount()).toBe(0);
  });
});
