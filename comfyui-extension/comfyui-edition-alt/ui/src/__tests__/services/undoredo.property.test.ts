/**
 * STRICT Property Tests for Undo/Redo System
 * 
 * Tests the invariants that must hold for a correct history stack:
 * 1. Undo/redo are inverse operations
 * 2. State is fully recoverable
 * 3. Branch trimming works correctly
 * 4. Memory limits are enforced
 * 5. Deep cloning prevents reference sharing
 * 
 * TOLERANCE: ZERO - History corruption is catastrophic
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import { setActivePinia, createPinia } from 'pinia';
import { useHistoryStore } from '@/stores/historyStore';
import type { LatticeProject, Layer, AnimatableProperty, Composition } from '@/types/project';

// Helper to reset pinia at start of each fast-check iteration
// This is needed because beforeEach only runs once per test definition,
// not per fast-check iteration
const resetPinia = () => {
  setActivePinia(createPinia());
};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                // test // data // generators
// ════════════════════════════════════════════════════════════════════════════

/**
 * Generate a valid AnimatableProperty
 */
const arbitraryAnimatableProperty = <T>(valueArb: fc.Arbitrary<T>): fc.Arbitrary<AnimatableProperty<T>> =>
  fc.record({
    id: fc.uuid(),
    name: fc.string({ minLength: 1, maxLength: 20 }),
    type: fc.constantFrom('number', 'position', 'color', 'vector3', 'enum') as fc.Arbitrary<"number" | "position" | "color" | "vector3" | "enum">,
    value: valueArb,
    animated: fc.boolean(),
    keyframes: fc.array(
      fc.record({
        id: fc.uuid(),
        frame: fc.integer({ min: 0, max: 1000 }),
        value: valueArb,
        interpolation: fc.constantFrom('linear', 'bezier', 'hold') as fc.Arbitrary<"linear" | "bezier" | "hold">,
        inHandle: fc.record({
          frame: fc.double({ min: -10, max: 0, noNaN: true }),
          value: fc.double({ min: -100, max: 100, noNaN: true }),
          enabled: fc.boolean(),
        }),
        outHandle: fc.record({
          frame: fc.double({ min: 0, max: 10, noNaN: true }),
          value: fc.double({ min: -100, max: 100, noNaN: true }),
          enabled: fc.boolean(),
        }),
        controlMode: fc.constantFrom('smooth', 'corner', 'auto') as fc.Arbitrary<"smooth" | "corner" | "auto">,
      }),
      { maxLength: 10 }
    ),
  }) as fc.Arbitrary<AnimatableProperty<T>>;

/**
 * Generate a minimal valid layer
 */
const arbitraryLayer = (): fc.Arbitrary<Layer> =>
  fc.record({
    id: fc.uuid(),
    name: fc.string({ minLength: 1, maxLength: 50 }),
    type: fc.constantFrom('solid', 'text', 'image', 'video', 'shape', 'control', 'camera', 'light'),
    visible: fc.boolean(),
    locked: fc.boolean(),
    isolate: fc.boolean(),
    motionBlur: fc.boolean(),
    blendMode: fc.constantFrom('normal', 'multiply', 'screen', 'overlay'),
    threeD: fc.boolean(),
    parentId: fc.option(fc.uuid(), { nil: undefined }),
    opacity: arbitraryAnimatableProperty(fc.integer({ min: 0, max: 100 })),
    transform: arbitraryAnimatableProperty(
      fc.record({
        x: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
        y: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
        z: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
      })
    ).chain(origin => fc.record({
      position: arbitraryAnimatableProperty(
        fc.record({
          x: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
          y: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
          z: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
        })
      ),
      scale: arbitraryAnimatableProperty(
        fc.record({
          x: fc.double({ min: 0.1, max: 500, noNaN: true, noDefaultInfinity: true }),
          y: fc.double({ min: 0.1, max: 500, noNaN: true, noDefaultInfinity: true }),
          z: fc.double({ min: 0.1, max: 500, noNaN: true, noDefaultInfinity: true }),
        })
      ),
      rotation: arbitraryAnimatableProperty(fc.double({ min: -360, max: 360, noNaN: true, noDefaultInfinity: true })),
      origin: fc.constant(origin),
      anchorPoint: fc.constant(origin),
    })),
    effects: fc.constant([]),
    properties: fc.constant([]),
    masks: fc.constant([]),
    startFrame: fc.integer({ min: 0, max: 100 }),
    endFrame: fc.integer({ min: 100, max: 500 }),
    data: fc.constant(null),
  }) as fc.Arbitrary<Layer>;

/**
 * Generate a minimal valid composition
 */
const arbitraryComposition = (): fc.Arbitrary<Composition> =>
  fc.record({
    id: fc.uuid(),
    name: fc.string({ minLength: 1, maxLength: 50 }),
    settings: fc.record({
      width: fc.integer({ min: 100, max: 4096 }),
      height: fc.integer({ min: 100, max: 4096 }),
      frameCount: fc.integer({ min: 10, max: 1000 }),
      fps: fc.constantFrom(16, 24, 30, 60),
      duration: fc.double({ min: 1, max: 60, noNaN: true }),
      backgroundColor: fc.constantFrom('#000000', '#ffffff', '#ff0000', '#00ff00', '#0000ff'),
      autoResizeToContent: fc.boolean(),
      frameBlendingEnabled: fc.boolean(),
    }),
    layers: fc.array(arbitraryLayer(), { minLength: 0, maxLength: 10 }),
    currentFrame: fc.integer({ min: 0, max: 100 }),
    isNestedComp: fc.boolean(),
  }) as fc.Arbitrary<Composition>;

/**
 * Generate a minimal valid project
 */
const arbitraryProject = (): fc.Arbitrary<LatticeProject> =>
  fc.record({
    version: fc.constant('1.0.0'),
    schemaVersion: fc.constant(1),
    mainCompositionId: fc.uuid(),
    meta: fc.record({
      name: fc.string({ minLength: 1, maxLength: 50 }),
      //                                                                // bug // fix
      // Range: Jan 1, 2000 to Jan 1, 2030 (safe epoch values)
      created: fc.integer({ min: 946684800000, max: 1893456000000 }).map(ts => new Date(ts).toISOString()),
      modified: fc.integer({ min: 946684800000, max: 1893456000000 }).map(ts => new Date(ts).toISOString()),
    }),
    composition: fc.record({
      width: fc.integer({ min: 100, max: 4096 }),
      height: fc.integer({ min: 100, max: 4096 }),
      frameCount: fc.integer({ min: 10, max: 1000 }),
      fps: fc.constantFrom(16, 24, 30, 60),
      duration: fc.double({ min: 1, max: 60, noNaN: true }),
      backgroundColor: fc.constantFrom('#000000', '#ffffff', '#ff0000', '#00ff00', '#0000ff'),
      autoResizeToContent: fc.boolean(),
      frameBlendingEnabled: fc.boolean(),
    }),
    compositions: fc.dictionary(fc.uuid(), arbitraryComposition()),
    layers: fc.array(arbitraryLayer(), { minLength: 0, maxLength: 5 }),
    currentFrame: fc.integer({ min: 0, max: 100 }),
    assets: fc.constant({}),
    audioMappings: fc.constant([]),
  }) as fc.Arbitrary<LatticeProject>;

// ════════════════════════════════════════════════════════════════════════════
//                                              // strict // invariant // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRICT: Undo/Redo Invariants', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  describe('Fundamental Invariants', () => {
    test.prop([arbitraryProject()])('undo(push(state)) returns original state', (project) => {
      resetPinia();
      const history = useHistoryStore();
      
      // Initialize with project
      history.initialize(project);
      
      // Create a modified version
      const modified = JSON.parse(JSON.stringify(project)) as LatticeProject;
      modified.meta.name = 'Modified Project';
      
      // Push modified
      history.push(modified);
      
      // Undo should return original
      const undone = history.undo();
      expect(undone).not.toBeNull();
      
      // Deep equality check
      expect(JSON.stringify(undone)).toBe(JSON.stringify(project));
    });

    test.prop([arbitraryProject()])('redo(undo(state)) returns the same state', (project) => {
      resetPinia();
      const history = useHistoryStore();
      
      // Initialize and push changes
      history.initialize(project);
      
      const modified = JSON.parse(JSON.stringify(project)) as LatticeProject;
      modified.meta.name = 'Modified';
      history.push(modified);
      
      // Undo then redo
      history.undo();
      const redone = history.redo();
      
      expect(redone).not.toBeNull();
      expect(JSON.stringify(redone)).toBe(JSON.stringify(modified));
    });

    test.prop([
      arbitraryProject(),
      fc.integer({ min: 1, max: 10 })
    ])('multiple undo/redo cycles are reversible', (project, cycles) => {
      resetPinia();
      const history = useHistoryStore();
      history.initialize(project);
      
      // Create a chain of modifications
      const versions: LatticeProject[] = [project];
      for (let i = 0; i < cycles; i++) {
        const modified = JSON.parse(JSON.stringify(versions[versions.length - 1])) as LatticeProject;
        modified.meta.name = `Version ${i + 1}`;
        modified.meta.modified = new Date(Date.now() + i * 1000).toISOString();
        history.push(modified);
        versions.push(modified);
      }
      
      // Undo all
      for (let i = 0; i < cycles; i++) {
        const undone = history.undo();
        expect(undone).not.toBeNull();
        expect(JSON.stringify(undone)).toBe(JSON.stringify(versions[cycles - i - 1]));
      }
      
      // Should be back at original
      expect(history.canUndo).toBe(false);
      
      // Redo all
      for (let i = 0; i < cycles; i++) {
        const redone = history.redo();
        expect(redone).not.toBeNull();
        expect(JSON.stringify(redone)).toBe(JSON.stringify(versions[i + 1]));
      }
      
      // Should be at latest
      expect(history.canRedo).toBe(false);
    });
  });

  describe('Branch Trimming', () => {
    test.prop([arbitraryProject()])('push after undo trims future history', (project) => {
      resetPinia();
      const history = useHistoryStore();
      history.initialize(project);
      
      // Push three states
      const v1 = { ...JSON.parse(JSON.stringify(project)), meta: { ...project.meta, name: 'V1' } };
      const v2 = { ...JSON.parse(JSON.stringify(project)), meta: { ...project.meta, name: 'V2' } };
      const v3 = { ...JSON.parse(JSON.stringify(project)), meta: { ...project.meta, name: 'V3' } };
      
      history.push(v1);
      history.push(v2);
      history.push(v3);
      
      // Undo twice (back to v1)
      history.undo();
      history.undo();
      
      // Push new state (should trim v2, v3)
      const v1b = { ...JSON.parse(JSON.stringify(project)), meta: { ...project.meta, name: 'V1-Branch' } };
      history.push(v1b);
      
      // Redo should not be possible (v2, v3 are gone)
      expect(history.canRedo).toBe(false);
      
      // Stack should be: [original, v1, v1b]
      expect(history.stackSize).toBe(3);
    });
  });

  describe('Deep Cloning (Reference Isolation)', () => {
    test.prop([arbitraryProject()])('pushed state is isolated from original', (project) => {
      resetPinia();
      const history = useHistoryStore();
      history.initialize(project);
      
      const modified = JSON.parse(JSON.stringify(project)) as LatticeProject;
      history.push(modified);
      
      // Mutate the original object after pushing
      modified.meta.name = 'MUTATED AFTER PUSH';
      
      // Redo should return the state as it was when pushed
      history.undo();
      const redone = history.redo();
      
      expect(redone).not.toBeNull();
      expect(redone!.meta.name).not.toBe('MUTATED AFTER PUSH');
    });

    test.prop([arbitraryProject()])('undone state is isolated from stack', (project) => {
      resetPinia();
      const history = useHistoryStore();
      history.initialize(project);
      
      const modified = JSON.parse(JSON.stringify(project)) as LatticeProject;
      modified.meta.name = 'Original Modified';
      history.push(modified);
      
      // Get state via undo
      const undone = history.undo();
      
      // Mutate the returned state
      undone!.meta.name = 'MUTATED UNDONE STATE';
      
      // Redo and undo again should return original value
      history.redo();
      const undoneAgain = history.undo();
      
      expect(undoneAgain).not.toBeNull();
      expect(undoneAgain!.meta.name).toBe(project.meta.name);
    });
  });

  describe('Memory Limits', () => {
    test.prop([
      arbitraryProject(),
      fc.integer({ min: 1, max: 10 })
    ])('respects maxSize limit', (project, maxSize) => {
      resetPinia();
      const history = useHistoryStore();
      history.setMaxSize(maxSize);
      history.initialize(project);
      
      // Push more than maxSize states
      const totalPushes = maxSize + 5;
      for (let i = 0; i < totalPushes; i++) {
        const modified = JSON.parse(JSON.stringify(project)) as LatticeProject;
        modified.meta.name = `State ${i}`;
        history.push(modified);
      }
      
      // Stack should not exceed maxSize
      expect(history.stackSize).toBeLessThanOrEqual(maxSize);
    });

    test.prop([arbitraryProject()])('setMaxSize trims existing history', (project) => {
      resetPinia();
      const history = useHistoryStore();
      history.initialize(project);
      
      // Push 10 states
      for (let i = 0; i < 10; i++) {
        const modified = JSON.parse(JSON.stringify(project)) as LatticeProject;
        modified.meta.name = `State ${i}`;
        history.push(modified);
      }
      
      const sizeBefore = history.stackSize;
      expect(sizeBefore).toBe(11); // initial + 10 pushes
      
      // Reduce max size
      history.setMaxSize(5);
      
      // Stack should be trimmed
      expect(history.stackSize).toBeLessThanOrEqual(5);
    });
  });

  describe('Edge Cases', () => {
    test.prop([arbitraryProject()])('undo at beginning returns null', (project) => {
      resetPinia();
      const history = useHistoryStore();
      history.initialize(project);
      
      // Already at beginning
      expect(history.canUndo).toBe(false);
      expect(history.undo()).toBeNull();
    });

    test.prop([arbitraryProject()])('redo at end returns null', (project) => {
      resetPinia();
      const history = useHistoryStore();
      history.initialize(project);
      
      // Already at end
      expect(history.canRedo).toBe(false);
      expect(history.redo()).toBeNull();
    });

    test.prop([arbitraryProject()])('clear resets state completely', (project) => {
      resetPinia();
      const history = useHistoryStore();
      history.initialize(project);
      
      // Push some states
      for (let i = 0; i < 5; i++) {
        const modified = JSON.parse(JSON.stringify(project)) as LatticeProject;
        history.push(modified);
      }
      
      // Clear
      history.clear();
      
      expect(history.stackSize).toBe(0);
      expect(history.currentIndex).toBe(-1);
      expect(history.canUndo).toBe(false);
      expect(history.canRedo).toBe(false);
    });

    test.prop([arbitraryProject()])('initialize clears existing history', (project) => {
      resetPinia();
      const history = useHistoryStore();
      
      // Set up some history
      history.initialize(project);
      for (let i = 0; i < 5; i++) {
        const modified = JSON.parse(JSON.stringify(project)) as LatticeProject;
        history.push(modified);
      }
      
      // Re-initialize with new project
      const newProject = JSON.parse(JSON.stringify(project)) as LatticeProject;
      newProject.meta.name = 'New Project';
      history.initialize(newProject);
      
      // Should have only the new project
      expect(history.stackSize).toBe(1);
      expect(history.currentIndex).toBe(0);
      expect(history.canUndo).toBe(false);
      expect(history.canRedo).toBe(false);
    });
  });

  describe('State Integrity', () => {
    test.prop([
      fc.array(arbitraryProject(), { minLength: 2, maxLength: 5 })
    ])('all states in history are distinct objects', (projects) => {
      resetPinia();
      const history = useHistoryStore();
      history.initialize(projects[0]);
      
      for (let i = 1; i < projects.length; i++) {
        history.push(projects[i]);
      }
      
      // Navigate through history and collect all returned states
      const retrievedStates: LatticeProject[] = [];
      
      // Go to beginning
      while (history.canUndo) {
        const state = history.undo();
        if (state) retrievedStates.push(state);
      }
      
      // Go to end
      while (history.canRedo) {
        const state = history.redo();
        if (state) retrievedStates.push(state);
      }
      
      // All retrieved states should be distinct objects (no reference sharing)
      for (let i = 0; i < retrievedStates.length; i++) {
        for (let j = i + 1; j < retrievedStates.length; j++) {
          // Objects may be deeply equal but should not be the same reference
          expect(retrievedStates[i]).not.toBe(retrievedStates[j]);
        }
      }
    });
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                           // stress // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRESS: Undo/Redo Under Load', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  test.prop([
    arbitraryProject(),
    fc.array(fc.constantFrom('push', 'undo', 'redo'), { minLength: 10, maxLength: 50 })
  ])('random operation sequence maintains consistency', (project, operations) => {
    resetPinia();
    const history = useHistoryStore();
    history.initialize(project);
    
    let currentVersion = project;
    let versionCounter = 0;
    
    for (const op of operations) {
      switch (op) {
        case 'push': {
          const modified = JSON.parse(JSON.stringify(currentVersion)) as LatticeProject;
          modified.meta.name = `Version ${++versionCounter}`;
          modified.meta.modified = new Date().toISOString();
          history.push(modified);
          currentVersion = modified;
          break;
        }
        case 'undo': {
          if (history.canUndo) {
            const undone = history.undo();
            if (undone) currentVersion = undone;
          }
          break;
        }
        case 'redo': {
          if (history.canRedo) {
            const redone = history.redo();
            if (redone) currentVersion = redone;
          }
          break;
        }
      }
      
      // Invariant: stack size should always be positive after init
      expect(history.stackSize).toBeGreaterThan(0);
      
      // Invariant: index should be within bounds
      expect(history.currentIndex).toBeGreaterThanOrEqual(0);
      expect(history.currentIndex).toBeLessThan(history.stackSize);
    }
  });
});
