/**
 * History Store Tests
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { setActivePinia, createPinia } from 'pinia';
import { useHistoryStore } from '@/stores/historyStore';
import type { WeylProject } from '@/types/project';

// Helper to create mock project
function createMockProject(name: string): WeylProject {
  return {
    version: '1.0.0',
    meta: {
      name,
      created: new Date().toISOString(),
      modified: new Date().toISOString(),
    },
    composition: {
      width: 1920,
      height: 1080,
      frameCount: 100,
      fps: 30,
      duration: 100 / 30,
      backgroundColor: '#000000',
      autoResizeToContent: false,
    },
    compositions: {},
    mainCompositionId: 'main',
    assets: {},
    layers: [],
    currentFrame: 0,
  };
}

describe('HistoryStore', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
  });

  describe('initial state', () => {
    it('should start with empty history', () => {
      const store = useHistoryStore();
      expect(store.stack).toEqual([]);
      expect(store.index).toBe(-1);
    });

    it('should not allow undo or redo initially', () => {
      const store = useHistoryStore();
      expect(store.canUndo).toBe(false);
      expect(store.canRedo).toBe(false);
    });
  });

  describe('push', () => {
    it('should add project to history', () => {
      const store = useHistoryStore();
      const project = createMockProject('Test 1');

      store.push(project);

      expect(store.stackSize).toBe(1);
      expect(store.currentIndex).toBe(0);
    });

    it('should deep clone project', () => {
      const store = useHistoryStore();
      const project = createMockProject('Test 1');

      store.push(project);
      project.meta.name = 'Modified';

      expect(store.stack[0].meta.name).toBe('Test 1');
    });

    it('should increment index with each push', () => {
      const store = useHistoryStore();

      store.push(createMockProject('Test 1'));
      store.push(createMockProject('Test 2'));
      store.push(createMockProject('Test 3'));

      expect(store.currentIndex).toBe(2);
      expect(store.stackSize).toBe(3);
    });

    it('should trim future states when pushing after undo', () => {
      const store = useHistoryStore();

      store.push(createMockProject('Test 1'));
      store.push(createMockProject('Test 2'));
      store.push(createMockProject('Test 3'));
      store.undo();
      store.undo();

      store.push(createMockProject('Test 4'));

      expect(store.stackSize).toBe(2);
      expect(store.stack[1].meta.name).toBe('Test 4');
    });

    it('should respect max size', () => {
      const store = useHistoryStore();
      store.setMaxSize(3);

      store.push(createMockProject('Test 1'));
      store.push(createMockProject('Test 2'));
      store.push(createMockProject('Test 3'));
      store.push(createMockProject('Test 4'));

      expect(store.stackSize).toBe(3);
      expect(store.stack[0].meta.name).toBe('Test 2');
    });
  });

  describe('undo', () => {
    it('should return null when no history', () => {
      const store = useHistoryStore();
      expect(store.undo()).toBeNull();
    });

    it('should return null at beginning of history', () => {
      const store = useHistoryStore();
      store.push(createMockProject('Test 1'));
      expect(store.undo()).toBeNull();
    });

    it('should return previous state', () => {
      const store = useHistoryStore();
      store.push(createMockProject('Test 1'));
      store.push(createMockProject('Test 2'));

      const result = store.undo();

      expect(result?.meta.name).toBe('Test 1');
      expect(store.currentIndex).toBe(0);
    });

    it('should enable redo after undo', () => {
      const store = useHistoryStore();
      store.push(createMockProject('Test 1'));
      store.push(createMockProject('Test 2'));

      expect(store.canRedo).toBe(false);
      store.undo();
      expect(store.canRedo).toBe(true);
    });
  });

  describe('redo', () => {
    it('should return null when no redo available', () => {
      const store = useHistoryStore();
      store.push(createMockProject('Test 1'));
      expect(store.redo()).toBeNull();
    });

    it('should return next state after undo', () => {
      const store = useHistoryStore();
      store.push(createMockProject('Test 1'));
      store.push(createMockProject('Test 2'));
      store.undo();

      const result = store.redo();

      expect(result?.meta.name).toBe('Test 2');
      expect(store.currentIndex).toBe(1);
    });
  });

  describe('clear', () => {
    it('should reset history', () => {
      const store = useHistoryStore();
      store.push(createMockProject('Test 1'));
      store.push(createMockProject('Test 2'));

      store.clear();

      expect(store.stack).toEqual([]);
      expect(store.index).toBe(-1);
      expect(store.canUndo).toBe(false);
      expect(store.canRedo).toBe(false);
    });
  });

  describe('initialize', () => {
    it('should clear history and add initial state', () => {
      const store = useHistoryStore();
      store.push(createMockProject('Old'));

      store.initialize(createMockProject('New'));

      expect(store.stackSize).toBe(1);
      expect(store.stack[0].meta.name).toBe('New');
      expect(store.currentIndex).toBe(0);
    });
  });

  describe('setMaxSize', () => {
    it('should update max size', () => {
      const store = useHistoryStore();
      store.setMaxSize(10);
      expect(store.maxSize).toBe(10);
    });

    it('should not allow size less than 1', () => {
      const store = useHistoryStore();
      store.setMaxSize(0);
      expect(store.maxSize).toBe(1);

      store.setMaxSize(-5);
      expect(store.maxSize).toBe(1);
    });

    it('should trim existing history if needed', () => {
      const store = useHistoryStore();
      store.push(createMockProject('Test 1'));
      store.push(createMockProject('Test 2'));
      store.push(createMockProject('Test 3'));
      store.push(createMockProject('Test 4'));
      store.push(createMockProject('Test 5'));

      store.setMaxSize(2);

      expect(store.stackSize).toBe(2);
    });
  });

  describe('getters', () => {
    it('canUndo should be true when history exists', () => {
      const store = useHistoryStore();
      store.push(createMockProject('Test 1'));
      expect(store.canUndo).toBe(false);

      store.push(createMockProject('Test 2'));
      expect(store.canUndo).toBe(true);
    });

    it('canRedo should be true after undo', () => {
      const store = useHistoryStore();
      store.push(createMockProject('Test 1'));
      store.push(createMockProject('Test 2'));

      expect(store.canRedo).toBe(false);

      store.undo();
      expect(store.canRedo).toBe(true);

      store.redo();
      expect(store.canRedo).toBe(false);
    });
  });
});
