/**
 * History Store
 *
 * Manages undo/redo history for project state.
 * This is a focused store extracted from compositorStore for better maintainability.
 */
import { defineStore } from "pinia";
import { toRaw } from "vue";
import type { LatticeProject } from "@/types/project";
import { storeLogger } from "@/utils/logger";

interface HistoryState {
  stack: LatticeProject[];
  index: number;
  maxSize: number;
}

export const useHistoryStore = defineStore("history", {
  state: (): HistoryState => ({
    stack: [],
    index: -1,
    maxSize: 50, // Maximum history entries
  }),

  getters: {
    canUndo: (state) => state.index > 0,
    canRedo: (state) => state.index < state.stack.length - 1,
    currentIndex: (state) => state.index,
    stackSize: (state) => state.stack.length,
  },

  actions: {
    /**
     * Push a new state to history
     * This should be called after significant changes to the project
     */
    push(project: LatticeProject): void {
      // Remove any future states if we're not at the end
      if (this.index < this.stack.length - 1) {
        this.stack = this.stack.slice(0, this.index + 1);
      }

      // Deep clone the project to avoid reference issues
      // Use toRaw() to deproxy Vue reactive objects before cloning
      const snapshot = structuredClone(toRaw(project)) as LatticeProject;
      this.stack.push(snapshot);

      // Trim history if it exceeds max size
      if (this.stack.length > this.maxSize) {
        this.stack.shift();
      } else {
        this.index++;
      }

      storeLogger.debug(
        "History pushed, index:",
        this.index,
        "size:",
        this.stack.length,
      );
    },

    /**
     * Get the previous state (for undo)
     * Returns null if we can't undo
     */
    undo(): LatticeProject {
      if (!this.canUndo) {
        throw new Error("[HistoryStore] Cannot undo: at beginning of history");
      }

      this.index--;
      const state = this.stack[this.index];
      storeLogger.debug("Undo to index:", this.index);
      // Use toRaw to deproxy Pinia's reactive wrapper before cloning
      return structuredClone(toRaw(state)) as LatticeProject;
    },

    /**
     * Get the next state (for redo)
     * Returns null if we can't redo
     */
    redo(): LatticeProject {
      if (!this.canRedo) {
        throw new Error("[HistoryStore] Cannot redo: at end of history");
      }

      this.index++;
      const state = this.stack[this.index];
      storeLogger.debug("Redo to index:", this.index);
      // Use toRaw to deproxy Pinia's reactive wrapper before cloning
      return structuredClone(toRaw(state)) as LatticeProject;
    },

    /**
     * Clear all history
     */
    clear(): void {
      this.stack = [];
      this.index = -1;
      storeLogger.debug("History cleared");
    },

    /**
     * Initialize history with a starting state
     */
    initialize(project: LatticeProject): void {
      this.clear();
      this.push(project);
    },

    /**
     * Set maximum history size
     */
    setMaxSize(size: number): void {
      this.maxSize = Math.max(1, size);
      // Trim if needed
      while (this.stack.length > this.maxSize) {
        this.stack.shift();
        this.index = Math.max(0, this.index - 1);
      }
    },
  },
});

export type HistoryStore = ReturnType<typeof useHistoryStore>;
