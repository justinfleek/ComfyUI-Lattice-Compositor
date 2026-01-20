/**
 * Cache Store
 *
 * Domain store for frame cache management.
 * Handles rendered frame storage and invalidation.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { defineStore } from "pinia";
import {
  type CacheStats,
  getFrameCache,
  initializeFrameCache,
} from "@/services/frameCache";
import { storeLogger } from "@/utils/logger";
import { useProjectStore } from "./projectStore";

// ============================================================================
// STORE ACCESS INTERFACE
// ============================================================================

export interface CacheStoreAccess {
  frameCacheEnabled: boolean;
  projectStateHash: string;
  activeCompositionId: string;
  project: {
    meta: { modified: string };
    compositions: Record<
      string,
      {
        layers: { id: string }[];
        settings: object;
      }
    >;
  };
}

// ============================================================================
// PINIA STORE
// ============================================================================

export const useCacheStore = defineStore("cache", {
  state: () => ({
    frameCacheEnabled: true,
    projectStateHash: "",
  }),

  getters: {},

  actions: {
    async initializeCache(): Promise<void> {
      if (this.frameCacheEnabled) {
        await initializeFrameCache();
        storeLogger.info("Frame cache initialized");
      }
    },

    setFrameCacheEnabled(enabled: boolean): void {
      this.frameCacheEnabled = enabled;
      if (!enabled) {
        this.clearFrameCache();
      }
      storeLogger.info("Frame cache", enabled ? "enabled" : "disabled");
    },

    getCachedFrame(frame: number): ImageData | null {
      if (!this.frameCacheEnabled) return null;

      const projectStore = useProjectStore();
      const cache = getFrameCache();
      return cache.get(frame, projectStore.activeCompositionId, this.projectStateHash);
    },

    async cacheFrame(frame: number, imageData: ImageData): Promise<void> {
      if (!this.frameCacheEnabled) return;

      const projectStore = useProjectStore();
      const cache = getFrameCache();
      await cache.set(
        frame,
        projectStore.activeCompositionId,
        imageData,
        this.projectStateHash,
      );
    },

    isFrameCached(frame: number): boolean {
      if (!this.frameCacheEnabled) return false;

      const projectStore = useProjectStore();
      const cache = getFrameCache();
      return cache.has(frame, projectStore.activeCompositionId);
    },

    async startPreCache(
      currentFrame: number,
      direction: "forward" | "backward" | "both" = "both",
    ): Promise<void> {
      if (!this.frameCacheEnabled) return;

      const projectStore = useProjectStore();
      const cache = getFrameCache();
      await cache.startPreCache(
        currentFrame,
        projectStore.activeCompositionId,
        this.projectStateHash,
        direction,
      );
    },

    invalidateFrameCache(): void {
      this.projectStateHash = this.computeProjectHash();

      const projectStore = useProjectStore();
      const cache = getFrameCache();
      cache.invalidate(projectStore.activeCompositionId, this.projectStateHash);
    },

    /**
     * Clear all cached frames
     */
    clearFrameCache(): void {
      const cache = getFrameCache();
      cache.clear();
      storeLogger.info("Frame cache cleared");
    },

    /**
     * Get frame cache statistics
     */
    getFrameCacheStats(): CacheStats {
      const cache = getFrameCache();
      return cache.getStats();
    },

    computeProjectHash(): string {
      const projectStore = useProjectStore();
      const comp = projectStore.project.compositions[projectStore.activeCompositionId];
      if (!comp) return "";

      const fingerprint = {
        layerCount: comp.layers?.length ?? 0,
        layerIds: comp.layers?.map((l) => l.id).join(",") ?? "",
        modified: projectStore.project.meta.modified,
        settings: comp.settings,
      };

      let str: string;
      try {
        str = JSON.stringify(fingerprint);
      } catch {
        str = `${fingerprint.layerCount}:${fingerprint.layerIds}:${fingerprint.modified}`;
      }
      let hash = 0;
      for (let i = 0; i < str.length; i++) {
        const char = str.charCodeAt(i);
        hash = (hash << 5) - hash + char;
        hash = hash & hash;
      }
      return hash.toString(16);
    },
  },
});
