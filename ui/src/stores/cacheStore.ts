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
  state: () => ({}),

  getters: {},

  actions: {
    /**
     * Initialize the frame cache
     * Should be called on app startup
     */
    async initializeCache(store: CacheStoreAccess): Promise<void> {
      if (store.frameCacheEnabled) {
        await initializeFrameCache();
        storeLogger.info("Frame cache initialized");
      }
    },

    /**
     * Enable or disable frame caching
     */
    setFrameCacheEnabled(store: CacheStoreAccess, enabled: boolean): void {
      store.frameCacheEnabled = enabled;
      if (!enabled) {
        this.clearFrameCache();
      }
      storeLogger.info("Frame cache", enabled ? "enabled" : "disabled");
    },

    /**
     * Get frame from cache or null if not cached
     */
    getCachedFrame(store: CacheStoreAccess, frame: number): ImageData | null {
      if (!store.frameCacheEnabled) return null;

      const cache = getFrameCache();
      return cache.get(frame, store.activeCompositionId, store.projectStateHash);
    },

    /**
     * Cache a rendered frame
     */
    async cacheFrame(
      store: CacheStoreAccess,
      frame: number,
      imageData: ImageData,
    ): Promise<void> {
      if (!store.frameCacheEnabled) return;

      const cache = getFrameCache();
      await cache.set(
        frame,
        store.activeCompositionId,
        imageData,
        store.projectStateHash,
      );
    },

    /**
     * Check if a frame is cached
     */
    isFrameCached(store: CacheStoreAccess, frame: number): boolean {
      if (!store.frameCacheEnabled) return false;

      const cache = getFrameCache();
      return cache.has(frame, store.activeCompositionId);
    },

    /**
     * Start pre-caching frames around current position
     */
    async startPreCache(
      store: CacheStoreAccess,
      currentFrame: number,
      direction: "forward" | "backward" | "both" = "both",
    ): Promise<void> {
      if (!store.frameCacheEnabled) return;

      const cache = getFrameCache();
      await cache.startPreCache(
        currentFrame,
        store.activeCompositionId,
        store.projectStateHash,
        direction,
      );
    },

    /**
     * Invalidate frame cache (called when project changes)
     */
    invalidateFrameCache(store: CacheStoreAccess): void {
      // Update project state hash
      store.projectStateHash = this.computeProjectHash(store);

      // Clear cache for current composition
      const cache = getFrameCache();
      cache.invalidate(store.activeCompositionId, store.projectStateHash);
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

    /**
     * Compute a hash of the project state for cache invalidation
     * Uses a simplified hash of key state that affects rendering
     */
    computeProjectHash(store: CacheStoreAccess): string {
      const comp = store.project.compositions[store.activeCompositionId];
      if (!comp) return "";

      // Create a simplified fingerprint of the composition state
      const fingerprint = {
        layerCount: comp.layers?.length ?? 0,
        layerIds: comp.layers?.map((l) => l.id).join(",") ?? "",
        modified: store.project.meta.modified,
        settings: comp.settings,
      };

      // Simple hash function (with fallback for circular refs)
      let str: string;
      try {
        str = JSON.stringify(fingerprint);
      } catch {
        // Fallback if settings contains circular references
        str = `${fingerprint.layerCount}:${fingerprint.layerIds}:${fingerprint.modified}`;
      }
      let hash = 0;
      for (let i = 0; i < str.length; i++) {
        const char = str.charCodeAt(i);
        hash = (hash << 5) - hash + char;
        hash = hash & hash; // Convert to 32-bit integer
      }
      return hash.toString(16);
    },
  },
});
