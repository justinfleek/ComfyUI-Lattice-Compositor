/**
 * Cache Actions
 *
 * Frame cache management for rendered frame storage.
 * Extracted from compositorStore for better maintainability.
 */

import {
  type CacheStats,
  getFrameCache,
  initializeFrameCache,
} from "@/services/frameCache";
import { storeLogger } from "@/utils/logger";

export interface CacheStore {
  // State
  frameCacheEnabled: boolean;
  projectStateHash: string;
  activeCompositionId: string;

  // Methods the store must provide
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

/**
 * Initialize the frame cache
 * Should be called on app startup
 */
export async function initializeCache(store: CacheStore): Promise<void> {
  if (store.frameCacheEnabled) {
    await initializeFrameCache();
    storeLogger.info("Frame cache initialized");
  }
}

/**
 * Enable or disable frame caching
 */
export function setFrameCacheEnabled(
  store: CacheStore,
  enabled: boolean,
): void {
  store.frameCacheEnabled = enabled;
  if (!enabled) {
    clearFrameCache();
  }
  storeLogger.info("Frame cache", enabled ? "enabled" : "disabled");
}

/**
 * Get frame from cache or null if not cached
 */
export function getCachedFrame(
  store: CacheStore,
  frame: number,
): ImageData | null {
  if (!store.frameCacheEnabled) return null;

  const cache = getFrameCache();
  return cache.get(frame, store.activeCompositionId, store.projectStateHash);
}

/**
 * Cache a rendered frame
 */
export async function cacheFrame(
  store: CacheStore,
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
}

/**
 * Check if a frame is cached
 */
export function isFrameCached(store: CacheStore, frame: number): boolean {
  if (!store.frameCacheEnabled) return false;

  const cache = getFrameCache();
  return cache.has(frame, store.activeCompositionId);
}

/**
 * Start pre-caching frames around current position
 */
export async function startPreCache(
  store: CacheStore,
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
}

/**
 * Invalidate frame cache (called when project changes)
 */
export function invalidateFrameCache(store: CacheStore): void {
  // Update project state hash
  store.projectStateHash = computeProjectHash(store);

  // Clear cache for current composition
  const cache = getFrameCache();
  cache.invalidate(store.activeCompositionId, store.projectStateHash);
}

/**
 * Clear all cached frames
 */
export function clearFrameCache(): void {
  const cache = getFrameCache();
  cache.clear();
  storeLogger.info("Frame cache cleared");
}

/**
 * Get frame cache statistics
 */
export function getFrameCacheStats(): CacheStats {
  const cache = getFrameCache();
  return cache.getStats();
}

/**
 * Compute a hash of the project state for cache invalidation
 * Uses a simplified hash of key state that affects rendering
 */
export function computeProjectHash(store: CacheStore): string {
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
}
