/**
 * Frame Cache Service
 *
 * Implements intelligent frame caching for smooth timeline scrubbing.
 * Uses an LRU (Least Recently Used) eviction strategy with configurable
 * memory limits based on GPU tier.
 *
 * Features:
 * - LRU eviction with configurable max entries
 * - Memory-aware caching (auto-adjusts based on GPU tier)
 * - Predictive pre-caching for timeline scrubbing
 * - Compression support for reduced memory footprint
 * - Cache invalidation on composition changes
 */

import { detectGPUTier, type GPUTier } from './gpuDetection';

// ============================================================================
// TYPES
// ============================================================================

export interface CachedFrame {
  /** Frame number */
  frame: number;
  /** Composition ID (for multi-comp support) */
  compositionId: string;
  /** Cached ImageData or compressed blob */
  data: ImageData | Blob;
  /** Whether data is compressed */
  compressed: boolean;
  /** Original dimensions */
  width: number;
  height: number;
  /** Cache timestamp for LRU */
  timestamp: number;
  /** Approximate memory size in bytes */
  size: number;
  /** Hash of composition state when cached (for invalidation) */
  stateHash: string;
}

export interface FrameCacheConfig {
  /** Maximum number of frames to cache */
  maxFrames: number;
  /** Maximum memory usage in bytes */
  maxMemoryBytes: number;
  /** Enable compression for cached frames */
  compression: boolean;
  /** Compression quality (0-1) for lossy compression */
  compressionQuality: number;
  /** Pre-cache window (frames ahead/behind) */
  preCacheWindow: number;
  /** Enable predictive pre-caching */
  predictivePreCache: boolean;
}

export interface CacheStats {
  /** Number of cached frames */
  cachedFrames: number;
  /** Total memory used in bytes */
  memoryUsed: number;
  /** Cache hit ratio (0-1) */
  hitRatio: number;
  /** Total cache hits */
  hits: number;
  /** Total cache misses */
  misses: number;
}

// ============================================================================
// DEFAULT CONFIGURATIONS BY GPU TIER
// ============================================================================

const TIER_CONFIGS: Record<GPUTier['tier'], Partial<FrameCacheConfig>> = {
  blackwell: {
    maxFrames: 500,
    maxMemoryBytes: 4 * 1024 * 1024 * 1024, // 4GB
    compression: false, // Fast GPU, no need for compression
    preCacheWindow: 30,
  },
  webgpu: {
    maxFrames: 200,
    maxMemoryBytes: 1 * 1024 * 1024 * 1024, // 1GB
    compression: true,
    preCacheWindow: 15,
  },
  webgl: {
    maxFrames: 100,
    maxMemoryBytes: 512 * 1024 * 1024, // 512MB
    compression: true,
    preCacheWindow: 10,
  },
  cpu: {
    maxFrames: 50,
    maxMemoryBytes: 256 * 1024 * 1024, // 256MB
    compression: true,
    preCacheWindow: 5,
  },
};

const DEFAULT_CONFIG: FrameCacheConfig = {
  maxFrames: 100,
  maxMemoryBytes: 512 * 1024 * 1024,
  compression: true,
  compressionQuality: 0.92,
  preCacheWindow: 10,
  predictivePreCache: true,
};

// ============================================================================
// LRU LINKED LIST NODE
// ============================================================================

interface LRUNode {
  key: string;
  prev: LRUNode | null;
  next: LRUNode | null;
}

/**
 * O(1) LRU tracker using doubly-linked list + Map
 * - moveToEnd: O(1)
 * - remove: O(1)
 * - getOldest: O(1)
 */
class LRUTracker {
  private nodeMap: Map<string, LRUNode> = new Map();
  private head: LRUNode | null = null; // Oldest
  private tail: LRUNode | null = null; // Most recent

  add(key: string): void {
    if (this.nodeMap.has(key)) {
      this.moveToEnd(key);
      return;
    }

    const node: LRUNode = { key, prev: null, next: null };

    if (!this.tail) {
      this.head = this.tail = node;
    } else {
      node.prev = this.tail;
      this.tail.next = node;
      this.tail = node;
    }

    this.nodeMap.set(key, node);
  }

  moveToEnd(key: string): void {
    const node = this.nodeMap.get(key);
    if (!node || node === this.tail) return;

    // Remove from current position
    if (node.prev) node.prev.next = node.next;
    if (node.next) node.next.prev = node.prev;
    if (node === this.head) this.head = node.next;

    // Add to end
    node.prev = this.tail;
    node.next = null;
    if (this.tail) this.tail.next = node;
    this.tail = node;
  }

  remove(key: string): void {
    const node = this.nodeMap.get(key);
    if (!node) return;

    if (node.prev) node.prev.next = node.next;
    if (node.next) node.next.prev = node.prev;
    if (node === this.head) this.head = node.next;
    if (node === this.tail) this.tail = node.prev;

    this.nodeMap.delete(key);
  }

  getOldest(): string | null {
    return this.head?.key ?? null;
  }

  has(key: string): boolean {
    return this.nodeMap.has(key);
  }

  clear(): void {
    this.nodeMap.clear();
    this.head = null;
    this.tail = null;
  }

  get size(): number {
    return this.nodeMap.size;
  }
}

// ============================================================================
// FRAME CACHE CLASS
// ============================================================================

export class FrameCache {
  private cache: Map<string, CachedFrame> = new Map();
  private lru: LRUTracker = new LRUTracker(); // O(1) LRU tracking
  private config: FrameCacheConfig;
  private currentMemory: number = 0;
  private stats = { hits: 0, misses: 0 };

  // Pre-caching state
  private preCacheQueue: Array<{ frame: number; compositionId: string; priority: number }> = [];
  private isPreCaching: boolean = false;
  private preCacheAbort: AbortController | null = null;

  // Composition state tracking
  private stateHashCache: Map<string, string> = new Map();

  // Frame render callback (set by engine)
  private renderFrame: ((frame: number) => Promise<ImageData>) | null = null;

  constructor(config: Partial<FrameCacheConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * Initialize cache with GPU-tier-appropriate settings
   */
  async initializeForGPU(): Promise<void> {
    const tier = await detectGPUTier();
    const tierConfig = TIER_CONFIGS[tier.tier];
    this.config = { ...this.config, ...tierConfig };
  }

  /**
   * Set the frame render callback
   * This is called to render frames for pre-caching
   */
  setRenderCallback(callback: (frame: number) => Promise<ImageData>): void {
    this.renderFrame = callback;
  }

  /**
   * Generate a cache key for a frame
   */
  private getCacheKey(frame: number, compositionId: string): string {
    return `${compositionId}:${frame}`;
  }

  /**
   * Get a cached frame
   * @returns The cached frame or null if not found/invalid
   */
  get(frame: number, compositionId: string, currentStateHash?: string): ImageData | null {
    const key = this.getCacheKey(frame, compositionId);
    const cached = this.cache.get(key);

    if (!cached) {
      this.stats.misses++;
      return null;
    }

    // Check if cache is still valid (state hasn't changed)
    if (currentStateHash && cached.stateHash !== currentStateHash) {
      // State changed, invalidate this entry
      this.remove(frame, compositionId);
      this.stats.misses++;
      return null;
    }

    // Update LRU order - O(1)
    this.lru.moveToEnd(key);
    this.stats.hits++;

    // Return decompressed data if needed
    if (cached.compressed) {
      // Compressed data needs async decompression - return null for sync access
      // Caller should use getAsync for compressed frames
      return null;
    }

    return cached.data as ImageData;
  }

  /**
   * Get a cached frame (async, supports compression)
   */
  async getAsync(frame: number, compositionId: string, currentStateHash?: string): Promise<ImageData | null> {
    const key = this.getCacheKey(frame, compositionId);
    const cached = this.cache.get(key);

    if (!cached) {
      this.stats.misses++;
      return null;
    }

    // Check if cache is still valid
    if (currentStateHash && cached.stateHash !== currentStateHash) {
      this.remove(frame, compositionId);
      this.stats.misses++;
      return null;
    }

    // Update LRU order - O(1)
    this.lru.moveToEnd(key);
    this.stats.hits++;

    if (cached.compressed) {
      return this.decompressFrame(cached);
    }

    return cached.data as ImageData;
  }

  /**
   * Cache a frame
   */
  async set(
    frame: number,
    compositionId: string,
    imageData: ImageData,
    stateHash: string
  ): Promise<void> {
    const key = this.getCacheKey(frame, compositionId);

    // Remove existing entry if present
    if (this.cache.has(key)) {
      this.remove(frame, compositionId);
    }

    // Compress if enabled
    let data: ImageData | Blob = imageData;
    let compressed = false;
    let size = imageData.width * imageData.height * 4;

    if (this.config.compression) {
      const compressedData = await this.compressFrame(imageData);
      if (compressedData.size < size * 0.7) {
        // Only use compression if it saves >30%
        data = compressedData;
        compressed = true;
        size = compressedData.size;
      }
    }

    // Evict if necessary
    await this.ensureCapacity(size);

    // Add to cache
    const cachedFrame: CachedFrame = {
      frame,
      compositionId,
      data,
      compressed,
      width: imageData.width,
      height: imageData.height,
      timestamp: Date.now(),
      size,
      stateHash,
    };

    this.cache.set(key, cachedFrame);
    this.lru.add(key); // O(1) LRU tracking
    this.currentMemory += size;
  }

  /**
   * Remove a cached frame - O(1)
   */
  remove(frame: number, compositionId: string): void {
    const key = this.getCacheKey(frame, compositionId);
    const cached = this.cache.get(key);

    if (cached) {
      this.currentMemory -= cached.size;
      this.cache.delete(key);
      this.lru.remove(key); // O(1)
    }
  }

  /**
   * Check if a frame is cached
   */
  has(frame: number, compositionId: string): boolean {
    return this.cache.has(this.getCacheKey(frame, compositionId));
  }

  /**
   * Clear all cached frames for a composition
   */
  clearComposition(compositionId: string): void {
    const keysToRemove: string[] = [];

    for (const key of this.cache.keys()) {
      if (key.startsWith(`${compositionId}:`)) {
        keysToRemove.push(key);
      }
    }

    for (const key of keysToRemove) {
      const cached = this.cache.get(key);
      if (cached) {
        this.currentMemory -= cached.size;
      }
      this.cache.delete(key);
      this.lru.remove(key); // O(1) per removal
    }
  }

  /**
   * Clear all cached frames
   */
  clear(): void {
    this.cache.clear();
    this.lru.clear();
    this.currentMemory = 0;
    this.stats = { hits: 0, misses: 0 };
    this.abortPreCache();
  }

  /**
   * Invalidate cache for a composition (when state changes)
   */
  invalidate(compositionId: string, newStateHash: string): void {
    const oldHash = this.stateHashCache.get(compositionId);

    if (oldHash !== newStateHash) {
      // State changed - clear this composition's cache
      this.clearComposition(compositionId);
      this.stateHashCache.set(compositionId, newStateHash);
    }
  }

  /**
   * Start predictive pre-caching around the current frame
   */
  async startPreCache(
    currentFrame: number,
    compositionId: string,
    stateHash: string,
    direction: 'forward' | 'backward' | 'both' = 'both'
  ): Promise<void> {
    if (!this.config.predictivePreCache || !this.renderFrame) {
      return;
    }

    // Abort any existing pre-cache operation
    this.abortPreCache();

    this.preCacheAbort = new AbortController();
    const signal = this.preCacheAbort.signal;

    // Build priority queue
    this.preCacheQueue = [];
    const window = this.config.preCacheWindow;

    for (let i = 1; i <= window; i++) {
      if (direction !== 'backward') {
        this.preCacheQueue.push({
          frame: currentFrame + i,
          compositionId,
          priority: window - i, // Closer frames have higher priority
        });
      }
      if (direction !== 'forward') {
        this.preCacheQueue.push({
          frame: currentFrame - i,
          compositionId,
          priority: window - i,
        });
      }
    }

    // Sort by priority (highest first)
    this.preCacheQueue.sort((a, b) => b.priority - a.priority);

    // Start pre-caching
    this.isPreCaching = true;

    for (const item of this.preCacheQueue) {
      if (signal.aborted) {
        break;
      }

      if (!this.has(item.frame, item.compositionId)) {
        try {
          const imageData = await this.renderFrame(item.frame);
          if (!signal.aborted) {
            await this.set(item.frame, item.compositionId, imageData, stateHash);
          }
        } catch (error) {
          // Frame render failed, skip
          console.warn(`Pre-cache failed for frame ${item.frame}:`, error);
        }
      }
    }

    this.isPreCaching = false;
  }

  /**
   * Abort any ongoing pre-cache operation
   */
  abortPreCache(): void {
    if (this.preCacheAbort) {
      this.preCacheAbort.abort();
      this.preCacheAbort = null;
    }
    this.preCacheQueue = [];
    this.isPreCaching = false;
  }

  /**
   * Get cache statistics
   */
  getStats(): CacheStats {
    const total = this.stats.hits + this.stats.misses;
    return {
      cachedFrames: this.cache.size,
      memoryUsed: this.currentMemory,
      hitRatio: total > 0 ? this.stats.hits / total : 0,
      hits: this.stats.hits,
      misses: this.stats.misses,
    };
  }

  /**
   * Get current configuration
   */
  getConfig(): FrameCacheConfig {
    return { ...this.config };
  }

  /**
   * Update configuration
   */
  setConfig(config: Partial<FrameCacheConfig>): void {
    this.config = { ...this.config, ...config };
  }

  // ============================================================================
  // PRIVATE METHODS
  // ============================================================================

  private async ensureCapacity(requiredSize: number): Promise<void> {
    // Evict LRU entries until we have enough space - O(1) per eviction
    while (
      (this.cache.size >= this.config.maxFrames ||
        this.currentMemory + requiredSize > this.config.maxMemoryBytes) &&
      this.lru.size > 0
    ) {
      const oldestKey = this.lru.getOldest();
      if (!oldestKey) break;

      const cached = this.cache.get(oldestKey);
      if (cached) {
        this.currentMemory -= cached.size;
        this.cache.delete(oldestKey);
      }
      this.lru.remove(oldestKey);
    }
  }

  private async compressFrame(imageData: ImageData): Promise<Blob> {
    // Create offscreen canvas for compression
    const canvas = new OffscreenCanvas(imageData.width, imageData.height);
    const ctx = canvas.getContext('2d')!;
    ctx.putImageData(imageData, 0, 0);

    // Use WebP for good compression with quality
    return canvas.convertToBlob({
      type: 'image/webp',
      quality: this.config.compressionQuality,
    });
  }

  private async decompressFrame(cached: CachedFrame): Promise<ImageData> {
    if (!(cached.data instanceof Blob)) {
      return cached.data as ImageData;
    }

    // Create image from blob
    const bitmap = await createImageBitmap(cached.data);

    // Draw to canvas and extract ImageData
    const canvas = new OffscreenCanvas(cached.width, cached.height);
    const ctx = canvas.getContext('2d')!;
    ctx.drawImage(bitmap, 0, 0);
    bitmap.close();

    return ctx.getImageData(0, 0, cached.width, cached.height);
  }
}

// ============================================================================
// SINGLETON INSTANCE
// ============================================================================

let globalFrameCache: FrameCache | null = null;

/**
 * Get the global frame cache instance
 */
export function getFrameCache(): FrameCache {
  if (!globalFrameCache) {
    globalFrameCache = new FrameCache();
  }
  return globalFrameCache;
}

/**
 * Initialize the global frame cache with GPU-appropriate settings
 */
export async function initializeFrameCache(): Promise<FrameCache> {
  const cache = getFrameCache();
  await cache.initializeForGPU();
  return cache;
}

export default FrameCache;
