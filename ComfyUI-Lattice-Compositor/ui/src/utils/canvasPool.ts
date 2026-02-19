/**
 * Canvas Buffer Pool
 *
 * Reuses canvas elements to reduce allocation overhead and prevent memory leaks.
 * Used by effect processors and layer style renderers.
 */

export interface CanvasResult {
  canvas: HTMLCanvasElement;
  ctx: CanvasRenderingContext2D;
}

interface PooledCanvas {
  canvas: HTMLCanvasElement;
  ctx: CanvasRenderingContext2D;
  width: number;
  height: number;
  inUse: boolean;
  lastUsed: number;
}

/**
 * Canvas buffer pool for effect processing
 * Reduces GC pressure by reusing canvas elements
 */
export class CanvasPool {
  private pool: PooledCanvas[] = [];
  private readonly maxSize = 20; // Max pooled canvases
  private readonly maxAge = 60000; // 60 second TTL for unused canvases

  /**
   * Acquire a canvas of the specified dimensions
   */
  acquire(width: number, height: number): CanvasResult {
    const now = Date.now();

    // Try to find a matching canvas in the pool
    for (const item of this.pool) {
      if (!item.inUse && item.width === width && item.height === height) {
        item.inUse = true;
        item.lastUsed = now;
        // Clear the canvas for reuse
        item.ctx.clearRect(0, 0, width, height);
        return { canvas: item.canvas, ctx: item.ctx };
      }
    }

    // Create a new canvas
    const canvas = document.createElement("canvas");
    canvas.width = width;
    canvas.height = height;
    const ctx = canvas.getContext("2d")!;

    // Add to pool if not at capacity
    if (this.pool.length < this.maxSize) {
      this.pool.push({
        canvas,
        ctx,
        width,
        height,
        inUse: true,
        lastUsed: now,
      });
    }

    return { canvas, ctx };
  }

  /**
   * Release a canvas back to the pool
   * Call this when done with an effect result
   */
  release(canvas: HTMLCanvasElement): void {
    const item = this.pool.find((p) => p.canvas === canvas);
    if (item) {
      item.inUse = false;
      item.lastUsed = Date.now();
    }
  }

  /**
   * Clean up old unused canvases to free memory
   */
  cleanup(): void {
    const now = Date.now();
    this.pool = this.pool.filter((item) => {
      if (!item.inUse && now - item.lastUsed > this.maxAge) {
        // Let GC collect old canvases
        return false;
      }
      return true;
    });
  }

  /**
   * Clear all pooled canvases
   */
  clear(): void {
    this.pool = [];
  }

  /**
   * Get pool statistics
   */
  getStats(): { total: number; inUse: number; available: number } {
    const inUse = this.pool.filter((p) => p.inUse).length;
    return {
      total: this.pool.length,
      inUse,
      available: this.pool.length - inUse,
    };
  }
}

// Singleton canvas pool for shared use
export const canvasPool = new CanvasPool();
