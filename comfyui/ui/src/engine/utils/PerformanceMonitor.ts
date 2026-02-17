/**
 * PerformanceMonitor - FPS and Memory Tracking
 *
 * Monitors rendering performance:
 * - FPS calculation
 * - Frame time tracking
 * - WebGL statistics
 * - Memory usage (where available)
 */

import type * as THREE from "three";
import type { PerformanceStats } from "../types";

export class PerformanceMonitor {
  // Frame timing
  private frameCount: number = 0;
  private lastTime: number = 0;
  private frameTimes: number[] = [];
  private maxFrameTimes: number = 60;

  // FPS calculation
  private fps: number = 0;
  private fpsUpdateInterval: number = 500; // ms
  private lastFpsUpdate: number = 0;
  private framesInInterval: number = 0;

  // Frame start time (for measuring frame duration)
  private frameStartTime: number = 0;

  // Last captured stats
  private lastStats: PerformanceStats = {
    fps: 0,
    frameTime: 0,
    drawCalls: 0,
    triangles: 0,
    textures: 0,
    geometries: 0,
    memoryUsed: 0,
  };

  constructor() {
    this.lastTime = performance.now();
    this.lastFpsUpdate = this.lastTime;
  }

  /**
   * Call at the beginning of each frame
   */
  beginFrame(): void {
    this.frameStartTime = performance.now();
  }

  /**
   * Call at the end of each frame
   */
  endFrame(renderer: THREE.WebGLRenderer): PerformanceStats {
    const now = performance.now();
    const frameTime = now - this.frameStartTime;

    // Track frame times
    this.frameTimes.push(frameTime);
    if (this.frameTimes.length > this.maxFrameTimes) {
      this.frameTimes.shift();
    }

    // Update frame count
    this.frameCount++;
    this.framesInInterval++;

    // Calculate FPS periodically
    const timeSinceUpdate = now - this.lastFpsUpdate;
    if (timeSinceUpdate >= this.fpsUpdateInterval) {
      this.fps = Math.round((this.framesInInterval * 1000) / timeSinceUpdate);
      this.framesInInterval = 0;
      this.lastFpsUpdate = now;
    }

    // Get WebGL info
    const info = renderer.info;

    // Extended Performance interface for Chrome's memory API
    // performance.memory is available in Chrome but not in standard TypeScript DOM types
    interface PerformanceWithMemory extends Performance {
      memory?: {
        usedJSHeapSize: number;
        totalJSHeapSize: number;
        jsHeapSizeLimit: number;
      };
    }

    // Type guard to check if performance has memory API
    function hasMemoryAPI(perf: Performance): perf is PerformanceWithMemory {
      return "memory" in perf;
    }

    // Get memory usage (Chrome only) - type-safe access
    const memoryUsed = hasMemoryAPI(performance) && performance.memory
      ? performance.memory.usedJSHeapSize
      : 0;

    // Calculate average frame time
    const avgFrameTime =
      this.frameTimes.length > 0
        ? this.frameTimes.reduce((a, b) => a + b, 0) / this.frameTimes.length
        : 0;

    this.lastStats = {
      fps: this.fps,
      frameTime: Math.round(avgFrameTime * 100) / 100,
      drawCalls: info.render.calls,
      triangles: info.render.triangles,
      textures: info.memory.textures,
      geometries: info.memory.geometries,
      memoryUsed,
    };

    this.lastTime = now;

    return this.lastStats;
  }

  /**
   * Get the last captured stats
   */
  getStats(): PerformanceStats {
    return { ...this.lastStats };
  }

  /**
   * Get current FPS
   */
  getFPS(): number {
    return this.fps;
  }

  /**
   * Get average frame time in ms
   */
  getAverageFrameTime(): number {
    if (this.frameTimes.length === 0) return 0;
    return this.frameTimes.reduce((a, b) => a + b, 0) / this.frameTimes.length;
  }

  /**
   * Get min/max frame times
   */
  getFrameTimeRange(): { min: number; max: number } {
    if (this.frameTimes.length === 0) {
      return { min: 0, max: 0 };
    }
    return {
      min: Math.min(...this.frameTimes),
      max: Math.max(...this.frameTimes),
    };
  }

  /**
   * Get frame time history
   */
  getFrameTimeHistory(): number[] {
    return [...this.frameTimes];
  }

  /**
   * Get total frame count
   */
  getFrameCount(): number {
    return this.frameCount;
  }

  /**
   * Reset all statistics
   */
  reset(): void {
    this.frameCount = 0;
    this.frameTimes = [];
    this.fps = 0;
    this.framesInInterval = 0;
    this.lastTime = performance.now();
    this.lastFpsUpdate = this.lastTime;
    this.lastStats = {
      fps: 0,
      frameTime: 0,
      drawCalls: 0,
      triangles: 0,
      textures: 0,
      geometries: 0,
      memoryUsed: 0,
    };
  }

  /**
   * Check if performance is degraded
   */
  isPerformanceDegraded(targetFps: number = 30): boolean {
    return this.fps > 0 && this.fps < targetFps;
  }

  /**
   * Get performance report as string
   */
  getReport(): string {
    const stats = this.lastStats;
    const range = this.getFrameTimeRange();

    return [
      `FPS: ${stats.fps}`,
      `Frame Time: ${stats.frameTime.toFixed(2)}ms (min: ${range.min.toFixed(2)}, max: ${range.max.toFixed(2)})`,
      `Draw Calls: ${stats.drawCalls}`,
      `Triangles: ${stats.triangles.toLocaleString()}`,
      `Textures: ${stats.textures}`,
      `Geometries: ${stats.geometries}`,
      `Memory: ${(stats.memoryUsed / 1024 / 1024).toFixed(2)} MB`,
    ].join("\n");
  }
}
