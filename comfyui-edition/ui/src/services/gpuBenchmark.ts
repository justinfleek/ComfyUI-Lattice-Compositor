/**
 * GPU Effect Benchmark Service
 *
 * Provides performance benchmarking for GPU vs CPU effect processing.
 * Useful for:
 * - Validating GPU acceleration benefits
 * - Identifying effects that benefit most from GPU
 * - Detecting performance regressions
 */

import type { PropertyValue } from "@/types/project";
import type { EffectInstance } from "@/types/effects";
import { engineLogger } from "@/utils/logger";
import { processEffectStack, processEffectStackAsync } from "./effectProcessor";
import {
  gpuEffectDispatcher,
  initializeGPUEffects,
} from "./gpuEffectDispatcher";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

export interface BenchmarkResult {
  effectKey: string;
  cpuTimeMs: number;
  gpuTimeMs: number;
  speedup: number;
  renderPath: string;
  imageSize: { width: number; height: number };
  iterations: number;
}

export interface BenchmarkSuite {
  results: BenchmarkResult[];
  summary: {
    totalCpuTime: number;
    totalGpuTime: number;
    averageSpeedup: number;
    bestEffect: string;
    worstEffect: string;
    gpuAvailable: boolean;
    renderPath: string;
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                // test // data // generation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Create a test canvas with random noise pattern
 */
function createTestCanvas(width: number, height: number): HTMLCanvasElement {
  const canvas = document.createElement("canvas");
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext("2d")!;

  // Create a gradient + noise pattern for realistic testing
  const gradient = ctx.createLinearGradient(0, 0, width, height);
  gradient.addColorStop(0, "#ff6b6b");
  gradient.addColorStop(0.5, "#4ecdc4");
  gradient.addColorStop(1, "#45b7d1");
  ctx.fillStyle = gradient;
  ctx.fillRect(0, 0, width, height);

  // Add some noise
  const imageData = ctx.getImageData(0, 0, width, height);
  const data = imageData.data;
  for (let i = 0; i < data.length; i += 4) {
    const noise = (Math.random() - 0.5) * 30;
    data[i] = Math.max(0, Math.min(255, data[i] + noise));
    data[i + 1] = Math.max(0, Math.min(255, data[i + 1] + noise));
    data[i + 2] = Math.max(0, Math.min(255, data[i + 2] + noise));
  }
  ctx.putImageData(imageData, 0, 0);

  return canvas;
}

/**
 * Create a test effect instance
 */
function createTestEffect(
  effectKey: string,
  params: Record<string, PropertyValue> = {},
): EffectInstance {
  return {
    id: `test-${effectKey}`,
    effectKey,
    name: effectKey,
    enabled: true,
    expanded: true,
    category: "blur-sharpen",
    parameters: Object.fromEntries(
      Object.entries(params).map(([key, value]) => [
        key,
        {
          id: `param-${key}`,
          name: key,
          type: "number" as const,
          value,
          animated: false,
          keyframes: [],
        },
      ]),
    ),
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                      // benchmark // effects
// ════════════════════════════════════════════════════════════════════════════

const BENCHMARK_EFFECTS: Array<{ key: string; params: Record<string, PropertyValue> }> = [
  // Blur effects (high GPU benefit)
  { key: "gaussian-blur", params: { radius: 20 } },
  { key: "radial-blur", params: { centerX: 0.5, centerY: 0.5, amount: 50 } },
  { key: "directional-blur", params: { angle: 45, length: 30 } },

  // Color effects (moderate GPU benefit)
  { key: "brightness-contrast", params: { brightness: 20, contrast: 30 } },
  { key: "hue-saturation", params: { hue: 30, saturation: 20 } },
  { key: "levels", params: { inputBlack: 10, inputWhite: 245, gamma: 1.2 } },
  { key: "glow", params: { radius: 15, intensity: 0.8 } },

  // Distort effects (high GPU benefit)
  { key: "warp", params: { style: "wave", bend: 0.5 } },
  { key: "turbulent-displace", params: { amount: 50 } },
];

// ════════════════════════════════════════════════════════════════════════════
//                                                    // benchmark // functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Run a single effect benchmark
 */
async function benchmarkEffect(
  effectKey: string,
  params: Record<string, PropertyValue>,
  canvas: HTMLCanvasElement,
  iterations: number,
): Promise<BenchmarkResult> {
  const effect = createTestEffect(effectKey, params);
  const effects = [effect];

  // Warm-up run
  processEffectStack(effects, canvas, 0, "high");
  await processEffectStackAsync(effects, canvas, 0);

  //                                                                       // cpu
  const cpuStart = performance.now();
  for (let i = 0; i < iterations; i++) {
    processEffectStack(effects, canvas, 0, "high");
  }
  const cpuEnd = performance.now();
  const cpuTimeMs = (cpuEnd - cpuStart) / iterations;

  //                                                                       // gpu
  const gpuStart = performance.now();
  for (let i = 0; i < iterations; i++) {
    await processEffectStackAsync(effects, canvas, 0);
  }
  const gpuEnd = performance.now();
  const gpuTimeMs = (gpuEnd - gpuStart) / iterations;

  const _caps = gpuEffectDispatcher.getCapabilities();

  return {
    effectKey,
    cpuTimeMs,
    gpuTimeMs,
    speedup: cpuTimeMs / Math.max(gpuTimeMs, 0.001),
    renderPath: gpuEffectDispatcher.getEffectRoute(effectKey),
    imageSize: { width: canvas.width, height: canvas.height },
    iterations,
  };
}

/**
 * Run the full benchmark suite
 */
export async function runBenchmarkSuite(
  width: number = 1920,
  height: number = 1080,
  iterations: number = 5,
): Promise<BenchmarkSuite> {
  engineLogger.info("Starting GPU benchmark suite", {
    width,
    height,
    iterations,
  });

  // Initialize GPU
  await initializeGPUEffects();
  const caps = gpuEffectDispatcher.getCapabilities();

  // Create test canvas
  const canvas = createTestCanvas(width, height);

  // Run benchmarks
  const results: BenchmarkResult[] = [];

  for (const { key, params } of BENCHMARK_EFFECTS) {
    try {
      const result = await benchmarkEffect(key, params, canvas, iterations);
      results.push(result);
      engineLogger.debug(`Benchmark: ${key}`, {
        cpu: result.cpuTimeMs.toFixed(2),
        gpu: result.gpuTimeMs.toFixed(2),
        speedup: result.speedup.toFixed(2),
      });
    } catch (error) {
      engineLogger.warn(`Benchmark failed for ${key}:`, error);
    }
  }

  // Calculate summary
  const totalCpuTime = results.reduce((sum, r) => sum + r.cpuTimeMs, 0);
  const totalGpuTime = results.reduce((sum, r) => sum + r.gpuTimeMs, 0);
  const averageSpeedup = totalCpuTime / Math.max(totalGpuTime, 0.001);

  const sortedBySpeedup = [...results].sort((a, b) => b.speedup - a.speedup);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const firstResult = (sortedBySpeedup != null && Array.isArray(sortedBySpeedup) && sortedBySpeedup.length > 0) ? sortedBySpeedup[0] : undefined;
  const bestEffect = (firstResult != null && typeof firstResult === "object" && "effectKey" in firstResult && typeof firstResult.effectKey === "string") ? firstResult.effectKey : "none";
  const lastResult = (sortedBySpeedup != null && Array.isArray(sortedBySpeedup) && sortedBySpeedup.length > 0) ? sortedBySpeedup[sortedBySpeedup.length - 1] : undefined;
  const worstEffect = (lastResult != null && typeof lastResult === "object" && "effectKey" in lastResult && typeof lastResult.effectKey === "string") ? lastResult.effectKey : "none";

  const summary = {
    totalCpuTime,
    totalGpuTime,
    averageSpeedup,
    bestEffect,
    worstEffect,
    gpuAvailable: caps.preferredPath !== "canvas2d",
    renderPath: caps.preferredPath,
  };

  engineLogger.info("Benchmark suite complete", summary);

  return { results, summary };
}

/**
 * Quick benchmark for a single effect
 */
export async function quickBenchmark(
  effectKey: string,
  params: Record<string, PropertyValue> = {},
  width: number = 1920,
  height: number = 1080,
): Promise<BenchmarkResult> {
  await initializeGPUEffects();
  const canvas = createTestCanvas(width, height);
  return benchmarkEffect(effectKey, params, canvas, 3);
}

/**
 * Print benchmark results to console
 */
export function printBenchmarkResults(suite: BenchmarkSuite): void {
  console.log("\n=== GPU Effect Benchmark Results ===\n");
  console.log(`GPU Available: ${suite.summary.gpuAvailable}`);
  console.log(`Render Path: ${suite.summary.renderPath}`);
  console.log("");

  console.log("Effect                | CPU (ms) | GPU (ms) | Speedup");
  console.log("---------------------|----------|----------|--------");

  for (const result of suite.results) {
    const effect = result.effectKey.padEnd(20);
    const cpu = result.cpuTimeMs.toFixed(2).padStart(8);
    const gpu = result.gpuTimeMs.toFixed(2).padStart(8);
    const speedup = result.speedup.toFixed(2).padStart(7);
    console.log(`${effect} | ${cpu} | ${gpu} | ${speedup}x`);
  }

  console.log("");
  console.log(`Total CPU Time: ${suite.summary.totalCpuTime.toFixed(2)}ms`);
  console.log(`Total GPU Time: ${suite.summary.totalGpuTime.toFixed(2)}ms`);
  console.log(`Average Speedup: ${suite.summary.averageSpeedup.toFixed(2)}x`);
  console.log(`Best Effect: ${suite.summary.bestEffect}`);
  console.log(`Worst Effect: ${suite.summary.worstEffect}`);
}

export default {
  runBenchmarkSuite,
  quickBenchmark,
  printBenchmarkResults,
};
