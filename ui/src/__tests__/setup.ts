/**
 * Vitest global setup
 *
 * This file runs before all tests and sets up any global mocks needed.
 *
 * Key mocks:
 * 1. workerEvaluator - bypassed because Web Workers don't work in happy-dom
 * 2. SES Compartment/harden - mocked because real SES lockdown breaks Vue/Three.js
 * 3. ImageData - polyfill for Node.js/happy-dom environment
 */

import { vi } from 'vitest';

// ============================================================================
// ImageData Polyfill for Node.js/happy-dom environment
// ============================================================================

/**
 * Polyfill for ImageData browser API.
 * Required for depth renderer tests that create ImageData objects.
 */
if (typeof globalThis.ImageData === 'undefined') {
  class ImageDataPolyfill {
    readonly data: Uint8ClampedArray;
    readonly width: number;
    readonly height: number;
    readonly colorSpace: PredefinedColorSpace = 'srgb';

    constructor(widthOrData: number | Uint8ClampedArray, heightOrWidth: number, height?: number) {
      if (widthOrData instanceof Uint8ClampedArray) {
        // Constructor: ImageData(data, width, height)
        this.data = widthOrData;
        this.width = heightOrWidth;
        this.height = height!;
      } else {
        // Constructor: ImageData(width, height)
        this.width = widthOrData;
        this.height = heightOrWidth;
        this.data = new Uint8ClampedArray(this.width * this.height * 4);
      }
    }
  }

  (globalThis as unknown as Record<string, unknown>).ImageData = ImageDataPolyfill;
}

// Mock the workerEvaluator module to bypass worker-based validation
// The worker doesn't work properly in happy-dom environment
vi.mock('@/services/expressions/workerEvaluator', async () => {
  const actual = await vi.importActual<typeof import('@/services/expressions/workerEvaluator')>(
    '@/services/expressions/workerEvaluator'
  );
  return {
    ...actual,
    isWorkerAvailable: () => false,
    // Return actual evaluation result using simple eval for tests
    // This allows expression validation to work properly
    evaluateWithTimeout: async (code: string, context: Record<string, unknown>) => {
      try {
        const keys = Object.keys(context);
        const values = Object.values(context);
        // eslint-disable-next-line @typescript-eslint/no-implied-eval
        const fn = new Function(...keys, `return (${code});`);
        const value = fn(...values);
        return { value, timedOut: false, error: undefined };
      } catch (e) {
        return { value: undefined, timedOut: false, error: String(e) };
      }
    },
  };
});

// Simple harden function that just returns the object unchanged
// Security is not a concern in test environment
const mockHarden = <T>(obj: T): T => obj;

/**
 * Mock Compartment class for test expression evaluation.
 *
 * This provides a simplified version of SES Compartment that:
 * - Accepts globals in constructor
 * - Evaluates expressions with those globals in scope
 * - Does NOT provide security isolation (not needed in tests)
 */
class MockCompartment {
  private globals: Record<string, unknown>;

  constructor(globals: Record<string, unknown>) {
    this.globals = globals;
  }

  evaluate(code: string): unknown {
    // Filter out undefined values from globals
    const safeGlobals: Record<string, unknown> = {};
    for (const [key, value] of Object.entries(this.globals)) {
      if (value !== undefined) {
        safeGlobals[key] = value;
      }
    }

    const keys = Object.keys(safeGlobals);
    const values = Object.values(safeGlobals);

    try {
      // Handle pre-wrapped code (IIFEs)
      const isWrapped =
        code.trim().startsWith("(function") || code.trim().startsWith("(()");

      // eslint-disable-next-line @typescript-eslint/no-implied-eval
      const fn = new Function(
        ...keys,
        isWrapped ? `return ${code};` : `return (${code});`,
      );
      return fn(...values);
    } catch (e) {
      // Keep error logging for debugging test failures
      console.error(`[MockCompartment] Expression error:`, e);
      console.error(`[MockCompartment] Code:`, code);
      console.error(`[MockCompartment] Globals:`, Object.keys(safeGlobals));
      throw new Error(`Expression error: ${e}`);
    }
  }
}

// Add to globalThis so sesEvaluator can find them
// IMPORTANT: This must happen BEFORE any imports that use sesEvaluator
(globalThis as unknown as Record<string, unknown>).Compartment = MockCompartment;
(globalThis as unknown as Record<string, unknown>).harden = mockHarden;

// Initialize SES after adding the globals
// Use top-level await to ensure SES is initialized before tests run
const { initializeSES } = await import("@/services/expressions/sesEvaluator");
await initializeSES();
