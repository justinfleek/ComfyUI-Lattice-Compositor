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

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// ImageData Polyfill for Node.js/happy-dom environment
// ═══════════════════════════════════════════════════════════════════════════

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

  // Type-safe polyfill assignment - ImageData exists at runtime but may not be in TypeScript types
  // Properly extend globalThis type instead of using double assertion
  // Use type assertion to assign polyfill - ImageDataPolyfill implements ImageData interface
  const globalWithImageData = globalThis as typeof globalThis & { ImageData: typeof ImageDataPolyfill };
  globalWithImageData.ImageData = ImageDataPolyfill as typeof ImageDataPolyfill & typeof ImageData;
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
    evaluateWithTimeout: async (code: string, context: Record<string, JSONValue>) => {
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
import type { SESCompartment } from "@/types/ses-ambient";
import type { JSONValue } from "@/types/dataAsset";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

class MockCompartment implements SESCompartment {
  public readonly globalThis: Record<PropertyKey, JSONValue>;
  public readonly name: string = "MockCompartment";
  private globals: Record<string, JSONValue>;

  constructor(
    globals?: Record<PropertyKey, JSONValue>,
    _modules?: Record<string, JSONValue>,
    _options?: Record<string, JSONValue>,
  ) {
    // Match SESCompartmentConstructor signature exactly: globals, modules, options are all optional
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const globalsObj = (globals !== null && globals !== undefined && typeof globals === "object" && globals !== null) ? (globals as Record<string, JSONValue>) : {};
    this.globals = globalsObj;
    // SESCompartment requires globalThis property
    const globalThisObj = (globals !== null && globals !== undefined && typeof globals === "object" && globals !== null) ? globals : {};
    this.globalThis = globalThisObj;
  }

  evaluate(code: string): RuntimeValue {
    // Filter out undefined values from globals
    const safeGlobals: Record<string, JSONValue> = {};
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
// Type-safe polyfill assignment - these exist at runtime but may not be in TypeScript types
// Properly extend globalThis type instead of using double assertion
import type { SESCompartmentConstructor } from "@/types/ses-ambient";

interface GlobalThisWithSES {
  Compartment: SESCompartmentConstructor;
  harden: typeof mockHarden;
}
const globalWithSES = globalThis as typeof globalThis & GlobalThisWithSES;
// Type assertion: MockCompartment constructor signature matches SESCompartmentConstructor
// Both are constructors that take (globals?, modules?, options?) and return SESCompartment
// MockCompartment implements SESCompartment and has matching constructor signature
globalWithSES.Compartment = MockCompartment as SESCompartmentConstructor;
globalWithSES.harden = mockHarden;

// Initialize SES after adding the globals
// Use top-level await to ensure SES is initialized before tests run
const { initializeSES } = await import("@/services/expressions/sesEvaluator");
await initializeSES();
