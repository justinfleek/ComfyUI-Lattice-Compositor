/**
 * Ambient declarations for SES (Secure ECMAScript) globals
 *
 * SES injects these globals at runtime after lockdown() is called.
 * The ses package has type declarations but they don't augment globalThis properly.
 */

import type { JSONValue } from "./dataAsset";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
export type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

/**
 * SES Compartment globals type
 * Deterministic: Explicit union of allowed types
 * SES accepts JSONValue OR functions (functions are hardened at runtime)
 */
export type SESGlobalsValue = JSONValue | ((...args: JSONValue[]) => JSONValue) | Record<string, SESGlobalsValue>;

export interface SESCompartment {
  globalThis: Record<PropertyKey, SESGlobalsValue>;
  name: string;
  evaluate(code: string, options?: Record<string, JSONValue>): RuntimeValue;
}

export interface SESCompartmentConstructor {
  new (
    globals?: Record<PropertyKey, SESGlobalsValue>,
    modules?: Record<string, JSONValue>,
    options?: Record<string, JSONValue>,
  ): SESCompartment;
}

export type HardenFunction = <T>(value: T) => T;

declare global {
  interface Window {
    Compartment?: SESCompartmentConstructor;
    harden?: HardenFunction;
    lockdown?: (options?: Record<string, JSONValue>) => void;
  }

  // Make these available on globalThis too
  var Compartment: SESCompartmentConstructor | undefined;
  var harden: HardenFunction | undefined;
  var lockdown: ((options?: Record<string, JSONValue>) => void) | undefined;
}

export {};
