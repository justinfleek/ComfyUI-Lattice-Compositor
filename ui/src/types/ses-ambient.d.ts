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

export interface SESCompartment {
  globalThis: Record<PropertyKey, JSONValue>;
  name: string;
  evaluate(code: string, options?: Record<string, JSONValue>): RuntimeValue;
}

export interface SESCompartmentConstructor {
  new (
    globals?: Record<PropertyKey, JSONValue>,
    modules?: Record<string, JSONValue>,
    options?: Record<string, JSONValue>,
  ): SESCompartment;
}

type HardenFunction = <T>(value: T) => T;

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
