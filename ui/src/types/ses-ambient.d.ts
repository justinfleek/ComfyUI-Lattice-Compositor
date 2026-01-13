/**
 * Ambient declarations for SES (Secure ECMAScript) globals
 *
 * SES injects these globals at runtime after lockdown() is called.
 * The ses package has type declarations but they don't augment globalThis properly.
 */

/* eslint-disable @typescript-eslint/no-explicit-any */

export interface SESCompartment {
  globalThis: Record<PropertyKey, any>;
  name: string;
  evaluate(code: string, options?: Record<string, unknown>): any;
}

interface SESCompartmentConstructor {
  new (
    globals?: Record<PropertyKey, any>,
    modules?: Record<string, unknown>,
    options?: Record<string, unknown>,
  ): SESCompartment;
}

type HardenFunction = <T>(value: T) => T;

declare global {
  interface Window {
    Compartment?: SESCompartmentConstructor;
    harden?: HardenFunction;
    lockdown?: (options?: Record<string, unknown>) => void;
  }

  // Make these available on globalThis too
  var Compartment: SESCompartmentConstructor | undefined;
  var harden: HardenFunction | undefined;
  var lockdown: ((options?: Record<string, unknown>) => void) | undefined;
}

export {};
