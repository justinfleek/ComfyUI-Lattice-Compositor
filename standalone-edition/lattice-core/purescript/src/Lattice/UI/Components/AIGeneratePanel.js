// AIGeneratePanel FFI
// Provides safe numeric conversion functions

export const toNumberImpl = (n) => n;

export const unsafeFloor = (n) => Math.floor(n) | 0;
