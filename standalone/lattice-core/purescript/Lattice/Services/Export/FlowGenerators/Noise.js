//                                                                       // ffi
// Bitwise operations and imul for hash functions

export const zshr = (a) => (b) => a >>> b;
export const and = (a) => (b) => a & b;
export const xor = (a) => (b) => a ^ b;
export const imul = (a) => (b) => Math.imul(a, b);
