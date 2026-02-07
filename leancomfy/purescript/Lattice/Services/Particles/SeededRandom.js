// FFI for Lattice.Services.Particles.SeededRandom
// Bitwise operations for simulating 32-bit unsigned integers

export const xorBitwise = function(a) {
  return function(b) {
    return (a ^ b) >>> 0;
  };
};

export const orBitwise = function(a) {
  return function(b) {
    return (a | b) >>> 0;
  };
};
