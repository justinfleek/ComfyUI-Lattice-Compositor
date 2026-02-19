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

// Core mulberry32 step implemented in JS for correct bitwise behavior.
// Takes the current state (as a Number representing uint32), returns
// { value: Number in [0,1), newState: Number representing uint32 }
export const mulberry32NextImpl = function(state) {
  var newState = (state + 0x6D2B79F5) >>> 0;
  var t = newState;
  t = Math.imul(t ^ (t >>> 15), t | 1);
  t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
  var value = ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  return { value: value, newState: newState };
};

// Wrap a number to uint32 range using bitwise unsigned shift
export const wrap32Impl = function(n) {
  return n >>> 0;
};
