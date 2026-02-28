// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                 // hydrogen // runtime // animate
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Array helpers for animation sequencing
// These are minimal FFI to avoid depending on Data.Array's full implementation

// | Get array length
export const arrayLength = (arr) => arr.length;

// | Safe array index access
// | Takes Just and Nothing constructors from PureScript for proper Maybe encoding
export const arrayIndexImpl = (just) => (nothing) => (idx) => (arr) => {
  if (idx >= 0 && idx < arr.length) {
    return just(arr[idx]);
  }
  return nothing;
};

// | Left fold over array
export const foldlArray = (f) => (init) => (arr) => {
  let acc = init;
  for (let i = 0; i < arr.length; i++) {
    acc = f(acc)(arr[i]);
  }
  return acc;
};
