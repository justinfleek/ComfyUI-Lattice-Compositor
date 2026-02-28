// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                   // hydrogen // render // style
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// FFI for Hydrogen.Render.Style

// foldl for arrays
export const foldlArrayImpl = (f) => (init) => (arr) => {
  let acc = init;
  for (let i = 0; i < arr.length; i++) {
    acc = f(acc)(arr[i]);
  }
  return acc;
};
