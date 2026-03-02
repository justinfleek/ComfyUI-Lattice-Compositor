// FFI bindings for Lattice.Services.RenderQueue.Manager
// Timer and utility operations

// Get current timestamp
export const now = () => () => Date.now();

// Generate unique ID
export const generateId = () => () => {
  return `render-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`;
};

// Set interval timer
export const setIntervalImpl = (callback) => (interval) => () => {
  return window.setInterval(callback, interval);
};

// Clear interval timer
export const clearIntervalImpl = (timerId) => () => {
  window.clearInterval(timerId);
};

// Fold left over array
export const foldlImpl = (f) => (init) => (arr) => {
  let acc = init;
  for (let i = 0; i < arr.length; i++) {
    acc = f(acc)(arr[i]);
  }
  return acc;
};

// Array length
export const lengthImpl = (arr) => arr.length;

// Unsafe array index (internal use only)
export const unsafeIndex = (arr) => (i) => arr[i];

// Run effect (unsafe, for lifting Effect into Aff)
// Note: This should be replaced with proper Effect.Aff.liftEffect
export const runEffect = (eff) => eff();
