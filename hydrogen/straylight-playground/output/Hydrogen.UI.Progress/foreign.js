// FFI for Progress component
export const intToString = (n) => String(n);
export const intToPercent = (n) => String(Math.min(100, Math.max(0, n)));
