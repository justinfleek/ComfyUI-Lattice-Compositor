// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                     // hydrogen // datepicker
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// DatePicker FFI helpers

/**
 * Parse integer from string
 * @param {Function} just - Constructor for Just
 * @param {*} nothing - Nothing value
 * @param {string} str - String to parse
 * @returns {*} Maybe Int
 */
export const parseIntImpl = (just) => (nothing) => (str) => {
  const trimmed = str.trim();
  if (trimmed === "") return nothing;
  const parsed = parseInt(trimmed, 10);
  return isNaN(parsed) ? nothing : just(parsed);
};
