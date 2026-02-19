// @ts-check
/**
 * Lattice UI Core FFI
 * Theme switching and core UI utilities
 */

/**
 * Set the current theme by updating the data-theme attribute on document.body
 * @param {string} theme - Theme name (violet, ocean, rose, forest, ember, mono)
 * @returns {function(): void}
 */
export function setThemeImpl(theme) {
  return () => {
    if (typeof document !== "undefined" && document.body) {
      document.body.setAttribute("data-theme", theme);
      // Also set on document element for CSS custom properties
      document.documentElement.setAttribute("data-theme", theme);
    }
  };
}
