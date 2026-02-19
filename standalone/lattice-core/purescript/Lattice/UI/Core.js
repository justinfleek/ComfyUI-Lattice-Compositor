// Core.js - Theme switching FFI

export const setThemeImpl = (theme) => () => {
  document.documentElement.setAttribute("data-theme", theme);
  // Store in localStorage for persistence
  localStorage.setItem("lattice-theme", theme);
};

// Initialize theme from localStorage on load
(() => {
  const stored = localStorage.getItem("lattice-theme");
  if (stored) {
    document.documentElement.setAttribute("data-theme", stored);
  }
})();
