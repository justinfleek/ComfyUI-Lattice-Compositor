import { defineStore } from "pinia";

export type ThemeName =
  | "violet"
  | "ocean"
  | "sunset"
  | "forest"
  | "ember"
  | "mono";

export interface ThemeState {
  currentTheme: ThemeName;
}

export const useThemeStore = defineStore("theme", {
  state: (): ThemeState => ({
    currentTheme: "violet",
  }),

  getters: {
    themeGradient: (state) =>
      `var(--lattice-theme-${state.currentTheme}-gradient)`,
    themePrimary: (state) =>
      `var(--lattice-theme-${state.currentTheme}-primary)`,
    themeSecondary: (state) =>
      `var(--lattice-theme-${state.currentTheme}-secondary)`,
  },

  actions: {
    setTheme(theme: ThemeName) {
      this.currentTheme = theme;

      // Update CSS custom properties
      const root = document.documentElement;
      root.style.setProperty(
        "--lattice-accent",
        `var(--lattice-theme-${theme}-primary)`,
      );
      root.style.setProperty(
        "--lattice-accent-secondary",
        `var(--lattice-theme-${theme}-secondary)`,
      );
      root.style.setProperty(
        "--lattice-accent-gradient",
        `var(--lattice-theme-${theme}-gradient)`,
      );

      // Update glow color based on theme
      const glowColors: Record<ThemeName, string> = {
        violet: "rgba(139, 92, 246, 0.3)",
        ocean: "rgba(6, 182, 212, 0.3)",
        sunset: "rgba(251, 113, 133, 0.3)",
        forest: "rgba(16, 185, 129, 0.3)",
        ember: "rgba(239, 68, 68, 0.3)",
        mono: "rgba(107, 114, 128, 0.3)",
      };
      root.style.setProperty("--lattice-accent-glow", glowColors[theme]);

      // Persist to localStorage
      localStorage.setItem("lattice-theme", theme);
    },

    loadSavedTheme() {
      const saved = localStorage.getItem("lattice-theme") as ThemeName | null;
      if (
        saved &&
        ["violet", "ocean", "sunset", "forest", "ember", "mono"].includes(saved)
      ) {
        this.setTheme(saved);
      }
    },
  },
});
