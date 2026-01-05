import { fileURLToPath } from "node:url";
import vue from "@vitejs/plugin-vue";
import { defineConfig } from "vitest/config";

export default defineConfig({
  plugins: [vue()],
  test: {
    globals: true,
    environment: "happy-dom",
    setupFiles: ["./src/__tests__/setup.ts"],
    include: ["src/**/*.{test,spec}.{js,ts}"],
    exclude: ["**/node_modules/**", "**/_archived/**", "**/browser/**"],
    coverage: {
      provider: "v8",
      reporter: ["text", "json", "html"],
      exclude: ["node_modules/**", "src/**/*.d.ts", "src/main.ts"],
    },
    // Server config for resolving three.js properly
    server: {
      deps: {
        inline: ["three"],
      },
    },
  },
  resolve: {
    alias: {
      "@": fileURLToPath(new URL("./src", import.meta.url)),
      // Use real three.js instead of mock for tests that need it
      three: "three",
    },
  },
});
