import { defineConfig } from "vitest/config";

export default defineConfig({
  test: {
    testTimeout: 60000,
    hookTimeout: 30000,
    globals: true,
    include: ["tests/**/*.spec.ts"],
    reporters: ["verbose"],
    pool: "forks",
    poolOptions: {
      forks: {
        singleFork: true, // Run tests serially to avoid browser conflicts
      },
    },
  },
});
