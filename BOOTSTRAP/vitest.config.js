import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    include: ['tests/**/*.test.js'],
    coverage: {
      provider: 'v8',
      reporter: ['text', 'json', 'html'],
      exclude: [
        'node_modules/',
        'tests/',
        '*.config.js',
        '.claude/',
        '.cursor/',
        '.opencode/',
        '.github/',
      ],
    },
    globals: true,
    testTimeout: 30000,
  },
});
