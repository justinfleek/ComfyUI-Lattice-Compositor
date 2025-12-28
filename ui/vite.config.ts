/// <reference types="vitest" />
import { defineConfig } from 'vite'
import vue from '@vitejs/plugin-vue'
import { resolve } from 'path'

export default defineConfig({
  plugins: [vue()],
  resolve: {
    alias: { '@': resolve(__dirname, 'src') },
  },
  test: {
    globals: true,
    environment: 'node',
    setupFiles: ['./src/__tests__/setup.ts'],
    include: ['src/**/*.{test,spec}.{js,ts}'],
    exclude: ['node_modules', 'dist'],
    coverage: {
      provider: 'v8',
      reporter: ['text', 'json', 'html'],
      exclude: [
        'node_modules/',
        'src/__tests__/',
        '**/*.d.ts',
      ],
    },
  },
  define: {
    'process.env.NODE_ENV': '"production"',
    'process.env': '{}',
    'process': '{"env": {}}'
  },
  build: {
    outDir: '../web/js',
    emptyOutDir: false,
    lib: {
      entry: resolve(__dirname, 'src/main.ts'),
      name: 'LatticeCompositor',
      fileName: () => 'lattice-compositor.js',
      formats: ['es']
    },
    rollupOptions: {
      output: {
        // Allow code splitting for lazy-loaded modules
        inlineDynamicImports: false,
        assetFileNames: 'lattice-compositor[extname]',
        // Named chunks for better caching
        chunkFileNames: 'lattice-[name].js',
        entryFileNames: 'lattice-compositor.js',
        // Manual chunks for heavy dependencies
        manualChunks(id) {
          // Three.js and related 3D libraries
          if (id.includes('node_modules/three') ||
              id.includes('node_modules/troika')) {
            return 'three-vendor';
          }
          // Export/encoding libraries
          if (id.includes('node_modules/jszip') ||
              id.includes('node_modules/mp4-muxer') ||
              id.includes('node_modules/webm-muxer')) {
            return 'export-vendor';
          }
          // Vue ecosystem
          if (id.includes('node_modules/vue') ||
              id.includes('node_modules/pinia') ||
              id.includes('node_modules/@vue') ||
              id.includes('node_modules/@vueuse')) {
            return 'vue-vendor';
          }
          // UI components
          if (id.includes('node_modules/splitpanes') ||
              id.includes('node_modules/primevue') ||
              id.includes('node_modules/primeicons')) {
            return 'ui-vendor';
          }
          // Security: SES sandbox (must be included, has side effects)
          if (id.includes('node_modules/ses')) {
            return 'security-vendor';
          }
        },
      },
      // Tree shaking configuration
      treeshake: {
        // Aggressive tree shaking
        moduleSideEffects: false,
        // Remove unused properties
        propertyReadSideEffects: false,
        // Don't preserve external modules' side effects
        tryCatchDeoptimization: false,
      },
    },
    // Minification settings
    minify: 'terser',
    terserOptions: {
      compress: {
        // Remove console.log in production (keep warn/error)
        pure_funcs: ['console.debug'],
        // Dead code elimination
        dead_code: true,
        // Remove unreachable code
        unused: true,
        // Collapse variable declarations
        collapse_vars: true,
        // Reduce variable names
        reduce_vars: true,
        // Inline single-use functions
        inline: 2,
        // Maximum optimization passes
        passes: 3,
      },
      mangle: {
        // Mangle property names for smaller output
        properties: {
          regex: /^_private_/,
        },
      },
      format: {
        // Remove comments
        comments: false,
      },
    },
    // Target modern browsers for smaller output
    target: 'esnext',
    // Asset inlining
    assetsInlineLimit: 100000,
    // No sourcemaps in production
    sourcemap: false,
    // Report compressed size
    reportCompressedSize: true,
  },
  // Dependency optimization
  optimizeDeps: {
    // Pre-bundle these heavy dependencies
    include: [
      'three',
      'pinia',
      'vue',
      'ses', // Security sandbox - must be pre-bundled
    ],
    // Exclude workers from pre-bundling
    exclude: [],
  },
  // Worker configuration
  worker: {
    format: 'es',
    plugins: () => [vue()],
    rollupOptions: {
      output: {
        // Workers get their own chunks
        entryFileNames: 'worker-[name].js',
      },
    },
  },
  server: {
    port: 5173,
    proxy: {
      '/lattice': 'http://localhost:8188',
      '/api': 'http://localhost:8188',
    }
  },
})
