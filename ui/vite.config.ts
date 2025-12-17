import { defineConfig } from 'vite'
import vue from '@vitejs/plugin-vue'
import { resolve } from 'path'

export default defineConfig({
  plugins: [vue()],
  resolve: {
    alias: { '@': resolve(__dirname, 'src') },
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
      name: 'WeylCompositor',
      fileName: () => 'weyl-compositor.js',
      formats: ['es']
    },
    rollupOptions: {
      output: {
        inlineDynamicImports: true,
        assetFileNames: 'weyl-compositor[extname]',
        // Preserve module structure for better tree shaking
        preserveModules: false,
        // Optimize chunk names
        chunkFileNames: '[name]-[hash].js',
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
      'fabric',
      'pinia',
      'vue',
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
      '/weyl': 'http://localhost:8188',
      '/api': 'http://localhost:8188',
    }
  },
})
