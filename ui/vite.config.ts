import { defineConfig } from 'vite'
import vue from '@vitejs/plugin-vue'
import { resolve } from 'path'

export default defineConfig({
  plugins: [vue()],
  resolve: {
    alias: { '@': resolve(__dirname, 'src') },
  },
  define: {
    'process.env.NODE_ENV': '"production"'
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
        assetFileNames: 'weyl-compositor[extname]'
      }
    },
    assetsInlineLimit: 100000,
    sourcemap: false,
  },
  server: {
    port: 5173,
    proxy: {
      '/weyl': 'http://localhost:8188',
      '/api': 'http://localhost:8188',
    }
  },
})
