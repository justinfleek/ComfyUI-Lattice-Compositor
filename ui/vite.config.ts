import { defineConfig } from 'vite'
import vue from '@vitejs/plugin-vue'
import { resolve } from 'path'

export default defineConfig({
  plugins: [vue()],
  resolve: {
    alias: { '@': resolve(__dirname, 'src') },
  },
  build: {
    outDir: '../web/dist',
    emptyOutDir: true,
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
    sourcemap: true,
  },
  server: {
    port: 5173,
    proxy: {
      '/weyl': 'http://localhost:8188',
      '/api': 'http://localhost:8188',
    }
  },
})
