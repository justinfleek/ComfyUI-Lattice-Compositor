import { defineConfig } from 'vite';
import vue from '@vitejs/plugin-vue';
import { resolve } from 'path';

export default defineConfig({
  plugins: [vue()],

  build: {
    outDir: '../dist',
    emptyOutDir: true,

    lib: {
      entry: resolve(__dirname, 'src/main.ts'),
      name: 'WeylCompositor',
      formats: ['es'],
      fileName: () => 'weyl-compositor.js'
    },

    rollupOptions: {
      external: [],
      output: {
        assetFileNames: 'weyl-[name].[ext]',
        chunkFileNames: 'weyl-[name].js'
      }
    },

    commonjsOptions: {
      include: [/bezier-js/, /node_modules/]
    }
  },

  optimizeDeps: {
    include: ['bezier-js']
  },

  resolve: {
    alias: {
      '@': resolve(__dirname, 'src')
    }
  }
});
