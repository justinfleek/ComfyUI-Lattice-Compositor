import { createApp, App as VueApp } from 'vue'
import { createPinia } from 'pinia'
import App from './App.vue'
import 'splitpanes/dist/splitpanes.css'

let appInstance: VueApp | null = null;

export function mountApp(container?: HTMLElement | string): VueApp | null {
  let el: HTMLElement | null = null;
  
  if (typeof container === 'string') {
    el = document.getElementById(container) || document.querySelector(container);
  } else if (container instanceof HTMLElement) {
    el = container;
  } else {
    el = document.getElementById('weyl-compositor-root') || document.getElementById('app');
  }
  
  if (!el) return null;
  
  const app = createApp(App);
  app.use(createPinia());
  app.mount(el);
  appInstance = app;
  
  setupBridge();
  return app;
}

function setupBridge() {
  window.addEventListener('weyl:inputs-ready', ((e: CustomEvent) => {
    window.dispatchEvent(new CustomEvent('weyl:load-project-inputs', { detail: e.detail }));
  }) as EventListener);
}

export async function sendToComfyUI(matte: string, preview: string): Promise<boolean> {
  return window.WeylCompositor?.sendOutput?.(matte, preview) ?? false;
}

declare global {
  interface Window {
    WeylCompositor?: {
      getNodeId: () => string | null;
      sendOutput: (matte: string, preview: string) => Promise<boolean>;
    };
  }
}

if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', () => mountApp());
} else {
  setTimeout(() => { if (!appInstance) mountApp(); }, 0);
}
