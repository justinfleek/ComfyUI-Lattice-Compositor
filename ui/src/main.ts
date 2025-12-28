import { createApp, App as VueApp } from 'vue'
import { createPinia } from 'pinia'
import App from './App.vue'
import 'splitpanes/dist/splitpanes.css'
import './styles/design-tokens.css'
import { initializeEffects } from './services/effects'
import { initializeSES } from './services/expressions/sesEvaluator'

let appInstance: VueApp | null = null;
let sesInitialized = false;

/**
 * Initialize SES (Secure ECMAScript) sandbox
 *
 * SECURITY: This MUST be called before any user expressions are evaluated.
 * SES freezes all JavaScript intrinsics to prevent prototype pollution
 * and sandbox escape attacks.
 *
 * If SES fails to initialize, expressions will be DISABLED (fail closed).
 */
async function initializeSecuritySandbox(): Promise<void> {
  if (sesInitialized) return;

  try {
    const success = await initializeSES();
    sesInitialized = true;

    if (success) {
      console.log('[Security] SES sandbox initialized - expressions enabled');
    } else {
      console.warn('[Security] SES initialization failed - expressions DISABLED for security');
      console.warn('[Security] Install @endo/ses package: npm install @endo/ses');
    }
  } catch (error) {
    sesInitialized = true; // Mark as attempted
    console.error('[Security] SES initialization error:', error);
    console.warn('[Security] Expressions are DISABLED - this is a security feature');
  }
}

export async function mountApp(container?: HTMLElement | string): Promise<VueApp | null> {
  let el: HTMLElement | null = null;

  if (typeof container === 'string') {
    el = document.getElementById(container) || document.querySelector(container);
  } else if (container instanceof HTMLElement) {
    el = container;
  } else {
    el = document.getElementById('lattice-compositor-root') || document.getElementById('app');
  }

  if (!el) return null;

  // SECURITY: Initialize SES sandbox BEFORE any user code can run
  await initializeSecuritySandbox();

  // Initialize effects system before mounting
  initializeEffects();

  const app = createApp(App);
  app.use(createPinia());
  app.mount(el);
  appInstance = app;

  setupBridge();
  return app;
}

function setupBridge() {
  window.addEventListener('lattice:inputs-ready', ((e: CustomEvent) => {
    window.dispatchEvent(new CustomEvent('lattice:load-project-inputs', { detail: e.detail }));
  }) as EventListener);
}

export async function sendToComfyUI(matte: string, preview: string): Promise<boolean> {
  return window.LatticeCompositor?.sendOutput?.(matte, preview) ?? false;
}

declare global {
  interface Window {
    LatticeCompositor?: {
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
