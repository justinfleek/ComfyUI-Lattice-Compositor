import { createApp, App as VueApp } from 'vue'
import { createPinia } from 'pinia'
import App from './App.vue'
import 'splitpanes/dist/splitpanes.css'
import './styles/design-tokens.css'
import { initializeEffects } from './services/effects'
import { initializeSES } from './services/expressions/sesEvaluator'

let appInstance: VueApp | null = null
let effectsInitialized = false

let sesInitialized = false
let sesInitPromise: Promise<void> | null = null

let bridgeHandler: EventListener | null = null

/**
 * SECURITY: Initialize expression security.
 *
 * Expression evaluation is secured via Web Worker isolation:
 * - Expressions run in an isolated worker with SES lockdown
 * - 100ms timeout protects against infinite loops
 * - Main thread is never blocked
 *
 * NOTE: Main thread lockdown is DISABLED because it breaks Vue/Three.js.
 * This is safe because expressions never execute in the main thread.
 */
async function initializeSecuritySandbox(): Promise<void> {
  if (sesInitialized) return

  if (!sesInitPromise) {
    sesInitPromise = (async () => {
      try {
        await initializeSES()
        sesInitialized = true
        // Logging is handled in initializeSES()
      } catch (error) {
        sesInitialized = true
        console.error('[Security] Expression security initialization error:', error)
      }
    })()
  }

  await sesInitPromise
}

/**
 * Initialize effects exactly once for the lifetime of the extension.
 */
function initializeEffectsOnce(): void {
  if (effectsInitialized) return
  initializeEffects()
  effectsInitialized = true
}

/**
 * Setup frontend ↔ ComfyUI bridge.
 * Idempotent and fully reversible.
 */
function setupBridge(): void {
  if (bridgeHandler) return

  bridgeHandler = ((e: CustomEvent) => {
    window.dispatchEvent(
      new CustomEvent('lattice:load-project-inputs', { detail: e.detail })
    )
  }) as EventListener

  window.addEventListener('lattice:inputs-ready', bridgeHandler)
}

function teardownBridge(): void {
  if (!bridgeHandler) return
  window.removeEventListener('lattice:inputs-ready', bridgeHandler)
  bridgeHandler = null
}

/**
 * Mount the Vue application into an explicit container.
 * Safe to call multiple times.
 */
export async function mountApp(
  container: HTMLElement | string
): Promise<VueApp | null> {
  // If already mounted, unmount first (idempotence)
  if (appInstance) {
    unmountApp()
  }

  let el: HTMLElement | null = null

  if (typeof container === 'string') {
    el = document.getElementById(container) || document.querySelector(container)
  } else if (container instanceof HTMLElement) {
    el = container
  }

  if (!el) {
    console.error('[Lattice] mountApp failed: container not found')
    return null
  }

  await initializeSecuritySandbox()
  initializeEffectsOnce()

  const app = createApp(App)
  app.use(createPinia())
  app.mount(el)

  appInstance = app
  setupBridge()

  return app
}

/**
 * Fully tear down the Vue application and all side effects.
 */
export function unmountApp(): void {
  if (!appInstance) return

  try {
    teardownBridge()
    appInstance.unmount()
  } catch (error) {
    console.error('[Lattice] unmount failed:', error)
  } finally {
    appInstance = null
  }
}

/**
 * Backend bridge helper.
 */
export async function sendToComfyUI(
  matte: string,
  preview: string
): Promise<boolean> {
  const bridge = window.LatticeCompositor
  if (!bridge?.sendOutput) {
    console.warn('[Lattice] sendToComfyUI called before backend bridge ready')
    return false
  }
  return bridge.sendOutput(matte, preview)
}

declare global {
  interface Window {
    LatticeCompositor?: {
      getNodeId: () => string | null
      sendOutput: (matte: string, preview: string) => Promise<boolean>
    }
  }
}
