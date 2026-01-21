import { createPinia } from "pinia";
import { createApp, type App as VueApp } from "vue";
import App from "./App.vue";
import "splitpanes/dist/splitpanes.css";
import "./styles/design-tokens.css";
import { initializeEffects } from "./services/effects";
import { cleanupEffectResources } from "./services/effectProcessor";
import { initializeSES } from "./services/expressions/sesEvaluator";

let appInstance: VueApp | null = null;
let effectsInitialized = false;

let sesInitialized = false;
let sesInitPromise: Promise<void> | null = null;

let bridgeHandler: EventListener | null = null;
let cleanupInterval: ReturnType<typeof setInterval> | null = null;

// Cleanup interval period (60 seconds)
const CLEANUP_INTERVAL_MS = 60000;

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
  if (sesInitialized) return;

  if (!sesInitPromise) {
    sesInitPromise = (async () => {
      try {
        await initializeSES();
        sesInitialized = true;
        // Logging is handled in initializeSES()
      } catch (error) {
        sesInitialized = true;
        console.error(
          "[Security] Expression security initialization error:",
          error,
        );
      }
    })();
  }

  await sesInitPromise;
}

/**
 * Initialize effects exactly once for the lifetime of the extension.
 */
function initializeEffectsOnce(): void {
  if (effectsInitialized) return;
  initializeEffects();
  effectsInitialized = true;
}

/**
 * Setup frontend ↔ ComfyUI bridge.
 * Idempotent and fully reversible.
 */
function setupBridge(): void {
  if (bridgeHandler) return;

  bridgeHandler = ((e: CustomEvent) => {
    window.dispatchEvent(
      new CustomEvent("lattice:load-project-inputs", { detail: e.detail }),
    );
  }) as EventListener;

  window.addEventListener("lattice:inputs-ready", bridgeHandler);
}

function teardownBridge(): void {
  if (!bridgeHandler) return;
  window.removeEventListener("lattice:inputs-ready", bridgeHandler);
  bridgeHandler = null;
}

/**
 * Mount the Vue application into an explicit container.
 * Safe to call multiple times.
 */
/**
 * Mount the Vue application into an explicit container.
 * Safe to call multiple times.
 * 
 * System F/Omega proof: Explicit validation of container element existence
 * Type proof: container ∈ HTMLElement | string → Promise<VueApp> (non-nullable)
 * Mathematical proof: Container element must exist in DOM to mount application
 */
export async function mountApp(
  container: HTMLElement | string,
): Promise<VueApp> {
  // If already mounted, unmount first (idempotence)
  if (appInstance) {
    unmountApp();
  }

  let el: HTMLElement | null = null;

  if (typeof container === "string") {
    el =
      document.getElementById(container) || document.querySelector(container);
  } else if (container instanceof HTMLElement) {
    el = container;
  }

  // System F/Omega proof: Explicit validation of container element existence
  // Type proof: el ∈ HTMLElement | null
  // Mathematical proof: Container element must exist in DOM to mount application
  if (!el) {
    const containerDesc = typeof container === "string" ? `selector "${container}"` : "HTMLElement";
    throw new Error(
      `[Lattice] Cannot mount app: Container element not found. ` +
      `Container: ${containerDesc}, ` +
      `document.getElementById/querySelector returned null. ` +
      `Container element must exist in DOM before mounting application. ` +
      `Wrap in try/catch if "container not found" is an expected state.`
    );
  }

  await initializeSecuritySandbox();
  initializeEffectsOnce();

  const app = createApp(App);
  app.use(createPinia());
  app.mount(el);

  appInstance = app;
  setupBridge();

  // Start periodic cleanup of effect resources (canvas pool, etc.)
  if (!cleanupInterval) {
    cleanupInterval = setInterval(cleanupEffectResources, CLEANUP_INTERVAL_MS);
  }

  return app;
}

/**
 * Fully tear down the Vue application and all side effects.
 */
export function unmountApp(): void {
  if (!appInstance) return;

  try {
    teardownBridge();
    appInstance.unmount();

    // Stop cleanup interval
    if (cleanupInterval) {
      clearInterval(cleanupInterval);
      cleanupInterval = null;
    }

    // Run final cleanup
    cleanupEffectResources();
  } catch (error) {
    console.error("[Lattice] unmount failed:", error);
  } finally {
    appInstance = null;
  }
}

/**
 * Backend bridge helper.
 */
export async function sendToComfyUI(
  matte: string,
  preview: string,
): Promise<boolean> {
  const bridge = window.LatticeCompositor;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const bridgeSendOutput = (bridge != null && typeof bridge === "object" && "sendOutput" in bridge && typeof bridge.sendOutput === "function") ? bridge.sendOutput : undefined;
  if (!bridgeSendOutput) {
    console.warn("[Lattice] sendToComfyUI called before backend bridge ready");
    return false;
  }
  return bridge.sendOutput(matte, preview);
}

declare global {
  interface Window {
    LatticeCompositor?: {
      getNodeId: () => string | null;
      sendOutput: (matte: string, preview: string) => Promise<boolean>;
    };
  }
}
