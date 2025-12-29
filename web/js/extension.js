/**
 * Lattice Compositor - ComfyUI Extension
 * Lifecycle-stabilized: idempotent render, guarded listeners, explicit cleanup
 */
import { app } from "../../../scripts/app.js";
import { api } from "../../../scripts/api.js";

// Centralized mutable state for lifecycle tracking
const state = {
  vueAppLoaded: false,
  pendingMessages: [],
  currentNodeId: null,
  eventListenerAttached: false,
  preloadLinksInjected: false,
  cssLinkInjected: false,
  loadedModule: null,
  patchedNodeType: null
};

function getExtensionBase() {
  const scripts = document.querySelectorAll('script[type="module"]');
  for (const script of scripts) {
    const match = script.src?.match(/\/extensions\/([^/]+)\/js\/extension\.js/);
    if (match) return `/extensions/${match[1]}`;
  }
  return '/extensions/weyl-compositor';
}

function handleInputsReady(event) {
  state.currentNodeId = event.detail.node_id;
  if (state.vueAppLoaded) {
    window.dispatchEvent(new CustomEvent('lattice:inputs-ready', { detail: event.detail }));
  } else {
    state.pendingMessages.push(event.detail);
  }
}

app.registerExtension({
  name: "lattice.compositor",

  async setup() {
    const base = getExtensionBase();

    console.log('[Lattice] Extension setup starting...');
    console.log('[Lattice] app.extensionManager:', app.extensionManager);
    console.log('[Lattice] registerSidebarTab:', app.extensionManager?.registerSidebarTab);

    // Guard: extensionManager may not exist in older ComfyUI versions
    if (app.extensionManager?.registerSidebarTab) {
      console.log('[Lattice] Registering sidebar tab...');
      app.extensionManager.registerSidebarTab({
        id: "lattice-compositor",
        icon: "pi pi-video",
        title: "Motion Compositor",
        tooltip: "Lattice Motion Compositor",
        type: "custom",
        render: (el) => renderCompositor(el, base)
      });
      console.log('[Lattice] Sidebar tab registered successfully');
    } else {
      console.warn('[Lattice] extensionManager.registerSidebarTab not available - ComfyUI version may be too old');
      console.warn('[Lattice] Try updating ComfyUI to the latest version with the new frontend');
    }

    // Guard: only attach listener once
    if (!state.eventListenerAttached) {
      api.addEventListener("lattice.compositor.inputs_ready", handleInputsReady);
      state.eventListenerAttached = true;
    }
  },

  async beforeRegisterNodeDef(nodeType, nodeData) {
    if (nodeData.name === "LatticeCompositorEditor") {
      // Guard: only patch once per nodeType
      if (state.patchedNodeType === nodeType) return;
      state.patchedNodeType = nodeType;

      const orig = nodeType.prototype.onNodeCreated;
      nodeType.prototype.onNodeCreated = function() {
        orig?.apply(this, arguments);
        this.bgcolor = "#2a4a6a";
        this.color = "#4a90d9";
      };
    }
  }
});

async function renderCompositor(el, base) {
  // If already rendered, unmount first (idempotence)
  if (state.loadedModule?.unmountApp) {
    try {
      state.loadedModule.unmountApp();
    } catch (e) {
      console.warn('[Lattice] unmount during re-render failed:', e);
    }
    state.vueAppLoaded = false;
  }

  // Clear container
  el.innerHTML = '';

  const container = document.createElement('div');
  container.id = 'lattice-compositor-root';
  container.style.cssText = 'width:100%;height:100%;min-height:100vh;overflow:hidden;background:#050505;position:relative;';
  el.appendChild(container);

  // Ensure parent element has proper sizing for flex layout
  el.style.cssText = 'width:100%;height:100%;display:flex;flex-direction:column;';

  // Guard: inject CSS only once
  const cssUrl = `${base}/js/lattice-compositor.css`;
  if (!state.cssLinkInjected && !document.querySelector(`link[href="${cssUrl}"]`)) {
    const link = document.createElement('link');
    link.rel = 'stylesheet';
    link.href = cssUrl;
    document.head.appendChild(link);
    state.cssLinkInjected = true;
  }

  // Guard: inject preload links only once
  if (!state.preloadLinksInjected) {
    const vendorChunks = [
      'lattice-vue-vendor.js',
      'lattice-three-vendor.js',
      'lattice-ui-vendor.js'
    ];
    vendorChunks.forEach(chunk => {
      const href = `${base}/js/${chunk}`;
      if (!document.querySelector(`link[href="${href}"]`)) {
        const preload = document.createElement('link');
        preload.rel = 'modulepreload';
        preload.href = href;
        document.head.appendChild(preload);
      }
    });
    state.preloadLinksInjected = true;
  }

  try {
    const module = await import(`${base}/js/lattice-compositor.js`);
    state.loadedModule = module;

    if (module.mountApp) {
      await module.mountApp(container);
    }

    state.vueAppLoaded = true;

    // Flush pending messages
    state.pendingMessages.forEach(data => {
      window.dispatchEvent(new CustomEvent('lattice:inputs-ready', { detail: data }));
    });
    state.pendingMessages = [];
  } catch (error) {
    console.error('[Lattice] Failed to load compositor:', error);
    container.innerHTML = `<div style="padding:24px;color:#ccc;font-family:system-ui;">
      <h3 style="color:#ff6b6b;">Failed to load compositor</h3>
      <p style="color:#888;">${error.message}</p>
    </div>`;
  }
}

window.LatticeCompositor = {
  getNodeId: () => state.currentNodeId,
  async sendOutput(matte, preview) {
    if (!state.currentNodeId) return false;
    try {
      const res = await fetch('/lattice/compositor/set_output', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ node_id: state.currentNodeId, matte, preview })
      });
      return res.ok;
    } catch { return false; }
  }
};
