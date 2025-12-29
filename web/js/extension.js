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
  fullscreenCssInjected: false,
  loadedModule: null,
  patchedNodeType: null,
  sidebarPanel: null,
  originalPanelWidth: null
};

/**
 * Inject CSS for fullscreen sidebar mode.
 * This overrides ComfyUI's sidebar panel width when Lattice is active.
 */
function injectFullscreenCSS() {
  if (state.fullscreenCssInjected) return;

  const style = document.createElement('style');
  style.id = 'lattice-fullscreen-css';
  style.textContent = `
    /* Lattice Fullscreen Mode - Expands sidebar panel to near-full width */
    .lattice-fullscreen-mode {
      width: calc(100vw - 48px) !important;
      max-width: none !important;
      min-width: calc(100vw - 48px) !important;
      transition: width 0.2s ease-out;
    }

    /* Hide the resize handle when in fullscreen */
    .lattice-fullscreen-mode .resize-handle,
    .lattice-fullscreen-mode [class*="resize"] {
      display: none !important;
    }

    /* Ensure content fills the expanded panel */
    .lattice-fullscreen-mode > * {
      width: 100% !important;
    }

    /* Close button styling */
    .lattice-close-btn {
      position: fixed;
      top: 8px;
      right: 12px;
      z-index: 10001;
      display: flex;
      align-items: center;
      gap: 6px;
      padding: 8px 14px;
      background: rgba(30, 30, 30, 0.95);
      border: 1px solid #444;
      border-radius: 6px;
      color: #e0e0e0;
      font-size: 13px;
      font-family: system-ui, -apple-system, sans-serif;
      cursor: pointer;
      backdrop-filter: blur(8px);
      transition: all 0.15s ease;
    }

    .lattice-close-btn:hover {
      background: rgba(60, 60, 60, 0.95);
      border-color: #666;
      color: #fff;
    }

    .lattice-close-btn svg {
      width: 14px;
      height: 14px;
    }
  `;
  document.head.appendChild(style);
  state.fullscreenCssInjected = true;
}

/**
 * Find the sidebar panel element that controls width.
 * Walks up the DOM tree from the render element to find the resizable panel.
 */
function findSidebarPanel(el) {
  let current = el;
  let maxIterations = 10;

  while (current && maxIterations-- > 0) {
    // Look for elements with explicit width styling or sidebar-related classes
    const style = window.getComputedStyle(current);
    const classes = current.className || '';

    // Check if this is a sidebar panel (typically has width constraints)
    if (
      (style.width && style.width !== '100%' && style.width !== 'auto') ||
      classes.includes('sidebar') ||
      classes.includes('panel') ||
      current.hasAttribute('data-sidebar')
    ) {
      // Verify it's a meaningful container, not just a wrapper
      if (current.offsetWidth > 200 && current.offsetWidth < window.innerWidth * 0.9) {
        return current;
      }
    }

    current = current.parentElement;
  }

  // Fallback: return the first parent with constrained width
  current = el.parentElement;
  while (current && current !== document.body) {
    if (current.offsetWidth < window.innerWidth * 0.5) {
      return current;
    }
    current = current.parentElement;
  }

  return el.parentElement;
}

/**
 * Expand sidebar to fullscreen mode.
 */
function enterFullscreen(el) {
  injectFullscreenCSS();

  const panel = findSidebarPanel(el);
  if (panel) {
    state.sidebarPanel = panel;
    state.originalPanelWidth = panel.style.width || '';
    panel.classList.add('lattice-fullscreen-mode');
    console.log('[Lattice] Entered fullscreen mode');
  }

  // Add close button
  addCloseButton();
}

/**
 * Exit fullscreen mode and restore sidebar.
 */
function exitFullscreen() {
  if (state.sidebarPanel) {
    state.sidebarPanel.classList.remove('lattice-fullscreen-mode');
    if (state.originalPanelWidth) {
      state.sidebarPanel.style.width = state.originalPanelWidth;
    }
    state.sidebarPanel = null;
    state.originalPanelWidth = null;
  }

  // Remove close button
  const closeBtn = document.getElementById('lattice-close-btn');
  if (closeBtn) closeBtn.remove();

  console.log('[Lattice] Exited fullscreen mode');
}

/**
 * Add close button to return to ComfyUI view.
 */
function addCloseButton() {
  // Remove existing button if any
  const existing = document.getElementById('lattice-close-btn');
  if (existing) existing.remove();

  const btn = document.createElement('button');
  btn.id = 'lattice-close-btn';
  btn.className = 'lattice-close-btn';
  btn.innerHTML = `
    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
      <path d="M18 6L6 18M6 6l12 12"/>
    </svg>
    Back to ComfyUI
  `;
  btn.onclick = () => {
    exitFullscreen();
    // Trigger ComfyUI to close the sidebar or switch tabs
    // This dispatches a custom event that can be caught if needed
    window.dispatchEvent(new CustomEvent('lattice:close-compositor'));
  };

  document.body.appendChild(btn);
}

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

    app.extensionManager.registerSidebarTab({
      id: "lattice-compositor",
      icon: "pi pi-video",
      title: "Motion Compositor",
      tooltip: "Lattice Motion Compositor",
      type: "custom",
      render: (el) => renderCompositor(el, base)
    });

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

  // Enter fullscreen mode - expand sidebar panel to full width
  enterFullscreen(el);

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
  exitFullscreen,
  isFullscreen: () => !!state.sidebarPanel,
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
