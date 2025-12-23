/**
 * Lattice Compositor - ComfyUI Extension
 */
import { app } from "../../../scripts/app.js";
import { api } from "../../../scripts/api.js";

let vueAppLoaded = false;
let pendingMessages = [];
let currentNodeId = null;

function getExtensionBase() {
  const scripts = document.querySelectorAll('script[type="module"]');
  for (const script of scripts) {
    const match = script.src?.match(/\/extensions\/([^/]+)\/js\/extension\.js/);
    if (match) return `/extensions/${match[1]}`;
  }
  return '/extensions/weyl-compositor';
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

    api.addEventListener("lattice.compositor.inputs_ready", (event) => {
      currentNodeId = event.detail.node_id;
      if (vueAppLoaded) {
        window.dispatchEvent(new CustomEvent('lattice:inputs-ready', { detail: event.detail }));
      } else {
        pendingMessages.push(event.detail);
      }
    });
  },

  async beforeRegisterNodeDef(nodeType, nodeData) {
    if (nodeData.name === "LatticeCompositorEditor") {
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
  const container = document.createElement('div');
  container.id = 'lattice-compositor-root';
  container.style.cssText = 'width:100%;height:100%;min-height:100vh;overflow:hidden;background:#050505;position:relative;';
  el.appendChild(container);

  // Ensure parent element has proper sizing for flex layout
  el.style.cssText = 'width:100%;height:100%;display:flex;flex-direction:column;';

  const cssUrl = `${base}/js/lattice-compositor.css`;
  if (!document.querySelector(`link[href="${cssUrl}"]`)) {
    const link = document.createElement('link');
    link.rel = 'stylesheet';
    link.href = cssUrl;
    document.head.appendChild(link);
  }

  // Preload vendor chunks for faster loading
  const vendorChunks = [
    'lattice-vue-vendor.js',
    'lattice-three-vendor.js',
    'lattice-ui-vendor.js'
  ];
  vendorChunks.forEach(chunk => {
    const preload = document.createElement('link');
    preload.rel = 'modulepreload';
    preload.href = `${base}/js/${chunk}`;
    document.head.appendChild(preload);
  });

  try {
    const module = await import(`${base}/js/lattice-compositor.js`);
    if (module.mountApp) module.mountApp(container);
    vueAppLoaded = true;
    pendingMessages.forEach(data => {
      window.dispatchEvent(new CustomEvent('lattice:inputs-ready', { detail: data }));
    });
    pendingMessages = [];
  } catch (error) {
    container.innerHTML = `<div style="padding:24px;color:#ccc;font-family:system-ui;">
      <h3 style="color:#ff6b6b;">Failed to load compositor</h3>
      <p style="color:#888;">${error.message}</p>
    </div>`;
  }
}

window.LatticeCompositor = {
  getNodeId: () => currentNodeId,
  async sendOutput(matte, preview) {
    if (!currentNodeId) return false;
    try {
      const res = await fetch('/lattice/compositor/set_output', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ node_id: currentNodeId, matte, preview })
      });
      return res.ok;
    } catch { return false; }
  }
};
