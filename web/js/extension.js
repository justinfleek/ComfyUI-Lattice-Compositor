/**
 * Weyl Compositor - ComfyUI Extension
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
  name: "weyl.compositor",

  async setup() {
    const base = getExtensionBase();

    app.extensionManager.registerSidebarTab({
      id: "weyl-compositor",
      icon: "pi pi-video",
      title: "Motion Compositor",
      tooltip: "Weyl Motion Compositor",
      type: "custom",
      render: (el) => renderCompositor(el, base)
    });

    api.addEventListener("weyl.compositor.inputs_ready", (event) => {
      currentNodeId = event.detail.node_id;
      if (vueAppLoaded) {
        window.dispatchEvent(new CustomEvent('weyl:inputs-ready', { detail: event.detail }));
      } else {
        pendingMessages.push(event.detail);
      }
    });
  },

  async beforeRegisterNodeDef(nodeType, nodeData) {
    if (nodeData.name === "WeylCompositorEditor") {
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
  container.id = 'weyl-compositor-root';
  container.style.cssText = 'width:100%;height:100%;min-height:600px;overflow:hidden;background:#1a1a2e;';
  el.appendChild(container);

  const cssUrl = `${base}/js/weyl-compositor.css`;
  if (!document.querySelector(`link[href="${cssUrl}"]`)) {
    const link = document.createElement('link');
    link.rel = 'stylesheet';
    link.href = cssUrl;
    document.head.appendChild(link);
  }

  try {
    const module = await import(`${base}/js/weyl-compositor.js`);
    if (module.mountApp) module.mountApp(container);
    vueAppLoaded = true;
    pendingMessages.forEach(data => {
      window.dispatchEvent(new CustomEvent('weyl:inputs-ready', { detail: data }));
    });
    pendingMessages = [];
  } catch (error) {
    container.innerHTML = `<div style="padding:24px;color:#ccc;font-family:system-ui;">
      <h3 style="color:#ff6b6b;">Failed to load compositor</h3>
      <p style="color:#888;">${error.message}</p>
    </div>`;
  }
}

window.WeylCompositor = {
  getNodeId: () => currentNodeId,
  async sendOutput(matte, preview) {
    if (!currentNodeId) return false;
    try {
      const res = await fetch('/weyl/compositor/set_output', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ node_id: currentNodeId, matte, preview })
      });
      return res.ok;
    } catch { return false; }
  }
};
