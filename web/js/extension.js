/**
 * Weyl Motion Graphics Compositor - ComfyUI Extension
 *
 * This file is auto-loaded by ComfyUI from the WEB_DIRECTORY.
 * It registers the sidebar tab and handles communication with the Vue app.
 */
import { app } from "../../scripts/app.js";
import { api } from "../../scripts/api.js";

// Track if Vue app is loaded
let vueAppLoaded = false;
let pendingMessages = [];

app.registerExtension({
  name: "weyl.compositor",

  async setup() {
    console.log("[Weyl] Registering compositor extension");

    // Register sidebar tab
    app.extensionManager.registerSidebarTab({
      id: "weyl-compositor",
      icon: "pi pi-video",
      title: "Motion Compositor",
      tooltip: "Weyl Motion Graphics Compositor",
      type: "custom",
      render: async (el) => {
        // Create container
        const container = document.createElement('div');
        container.id = 'weyl-compositor-root';
        container.style.cssText = 'width: 100%; height: 100%; overflow: hidden;';
        el.appendChild(container);

        // Load Vue app
        try {
          // The built Vue app is served from the extension's dist folder
          const scriptUrl = new URL(
            '/extensions/comfyui-weyl-compositor/dist/weyl-compositor.js',
            window.location.origin
          ).href;

          await import(scriptUrl);
          vueAppLoaded = true;

          // Send any pending messages
          pendingMessages.forEach(msg => {
            window.dispatchEvent(new CustomEvent(msg.type, { detail: msg.data }));
          });
          pendingMessages = [];

          console.log("[Weyl] Vue app loaded successfully");
        } catch (error) {
          console.error("[Weyl] Failed to load Vue app:", error);
          container.innerHTML = `
            <div style="padding: 20px; color: #ff6b6b; font-family: system-ui;">
              <h3>Failed to load Motion Compositor</h3>
              <p>Error: ${error.message}</p>
              <p>Check the browser console for details.</p>
            </div>
          `;
        }
      }
    });

    // Listen for messages from Python backend
    api.addEventListener("weyl.compositor.inputs_ready", (event) => {
      const msg = { type: 'weyl:inputs-ready', data: event.detail };

      if (vueAppLoaded) {
        window.dispatchEvent(new CustomEvent(msg.type, { detail: msg.data }));
      } else {
        pendingMessages.push(msg);
      }
    });

    // Add keyboard shortcuts
    document.addEventListener('keydown', (e) => {
      // Only handle if compositor is focused
      const compositorRoot = document.getElementById('weyl-compositor-root');
      if (!compositorRoot || !compositorRoot.contains(document.activeElement)) {
        return;
      }

      // Forward to Vue app
      window.dispatchEvent(new CustomEvent('weyl:keydown', {
        detail: {
          key: e.key,
          code: e.code,
          ctrlKey: e.ctrlKey,
          shiftKey: e.shiftKey,
          altKey: e.altKey,
          metaKey: e.metaKey
        }
      }));
    });

    console.log("[Weyl] Extension setup complete");
  }
});
