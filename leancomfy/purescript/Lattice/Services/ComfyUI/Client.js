// FFI bindings for Lattice.Services.ComfyUI.Client
// ComfyUI HTTP and WebSocket client implementation

// Client state storage
const clientState = new WeakMap();

// Helper to get base URL
function getBaseUrl(config) {
  const protocol = config.secure ? "https" : "http";
  return `${protocol}://${config.host}:${config.port}`;
}

// Helper to get WebSocket URL
function getWsUrl(config) {
  const protocol = config.secure ? "wss" : "ws";
  return `${protocol}://${config.host}:${config.port}/ws?clientId=${config.clientId}`;
}

// Helper for fetch with timeout
async function fetchWithTimeout(url, options, timeout) {
  const controller = new AbortController();
  const timeoutId = setTimeout(() => controller.abort(), timeout);

  try {
    const response = await fetch(url, {
      ...options,
      signal: controller.signal
    });
    clearTimeout(timeoutId);
    return response;
  } catch (error) {
    clearTimeout(timeoutId);
    throw error;
  }
}

// Helper for retry logic
async function fetchWithRetry(url, options, config) {
  let lastError;
  for (let attempt = 0; attempt < config.retryAttempts; attempt++) {
    try {
      return await fetchWithTimeout(url, options, config.timeout);
    } catch (error) {
      lastError = error;
      if (attempt < config.retryAttempts - 1) {
        await new Promise(resolve => setTimeout(resolve, config.retryDelay));
      }
    }
  }
  throw lastError;
}

//------------------------------------------------------------------------------
// Client Management
//------------------------------------------------------------------------------

export const createClientImpl = (config) => () => {
  const client = { config };
  clientState.set(client, {
    ws: null,
    listeners: new Set(),
    connected: false
  });
  return client;
};

export const disposeClientImpl = (client) => () => {
  const state = clientState.get(client);
  if (state && state.ws) {
    state.ws.close();
    state.ws = null;
  }
  clientState.delete(client);
};

export const getBaseUrlImpl = (client) => () => {
  return getBaseUrl(client.config);
};

export const getWsUrlImpl = (client) => () => {
  return getWsUrl(client.config);
};

//------------------------------------------------------------------------------
// HTTP API
//------------------------------------------------------------------------------

export const checkConnectionImpl = (client) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const url = `${getBaseUrl(client.config)}/system_stats`;
      const response = await fetchWithRetry(url, { method: "GET" }, client.config);
      resolve(response.ok);
    } catch {
      resolve(false);
    }
  });

export const getSystemStatsImpl = (client) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const url = `${getBaseUrl(client.config)}/system_stats`;
      const response = await fetchWithRetry(url, { method: "GET" }, client.config);
      if (!response.ok) {
        reject(new Error(`Failed to get system stats: ${response.status}`));
        return;
      }
      const data = await response.json();
      resolve({
        system: {
          os: data.system?.os || "unknown",
          pythonVersion: data.system?.python_version || "unknown",
          embeddedPython: data.system?.embedded_python || false
        },
        devices: (data.devices || []).map(d => ({
          name: d.name || "unknown",
          deviceType: d.type || "unknown",
          index: d.index || 0,
          vramTotal: d.vram_total || 0,
          vramFree: d.vram_free || 0,
          torchVramTotal: d.torch_vram_total || 0,
          torchVramFree: d.torch_vram_free || 0
        }))
      });
    } catch (error) {
      reject(error);
    }
  });

export const getQueueStatusImpl = (client) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const url = `${getBaseUrl(client.config)}/queue`;
      const response = await fetchWithRetry(url, { method: "GET" }, client.config);
      if (!response.ok) {
        reject(new Error(`Failed to get queue: ${response.status}`));
        return;
      }
      const data = await response.json();

      const mapQueueItem = (item) => ({
        number: item[0] || 0,
        promptId: item[1] || "",
        prompt: { clientId: item[2]?.client_id || "" }
      });

      resolve({
        queueRunning: (data.queue_running || []).map(mapQueueItem),
        queuePending: (data.queue_pending || []).map(mapQueueItem)
      });
    } catch (error) {
      reject(error);
    }
  });

export const uploadImageImpl = (client) => (file) => (filename) => (subfolder) => (overwrite) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const formData = new FormData();
      formData.append("image", file, filename);
      formData.append("subfolder", subfolder);
      formData.append("overwrite", overwrite ? "true" : "false");
      formData.append("type", "input");

      const url = `${getBaseUrl(client.config)}/upload/image`;
      const response = await fetchWithRetry(url, {
        method: "POST",
        body: formData
      }, client.config);

      if (!response.ok) {
        reject(new Error(`Upload failed: ${response.status}`));
        return;
      }

      const data = await response.json();
      resolve({
        name: data.name || filename,
        subfolder: data.subfolder || subfolder,
        imageType: data.type || "input"
      });
    } catch (error) {
      reject(error);
    }
  });

export const uploadMaskImpl = (client) => (file) => (filename) => (originalRef) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const formData = new FormData();
      formData.append("image", file, filename);
      formData.append("original_ref", originalRef);
      formData.append("type", "input");

      const url = `${getBaseUrl(client.config)}/upload/mask`;
      const response = await fetchWithRetry(url, {
        method: "POST",
        body: formData
      }, client.config);

      if (!response.ok) {
        reject(new Error(`Mask upload failed: ${response.status}`));
        return;
      }

      const data = await response.json();
      resolve({
        name: data.name || filename,
        subfolder: data.subfolder || "",
        imageType: data.type || "input"
      });
    } catch (error) {
      reject(error);
    }
  });

export const uploadImageDataImpl = (client) => (imageData) => (filename) => () =>
  new Promise(async (resolve, reject) => {
    try {
      // Convert ImageData to Blob via canvas
      const canvas = document.createElement("canvas");
      canvas.width = imageData.width;
      canvas.height = imageData.height;
      const ctx = canvas.getContext("2d");
      ctx.putImageData(imageData, 0, 0);

      const blob = await new Promise(res => canvas.toBlob(res, "image/png"));

      const formData = new FormData();
      formData.append("image", blob, filename);
      formData.append("type", "input");

      const url = `${getBaseUrl(client.config)}/upload/image`;
      const response = await fetchWithRetry(url, {
        method: "POST",
        body: formData
      }, client.config);

      if (!response.ok) {
        reject(new Error(`ImageData upload failed: ${response.status}`));
        return;
      }

      const data = await response.json();
      resolve({
        name: data.name || filename,
        subfolder: data.subfolder || "",
        imageType: data.type || "input"
      });
    } catch (error) {
      reject(error);
    }
  });

export const uploadCanvasImpl = (client) => (canvas) => (filename) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const blob = await new Promise(res => canvas.toBlob(res, "image/png"));

      const formData = new FormData();
      formData.append("image", blob, filename);
      formData.append("type", "input");

      const url = `${getBaseUrl(client.config)}/upload/image`;
      const response = await fetchWithRetry(url, {
        method: "POST",
        body: formData
      }, client.config);

      if (!response.ok) {
        reject(new Error(`Canvas upload failed: ${response.status}`));
        return;
      }

      const data = await response.json();
      resolve({
        name: data.name || filename,
        subfolder: data.subfolder || "",
        imageType: data.type || "input"
      });
    } catch (error) {
      reject(error);
    }
  });

export const queuePromptImpl = (client) => (workflow) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const body = {
        prompt: workflow,
        client_id: client.config.clientId
      };

      const url = `${getBaseUrl(client.config)}/prompt`;
      const response = await fetchWithRetry(url, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(body)
      }, client.config);

      if (!response.ok) {
        reject(new Error(`Queue prompt failed: ${response.status}`));
        return;
      }

      const data = await response.json();
      resolve({
        promptId: data.prompt_id || "",
        number: data.number || 0,
        nodeErrors: Object.keys(data.node_errors || {})
      });
    } catch (error) {
      reject(error);
    }
  });

export const getHistoryImpl = (client) => (promptId) => (maxItems) => () =>
  new Promise(async (resolve, reject) => {
    try {
      let url = `${getBaseUrl(client.config)}/history`;
      if (promptId) {
        url += `/${promptId}`;
      }
      if (maxItems > 0) {
        url += `?max_items=${maxItems}`;
      }

      const response = await fetchWithRetry(url, { method: "GET" }, client.config);
      if (!response.ok) {
        reject(new Error(`Get history failed: ${response.status}`));
        return;
      }

      const data = await response.json();
      const entries = Object.entries(data).map(([id, entry]) => ({
        promptId: id,
        outputs: Object.entries(entry.outputs || {}).map(([nodeId, output]) => ({
          nodeId,
          images: (output.images || []).map(img => ({
            filename: img.filename || "",
            subfolder: img.subfolder || "",
            imageType: img.type || "output"
          }))
        })),
        status: {
          completed: entry.status?.completed || false,
          statusStr: entry.status?.status_str || "unknown"
        }
      }));

      resolve(entries);
    } catch (error) {
      reject(error);
    }
  });

export const getOutputImpl = (client) => (filename) => (subfolder) => (imageType) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const params = new URLSearchParams({
        filename,
        subfolder,
        type: imageType
      });

      const url = `${getBaseUrl(client.config)}/view?${params}`;
      const response = await fetchWithRetry(url, { method: "GET" }, client.config);

      if (!response.ok) {
        reject(new Error(`Get output failed: ${response.status}`));
        return;
      }

      const blob = await response.blob();
      resolve(blob);
    } catch (error) {
      reject(error);
    }
  });

export const interruptImpl = (client) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const url = `${getBaseUrl(client.config)}/interrupt`;
      const response = await fetchWithRetry(url, { method: "POST" }, client.config);

      if (!response.ok) {
        reject(new Error(`Interrupt failed: ${response.status}`));
        return;
      }

      resolve();
    } catch (error) {
      reject(error);
    }
  });

export const clearQueueImpl = (client) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const url = `${getBaseUrl(client.config)}/queue`;
      const response = await fetchWithRetry(url, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ clear: true })
      }, client.config);

      if (!response.ok) {
        reject(new Error(`Clear queue failed: ${response.status}`));
        return;
      }

      resolve();
    } catch (error) {
      reject(error);
    }
  });

export const deleteFromQueueImpl = (client) => (promptId) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const url = `${getBaseUrl(client.config)}/queue`;
      const response = await fetchWithRetry(url, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ delete: [promptId] })
      }, client.config);

      if (!response.ok) {
        reject(new Error(`Delete from queue failed: ${response.status}`));
        return;
      }

      resolve();
    } catch (error) {
      reject(error);
    }
  });

export const getModelsImpl = (client) => (category) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const url = `${getBaseUrl(client.config)}/models/${category}`;
      const response = await fetchWithRetry(url, { method: "GET" }, client.config);

      if (!response.ok) {
        reject(new Error(`Get models failed: ${response.status}`));
        return;
      }

      const data = await response.json();
      const models = (Array.isArray(data) ? data : []).map(name => ({
        name: typeof name === "string" ? name : name.name || "",
        path: typeof name === "string" ? name : name.path || name.name || "",
        category: { tag: "ModelOther", value: category }
      }));

      resolve(models);
    } catch (error) {
      reject(error);
    }
  });

//------------------------------------------------------------------------------
// WebSocket
//------------------------------------------------------------------------------

export const connectWebSocketImpl = (client) => () =>
  new Promise((resolve, reject) => {
    const state = clientState.get(client);
    if (!state) {
      reject(new Error("Client disposed"));
      return;
    }

    if (state.ws && state.ws.readyState === WebSocket.OPEN) {
      resolve(state.ws);
      return;
    }

    const wsUrl = getWsUrl(client.config);
    const ws = new WebSocket(wsUrl);

    ws.onopen = () => {
      state.connected = true;
      resolve(ws);
    };

    ws.onerror = (error) => {
      reject(new Error("WebSocket connection failed"));
    };

    ws.onclose = () => {
      state.connected = false;
    };

    ws.onmessage = (event) => {
      try {
        const data = JSON.parse(event.data);
        state.listeners.forEach(listener => {
          try {
            listener(data)();
          } catch (e) {
            console.error("WebSocket listener error:", e);
          }
        });
      } catch {
        // Ignore non-JSON messages
      }
    };

    state.ws = ws;
  });

export const disconnectWebSocketImpl = (client) => () => {
  const state = clientState.get(client);
  if (state && state.ws) {
    state.ws.close();
    state.ws = null;
    state.connected = false;
  }
};

export const isWebSocketConnectedImpl = (client) => () => {
  const state = clientState.get(client);
  return state ? state.connected : false;
};

export const onMessageImpl = (client) => (callback) => () => {
  const state = clientState.get(client);
  if (!state) return () => {};

  state.listeners.add(callback);

  // Return unsubscribe function
  return () => {
    state.listeners.delete(callback);
  };
};

export const offMessageImpl = (client) => (callback) => () => {
  const state = clientState.get(client);
  if (state) {
    state.listeners.delete(callback);
  }
};

//------------------------------------------------------------------------------
// Convenience Methods
//------------------------------------------------------------------------------

export const waitForPromptImpl = (client) => (promptId) => (timeout) => () =>
  new Promise(async (resolve, reject) => {
    const state = clientState.get(client);
    if (!state) {
      reject(new Error("Client disposed"));
      return;
    }

    const outputs = [];
    let resolved = false;

    const timeoutId = setTimeout(() => {
      if (!resolved) {
        resolved = true;
        cleanup();
        reject(new Error("Timeout waiting for prompt"));
      }
    }, timeout);

    const listener = (data) => () => {
      if (resolved) return;

      if (data.type === "executed" && data.data?.prompt_id === promptId) {
        const images = (data.data.output?.images || []).map(img => ({
          filename: img.filename || "",
          subfolder: img.subfolder || "",
          imageType: img.type || "output"
        }));
        outputs.push(...images);
      }

      if (data.type === "executing" &&
          data.data?.prompt_id === promptId &&
          data.data?.node === null) {
        // Execution complete
        resolved = true;
        cleanup();
        resolve(outputs);
      }

      if (data.type === "execution_error" && data.data?.prompt_id === promptId) {
        resolved = true;
        cleanup();
        reject(new Error(data.data.exception_message || "Execution error"));
      }
    };

    const cleanup = () => {
      clearTimeout(timeoutId);
      state.listeners.delete(listener);
    };

    state.listeners.add(listener);

    // Connect WebSocket if not connected
    if (!state.ws || state.ws.readyState !== WebSocket.OPEN) {
      try {
        await connectWebSocketImpl(client)();
      } catch (error) {
        cleanup();
        reject(error);
      }
    }
  });

export const executeWorkflowImpl = (client) => (workflow) => (timeout) => () =>
  new Promise(async (resolve, reject) => {
    try {
      // Queue the prompt
      const promptResponse = await queuePromptImpl(client)(workflow)();

      if (promptResponse.nodeErrors.length > 0) {
        reject(new Error(`Node errors: ${promptResponse.nodeErrors.join(", ")}`));
        return;
      }

      // Wait for completion
      const outputs = await waitForPromptImpl(client)(promptResponse.promptId)(timeout)();
      resolve(outputs);
    } catch (error) {
      reject(error);
    }
  });
