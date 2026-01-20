/**
 * ComfyUI API Client
 * HTTP and WebSocket client for ComfyUI server communication
 */

import type {
  ComfyUIHistoryEntry,
  ComfyUIPromptResult,
  ComfyUIWorkflow,
  GenerationProgress,
} from "@/types/export";
import { parseAndSanitize } from "@/services/security/jsonSanitizer";
import { createLogger } from "@/utils/logger";
import { secureUUID } from "@/utils/security";

// ============================================================================
// Types
// ============================================================================

export interface ComfyUIClientConfig {
  serverAddress: string;
  clientId?: string;
}

const comfyLogger = createLogger("ComfyUI");

export interface UploadResult {
  name: string;
  subfolder: string;
  type: string;
}

export interface SystemStats {
  system: {
    os: string;
    python_version: string;
    embedded_python: boolean;
  };
  devices: Array<{
    name: string;
    type: string;
    index: number;
    vram_total: number;
    vram_free: number;
    torch_vram_total: number;
    torch_vram_free: number;
  }>;
}

export interface QueueStatus {
  exec_info: {
    queue_remaining: number;
  };
}

// ============================================================================
// ComfyUI API Client
// ============================================================================

export class ComfyUIClient {
  private serverAddress: string;
  private clientId: string;
  private ws: WebSocket | null = null;
  private messageHandlers: Map<string, (data: unknown) => void> = new Map();

  constructor(config: ComfyUIClientConfig) {
    this.serverAddress = config.serverAddress.replace(/\/$/, "");
    this.clientId = config.clientId || this.generateClientId();
  }

  private generateClientId(): string {
    // Use cryptographically secure UUID generation
    return `lattice_${secureUUID()}`;
  }

  // ============================================================================
  // HTTP Endpoints
  // ============================================================================

  /**
   * Check server connectivity
   */
  async checkConnection(): Promise<boolean> {
    try {
      const response = await fetch(
        `http://${this.serverAddress}/system_stats`,
        {
          method: "GET",
          signal: AbortSignal.timeout(5000),
        },
      );
      return response.ok;
    } catch {
      return false;
    }
  }

  /**
   * Get system stats (GPU, memory, etc.)
   */
  async getSystemStats(): Promise<SystemStats | null> {
    try {
      const response = await fetch(`http://${this.serverAddress}/system_stats`);
      if (!response.ok) return null;
      return response.json();
    } catch {
      return null;
    }
  }

  /**
   * Get queue status
   */
  async getQueueStatus(): Promise<QueueStatus | null> {
    try {
      const response = await fetch(`http://${this.serverAddress}/prompt`);
      if (!response.ok) return null;
      return response.json();
    } catch {
      return null;
    }
  }

  /**
   * Upload image to ComfyUI input folder
   */
  async uploadImage(
    imageData: Blob | File,
    filename: string,
    type: "input" | "temp" = "input",
    subfolder?: string,
    overwrite: boolean = true,
  ): Promise<UploadResult> {
    const formData = new FormData();
    formData.append("image", imageData, filename);
    formData.append("type", type);
    formData.append("overwrite", overwrite.toString());
    if (subfolder) {
      formData.append("subfolder", subfolder);
    }

    const response = await fetch(`http://${this.serverAddress}/upload/image`, {
      method: "POST",
      body: formData,
    });

    if (!response.ok) {
      const error = await response.text();
      throw new Error(`Failed to upload image: ${error}`);
    }

    return response.json();
  }

  /**
   * Upload mask image
   */
  async uploadMask(
    maskData: Blob | File,
    filename: string,
    originalRef: { filename: string; subfolder?: string; type?: string },
  ): Promise<UploadResult> {
    const formData = new FormData();
    formData.append("image", maskData, filename);
    formData.append("original_ref", JSON.stringify(originalRef));
    formData.append("type", "input");

    const response = await fetch(`http://${this.serverAddress}/upload/mask`, {
      method: "POST",
      body: formData,
    });

    if (!response.ok) {
      throw new Error(`Failed to upload mask: ${await response.text()}`);
    }

    return response.json();
  }

  /**
   * Queue a workflow for execution
   */
  async queuePrompt(
    workflow: ComfyUIWorkflow,
    extraData?: Record<string, string | number | boolean>,
  ): Promise<ComfyUIPromptResult> {
    const payload = {
      prompt: workflow,
      client_id: this.clientId,
      extra_data: extraData,
    };

    const response = await fetch(`http://${this.serverAddress}/prompt`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(payload),
    });

    if (!response.ok) {
      const error = await response.text();
      throw new Error(`Failed to queue prompt: ${error}`);
    }

    return response.json();
  }

  /**
   * Get execution history for a prompt
   */
  async getHistory(
    promptId?: string,
  ): Promise<Record<string, ComfyUIHistoryEntry>> {
    const url = promptId
      ? `http://${this.serverAddress}/history/${promptId}`
      : `http://${this.serverAddress}/history`;

    const response = await fetch(url);

    if (!response.ok) {
      throw new Error(`Failed to get history: ${await response.text()}`);
    }

    return response.json();
  }

  /**
   * Get a specific output image/video
   */
  async getOutput(
    filename: string,
    subfolder: string = "",
    type: "output" | "temp" | "input" = "output",
  ): Promise<Blob> {
    const params = new URLSearchParams({
      filename,
      subfolder,
      type,
    });

    const response = await fetch(`http://${this.serverAddress}/view?${params}`);

    if (!response.ok) {
      throw new Error(`Failed to get output: ${await response.text()}`);
    }

    return response.blob();
  }

  /**
   * Get output as data URL
   */
  async getOutputAsDataURL(
    filename: string,
    subfolder: string = "",
    type: "output" | "temp" | "input" = "output",
  ): Promise<string> {
    const blob = await this.getOutput(filename, subfolder, type);
    return new Promise((resolve, reject) => {
      const reader = new FileReader();
      reader.onloadend = () => resolve(reader.result as string);
      reader.onerror = reject;
      reader.readAsDataURL(blob);
    });
  }

  /**
   * Cancel current execution
   */
  async interrupt(): Promise<void> {
    const response = await fetch(`http://${this.serverAddress}/interrupt`, {
      method: "POST",
    });

    if (!response.ok) {
      throw new Error(`Failed to interrupt: ${await response.text()}`);
    }
  }

  /**
   * Clear queue
   */
  async clearQueue(): Promise<void> {
    const response = await fetch(`http://${this.serverAddress}/queue`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ clear: true }),
    });

    if (!response.ok) {
      throw new Error(`Failed to clear queue: ${await response.text()}`);
    }
  }

  /**
   * Delete item from queue
   */
  async deleteFromQueue(
    deleteType: "queue" | "history",
    ids: string[],
  ): Promise<void> {
    const response = await fetch(`http://${this.serverAddress}/${deleteType}`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ delete: ids }),
    });

    if (!response.ok) {
      throw new Error(
        `Failed to delete from ${deleteType}: ${await response.text()}`,
      );
    }
  }

  /**
   * Get available models
   */
  async getModels(
    type: "checkpoints" | "loras" | "vae" | "controlnet",
  ): Promise<string[]> {
    const folderMap: Record<string, string> = {
      checkpoints: "checkpoints",
      loras: "loras",
      vae: "vae",
      controlnet: "controlnet",
    };

    const response = await fetch(
      `http://${this.serverAddress}/models/${folderMap[type]}`,
    );

    if (!response.ok) {
      return [];
    }

    return response.json();
  }

  /**
   * Get available ControlNet models
   */
  async getControlNetModels(): Promise<string[]> {
    return this.getModels("controlnet");
  }

  // ============================================================================
  // WebSocket Connection
  // ============================================================================

  /**
   * Connect WebSocket for real-time progress updates
   */
  connectWebSocket(): Promise<void> {
    return new Promise((resolve, reject) => {
      const wsUrl = `ws://${this.serverAddress}/ws?clientId=${this.clientId}`;

      this.ws = new WebSocket(wsUrl);

      this.ws.onopen = () => {
        comfyLogger.debug("WebSocket connected");
        resolve();
      };

      this.ws.onerror = (event) => {
        comfyLogger.error("WebSocket error:", event);
        reject(new Error("WebSocket connection failed"));
      };

      this.ws.onclose = () => {
        comfyLogger.debug("WebSocket disconnected");
        this.ws = null;
      };

      this.ws.onmessage = (event) => {
        const result = parseAndSanitize(event.data);
        if (result.valid) {
          this.handleWebSocketMessage(result.data);
        } else {
          comfyLogger.error("Failed to parse WebSocket message:", result.error);
        }
      };
    });
  }

  /**
   * Disconnect WebSocket
   */
  disconnectWebSocket(): void {
    if (this.ws) {
      this.ws.close();
      this.ws = null;
    }
    this.messageHandlers.clear();
  }

  /**
   * Clean up all resources (WebSocket, handlers)
   * Call this when the client is no longer needed
   */
  destroy(): void {
    this.disconnectWebSocket();
    comfyLogger.debug("ComfyUI client destroyed");
  }

  /**
   * Check if WebSocket is connected
   */
  isWebSocketConnected(): boolean {
    return this.ws !== null && this.ws.readyState === WebSocket.OPEN;
  }

  /**
   * Register a message handler for a specific message type
   */
  onMessage(type: string, handler: (data: unknown) => void): void {
    this.messageHandlers.set(type, handler);
  }

  /**
   * Remove a message handler
   */
  offMessage(type: string): void {
    this.messageHandlers.delete(type);
  }

  private handleWebSocketMessage(data: unknown): void {
    if (typeof data !== "object" || data === null || !("type" in data)) return;
    const { type } = data as { type: string };

    // Call registered handler
    const handler = this.messageHandlers.get(type);
    if (handler) {
      handler(data);
    }

    // Also call 'all' handler if registered
    const allHandler = this.messageHandlers.get("all");
    if (allHandler) {
      allHandler(data);
    }
  }

  // ============================================================================
  // Convenience Methods
  // ============================================================================

  /**
   * Upload an ImageData object as PNG
   */
  async uploadImageData(
    imageData: ImageData,
    filename: string,
    subfolder?: string,
  ): Promise<UploadResult> {
    // Convert ImageData to PNG blob using canvas
    const canvas = new OffscreenCanvas(imageData.width, imageData.height);
    const ctx = canvas.getContext("2d")!;
    ctx.putImageData(imageData, 0, 0);
    const blob = await canvas.convertToBlob({ type: "image/png" });

    return this.uploadImage(blob, filename, "input", subfolder);
  }

  /**
   * Upload a canvas as PNG
   */
  async uploadCanvas(
    canvas: HTMLCanvasElement | OffscreenCanvas,
    filename: string,
    subfolder?: string,
  ): Promise<UploadResult> {
    let blob: Blob;

    if (canvas instanceof OffscreenCanvas) {
      blob = await canvas.convertToBlob({ type: "image/png" });
    } else {
      blob = await new Promise<Blob>((resolve, reject) => {
        canvas.toBlob((b) => {
          if (b) resolve(b);
          else reject(new Error("Failed to convert canvas to blob"));
        }, "image/png");
      });
    }

    return this.uploadImage(blob, filename, "input", subfolder);
  }

  /**
   * Wait for a prompt to complete
   */
  async waitForPrompt(
    promptId: string,
    onProgress?: (progress: GenerationProgress) => void,
    timeoutMs: number = 300000, // 5 minutes default
  ): Promise<ComfyUIHistoryEntry> {
    const startTime = Date.now();

    // Ensure WebSocket is connected
    if (!this.isWebSocketConnected()) {
      await this.connectWebSocket();
    }

    return new Promise((resolve, reject) => {
      let completed = false;

      const cleanup = () => {
        this.offMessage("progress");
        this.offMessage("executing");
        this.offMessage("executed");
        this.offMessage("execution_error");
      };

      const checkTimeout = () => {
        if (Date.now() - startTime > timeoutMs) {
          cleanup();
          reject(new Error("Prompt execution timed out"));
        }
      };

      // Progress updates
      this.onMessage("progress", (data) => {
        checkTimeout();
        if (typeof data === "object" && data !== null && "data" in data) {
          const progressData = data.data as { value: number; max: number };
          onProgress?.({
            status: "executing",
            currentStep: progressData.value,
            totalSteps: progressData.max,
            percentage: (progressData.value / progressData.max) * 100,
          });
        }
      });

      // Node execution
      this.onMessage("executing", (data) => {
        checkTimeout();
        if (typeof data === "object" && data !== null && "data" in data) {
          const execData = data.data as { prompt_id?: string; node?: string };
          if (execData.prompt_id === promptId) {
            onProgress?.({
              status: "executing",
              currentNode: execData.node,
              percentage: 10, // Approximate
            });
          }
        }
      });

      // Completion
      this.onMessage("executed", async (data) => {
        if (typeof data === "object" && data !== null && "data" in data) {
          const execData = data.data as { prompt_id?: string };
          if (execData.prompt_id === promptId && !completed) {
            completed = true;
            cleanup();

            onProgress?.({
              status: "completed",
              percentage: 100,
            });

            // Fetch final history
            const history = await this.getHistory(promptId);
            resolve(history[promptId]);
          }
        }
      });

      // Error
      this.onMessage("execution_error", (data) => {
        if (typeof data === "object" && data !== null && "data" in data) {
          const errorData = data.data as { prompt_id?: string; exception_message?: string };
          if (errorData.prompt_id === promptId) {
            cleanup();

            onProgress?.({
              status: "error",
              percentage: 0,
            });

            reject(new Error(errorData.exception_message || "Execution failed"));
          }
        }
      });
    });
  }

  /**
   * Execute a workflow and wait for completion
   */
  async executeWorkflow(
    workflow: ComfyUIWorkflow,
    onProgress?: (progress: GenerationProgress) => void,
  ): Promise<{
    promptId: string;
    history: ComfyUIHistoryEntry;
    outputs: Array<{ filename: string; subfolder: string; type: string }>;
  }> {
    // Queue the prompt
    const { prompt_id } = await this.queuePrompt(workflow);

    onProgress?.({
      status: "queued",
      percentage: 0,
    });

    // Wait for completion
    const history = await this.waitForPrompt(prompt_id, onProgress);

    // Collect outputs
    const outputs: Array<{
      filename: string;
      subfolder: string;
      type: string;
    }> = [];

    for (const nodeOutputs of Object.values(history.outputs)) {
      if (nodeOutputs.images) {
        outputs.push(...nodeOutputs.images);
      }
      if (nodeOutputs.gifs) {
        outputs.push(...nodeOutputs.gifs);
      }
    }

    return {
      promptId: prompt_id,
      history,
      outputs,
    };
  }

  // ============================================================================
  // Getters
  // ============================================================================

  get server(): string {
    return this.serverAddress;
  }

  get id(): string {
    return this.clientId;
  }
}

// ============================================================================
// Singleton Instance
// ============================================================================

let defaultClient: ComfyUIClient | null = null;

export function getComfyUIClient(serverAddress?: string): ComfyUIClient {
  if (
    !defaultClient ||
    (serverAddress && serverAddress !== defaultClient.server)
  ) {
    defaultClient = new ComfyUIClient({
      serverAddress: serverAddress || "127.0.0.1:8188",
    });
  }
  return defaultClient;
}

export function setComfyUIServer(serverAddress: string): void {
  defaultClient = new ComfyUIClient({ serverAddress });
}
