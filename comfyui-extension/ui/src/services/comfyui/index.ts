/**
 * ComfyUI Services Index
 * Central export point for ComfyUI integration
 */

// ComfyUI client
export {
  ComfyUIClient,
  type ComfyUIClientConfig,
  getComfyUIClient,
  type QueueStatus,
  type SystemStats,
  setComfyUIServer,
  type UploadResult,
} from "./comfyuiClient";

// Workflow templates
export {
  generateAnimateDiffCameraCtrlWorkflow,
  generateCogVideoXWorkflow,
  generateControlNetDepthWorkflow,
  generateControlNetWorkflow,
  generateMotionCtrlWorkflow,
  generateUni3CWorkflow,
  generateWan22FirstLastWorkflow,
  generateWan22FunCameraWorkflow,
  generateWan22I2VWorkflow,
  generateWorkflowForTarget,
  getWorkflowInputNodes,
  getWorkflowOutputNodes,
  injectParameters,
  validateWorkflow,
  type WorkflowParams,
} from "./workflowTemplates";
