/**
 * ComfyUI Services Index
 * Central export point for ComfyUI integration
 */

// ComfyUI client
export {
  ComfyUIClient,
  getComfyUIClient,
  setComfyUIServer,
  type ComfyUIClientConfig,
  type UploadResult,
  type SystemStats,
  type QueueStatus,
} from './comfyuiClient';

// Workflow templates
export {
  generateWan22I2VWorkflow,
  generateWan22FunCameraWorkflow,
  generateWan22FirstLastWorkflow,
  generateUni3CWorkflow,
  generateMotionCtrlWorkflow,
  generateControlNetDepthWorkflow,
  generateAnimateDiffCameraCtrlWorkflow,
  generateCogVideoXWorkflow,
  generateControlNetWorkflow,
  generateTTMWorkflow,
  generateWanMoveWorkflow,
  generateATIWorkflow,
  generateLightXWorkflow,
  generateSCAILWorkflow,
  generateWorkflowForTarget,
  injectParameters,
  validateWorkflow,
  getWorkflowInputNodes,
  getWorkflowOutputNodes,
  type WorkflowParams,
} from './workflowTemplates';
