/**
 * AI Services Index
 *
 * Exports all AI-related services for the Lattice Compositor.
 */

export type {
  AIAgentConfig,
  AIAgentState,
  AIMessage,
} from "./AICompositorAgent";
// Main agent
export { AICompositorAgent, getAIAgent } from "./AICompositorAgent";
// Action executor
export { executeToolCall } from "./actionExecutor";
export type {
  CameraMotionAnalysisRequest,
  CameraMotionAnalysisResult,
  CameraMotionPrimitive,
  DepthBasedTrackingRequest,
  Uni3CCameraData,
} from "./cameraTrackingAI";
// Camera tracking AI
export {
  analyzeHybrid,
  analyzeWithVLM,
  CAMERA_MOTION_SYSTEM_PROMPT,
  estimateCameraPosesFromDepth,
  exportToUni3CFormat,
  MOTION_TO_TRAJECTORY,
  parseUni3CFormat,
} from "./cameraTrackingAI";
export type {
  DepthEstimationOptions,
  DepthEstimationResult,
  LayerAnalysisInput,
  LayerDepthEstimate,
  LLMProvider,
} from "./depthEstimation";
// Depth estimation
export {
  estimateDepthsHeuristic,
  getLLMDepthEstimator,
  LLMDepthEstimator,
} from "./depthEstimation";
export type {
  SapiensBodyPart,
  SapiensConfig,
  SapiensDepthResult,
  SapiensKeypoint,
  SapiensModelSize,
  SapiensNormalResult,
  SapiensPoseResult,
  SapiensSegmentationResult,
  SapiensTask,
} from "./sapiensIntegration";
// Sapiens integration (Meta AI foundation models for human vision)
export {
  createUni3CCameraData,
  DEFAULT_SAPIENS_CONFIG,
  depthToPointCloud,
  getSapiensService,
  SAPIENS_BODY_PARTS,
  SapiensService,
} from "./sapiensIntegration";
export type {
  SerializedAnimatableProperty,
  SerializedComposition,
  SerializedEffect,
  SerializedKeyframe,
  SerializedLayer,
  SerializedProjectState,
  SerializedTransform,
} from "./stateSerializer";
// State serialization
export {
  compareStates,
  generateStateSummary,
  serializeLayerDetails,
  serializeLayerList,
  serializeProjectState,
} from "./stateSerializer";
// System prompt
export { SYSTEM_PROMPT } from "./systemPrompt";
export type { ToolCall, ToolDefinition, ToolResult } from "./toolDefinitions";
// Tool definitions
export { TOOL_DEFINITIONS } from "./toolDefinitions";
