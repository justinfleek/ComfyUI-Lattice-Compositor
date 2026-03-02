/**
 * AI Security Module
 *
 * BATTLE-HARDENED security utilities for LLM agent operations:
 * - Hardened scope management (default deny, time-limited elevation, kill switch)
 * - Prompt injection detection (77 patterns, homoglyphs, fragmented attacks)
 * - ComfyUI output validation (custom_node sanitization)
 *
 * SECURITY: Import this module when working with AI/LLM features.
 *
 * @see docs/SECURITY_THREAT_MODEL.md
 */

// Hardened Scope Management (RECOMMENDED)
export {
  type ScopeLevel,
  type ScopeGrant,
  type ScopeSession,
  type PendingApproval,
  type ToolPermission,
  hardenedScopeManager,
  checkTool,
  getCurrentScope,
  isLockedDown,
  activateKillSwitch,
  reportInjectionDetected,
} from "./hardenedScopeManager";

// Legacy scope management (for backwards compatibility)
export {
  type AgentScope,
  type ScopeCheckResult,
  type ToolRisk,
  SCOPE_PRESETS,
  ScopeManager,
  scopeManager,
  isToolAllowed,
  getCurrentScopeName,
  requestScopeElevation,
} from "./scopeManager";

// Prompt injection detection
export {
  type InjectionDetectionResult,
  type InjectionType,
  detectPromptInjection,
  detectFragmentedAttack,
  sanitizeForLLM,
  sanitizeObjectForLLM,
  scanForInjections,
  scanLayerForInjections,
  scanProjectForInjections,
} from "./promptInjectionDetector";

// ComfyUI validation
export {
  ComfyImageOutputSchema,
  ComfyNodeResultSchema,
  ComfyExecutionStatusSchema,
  ComfyPromptInfoSchema,
  validateComfyImageOutput,
  validateComfyNodeResult,
  validateComfyExecutionStatus,
  validateCustomNodeOutput,
  validateComfyWorkflow,
  validateImageData,
} from "./comfyOutputValidator";

// Agent Security Framework
export {
  agentSandbox,
  type SandboxState,
  type SandboxAction,
  type SandboxDiff,
} from "./agentSandbox";

export {
  actionApproval,
  type ActionPlan,
  type PlannedAction,
  type ApprovalDecision,
} from "./actionApproval";

export {
  provenanceTracker,
  type ProvenanceEntry,
  type ProvenanceQuery,
} from "./provenanceTracker";

export {
  agentRollback,
  type AgentAction,
  type RollbackPoint,
} from "./agentRollback";
