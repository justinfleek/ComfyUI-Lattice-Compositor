<template>
  <div class="action-plan-review-overlay" @click.self="emit('close')">
    <div class="action-plan-review">
      <div class="dialog-header">
        <h3>📋 Action Plan Review</h3>
        <button class="close-btn" @click="emit('close')">
          <i class="pi pi-times" />
        </button>
      </div>

      <div class="dialog-content">
        <!-- Plan Overview -->
        <div class="plan-overview">
          <div class="overview-section">
            <div class="section-header">
              <i class="pi pi-user" />
              <span>User Request</span>
            </div>
            <p class="user-instruction">{{ plan?.userInstruction }}</p>
          </div>

          <div class="overview-section">
            <div class="section-header">
              <i class="pi pi-brain" />
              <span>Agent Reasoning</span>
            </div>
            <p class="agent-reasoning">{{ plan?.reasoning }}</p>
          </div>

          <div class="overview-section">
            <div class="section-header">
              <i class="pi pi-list" />
              <span>Planned Actions</span>
            </div>
            <div class="actions-summary">
              <div class="summary-stat">
                <span class="stat-value">{{ plan?.actions.length || 0 }}</span>
                <span class="stat-label">Total Actions</span>
              </div>
              <div class="summary-stat">
                <span class="stat-value">{{ highRiskCount }}</span>
                <span class="stat-label">High Risk</span>
              </div>
              <div class="summary-stat">
                <span class="stat-value">{{ mediumRiskCount }}</span>
                <span class="stat-label">Medium Risk</span>
              </div>
            </div>
          </div>
        </div>

        <!-- Actions Timeline -->
        <div class="actions-timeline">
          <div class="timeline-header">
            <h4>Action Sequence</h4>
            <small>Review each action before approval</small>
          </div>
          <div class="timeline-items">
            <div
              v-for="(action, index) in plan?.actions"
              :key="action.id"
              class="timeline-item"
            >
              <div class="timeline-marker">
                <div class="marker-number">{{ index + 1 }}</div>
                <div class="marker-line" v-if="index < (plan?.actions.length || 0) - 1" />
              </div>
              <div class="timeline-content">
                <div class="action-card">
                  <div class="action-title">
                    <span class="action-icon">
                      <i :class="getActionIcon(action.toolName)" />
                    </span>
                    <div class="action-title-text">
                      <strong>{{ action.toolName }}</strong>
                      <span class="action-scope" :class="getScopeClass(action.requiredScope)">
                        {{ action.requiredScope || "standard" }}
                      </span>
                    </div>
                  </div>
                  <div class="action-reasoning">
                    <i class="pi pi-lightbulb" />
                    <span>{{ action.reasoning }}</span>
                  </div>
                  <div class="action-preview">
                    <details>
                      <summary>View Arguments</summary>
                      <pre>{{ JSON.stringify(action.arguments, null, 2) }}</pre>
                    </details>
                  </div>
                </div>
              </div>
            </div>
          </div>
        </div>

        <!-- Sandbox Preview -->
        <div class="sandbox-preview" v-if="sandboxDiff">
          <div class="preview-header">
            <i class="pi pi-code" />
            <span>Preview Changes</span>
          </div>
          <div class="preview-content">
            <div v-if="sandboxDiff.layersAdded.length > 0" class="diff-section">
              <strong>Layers to Add:</strong>
              <ul>
                <li v-for="layerId in sandboxDiff.layersAdded" :key="layerId">
                  {{ layerId }}
                </li>
              </ul>
            </div>
            <div v-if="sandboxDiff.layersRemoved.length > 0" class="diff-section">
              <strong>Layers to Remove:</strong>
              <ul>
                <li v-for="layerId in sandboxDiff.layersRemoved" :key="layerId">
                  {{ layerId }}
                </li>
              </ul>
            </div>
            <div v-if="sandboxDiff.layersModified.length > 0" class="diff-section">
              <strong>Layers to Modify:</strong>
              <ul>
                <li v-for="layerId in sandboxDiff.layersModified" :key="layerId">
                  {{ layerId }}
                </li>
              </ul>
            </div>
            <div v-if="hasNoChanges" class="diff-empty">
              <i class="pi pi-info-circle" />
              <span>No changes detected (read-only operations)</span>
            </div>
          </div>
        </div>
      </div>

      <div class="dialog-footer">
        <button class="btn btn-secondary" @click="emit('close')">
          <i class="pi pi-times" />
          Cancel
        </button>
        <button class="btn btn-primary" @click="handleApprove">
          <i class="pi pi-check" />
          Approve & Execute
        </button>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted } from "vue";
import { actionApproval, type ActionPlan } from "@/services/ai/security/actionApproval";
import { agentSandbox, type SandboxDiff } from "@/services/ai/security/agentSandbox";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // props
// ════════════════════════════════════════════════════════════════════════════

interface Props {
  planId: string;
  sandboxId?: string;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  close: [];
  approved: [planId: string];
}>();

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // state
// ════════════════════════════════════════════════════════════════════════════

const plan = ref<ActionPlan | null>(null);
const sandboxDiff = ref<SandboxDiff | null>(null);

// ════════════════════════════════════════════════════════════════════════════
//                                                                  // computed
// ════════════════════════════════════════════════════════════════════════════

const highRiskCount = computed(() => {
  return plan.value?.actions.filter((a) =>
    ["deleteLayer", "decomposeImage", "vectorizeImage"].includes(a.toolName),
  ).length || 0;
});

const mediumRiskCount = computed(() => {
  return plan.value?.actions.filter((a) =>
    !["deleteLayer", "decomposeImage", "vectorizeImage", "getProjectState", "getLayerInfo", "findLayers"].includes(a.toolName),
  ).length || 0;
});

const hasNoChanges = computed(() => {
  if (!sandboxDiff.value) return true;
  return (
    sandboxDiff.value.layersAdded.length === 0 &&
    sandboxDiff.value.layersRemoved.length === 0 &&
    sandboxDiff.value.layersModified.length === 0
  );
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // methods
// ════════════════════════════════════════════════════════════════════════════

function getActionIcon(toolName: string): string {
  if (toolName.includes("create")) return "pi pi-plus-circle";
  if (toolName.includes("delete")) return "pi pi-trash";
  if (toolName.includes("set") || toolName.includes("update")) return "pi pi-pencil";
  if (toolName.includes("get") || toolName.includes("find")) return "pi pi-search";
  return "pi pi-cog";
}

function getScopeClass(scope?: string): string {
  const scopeValue = scope || "standard";
  return `scope-${scopeValue}`;
}

function handleApprove(): void {
  if (!plan.value) {
    return;
  }

  // Approve the plan (all actions)
  actionApproval.approvePlan({
    planId: plan.value.id,
    approved: true,
  });

  emit("approved", plan.value.id);
  emit("close");
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                 // lifecycle
// ════════════════════════════════════════════════════════════════════════════

onMounted(() => {
  const loadedPlan = actionApproval.getActionPlan(props.planId);
  if (!loadedPlan) {
    console.error(`[ActionPlanReview] Plan "${props.planId}" not found`);
    emit("close");
    return;
  }

  plan.value = loadedPlan;

  // Load sandbox diff if sandbox ID provided
  if (props.sandboxId) {
    try {
      sandboxDiff.value = agentSandbox.getSandboxDiff(props.sandboxId);
    } catch (error) {
      console.warn("[ActionPlanReview] Could not load sandbox diff:", error);
    }
  }
});
</script>

<style scoped>
.action-plan-review-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 10000;
}

.action-plan-review {
  background: var(--bg-primary);
  border-radius: 8px;
  width: 90%;
  max-width: 900px;
  max-height: 90vh;
  display: flex;
  flex-direction: column;
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.3);
}

.dialog-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 1.5rem;
  border-bottom: 1px solid var(--border-color);
}

.dialog-header h3 {
  margin: 0;
  font-size: 1.25rem;
  font-weight: 600;
}

.close-btn {
  background: none;
  border: none;
  font-size: 1.5rem;
  cursor: pointer;
  color: var(--text-secondary);
  padding: 0.25rem;
}

.close-btn:hover {
  color: var(--text-primary);
}

.dialog-content {
  padding: 1.5rem;
  overflow-y: auto;
  flex: 1;
}

.plan-overview {
  margin-bottom: 2rem;
}

.overview-section {
  margin-bottom: 1.5rem;
  padding: 1rem;
  background: var(--bg-secondary);
  border-radius: 6px;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 0.5rem;
  margin-bottom: 0.75rem;
  font-weight: 600;
  color: var(--text-primary);
}

.user-instruction,
.agent-reasoning {
  margin: 0;
  color: var(--text-secondary);
  line-height: 1.6;
}

.actions-summary {
  display: flex;
  gap: 2rem;
}

.summary-stat {
  display: flex;
  flex-direction: column;
  align-items: center;
}

.stat-value {
  font-size: 2rem;
  font-weight: 700;
  color: var(--accent-color);
}

.stat-label {
  font-size: 0.875rem;
  color: var(--text-secondary);
}

.actions-timeline {
  margin-bottom: 2rem;
}

.timeline-header {
  margin-bottom: 1rem;
}

.timeline-header h4 {
  margin: 0 0 0.25rem 0;
  font-size: 1.125rem;
}

.timeline-header small {
  color: var(--text-secondary);
}

.timeline-items {
  display: flex;
  flex-direction: column;
  gap: 1.5rem;
}

.timeline-item {
  display: flex;
  gap: 1rem;
}

.timeline-marker {
  display: flex;
  flex-direction: column;
  align-items: center;
}

.marker-number {
  width: 32px;
  height: 32px;
  border-radius: 50%;
  background: var(--accent-color);
  color: white;
  display: flex;
  align-items: center;
  justify-content: center;
  font-weight: 600;
  font-size: 0.875rem;
}

.marker-line {
  width: 2px;
  flex: 1;
  background: var(--border-color);
  margin-top: 0.5rem;
}

.timeline-content {
  flex: 1;
}

.action-card {
  background: var(--bg-secondary);
  border-radius: 6px;
  padding: 1rem;
  border: 1px solid var(--border-color);
}

.action-title {
  display: flex;
  align-items: center;
  gap: 1rem;
  margin-bottom: 0.75rem;
}

.action-icon {
  font-size: 1.5rem;
  color: var(--accent-color);
}

.action-title-text {
  flex: 1;
  display: flex;
  align-items: center;
  justify-content: space-between;
}

.action-title-text strong {
  font-family: monospace;
  color: var(--text-primary);
}

.action-scope {
  padding: 0.25rem 0.5rem;
  border-radius: 4px;
  font-size: 0.75rem;
  font-weight: 600;
}

.scope-readonly {
  background: rgba(59, 130, 246, 0.2);
  color: rgb(59, 130, 246);
}

.scope-limited {
  background: rgba(34, 197, 94, 0.2);
  color: rgb(34, 197, 94);
}

.scope-standard {
  background: rgba(251, 191, 36, 0.2);
  color: rgb(251, 191, 36);
}

.scope-full {
  background: rgba(239, 68, 68, 0.2);
  color: rgb(239, 68, 68);
}

.action-reasoning {
  display: flex;
  align-items: start;
  gap: 0.5rem;
  margin-bottom: 0.75rem;
  color: var(--text-secondary);
  font-size: 0.875rem;
}

.action-preview details {
  cursor: pointer;
  color: var(--text-secondary);
  font-size: 0.75rem;
}

.action-preview pre {
  margin-top: 0.5rem;
  padding: 0.5rem;
  background: var(--bg-primary);
  border-radius: 4px;
  overflow-x: auto;
  font-size: 0.75rem;
}

.sandbox-preview {
  border-top: 1px solid var(--border-color);
  padding-top: 1.5rem;
}

.preview-header {
  display: flex;
  align-items: center;
  gap: 0.5rem;
  margin-bottom: 1rem;
  font-weight: 600;
}

.preview-content {
  background: var(--bg-secondary);
  border-radius: 6px;
  padding: 1rem;
}

.diff-section {
  margin-bottom: 1rem;
}

.diff-section strong {
  display: block;
  margin-bottom: 0.5rem;
  color: var(--text-primary);
}

.diff-section ul {
  margin: 0;
  padding-left: 1.5rem;
  color: var(--text-secondary);
}

.diff-empty {
  display: flex;
  align-items: center;
  gap: 0.5rem;
  color: var(--text-secondary);
  font-style: italic;
}

.dialog-footer {
  display: flex;
  justify-content: flex-end;
  gap: 1rem;
  padding: 1.5rem;
  border-top: 1px solid var(--border-color);
}

.btn {
  padding: 0.75rem 1.5rem;
  border: none;
  border-radius: 6px;
  font-weight: 600;
  cursor: pointer;
  display: flex;
  align-items: center;
  gap: 0.5rem;
  transition: all 0.2s;
}

.btn-secondary {
  background: var(--bg-secondary);
  color: var(--text-primary);
}

.btn-secondary:hover {
  background: var(--bg-tertiary);
}

.btn-primary {
  background: var(--accent-color);
  color: white;
}

.btn-primary:hover {
  opacity: 0.9;
}
</style>
