<template>
  <div class="action-approval-dialog-overlay" @click.self="emit('close')">
    <div class="action-approval-dialog">
      <div class="dialog-header">
        <h3>🔒 Agent Action Approval</h3>
        <button class="close-btn" @click="emit('close')">
          <i class="pi pi-times" />
        </button>
      </div>

      <div class="dialog-content">
        <!-- Action Plan Summary -->
        <div class="plan-summary">
          <div class="summary-header">
            <i class="pi pi-info-circle" />
            <span>Action Plan Review</span>
          </div>
          <div class="summary-content">
            <div class="summary-item">
              <strong>User Instruction:</strong>
              <p>{{ plan?.userInstruction }}</p>
            </div>
            <div class="summary-item">
              <strong>Agent Reasoning:</strong>
              <p>{{ plan?.reasoning }}</p>
            </div>
            <div class="summary-item">
              <strong>Planned Actions:</strong>
              <span class="action-count">{{ plan?.actions.length || 0 }} action(s)</span>
            </div>
          </div>
        </div>

        <!-- Actions List -->
        <div class="actions-list">
          <div
            v-for="(action, index) in plan?.actions"
            :key="action.id"
            class="action-item"
            :class="{ selected: selectedActions.has(action.id) }"
          >
            <div class="action-header">
              <label class="action-checkbox">
                <input
                  type="checkbox"
                  :checked="selectedActions.has(action.id)"
                  @change="toggleAction(action.id)"
                />
                <span class="action-number">{{ index + 1 }}</span>
              </label>
              <div class="action-info">
                <strong class="action-name">{{ action.toolName }}</strong>
                <span class="action-risk" :class="getRiskClass(action.toolName)">
                  {{ getRiskLevel(action.toolName) }}
                </span>
              </div>
            </div>
            <div class="action-reasoning">
              <i class="pi pi-question-circle" />
              <span>{{ action.reasoning }}</span>
            </div>
            <div class="action-args">
              <details>
                <summary>Arguments</summary>
                <pre>{{ JSON.stringify(action.arguments, null, 2) }}</pre>
              </details>
            </div>
          </div>
        </div>

        <!-- Approval Options -->
        <div class="approval-options">
          <div class="option-group">
            <label class="checkbox-label">
              <input
                type="checkbox"
                v-model="approveAll"
                @change="handleApproveAll"
              />
              <span>Approve all actions</span>
            </label>
          </div>
          <div class="option-group">
            <label>Comment (optional)</label>
            <textarea
              v-model="comment"
              placeholder="Add a comment about this approval..."
              rows="3"
            />
          </div>
        </div>
      </div>

      <div class="dialog-footer">
        <button class="btn btn-secondary" @click="handleDeny">
          <i class="pi pi-times" />
          Deny All
        </button>
        <button
          class="btn btn-primary"
          @click="handleApprove"
          :disabled="selectedActions.size === 0"
        >
          <i class="pi pi-check" />
          Approve Selected ({{ selectedActions.size }})
        </button>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted } from "vue";
import { actionApproval, type ActionPlan } from "@/services/ai/security/actionApproval";
import { hardenedScopeManager } from "@/services/ai/security/hardenedScopeManager";

// ============================================================================
// PROPS & EMITS
// ============================================================================

interface Props {
  planId: string;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  close: [];
  approved: [planId: string, approvedActionIds: string[]];
  denied: [planId: string];
}>();

// ============================================================================
// STATE
// ============================================================================

const plan = ref<ActionPlan | null>(null);
const selectedActions = ref<Set<string>>(new Set());
const approveAll = ref(false);
const comment = ref("");

// ============================================================================
// COMPUTED
// ============================================================================

// ============================================================================
// METHODS
// ============================================================================

function getRiskLevel(toolName: string): string {
  // Map tool names to risk levels (simplified - would use toolDefinitions in production)
  if (toolName === "deleteLayer" || toolName === "decomposeImage" || toolName === "vectorizeImage") {
    return "HIGH";
  }
  if (toolName === "createLayer" || toolName === "setLayerProperty") {
    return "LOW";
  }
  return "MEDIUM";
}

function getRiskClass(toolName: string): string {
  const level = getRiskLevel(toolName);
  return `risk-${level.toLowerCase()}`;
}

function toggleAction(actionId: string): void {
  if (selectedActions.value.has(actionId)) {
    selectedActions.value.delete(actionId);
  } else {
    selectedActions.value.add(actionId);
  }
  approveAll.value = selectedActions.value.size === plan.value?.actions.length;
}

function handleApproveAll(): void {
  if (approveAll.value && plan.value) {
    selectedActions.value = new Set(plan.value.actions.map((a) => a.id));
  } else {
    selectedActions.value.clear();
  }
}

function handleApprove(): void {
  if (!plan.value || selectedActions.value.size === 0) {
    return;
  }

  const approvedActionIds = Array.from(selectedActions.value);
  actionApproval.approvePlan({
    planId: plan.value.id,
    approved: true,
    approvedActionIds,
    comment: comment.value || undefined,
  });

  emit("approved", plan.value.id, approvedActionIds);
  emit("close");
}

function handleDeny(): void {
  if (!plan.value) {
    return;
  }

  actionApproval.denyPlan(plan.value.id, comment.value || undefined);
  emit("denied", plan.value.id);
  emit("close");
}

// ============================================================================
// LIFECYCLE
// ============================================================================

onMounted(() => {
  const loadedPlan = actionApproval.getActionPlan(props.planId);
  if (!loadedPlan) {
    console.error(`[ActionApprovalDialog] Plan "${props.planId}" not found`);
    emit("close");
    return;
  }

  plan.value = loadedPlan;

  // Auto-select all actions by default
  selectedActions.value = new Set(loadedPlan.actions.map((a) => a.id));
  approveAll.value = true;
});
</script>

<style scoped>
.action-approval-dialog-overlay {
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

.action-approval-dialog {
  background: var(--bg-primary);
  border-radius: 8px;
  width: 90%;
  max-width: 800px;
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

.plan-summary {
  background: var(--bg-secondary);
  border-radius: 6px;
  padding: 1rem;
  margin-bottom: 1.5rem;
}

.summary-header {
  display: flex;
  align-items: center;
  gap: 0.5rem;
  margin-bottom: 1rem;
  font-weight: 600;
  color: var(--text-primary);
}

.summary-item {
  margin-bottom: 0.75rem;
}

.summary-item strong {
  display: block;
  margin-bottom: 0.25rem;
  color: var(--text-secondary);
  font-size: 0.875rem;
}

.summary-item p {
  margin: 0;
  color: var(--text-primary);
}

.action-count {
  font-weight: 600;
  color: var(--accent-color);
}

.actions-list {
  display: flex;
  flex-direction: column;
  gap: 1rem;
  margin-bottom: 1.5rem;
}

.action-item {
  border: 2px solid var(--border-color);
  border-radius: 6px;
  padding: 1rem;
  background: var(--bg-secondary);
  transition: all 0.2s;
}

.action-item.selected {
  border-color: var(--accent-color);
  background: var(--bg-tertiary);
}

.action-header {
  display: flex;
  align-items: center;
  gap: 1rem;
  margin-bottom: 0.75rem;
}

.action-checkbox {
  display: flex;
  align-items: center;
  cursor: pointer;
}

.action-checkbox input {
  margin-right: 0.5rem;
}

.action-number {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  width: 24px;
  height: 24px;
  background: var(--bg-tertiary);
  border-radius: 4px;
  font-weight: 600;
  font-size: 0.875rem;
}

.action-info {
  flex: 1;
  display: flex;
  align-items: center;
  justify-content: space-between;
}

.action-name {
  font-family: monospace;
  color: var(--text-primary);
}

.action-risk {
  padding: 0.25rem 0.5rem;
  border-radius: 4px;
  font-size: 0.75rem;
  font-weight: 600;
}

.risk-low {
  background: rgba(34, 197, 94, 0.2);
  color: rgb(34, 197, 94);
}

.risk-medium {
  background: rgba(251, 191, 36, 0.2);
  color: rgb(251, 191, 36);
}

.risk-high {
  background: rgba(239, 68, 68, 0.2);
  color: rgb(239, 68, 68);
}

.action-reasoning {
  display: flex;
  align-items: start;
  gap: 0.5rem;
  margin-bottom: 0.5rem;
  color: var(--text-secondary);
  font-size: 0.875rem;
}

.action-args {
  margin-top: 0.5rem;
}

.action-args details {
  cursor: pointer;
  color: var(--text-secondary);
  font-size: 0.75rem;
}

.action-args pre {
  margin-top: 0.5rem;
  padding: 0.5rem;
  background: var(--bg-primary);
  border-radius: 4px;
  overflow-x: auto;
  font-size: 0.75rem;
}

.approval-options {
  border-top: 1px solid var(--border-color);
  padding-top: 1rem;
}

.option-group {
  margin-bottom: 1rem;
}

.option-group label {
  display: block;
  margin-bottom: 0.5rem;
  font-weight: 500;
}

.checkbox-label {
  display: flex;
  align-items: center;
  gap: 0.5rem;
  cursor: pointer;
}

textarea {
  width: 100%;
  padding: 0.5rem;
  border: 1px solid var(--border-color);
  border-radius: 4px;
  background: var(--bg-primary);
  color: var(--text-primary);
  font-family: inherit;
  resize: vertical;
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

.btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.btn-secondary {
  background: var(--bg-secondary);
  color: var(--text-primary);
}

.btn-secondary:hover:not(:disabled) {
  background: var(--bg-tertiary);
}

.btn-primary {
  background: var(--accent-color);
  color: white;
}

.btn-primary:hover:not(:disabled) {
  opacity: 0.9;
}
</style>
