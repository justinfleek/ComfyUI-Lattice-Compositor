<!--
  @component SecurityWarningDialog
  @description Security warning shown before loading external project files.
  Warns users that project files may contain expressions that execute code.

  @features
  - Warning message about expression execution risks
  - "Don't show again" checkbox with localStorage persistence
  - Cancel/Open Anyway buttons
  - Keyboard shortcuts: Escape to cancel, Enter to proceed
-->
<template>
  <Teleport to="body">
    <div v-if="visible" class="dialog-overlay" @click.self="cancel">
      <div class="dialog-container">
        <div class="dialog-header warning">
          <span class="warning-icon">&#9888;</span>
          <h2>Security Warning</h2>
        </div>

        <div class="dialog-body">
          <p class="warning-text">
            <strong>This project file may contain expressions that will execute code.</strong>
          </p>

          <p class="explanation">
            Expressions are JavaScript code that runs when the project loads.
            A malicious project could contain code that freezes your browser.
          </p>

          <div class="file-info" v-if="fileName">
            <span class="label">File:</span>
            <span class="value">{{ fileName }}</span>
          </div>

          <div class="recommendation">
            <strong>Only open project files from sources you trust.</strong>
          </div>

          <label class="checkbox-row">
            <input type="checkbox" v-model="dontShowAgain" />
            <span>Don't show this warning again</span>
          </label>
        </div>

        <div class="dialog-footer">
          <button class="btn btn-secondary" @click="cancel">Cancel</button>
          <button class="btn btn-warning" @click="proceed">Open Anyway</button>
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { ref, onMounted, onUnmounted } from 'vue';

const props = defineProps<{
  visible: boolean;
  fileName?: string;
}>();

const emit = defineEmits<{
  (e: 'cancel'): void;
  (e: 'proceed', dontShowAgain: boolean): void;
}>();

const dontShowAgain = ref(false);

function cancel() {
  dontShowAgain.value = false; // Reset on cancel
  emit('cancel');
}

function proceed() {
  // Emit with dontShowAgain value - securityConfirmation.ts handles localStorage
  emit('proceed', dontShowAgain.value);
  dontShowAgain.value = false; // Reset for next use
}

// Keyboard shortcut handler
function handleKeyDown(e: KeyboardEvent) {
  if (!props.visible) return;

  if (e.key === 'Escape') {
    cancel();
  } else if (e.key === 'Enter') {
    proceed();
  }
}

onMounted(() => {
  document.addEventListener('keydown', handleKeyDown);
});

onUnmounted(() => {
  document.removeEventListener('keydown', handleKeyDown);
});
</script>

<style scoped>
.dialog-overlay {
  position: fixed;
  inset: 0;
  background: rgba(0, 0, 0, 0.8);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 10000;
}

.dialog-container {
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-warning, #f59e0b);
  border-radius: var(--lattice-radius-lg, 8px);
  box-shadow: 0 8px 32px rgba(245, 158, 11, 0.2);
  min-width: 420px;
  max-width: 500px;
}

.dialog-header {
  display: flex;
  align-items: center;
  gap: 12px;
  padding: 16px 20px;
  border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);
  background: rgba(245, 158, 11, 0.1);
}

.dialog-header.warning {
  border-bottom-color: var(--lattice-warning, #f59e0b);
}

.warning-icon {
  font-size: 24px;
  color: var(--lattice-warning, #f59e0b);
}

.dialog-header h2 {
  margin: 0;
  font-size: 16px;
  font-weight: 600;
  color: var(--lattice-warning, #f59e0b);
}

.dialog-body {
  padding: 20px;
  display: flex;
  flex-direction: column;
  gap: 16px;
}

.warning-text {
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 14px;
  margin: 0;
  line-height: 1.5;
}

.explanation {
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 13px;
  margin: 0;
  line-height: 1.5;
}

.file-info {
  background: var(--lattice-surface-1, #121212);
  border-radius: var(--lattice-radius-md, 4px);
  padding: 10px 14px;
  display: flex;
  gap: 8px;
}

.file-info .label {
  color: var(--lattice-text-muted, #6b7280);
  font-size: 12px;
}

.file-info .value {
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 12px;
  font-family: monospace;
  word-break: break-all;
}

.recommendation {
  background: rgba(245, 158, 11, 0.1);
  border-left: 3px solid var(--lattice-warning, #f59e0b);
  padding: 12px 14px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 13px;
}

.checkbox-row {
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 13px;
  padding-top: 8px;
  border-top: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.checkbox-row input {
  width: 16px;
  height: 16px;
  accent-color: var(--lattice-warning, #f59e0b);
}

.dialog-footer {
  display: flex;
  justify-content: flex-end;
  gap: 8px;
  padding: 16px 20px;
  border-top: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.btn {
  padding: 8px 16px;
  border-radius: var(--lattice-radius-md, 4px);
  font-size: 13px;
  font-weight: 500;
  cursor: pointer;
  transition: all 0.15s ease;
}

.btn-secondary {
  background: var(--lattice-surface-3, #222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  color: var(--lattice-text-secondary, #9ca3af);
}

.btn-secondary:hover {
  background: var(--lattice-surface-4, #2a2a2a);
  color: var(--lattice-text-primary, #e5e5e5);
}

.btn-warning {
  background: var(--lattice-warning, #f59e0b);
  border: 1px solid var(--lattice-warning, #f59e0b);
  color: #000;
}

.btn-warning:hover {
  background: #fbbf24;
  border-color: #fbbf24;
}
</style>
