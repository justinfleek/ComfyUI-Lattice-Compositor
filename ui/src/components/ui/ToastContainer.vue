<!--
  @component ToastContainer
  @description Global toast notification container
  Renders all active toasts from the toast store
-->
<template>
  <Teleport to="body">
    <div class="toast-container" role="status" aria-live="polite">
      <TransitionGroup name="toast">
        <div
          v-for="toast in toasts"
          :key="toast.id"
          class="toast"
          :class="[`toast-${toast.type}`]"
        >
          <span class="toast-icon">{{ getIcon(toast.type) }}</span>
          <span class="toast-message">{{ toast.message }}</span>
          <button class="toast-close" @click="dismiss(toast.id)" aria-label="Dismiss">
            &times;
          </button>
        </div>
      </TransitionGroup>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import { useToastStore, type ToastType } from '@/stores/toastStore';

const toastStore = useToastStore();

const toasts = computed(() => toastStore.toasts);

function dismiss(id: string): void {
  toastStore.removeToast(id);
}

function getIcon(type: ToastType): string {
  switch (type) {
    case 'success': return '✓';
    case 'error': return '✕';
    case 'warning': return '⚠';
    case 'info': return 'ℹ';
    default: return '';
  }
}
</script>

<style scoped>
.toast-container {
  position: fixed;
  bottom: 20px;
  right: 20px;
  z-index: 100000;
  display: flex;
  flex-direction: column;
  gap: 8px;
  max-width: 400px;
  pointer-events: none;
}

.toast {
  display: flex;
  align-items: center;
  gap: 10px;
  padding: 12px 16px;
  border-radius: 6px;
  background: var(--weyl-surface-3, #222);
  border: 1px solid var(--weyl-border-default, #333);
  box-shadow: 0 4px 16px rgba(0, 0, 0, 0.4);
  font-size: 13px;
  color: var(--weyl-text-primary, #e5e5e5);
  pointer-events: auto;
}

.toast-icon {
  font-size: 16px;
  flex-shrink: 0;
  width: 20px;
  text-align: center;
}

.toast-message {
  flex: 1;
}

.toast-close {
  width: 24px;
  height: 24px;
  border: none;
  background: transparent;
  color: var(--weyl-text-muted, #6b7280);
  font-size: 18px;
  cursor: pointer;
  border-radius: 4px;
  display: flex;
  align-items: center;
  justify-content: center;
  flex-shrink: 0;
}

.toast-close:hover {
  background: rgba(255, 255, 255, 0.1);
  color: var(--weyl-text-primary, #e5e5e5);
}

/* Toast types */
.toast-success {
  border-color: #10b981;
}

.toast-success .toast-icon {
  color: #10b981;
}

.toast-error {
  border-color: #ef4444;
}

.toast-error .toast-icon {
  color: #ef4444;
}

.toast-warning {
  border-color: #f59e0b;
}

.toast-warning .toast-icon {
  color: #f59e0b;
}

.toast-info {
  border-color: var(--weyl-accent, #8b5cf6);
}

.toast-info .toast-icon {
  color: var(--weyl-accent, #8b5cf6);
}

/* Transitions */
.toast-enter-active,
.toast-leave-active {
  transition: all 0.3s ease;
}

.toast-enter-from {
  opacity: 0;
  transform: translateX(100%);
}

.toast-leave-to {
  opacity: 0;
  transform: translateX(100%);
}

.toast-move {
  transition: transform 0.3s ease;
}
</style>
