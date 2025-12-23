/**
 * @file toastStore.ts
 * @description Global toast notification store
 *
 * Provides a simple API for showing toast notifications:
 * - toastStore.success('Message') - Green success toast
 * - toastStore.error('Message') - Red error toast
 * - toastStore.warning('Message') - Yellow warning toast
 * - toastStore.info('Message') - Blue info toast
 */
import { ref } from 'vue';
import { defineStore } from 'pinia';

export type ToastType = 'success' | 'error' | 'warning' | 'info';

export interface Toast {
  id: string;
  message: string;
  type: ToastType;
  duration: number;
}

let toastIdCounter = 0;

export const useToastStore = defineStore('toast', () => {
  const toasts = ref<Toast[]>([]);

  function addToast(message: string, type: ToastType = 'info', duration: number = 3000): string {
    const id = `toast-${++toastIdCounter}`;

    const toast: Toast = {
      id,
      message,
      type,
      duration
    };

    toasts.value.push(toast);

    // Auto-remove after duration
    if (duration > 0) {
      setTimeout(() => {
        removeToast(id);
      }, duration);
    }

    return id;
  }

  function removeToast(id: string): void {
    const index = toasts.value.findIndex(t => t.id === id);
    if (index !== -1) {
      toasts.value.splice(index, 1);
    }
  }

  function clearAll(): void {
    toasts.value = [];
  }

  // Convenience methods
  function success(message: string, duration: number = 3000): string {
    return addToast(message, 'success', duration);
  }

  function error(message: string, duration: number = 5000): string {
    return addToast(message, 'error', duration);
  }

  function warning(message: string, duration: number = 4000): string {
    return addToast(message, 'warning', duration);
  }

  function info(message: string, duration: number = 3000): string {
    return addToast(message, 'info', duration);
  }

  return {
    toasts,
    addToast,
    removeToast,
    clearAll,
    success,
    error,
    warning,
    info
  };
});
