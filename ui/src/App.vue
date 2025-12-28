<template>
  <WorkspaceLayout />
  <!-- Security warning dialog for loading external files -->
  <SecurityWarningDialog
    :visible="securityDialogState.visible"
    :file-name="securityDialogState.fileName"
    @cancel="handleSecurityCancel"
    @proceed="handleSecurityProceed"
  />
</template>

<script setup lang="ts">
import { onMounted, onUnmounted, reactive } from 'vue';
import WorkspaceLayout from './components/layout/WorkspaceLayout.vue';
import SecurityWarningDialog from './components/dialogs/SecurityWarningDialog.vue';
import { useThemeStore } from './stores/themeStore';
import {
  registerSecurityDialog,
  unregisterSecurityDialog,
  handleSecurityDialogResult,
  type SecurityConfirmationState
} from './services/securityConfirmation';

const themeStore = useThemeStore();

// Security dialog state
const securityDialogState = reactive<SecurityConfirmationState>({
  visible: false,
  fileName: '',
  resolve: null
});

function handleSecurityCancel() {
  handleSecurityDialogResult(false, false);
}

function handleSecurityProceed(dontShowAgain: boolean) {
  handleSecurityDialogResult(true, dontShowAgain);
}

onMounted(() => {
  themeStore.loadSavedTheme();

  // Register security dialog with the service
  registerSecurityDialog(securityDialogState, (update) => {
    Object.assign(securityDialogState, update);
  });
});

onUnmounted(() => {
  unregisterSecurityDialog();
});
</script>

<style>
/* Global styles for the app - using design tokens */
* {
  box-sizing: border-box;
}

html, body, #app {
  margin: 0;
  padding: 0;
  width: 100%;
  height: 100%;
  overflow: hidden;
  font-family: var(--lattice-font-sans, -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif);
  font-size: var(--lattice-text-base, 12px);
  line-height: var(--lattice-leading-normal, 1.5);
  background: var(--lattice-void, #050505);
  color: var(--lattice-text-primary, #E5E5E5);
}

/* Global font size for form elements */
button, input, select, textarea, label {
  font-size: var(--lattice-text-base, 12px);
  font-family: inherit;
}

/* Ensure small text is still readable */
.small-text, small {
  font-size: var(--lattice-text-sm, 11px);
}

/* Floating panel utility class */
.floating-panel {
  background: var(--lattice-surface-1);
  border-radius: var(--lattice-radius-xl);
  box-shadow: var(--lattice-shadow-panel);
  border: none;
  overflow: hidden;
}

/* Surface level utilities */
.surface-0 { background: var(--lattice-surface-0); }
.surface-1 { background: var(--lattice-surface-1); }
.surface-2 { background: var(--lattice-surface-2); }
.surface-3 { background: var(--lattice-surface-3); }
.surface-4 { background: var(--lattice-surface-4); }

/* Text utilities */
.text-primary { color: var(--lattice-text-primary); }
.text-secondary { color: var(--lattice-text-secondary); }
.text-muted { color: var(--lattice-text-muted); }
.text-accent { color: var(--lattice-accent); }

/* Focus ring for accessibility */
.focus-ring:focus,
.focus-ring:focus-visible {
  outline: none;
  box-shadow: 0 0 0 2px var(--lattice-void), 0 0 0 4px var(--lattice-accent);
}
</style>
