/**
 * Security Confirmation Service
 *
 * Provides confirmation dialogs before loading external project files.
 * This is a SECURITY FEATURE - users must acknowledge the risk of
 * executing expression code from untrusted files.
 *
 * @see SECURITY.md for full documentation
 */

const STORAGE_KEY = 'lattice-skip-security-warning';

/**
 * Check if security warning should be shown
 * Returns false if user opted out via "Don't show again"
 */
export function shouldShowSecurityWarning(): boolean {
  try {
    return localStorage.getItem(STORAGE_KEY) !== 'true';
  } catch {
    return true; // Show warning if localStorage unavailable
  }
}

/**
 * Save user's preference to skip security warning
 */
export function skipSecurityWarning(): void {
  try {
    localStorage.setItem(STORAGE_KEY, 'true');
  } catch {
    // Ignore - localStorage might be unavailable
  }
}

/**
 * Reset the "don't show again" preference
 * Useful for testing or if user wants to re-enable warnings
 */
export function resetSecurityWarningPreference(): void {
  try {
    localStorage.removeItem(STORAGE_KEY);
  } catch {
    // Ignore
  }
}

/**
 * State for the security confirmation dialog
 * This is used by the App component to show/hide the dialog
 */
export interface SecurityConfirmationState {
  visible: boolean;
  fileName: string;
  resolve: ((proceed: boolean) => void) | null;
}

// Global state - will be set by App.vue
let globalState: SecurityConfirmationState | null = null;
let setGlobalState: ((state: Partial<SecurityConfirmationState>) => void) | null = null;

/**
 * Register the dialog state from App.vue
 * This connects the service to the Vue component
 */
export function registerSecurityDialog(
  state: SecurityConfirmationState,
  setState: (update: Partial<SecurityConfirmationState>) => void
): void {
  globalState = state;
  setGlobalState = setState;
}

/**
 * Unregister the dialog (cleanup)
 */
export function unregisterSecurityDialog(): void {
  globalState = null;
  setGlobalState = null;
}

/**
 * Show security confirmation dialog before loading a project
 *
 * @param fileName - Name of the file being loaded (for display)
 * @returns Promise that resolves to true if user proceeds, false if cancelled
 */
export async function confirmProjectLoad(fileName: string): Promise<boolean> {
  // If user opted out, proceed without warning
  if (!shouldShowSecurityWarning()) {
    return true;
  }

  // If no dialog registered, fall back to native confirm
  if (!globalState || !setGlobalState) {
    return confirm(
      `Security Warning\n\n` +
      `This project file may contain expressions that will execute code.\n\n` +
      `File: ${fileName}\n\n` +
      `Only open project files from sources you trust.\n\n` +
      `Do you want to open this file?`
    );
  }

  // Show the Vue dialog
  return new Promise((resolve) => {
    setGlobalState!({
      visible: true,
      fileName,
      resolve,
    });
  });
}

/**
 * Handle dialog result (called by SecurityWarningDialog)
 */
export function handleSecurityDialogResult(proceed: boolean, dontShowAgain: boolean): void {
  if (globalState?.resolve) {
    if (proceed && dontShowAgain) {
      skipSecurityWarning();
    }
    globalState.resolve(proceed);
    setGlobalState?.({
      visible: false,
      resolve: null,
    });
  }
}
