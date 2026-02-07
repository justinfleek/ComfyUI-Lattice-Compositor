// Type guards for deterministic type narrowing (no assertions)

export function isHTMLInputElement(value: EventTarget | null): value is HTMLInputElement {
  if (value === null) {
    return false;
  }
  return value instanceof HTMLInputElement;
}

export function isHTMLElement(value: Element | null): value is HTMLElement {
  if (value === null) {
    return false;
  }
  return value instanceof HTMLElement;
}

export function isValidMonitorType(value: string): value is "OLED" | "LCD" {
  return value === "OLED" || value === "LCD";
}

export function isValidThemeMode(value: string): value is "dark" | "light" {
  return value === "dark" || value === "light";
}

// VSCode API type guard
export interface VSCodeAPI {
  postMessage(message: { command: string; [key: string]: unknown }): void;
}

export function getVSCodeAPI(): VSCodeAPI {
  // Check if acquireVsCodeApi exists on window
  const windowObj = window as { acquireVsCodeApi?: () => VSCodeAPI };
  if (typeof windowObj.acquireVsCodeApi === "function") {
    return windowObj.acquireVsCodeApi();
  }
  throw new Error("VSCode API not available - acquireVsCodeApi not found");
}

// Safe color access with explicit defaults
export function getColorOrDefault(
  colors: { [key: string]: string },
  key: string,
  defaultValue: string
): string {
  const value = colors[key];
  if (value === undefined || value === null || value === "") {
    return defaultValue;
  }
  return value;
}
