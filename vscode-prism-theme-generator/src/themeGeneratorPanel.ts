import * as vscode from "vscode";
import * as path from "path";
import { ColorWheel } from "./colorWheel";
import { ThemeConfig, MonitorType, ThemeVariant } from "./types";

export class ThemeGeneratorPanel {
  public static currentPanel: ThemeGeneratorPanel | undefined;
  public static readonly viewType = "prismThemeGenerator";

  private readonly _panel: vscode.WebviewPanel;
  private readonly _extensionUri: vscode.Uri;
  private _disposables: vscode.Disposable[] = [];

  public static createOrShow(extensionUri: vscode.Uri) {
    const column = vscode.window.activeTextEditor
      ? vscode.window.activeTextEditor.viewColumn
      : undefined;

    // If we already have a panel, show it
    if (ThemeGeneratorPanel.currentPanel) {
      ThemeGeneratorPanel.currentPanel._panel.reveal(column);
      return;
    }

    // Otherwise, create a new panel
    const viewColumn = column !== undefined ? column : vscode.ViewColumn.One;
    const panel = vscode.window.createWebviewPanel(
      ThemeGeneratorPanel.viewType,
      "Prism Theme Generator",
      viewColumn,
      {
        enableScripts: true,
        localResourceRoots: [
          vscode.Uri.joinPath(extensionUri, "media"),
          vscode.Uri.joinPath(extensionUri, "out")
        ]
      }
    );

    ThemeGeneratorPanel.currentPanel = new ThemeGeneratorPanel(
      panel,
      extensionUri
    );
  }

  private constructor(panel: vscode.WebviewPanel, extensionUri: vscode.Uri) {
    this._panel = panel;
    this._extensionUri = extensionUri;

    // Set the webview's initial html content
    this._update();

    // Listen for when the panel is disposed
    // This happens when the user closes the panel or when the panel is closed programmatically
    this._panel.onDidDispose(() => this.dispose(), null, this._disposables);

    // Handle messages from the webview
    this._panel.webview.onDidReceiveMessage(
      (message) => {
        switch (message.command) {
          case "generateTheme":
            this._generateTheme(message.config);
            return;
          case "previewTheme":
            this._previewTheme(message.config);
            return;
          case "previewVariant":
            this._previewVariant(message.variant);
            return;
        }
      },
      null,
      this._disposables
    );
  }

  private _update() {
    const webview = this._panel.webview;
    this._panel.webview.html = this._getHtmlForWebview(webview);
  }

  private _getHtmlForWebview(webview: vscode.Webview): string {
    const scriptUri = webview.asWebviewUri(
      vscode.Uri.joinPath(this._extensionUri, "out", "themeGenerator.js")
    );
    const styleUri = webview.asWebviewUri(
      vscode.Uri.joinPath(this._extensionUri, "media", "themeGenerator.css")
    );

    return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <link href="${styleUri}" rel="stylesheet">
  <title>Prism Theme Generator</title>
</head>
<body>
  <div class="container">
    <h1>Prism Theme Generator</h1>
    
    <div class="section">
      <h2>Base Color</h2>
      <div id="baseColorWheel" class="color-wheel-container"></div>
      <div class="color-info">
        <label>HSL: <span id="baseHSL">211°, 100%, 50%</span></label>
        <label>Hex: <span id="baseHex">#54aeff</span></label>
      </div>
    </div>

    <div class="section">
      <h2>Hero Color</h2>
      <div id="heroColorWheel" class="color-wheel-container"></div>
      <div class="color-info">
        <label>HSL: <span id="heroHSL">211°, 100%, 66%</span></label>
        <label>Hex: <span id="heroHex">#54aeff</span></label>
      </div>
    </div>

    <div class="section">
      <h2>Monitor Settings</h2>
      <div class="monitor-controls">
        <label>
          <input type="radio" name="monitorType" value="OLED" checked>
          OLED
        </label>
        <label>
          <input type="radio" name="monitorType" value="LCD">
          LCD
        </label>
      </div>
      <div class="slider-container">
        <label>Black Balance: <span id="blackBalanceValue">11%</span></label>
        <input type="range" id="blackBalanceSlider" min="0" max="20" value="11" step="0.1">
      </div>
    </div>

    <div class="section">
      <h2>Theme Mode</h2>
      <div class="mode-controls">
        <label>
          <input type="radio" name="themeMode" value="dark" checked>
          Dark Mode
        </label>
        <label>
          <input type="radio" name="themeMode" value="light">
          Light Mode
        </label>
      </div>
    </div>

    <div class="section">
      <button id="generateBtn" class="generate-btn">Generate Themes</button>
      <button id="previewBtn" class="preview-btn">Preview</button>
    </div>

    <div id="themeList" class="theme-list"></div>
  </div>

  <script src="${scriptUri}"></script>
</body>
</html>`;
  }

  private async _generateTheme(config: ThemeConfig) {
    try {
      // Try to use generated FFI bridge, fallback to mock if not available
      try {
        const { generateThemeVariants } = await import("./ffiBridge");
        const variants = await generateThemeVariants(config);
        this._panel.webview.postMessage({
          command: "themesGenerated",
          variants: variants
        });
      } catch (ffiError) {
        // Fallback to mock if FFI bridge not available
        console.warn("FFI bridge not available, using mock:", ffiError);
        const variants = this._mockGenerateThemes(config);
        this._panel.webview.postMessage({
          command: "themesGenerated",
          variants: variants
        });
      }
    } catch (error) {
      vscode.window.showErrorMessage(`Failed to generate themes: ${error}`);
      this._panel.webview.postMessage({
        command: "themeGenerationError",
        error: String(error)
      });
    }
  }

  private _mockGenerateThemes(config: ThemeConfig): ThemeVariant[] {
    // Mock implementation - generates sample themes
    // TODO: Replace with actual FFI call to generateThemeVariantsFFI
    const baseLightness = config.blackBalance;
    const variants: ThemeVariant[] = [];
    
    if (config.mode === "dark") {
      const lightnesses = config.monitorType === "OLED" 
        ? [0.0, 0.04, 0.08, 0.11, Math.max(baseLightness, 0.11)]
        : [0.02, 0.08, Math.max(baseLightness, 0.11), 0.16, 0.20];
      const names = config.monitorType === "OLED"
        ? ["pure-black", "ultra-dark", "dark", "tuned", "balanced"]
        : ["minimum", "dark", "balanced", "github", "bright"];
      
      for (let i = 0; i < lightnesses.length; i++) {
        variants.push(this._createMockVariant(names[i], lightnesses[i], config));
      }
    } else {
      const lightnesses = [0.95, 0.98, 0.96];
      const names = ["light", "bright", "paper"];
      for (let i = 0; i < lightnesses.length; i++) {
        variants.push(this._createMockVariant(names[i], lightnesses[i], config));
      }
    }
    
    return variants;
  }

  private _createMockVariant(name: string, bgLightness: number, config: ThemeConfig): ThemeVariant {
    // Generate mock colors based on background lightness
    // TODO: Replace with actual palette generation from Haskell
    const baseHue = config.baseColor.hue;
    const heroHue = config.heroColor.hue;
    
    // Simple mock: generate grayscale ramp with slight hue tint
    const colors = {
      base00: this._lightnessToHex(bgLightness, baseHue, 0.12),
      base01: this._lightnessToHex(Math.min(1.0, bgLightness + 0.03), baseHue, 0.16),
      base02: this._lightnessToHex(Math.min(1.0, bgLightness + 0.08), baseHue, 0.17),
      base03: this._lightnessToHex(Math.min(1.0, bgLightness + 0.17), baseHue, 0.15),
      base04: this._lightnessToHex(0.48, baseHue, 0.12),
      base05: this._lightnessToHex(0.81, baseHue, 0.28),
      base06: this._lightnessToHex(0.89, baseHue, 0.32),
      base07: this._lightnessToHex(0.95, baseHue, 0.36),
      base08: this._lightnessToHex(0.86, 201, 1.0),
      base09: this._lightnessToHex(0.75, 201, 1.0),
      base0A: this._lightnessToHex(0.66, heroHue, 1.0),  // HERO
      base0B: this._lightnessToHex(0.57, heroHue, 1.0),
      base0C: this._lightnessToHex(0.45, heroHue, 0.94),
      base0D: this._lightnessToHex(0.65, heroHue, 1.0),
      base0E: this._lightnessToHex(0.71, heroHue, 1.0),
      base0F: this._lightnessToHex(0.53, heroHue, 0.86)
    };
    
    return {
      name: name,
      backgroundLightness: bgLightness,
      colors: colors
    };
  }

  private _lightnessToHex(l: number, h: number, s: number): string {
    // Simple HSL to RGB conversion for mock
    const c = (1 - Math.abs(2 * l - 1)) * s;
    const x = c * (1 - Math.abs(((h / 60) % 2) - 1));
    const m = l - c / 2;
    
    let r = 0, g = 0, b = 0;
    if (h < 60) { r = c; g = x; b = 0; }
    else if (h < 120) { r = x; g = c; b = 0; }
    else if (h < 180) { r = 0; g = c; b = x; }
    else if (h < 240) { r = 0; g = x; b = c; }
    else if (h < 300) { r = x; g = 0; b = c; }
    else { r = c; g = 0; b = x; }
    
    const toHex = (n: number) => {
      const hex = Math.round((n + m) * 255).toString(16);
      return hex.length === 1 ? "0" + hex : hex;
    };
    
    return `#${toHex(r)}${toHex(g)}${toHex(b)}`;
  }

  private _previewTheme(config: ThemeConfig) {
    // Generate a single variant for preview
    const variant = this._createMockVariant("preview", config.blackBalance, config);
    ThemePreviewPanel.createOrShow(this._extensionUri, variant);
  }

  private _previewVariant(variant: ThemeVariant) {
    ThemePreviewPanel.createOrShow(this._extensionUri, variant);
  }

  public dispose() {
    ThemeGeneratorPanel.currentPanel = undefined;

    // Clean up our resources
    this._panel.dispose();

    while (this._disposables.length) {
      const x = this._disposables.pop();
      if (x) {
        x.dispose();
      }
    }
  }
}
