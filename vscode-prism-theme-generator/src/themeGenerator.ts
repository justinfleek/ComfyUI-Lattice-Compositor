import { ColorWheel } from "./colorWheel";
import { ThemeConfig, ThemeVariant } from "./types";
import {
  isHTMLInputElement,
  isValidMonitorType,
  isValidThemeMode,
  getVSCodeAPI
} from "./typeGuards";

export class ThemeGeneratorUI {
  private baseColorWheel: ColorWheel;
  private heroColorWheel: ColorWheel;
  private baseHSL: { h: number; s: number; l: number } = { h: 211, s: 0.12, l: 0.11 };
  private heroHSL: { h: number; s: number; l: number } = { h: 211, s: 1.0, l: 0.66 };
  private monitorType: "OLED" | "LCD" = "OLED";
  private blackBalance: number = 0.11;
  private themeMode: "dark" | "light" = "dark";

  constructor() {
    const baseContainer = document.getElementById("baseColorWheel");
    const heroContainer = document.getElementById("heroColorWheel");

    if (!baseContainer || !heroContainer) {
      throw new Error("Color wheel containers not found");
    }

    this.baseColorWheel = new ColorWheel(baseContainer, 300, (hsl) => {
      this.baseHSL = hsl;
      this.updateBaseColorDisplay();
    });

    this.heroColorWheel = new ColorWheel(heroContainer, 300, (hsl) => {
      this.heroHSL = hsl;
      this.updateHeroColorDisplay();
    });

    this.setupControls();
    this.setupMessageListener();
  }

  private setupMessageListener() {
    // Listen for messages from extension host
    window.addEventListener("message", (event) => {
      const message = event.data;
      switch (message.command) {
        case "themesGenerated":
          this.displayThemes(message.variants);
          break;
        case "themeGenerationError":
          const themeList = document.getElementById("themeList");
          if (themeList) {
            themeList.innerHTML = `<div class="error">Error: ${message.error}</div>`;
          }
          break;
      }
    });
  }

  private setupControls() {
    // Monitor type radio buttons
    const monitorRadios = document.querySelectorAll('input[name="monitorType"]');
    monitorRadios.forEach((radio) => {
      radio.addEventListener("change", (e) => {
        const target = e.target;
        if (isHTMLInputElement(target)) {
          const value = target.value;
          if (isValidMonitorType(value)) {
            this.monitorType = value;
            this.updateBlackBalanceRecommendation();
          }
        }
      });
    });

    // Black balance slider
    const blackBalanceSlider = document.getElementById("blackBalanceSlider");
    const blackBalanceValue = document.getElementById("blackBalanceValue");
    if (isHTMLInputElement(blackBalanceSlider) && blackBalanceValue) {
      blackBalanceSlider.addEventListener("input", (e) => {
        const target = e.target;
        if (isHTMLInputElement(target)) {
          const value = parseFloat(target.value);
          if (!isNaN(value)) {
            this.blackBalance = value / 100;
            blackBalanceValue.textContent = `${value.toFixed(1)}%`;
          }
        }
      });
    }

    // Theme mode radio buttons
    const modeRadios = document.querySelectorAll('input[name="themeMode"]');
    modeRadios.forEach((radio) => {
      radio.addEventListener("change", (e) => {
        const target = e.target;
        if (isHTMLInputElement(target)) {
          const value = target.value;
          if (isValidThemeMode(value)) {
            this.themeMode = value;
          }
        }
      });
    });

    // Generate button
    const generateBtn = document.getElementById("generateBtn");
    if (generateBtn) {
      generateBtn.addEventListener("click", () => {
        this.generateThemes();
      });
    }

    // Preview button
    const previewBtn = document.getElementById("previewBtn");
    if (previewBtn) {
      previewBtn.addEventListener("click", () => {
        this.previewTheme();
      });
    }

    this.updateBlackBalanceRecommendation();
  }

  private updateBlackBalanceRecommendation() {
    const recommended = this.monitorType === "OLED" ? 11 : 16;
    const slider = document.getElementById("blackBalanceSlider");
    const valueDisplay = document.getElementById("blackBalanceValue");
    if (isHTMLInputElement(slider) && valueDisplay) {
      slider.value = recommended.toString();
      this.blackBalance = recommended / 100;
      valueDisplay.textContent = `${recommended}%`;
    }
  }

  private updateBaseColorDisplay() {
    const hslDisplay = document.getElementById("baseHSL");
    const hexDisplay = document.getElementById("baseHex");
    if (hslDisplay) {
      hslDisplay.textContent = `${Math.round(this.baseHSL.h)}°, ${Math.round(this.baseHSL.s * 100)}%, ${Math.round(this.baseHSL.l * 100)}%`;
    }
    if (hexDisplay) {
      hexDisplay.textContent = this.hslToHex(this.baseHSL);
    }
  }

  private updateHeroColorDisplay() {
    const hslDisplay = document.getElementById("heroHSL");
    const hexDisplay = document.getElementById("heroHex");
    if (hslDisplay) {
      hslDisplay.textContent = `${Math.round(this.heroHSL.h)}°, ${Math.round(this.heroHSL.s * 100)}%, ${Math.round(this.heroHSL.l * 100)}%`;
    }
    if (hexDisplay) {
      hexDisplay.textContent = this.hslToHex(this.heroHSL);
    }
  }

  private hslToHex(hsl: { h: number; s: number; l: number }): string {
    const rgb = this.hslToRgb(hsl.h, hsl.s, hsl.l);
    return `#${[rgb.r, rgb.g, rgb.b].map((x) => {
      const hex = x.toString(16);
      return hex.length === 1 ? "0" + hex : hex;
    }).join("")}`;
  }

  private hslToRgb(h: number, s: number, l: number): { r: number; g: number; b: number } {
    h = h % 360;
    const c = (1 - Math.abs(2 * l - 1)) * s;
    const x = c * (1 - Math.abs(((h / 60) % 2) - 1));
    const m = l - c / 2;

    let r = 0;
    let g = 0;
    let b = 0;

    if (h < 60) {
      r = c;
      g = x;
      b = 0;
    } else if (h < 120) {
      r = x;
      g = c;
      b = 0;
    } else if (h < 180) {
      r = 0;
      g = c;
      b = x;
    } else if (h < 240) {
      r = 0;
      g = x;
      b = c;
    } else if (h < 300) {
      r = x;
      g = 0;
      b = c;
    } else {
      r = c;
      g = 0;
      b = x;
    }

    return {
      r: Math.round((r + m) * 255),
      g: Math.round((g + m) * 255),
      b: Math.round((b + m) * 255)
    };
  }

  private getConfig(): ThemeConfig {
    return {
      baseColor: {
        hue: this.baseHSL.h,
        saturation: this.baseHSL.s,
        lightness: this.baseHSL.l
      },
      heroColor: {
        hue: this.heroHSL.h,
        saturation: this.heroHSL.s,
        lightness: this.heroHSL.l
      },
      monitorType: this.monitorType,
      blackBalance: this.blackBalance,
      mode: this.themeMode
    };
  }

  private async generateThemes() {
    const config = this.getConfig();
    
    // Send message to extension host to generate themes via Haskell FFI
    try {
      const vscode = getVSCodeAPI();
      vscode.postMessage({
        command: "generateTheme",
        config: config
      });
    } catch (error) {
      console.error("Failed to get VSCode API:", error);
    }
  }

  private previewTheme() {
    const config = this.getConfig();
    
    try {
      const vscode = getVSCodeAPI();
      vscode.postMessage({
        command: "previewTheme",
        config: config
      });
    } catch (error) {
      console.error("Failed to get VSCode API:", error);
    }
  }

  public displayThemes(themes: ThemeVariant[]) {
    const themeList = document.getElementById("themeList");
    if (!themeList) {
      return;
    }

    themeList.innerHTML = "";

    themes.forEach((theme) => {
      const themeCard = document.createElement("div");
      themeCard.className = "theme-card";
      
      const previewButton = document.createElement("button");
      previewButton.textContent = "Preview";
      previewButton.className = "preview-variant-btn";
      previewButton.onclick = () => {
        try {
          const vscode = getVSCodeAPI();
          vscode.postMessage({
            command: "previewVariant",
            variant: theme
          });
        } catch (error) {
          console.error("Failed to get VSCode API:", error);
        }
      };
      
      themeCard.innerHTML = `
        <h3>${theme.name}</h3>
        <div class="theme-info">
          <span>Background: ${(theme.backgroundLightness * 100).toFixed(1)}%</span>
        </div>
        <div class="theme-preview">
          <div class="color-swatch" style="background: ${theme.colors.base00}" title="base00: ${theme.colors.base00}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base01}" title="base01: ${theme.colors.base01}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base02}" title="base02: ${theme.colors.base02}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base03}" title="base03: ${theme.colors.base03}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base04}" title="base04: ${theme.colors.base04}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base05}" title="base05: ${theme.colors.base05}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base06}" title="base06: ${theme.colors.base06}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base07}" title="base07: ${theme.colors.base07}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base08}" title="base08: ${theme.colors.base08}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base09}" title="base09: ${theme.colors.base09}"></div>
          <div class="color-swatch hero-color" style="background: ${theme.colors.base0A}" title="base0A (HERO): ${theme.colors.base0A}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base0B}" title="base0B: ${theme.colors.base0B}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base0C}" title="base0C: ${theme.colors.base0C}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base0D}" title="base0D: ${theme.colors.base0D}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base0E}" title="base0E: ${theme.colors.base0E}"></div>
          <div class="color-swatch" style="background: ${theme.colors.base0F}" title="base0F: ${theme.colors.base0F}"></div>
        </div>
      `;
      themeCard.appendChild(previewButton);
      themeList.appendChild(themeCard);
    });
  }
}

// Initialize when DOM is ready
if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", () => {
    new ThemeGeneratorUI();
  });
} else {
  new ThemeGeneratorUI();
}
