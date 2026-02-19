/**
 * Font Loading and Enumeration Service
 *
 * Handles: Web-safe fonts, Google Fonts, and Local Font Access API (Chrome/Edge)
 */

import { createLogger } from "@/utils/logger";

const fontLogger = createLogger("Font");

export interface FontInfo {
  family: string;
  fullName: string;
  style: string;
  source: "system" | "websafe" | "google";
}

export interface FontCategory {
  name: string;
  fonts: FontInfo[];
}

// Web-safe fonts that work everywhere
const WEB_SAFE_FONTS: FontInfo[] = [
  { family: "Arial", fullName: "Arial", style: "normal", source: "websafe" },
  {
    family: "Arial Black",
    fullName: "Arial Black",
    style: "normal",
    source: "websafe",
  },
  {
    family: "Verdana",
    fullName: "Verdana",
    style: "normal",
    source: "websafe",
  },
  { family: "Tahoma", fullName: "Tahoma", style: "normal", source: "websafe" },
  {
    family: "Trebuchet MS",
    fullName: "Trebuchet MS",
    style: "normal",
    source: "websafe",
  },
  {
    family: "Times New Roman",
    fullName: "Times New Roman",
    style: "normal",
    source: "websafe",
  },
  {
    family: "Georgia",
    fullName: "Georgia",
    style: "normal",
    source: "websafe",
  },
  {
    family: "Courier New",
    fullName: "Courier New",
    style: "normal",
    source: "websafe",
  },
  { family: "Impact", fullName: "Impact", style: "normal", source: "websafe" },
  {
    family: "Comic Sans MS",
    fullName: "Comic Sans MS",
    style: "normal",
    source: "websafe",
  },
];

// Popular Google Fonts
const GOOGLE_FONTS = [
  "Roboto",
  "Open Sans",
  "Lato",
  "Montserrat",
  "Oswald",
  "Raleway",
  "Poppins",
  "Nunito",
  "Playfair Display",
  "Merriweather",
  "Ubuntu",
  "PT Sans",
  "Roboto Mono",
  "Bebas Neue",
  "Source Sans Pro",
  "Inter",
  "Fira Sans",
  "Quicksand",
  "Work Sans",
  "Barlow",
];

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//               // type // extensions // for // local // font // access // api
// ════════════════════════════════════════════════════════════════════════════

/**
 * Extended Window interface for Local Font Access API
 * queryLocalFonts() is available in Chrome/Edge 103+ but not yet in TypeScript DOM types
 */
interface WindowWithFontAccess extends Window {
  queryLocalFonts?: () => Promise<Array<{
    family: string;
    fullName: string;
    style: string;
    postscriptName?: string;
  }>>;
}

/**
 * Type guard to check if window supports Local Font Access API
 */
function supportsLocalFontAccess(window: Window): window is WindowWithFontAccess {
  return "queryLocalFonts" in window;
}

class FontService {
  private systemFonts: FontInfo[] = [];
  private loadedGoogleFonts: Set<string> = new Set();
  private initialized: boolean = false;

  /**
   * Initialize font service and attempt to load system fonts
   */
  async initialize(): Promise<void> {
    if (this.initialized) return;

    // Try to load system fonts (Chrome/Edge 103+ only)
    if ("queryLocalFonts" in window) {
      await this.loadSystemFonts();
    }

    this.initialized = true;
  }

  /**
   * Load system fonts using Local Font Access API
   * Requires user permission
   */
  private async loadSystemFonts(): Promise<void> {
    try {
      // Type-safe access to queryLocalFonts API
      if (!supportsLocalFontAccess(window)) {
        fontLogger.info("Local Font Access API not available");
        return;
      }

      // Type proof: After guard, window has queryLocalFonts method
      // This will prompt for permission
      const windowWithFonts = window as WindowWithFontAccess;
      if (typeof windowWithFonts.queryLocalFonts !== "function") {
        return; // Font access API not available
      }
      const fonts = await windowWithFonts.queryLocalFonts();

      // Group by family, keep one entry per family
      const familyMap = new Map<string, FontInfo>();

      for (const font of fonts) {
        if (!familyMap.has(font.family) || font.style === "Regular") {
          familyMap.set(font.family, {
            family: font.family,
            fullName: font.fullName,
            style: font.style,
            source: "system",
          });
        }
      }

      this.systemFonts = Array.from(familyMap.values()).sort((a, b) =>
        a.family.localeCompare(b.family),
      );

      fontLogger.debug(`Loaded ${this.systemFonts.length} system fonts`);
    } catch (error) {
      if ((error as Error).name === "NotAllowedError") {
        fontLogger.info("User denied font access permission");
      } else {
        fontLogger.error("Error loading system fonts:", error);
      }
    }
  }

  /**
   * Get all available fonts organized by category
   */
  getFontCategories(): FontCategory[] {
    const categories: FontCategory[] = [];

    // System fonts (if available)
    if (this.systemFonts.length > 0) {
      categories.push({
        name: "System Fonts",
        fonts: this.systemFonts,
      });
    }

    // Web-safe fonts
    categories.push({
      name: "Web Safe",
      fonts: WEB_SAFE_FONTS,
    });

    // Google Fonts
    categories.push({
      name: "Google Fonts",
      fonts: GOOGLE_FONTS.map((family) => ({
        family,
        fullName: family,
        style: "normal",
        source: "google" as const,
      })),
    });

    return categories;
  }

  /**
   * Get flat list of all font families
   */
  getAllFontFamilies(): string[] {
    const families = new Set<string>();

    WEB_SAFE_FONTS.forEach((f) => families.add(f.family));
    GOOGLE_FONTS.forEach((f) => families.add(f));
    this.systemFonts.forEach((f) => families.add(f.family));

    return Array.from(families).sort();
  }

  /**
   * Load a Google Font dynamically
   */
  async loadGoogleFont(
    family: string,
    weights: string[] = ["400", "700"],
  ): Promise<void> {
    if (this.loadedGoogleFonts.has(family)) return;

    // Security: Only allow whitelisted Google Fonts to prevent arbitrary external resource loading
    if (!GOOGLE_FONTS.includes(family)) {
      fontLogger.warn(`Attempted to load non-whitelisted font: ${family}`);
      return;
    }

    const weightsStr = weights.join(";");
    const url = `https://fonts.googleapis.com/css2?family=${encodeURIComponent(family)}:wght@${weightsStr}&display=swap`;

    // Create and append link element
    const link = document.createElement("link");
    link.rel = "stylesheet";
    link.href = url;
    document.head.appendChild(link);

    // Wait for font to be ready
    try {
      await document.fonts.load(`400 16px "${family}"`);
      this.loadedGoogleFonts.add(family);
      fontLogger.debug(`Loaded Google Font: ${family}`);
    } catch (error) {
      fontLogger.error(`Failed to load Google Font: ${family}`, error);
    }
  }

  /**
   * Ensure a font is available before using it
   */
  async ensureFont(family: string): Promise<boolean> {
    // Check if it's web-safe
    if (WEB_SAFE_FONTS.some((f) => f.family === family)) {
      return true;
    }

    // Check if it's a Google Font
    if (GOOGLE_FONTS.includes(family)) {
      await this.loadGoogleFont(family);
      return true;
    }

    // Check if it's a loaded system font
    if (this.systemFonts.some((f) => f.family === family)) {
      return true;
    }

    // Try to detect if font is available
    return this.isFontAvailable(family);
  }

  /**
   * Check if a font is available by measuring text
   */
  private isFontAvailable(family: string): boolean {
    const testString = "mmmmmmmmmmlli";
    const canvas = document.createElement("canvas");
    const ctx = canvas.getContext("2d")!;

    // Measure with monospace fallback
    ctx.font = "72px monospace";
    const fallbackWidth = ctx.measureText(testString).width;

    // Measure with requested font
    ctx.font = `72px "${family}", monospace`;
    const testWidth = ctx.measureText(testString).width;

    return fallbackWidth !== testWidth;
  }

  /**
   * Get web-safe fonts list
   */
  getWebSafeFonts(): FontInfo[] {
    return WEB_SAFE_FONTS;
  }

  /**
   * Get Google fonts list
   */
  getGoogleFonts(): string[] {
    return GOOGLE_FONTS;
  }

  /**
   * Check if system fonts are available
   */
  hasSystemFonts(): boolean {
    return this.systemFonts.length > 0;
  }

  /**
   * Request system font access (must be triggered by user action)
   */
  async requestSystemFontAccess(): Promise<boolean> {
    if (!("queryLocalFonts" in window)) {
      fontLogger.info("Local Font Access API not available");
      return false;
    }

    await this.loadSystemFonts();
    return this.systemFonts.length > 0;
  }
}

// Singleton instance
export const fontService = new FontService();
export default fontService;
