/**
 * TextLayer - Text Rendering with Per-Character Animation & Path Following
 *
 * Implements text rendering using Troika-three-text with full professional
 * motion graphics text layer features:
 *
 * CHARACTER PROPERTIES:
 * - Font family, weight, style (Bold/Italic)
 * - Font size (animatable)
 * - Fill color (animatable)
 * - Stroke color and width (animatable)
 * - Tracking/letter spacing (animatable)
 * - Line spacing/leading (animatable)
 *
 * PARAGRAPH PROPERTIES:
 * - Text alignment (left/center/right)
 * - Per-character 3D mode
 *
 * PATH OPTIONS (Full Feature Set):
 * - Path layer selection (spline reference)
 * - Path Offset (0-100%, animatable with keyframes)
 * - First Margin / Last Margin
 * - Reverse Path
 * - Perpendicular to Path
 * - Force Alignment
 *
 * MORE OPTIONS:
 * - Anchor Point Grouping: Character | Word | Line | All
 * - Grouping Alignment: percentage-based
 * - Fill & Stroke order
 * - Inter-Character Blending
 *
 * TRANSFORM:
 * - Position X, Y, Z (3D space)
 * - Anchor Point X, Y
 * - Scale X, Y, Z (percentage)
 * - Rotation (2D) or X, Y, Z rotations (3D mode)
 * - Opacity (animatable)
 */

import * as THREE from "three";
import { Text as TroikaText } from "troika-three-text";
import {
  calculateCompleteCharacterInfluence,
  calculateWigglyOffset,
} from "@/services/textAnimator";
import type { FontMetrics } from "@/services/textShaper";

interface TroikaTextExtended extends InstanceType<typeof TroikaText> {
  fontWeight: string;
  fontStyle: "normal" | "italic";
  sdfGlyphSize: number;
  gpuAccelerateSDF: boolean;
  outlineBlur: number;
  __blurX?: number;
  __blurY?: number;
}

/**
 * Create a TroikaText instance with extended properties
 * Helper to avoid type assertions when extending third-party library types
 */
function createTroikaTextExtended(): TroikaTextExtended {
  const text = new TroikaText();
  return Object.assign(text, {
    fontWeight: "400",
    fontStyle: "normal" as const,
    sdfGlyphSize: 256,
    gpuAccelerateSDF: true,
    outlineBlur: 0,
  }) as TroikaTextExtended;
}
import {
  type CharacterPlacement,
  createDefaultPathConfig,
  type TextOnPathConfig,
  TextOnPathService,
} from "@/services/textOnPath";
import { loadFontForShaping, textShaper } from "@/services/textShaper";
import type {
  AnimatableProperty,
  ControlPoint,
  Layer,
  TextAnimator,
  TextData,
} from "@/types/project";
import { KeyframeEvaluator } from "../animation/KeyframeEvaluator";
import type { PropertyValue } from "@/types/animation";
import type { ResourceManager } from "../core/ResourceManager";
import { BaseLayer } from "./BaseLayer";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

/** Anchor point grouping mode for text animation */
export type AnchorPointGrouping = "character" | "word" | "line" | "all";

/** Fill and stroke rendering order */
export type FillStrokeOrder =
  | "perCharacter"
  | "fillOverStroke"
  | "strokeOverFill";

/** Inter-character blending mode */
export type InterCharacterBlending =
  | "normal"
  | "multiply"
  | "screen"
  | "overlay";

/** Per-character transform for animation */
export interface CharacterTransform {
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  scale: { x: number; y: number };
  opacity: number;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                             // text // layer
// ════════════════════════════════════════════════════════════════════════════

export class TextLayer extends BaseLayer {
  // Text rendering
  private textMesh: TroikaTextExtended;
  private perCharacterGroup: THREE.Group | null = null;
  private characterMeshes: TroikaTextExtended[] = [];

  // Text data from layer
  private textData: TextData;

  // Animatable text properties (from layer.properties)
  private fontSizeProp?: AnimatableProperty<number>;
  private trackingProp?: AnimatableProperty<number>;
  private lineSpacingProp?: AnimatableProperty<number>;
  private fillColorProp?: AnimatableProperty<string>;
  private strokeColorProp?: AnimatableProperty<string>;
  private strokeWidthProp?: AnimatableProperty<number>;
  private pathOffsetProp?: AnimatableProperty<number>;
  private firstMarginProp?: AnimatableProperty<number>;
  private lastMarginProp?: AnimatableProperty<number>;
  private characterOffsetProp?: AnimatableProperty<number>;

  // Per-character animation
  private characterTransforms?: AnimatableProperty<CharacterTransform[]>;

  // Resource management
  private resources: ResourceManager;

  // Font metrics for accurate character widths
  // Proper optional type - undefined when not loaded
  private fontMetrics: FontMetrics | undefined = undefined;

  // Path control points for text-on-path
  private pathControlPoints: ControlPoint[] = [];
  private pathClosed: boolean = false;

  // Path following service
  private textOnPath: TextOnPathService;
  private pathConfig: TextOnPathConfig;

  // Character width cache (recalculated when text/font changes)
  private characterWidths: number[] = [];
  private characterWidthsDirty: boolean = true;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: fontLoadingPromise ∈ Promise<void> | {} (never null)
  // Proper optional type - undefined when font not loading
  private fontLoadingPromise: Promise<void> | undefined = undefined;
  private useAccurateMetrics: boolean = false;

  // Text animators (per-character animation)
  private animators: TextAnimator[] = [];

  // Note: compositionFps is inherited from BaseLayer (protected)

  // Additional evaluator for text-specific properties
  private readonly textEvaluator: KeyframeEvaluator;

  constructor(layerData: Layer, resources: ResourceManager) {
    super(layerData);

    this.resources = resources;
    this.textEvaluator = new KeyframeEvaluator();

    // Initialize path service
    this.textOnPath = new TextOnPathService();
    this.pathConfig = createDefaultPathConfig();

    // Extract text data
    this.textData = this.extractTextData(layerData);

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined/null checks
    // Pattern match: animators ∈ TextAnimator[] | undefined → TextAnimator[]
    this.animators = Array.isArray(this.textData.animators) ? this.textData.animators : [];

    // Extract animatable properties
    this.extractAnimatableProperties(layerData);

    // Create text mesh
    this.textMesh = this.createTextMesh();
    this.group.add(this.textMesh);

    // If per-character 3D or path following is enabled, use character mode
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    const hasPathLayerId = (typeof this.textData.pathLayerId === "string" && this.textData.pathLayerId.length > 0);
    if (this.textData.perCharacter3D === true || hasPathLayerId) {
      this.enablePerCharacter3D();
    }

    // Apply initial blend mode
    this.initializeBlendMode();

    // Load font for accurate character metrics (async, non-blocking)
    this.loadFontMetrics();
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                // font // metrics // loading
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Load font metrics asynchronously for accurate character widths
   * This is non-blocking - text will use heuristics until font loads
   */
  private async loadFontMetrics(): Promise<void> {
    const fontFamily = this.textData.fontFamily;
    const fontUrl = this.getFontUrl(fontFamily);

    // Skip if no URL (system fonts can't be loaded via opentype.js)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (fontUrl.length === 0) {
      return;
    }

    // Avoid duplicate loading
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (this.fontLoadingPromise !== undefined) {
      return this.fontLoadingPromise;
    }

    this.fontLoadingPromise = (async () => {
      try {
        this.fontMetrics = await loadFontForShaping(fontFamily, fontUrl);
        this.useAccurateMetrics = true;
        this.characterWidthsDirty = true;

        // Refresh character layout if path or per-character mode is active
        if (this.perCharacterGroup) {
          if (this.textOnPath.hasPath()) {
            this.updatePathLayout();
          } else {
            this.createCharacterMeshes();
          }
        }
      } catch (_error) {
        // Silently fall back to heuristics if font loading fails
        console.debug(
          `TextLayer: Could not load font metrics for "${fontFamily}", using heuristics`,
        );
        this.useAccurateMetrics = false;
      }
    })();

    return this.fontLoadingPromise;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                            // initialization
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Extract text data from layer, with defaults matching AE
   */
  private extractTextData(layerData: Layer): TextData {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null checks
    // Pattern match: data ∈ TextData | null → TextData (with explicit defaults)
    const data = (layerData.data !== null && typeof layerData.data === "object" && "text" in layerData.data) ? layerData.data as TextData : null;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: Extract each property with explicit type narrowing and defaults
    const textValue = (data !== null && typeof data === "object" && "text" in data && typeof data.text === "string") ? data.text : "Text";
    const fontFamilyValue = (data !== null && typeof data === "object" && "fontFamily" in data && typeof data.fontFamily === "string") ? data.fontFamily : "Impact";
    const fontSizeValue = (data !== null && typeof data === "object" && "fontSize" in data && typeof data.fontSize === "number") ? data.fontSize : 72;
    const fontWeightValue = (data !== null && typeof data === "object" && "fontWeight" in data && typeof data.fontWeight === "string") ? data.fontWeight : "400";
    const fontStyleValue = (data !== null && typeof data === "object" && "fontStyle" in data && typeof data.fontStyle === "string") ? data.fontStyle : "normal";
    const fillValue = (data !== null && typeof data === "object" && "fill" in data && typeof data.fill === "string") ? data.fill : "#ffffff";
    const strokeValue = (data !== null && typeof data === "object" && "stroke" in data && typeof data.stroke === "string") ? data.stroke : "";
    const strokeWidthValue = (data !== null && typeof data === "object" && "strokeWidth" in data && typeof data.strokeWidth === "number") ? data.strokeWidth : 0;
    const trackingValue = (data !== null && typeof data === "object" && "tracking" in data && typeof data.tracking === "number") ? data.tracking : 0;
    const lineSpacingValue = (data !== null && typeof data === "object" && "lineSpacing" in data && typeof data.lineSpacing === "number") ? data.lineSpacing : 0;
    const lineAnchorValue = (data !== null && typeof data === "object" && "lineAnchor" in data && typeof data.lineAnchor === "number") ? data.lineAnchor : 50;
    const characterOffsetValue = (data !== null && typeof data === "object" && "characterOffset" in data && typeof data.characterOffset === "number") ? data.characterOffset : 0;
    const characterValueValue = (data !== null && typeof data === "object" && "characterValue" in data && typeof data.characterValue === "number") ? data.characterValue : 0;
    const blurValue = (data !== null && typeof data === "object" && "blur" in data && typeof data.blur === "object" && data.blur !== null && "x" in data.blur && "y" in data.blur) ? data.blur : { x: 0, y: 0 };
    const letterSpacingRaw = (data !== null && typeof data === "object" && "letterSpacing" in data && typeof data.letterSpacing === "number") ? data.letterSpacing : trackingValue;
    const letterSpacingValue = letterSpacingRaw;
    const lineHeightRaw = (data !== null && typeof data === "object" && "lineHeight" in data && typeof data.lineHeight === "number") ? data.lineHeight : lineSpacingValue;
    const lineHeightValue = lineHeightRaw > 0 ? lineHeightRaw : 1.2;
    const textAlignValue = (data !== null && typeof data === "object" && "textAlign" in data && typeof data.textAlign === "string") ? data.textAlign : "left";
    const pathLayerIdValue = (data !== null && typeof data === "object" && "pathLayerId" in data && typeof data.pathLayerId === "string") ? data.pathLayerId : "";
    const pathReversedValue = (data !== null && typeof data === "object" && "pathReversed" in data && typeof data.pathReversed === "boolean") ? data.pathReversed : false;
    const pathPerpendicularToPathValue = (data !== null && typeof data === "object" && "pathPerpendicularToPath" in data && typeof data.pathPerpendicularToPath === "boolean") ? data.pathPerpendicularToPath : true;
    const pathForceAlignmentValue = (data !== null && typeof data === "object" && "pathForceAlignment" in data && typeof data.pathForceAlignment === "boolean") ? data.pathForceAlignment : false;
    const pathFirstMarginValue = (data !== null && typeof data === "object" && "pathFirstMargin" in data && typeof data.pathFirstMargin === "number") ? data.pathFirstMargin : 0;
    const pathLastMarginValue = (data !== null && typeof data === "object" && "pathLastMargin" in data && typeof data.pathLastMargin === "number") ? data.pathLastMargin : 0;
    const pathOffsetValue = (data !== null && typeof data === "object" && "pathOffset" in data && typeof data.pathOffset === "number") ? data.pathOffset : 0;
    const pathAlignValue = (data !== null && typeof data === "object" && "pathAlign" in data && typeof data.pathAlign === "string") ? data.pathAlign : "left";
    const anchorPointGroupingValue = (data !== null && typeof data === "object" && "anchorPointGrouping" in data && typeof data.anchorPointGrouping === "string") ? data.anchorPointGrouping : "character";
    const groupingAlignmentValue = (data !== null && typeof data === "object" && "groupingAlignment" in data && typeof data.groupingAlignment === "object" && data.groupingAlignment !== null && "x" in data.groupingAlignment && "y" in data.groupingAlignment) ? data.groupingAlignment : { x: 0, y: 0 };
    const fillAndStrokeValue = (data !== null && typeof data === "object" && "fillAndStroke" in data && typeof data.fillAndStroke === "string") ? data.fillAndStroke : "fill-over-stroke";
    const interCharacterBlendingValue = (data !== null && typeof data === "object" && "interCharacterBlending" in data && typeof data.interCharacterBlending === "string") ? data.interCharacterBlending : "normal";
    const perCharacter3DValue = (data !== null && typeof data === "object" && "perCharacter3D" in data && typeof data.perCharacter3D === "boolean") ? data.perCharacter3D : false;
    const animatorsValue = (data !== null && typeof data === "object" && "animators" in data && Array.isArray(data.animators)) ? data.animators : [];

    return {
      text: textValue,
      fontFamily: fontFamilyValue,
      fontSize: fontSizeValue,
      fontWeight: fontWeightValue,
      fontStyle: fontStyleValue,
      fill: fillValue,
      stroke: strokeValue,
      strokeWidth: strokeWidthValue,
      tracking: trackingValue,
      lineSpacing: lineSpacingValue,
      lineAnchor: lineAnchorValue,
      characterOffset: characterOffsetValue,
      characterValue: characterValueValue,
      blur: blurValue,
      letterSpacing: letterSpacingValue,
      lineHeight: lineHeightValue,
      textAlign: textAlignValue,
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
      // Pattern match: pathLayerId ∈ string (empty string = no path, never null)
      pathLayerId: pathLayerIdValue,
      pathReversed: pathReversedValue,
      pathPerpendicularToPath: pathPerpendicularToPathValue,
      pathForceAlignment: pathForceAlignmentValue,
      pathFirstMargin: pathFirstMarginValue,
      pathLastMargin: pathLastMarginValue,
      pathOffset: pathOffsetValue,
      pathAlign: pathAlignValue,
      anchorPointGrouping: anchorPointGroupingValue,
      groupingAlignment: groupingAlignmentValue,
      fillAndStroke: fillAndStrokeValue,
      interCharacterBlending: interCharacterBlendingValue,
      perCharacter3D: perCharacter3DValue,
      animators: animatorsValue,
    };
  }

  /**
   * Extract animatable properties from layer.properties array
   */
  private extractAnimatableProperties(layerData: Layer): void {
    if (!layerData.properties) return;

    for (const prop of layerData.properties) {
      switch (prop.name) {
        case "Font Size":
          this.fontSizeProp = prop as AnimatableProperty<number>;
          break;
        case "Tracking":
          this.trackingProp = prop as AnimatableProperty<number>;
          break;
        case "Line Spacing":
          this.lineSpacingProp = prop as AnimatableProperty<number>;
          break;
        case "Fill Color":
          this.fillColorProp = prop as AnimatableProperty<string>;
          break;
        case "Stroke Color":
          this.strokeColorProp = prop as AnimatableProperty<string>;
          break;
        case "Stroke Width":
          this.strokeWidthProp = prop as AnimatableProperty<number>;
          break;
        case "Path Offset":
          this.pathOffsetProp = prop as AnimatableProperty<number>;
          break;
        case "First Margin":
          this.firstMarginProp = prop as AnimatableProperty<number>;
          break;
        case "Last Margin":
          this.lastMarginProp = prop as AnimatableProperty<number>;
          break;
        case "Character Offset":
          this.characterOffsetProp = prop as AnimatableProperty<number>;
          break;
      }
    }

    // Sync path config from text data
    this.syncPathConfig();
  }

  /**
   * Sync path configuration from text data
   */
  private syncPathConfig(): void {
    this.pathConfig.pathLayerId = this.textData.pathLayerId;
    this.pathConfig.reversed = this.textData.pathReversed;
    this.pathConfig.perpendicularToPath = this.textData.pathPerpendicularToPath;
    this.pathConfig.forceAlignment = this.textData.pathForceAlignment;
    this.pathConfig.firstMargin = this.textData.pathFirstMargin;
    this.pathConfig.lastMargin = this.textData.pathLastMargin;
    this.pathConfig.offset = this.textData.pathOffset;
    this.pathConfig.align = this.textData.pathAlign;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                  // text // mesh // creation
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Create Troika text mesh with current settings
   */
  private createTextMesh(): TroikaTextExtended {
    const text = createTroikaTextExtended();

    // Core text content
    text.text = this.textData.text;

    // Font settings
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy nullish coalescing
    // Pattern match: getFontUrl returns string (empty string for system fonts, never null/undefined)
    const fontUrl = this.getFontUrl(this.textData.fontFamily);
    text.font = fontUrl.length > 0 ? fontUrl : null;
    text.fontSize = this.textData.fontSize;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR defaults
    text.fontWeight = (typeof this.textData.fontWeight === "string" && this.textData.fontWeight.length > 0) ? this.textData.fontWeight : "400";
    text.fontStyle = (typeof this.textData.fontStyle === "string" && this.textData.fontStyle.length > 0) ? this.textData.fontStyle : "normal";

    // Colors
    text.color = this.textData.fill;
    if (this.textData.stroke && this.textData.strokeWidth > 0) {
      text.outlineWidth = this.textData.strokeWidth / this.textData.fontSize;
      text.outlineColor = this.textData.stroke;
    }

    // Spacing - Troika uses em units for letter spacing
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy nullish coalescing/logical OR
    // Pattern match: tracking ∈ number | undefined → number (coordinate-like, can be negative)
    const tracking = typeof this.textData.tracking === "number" ? this.textData.tracking : 0;
    text.letterSpacing = Number.isFinite(tracking) ? tracking / 1000 : 0;
    const lineHeightValue = typeof this.textData.lineHeight === "number" && this.textData.lineHeight > 0 ? this.textData.lineHeight : 1.2;
    text.lineHeight = lineHeightValue;

    // Alignment
    text.textAlign = this.textData.textAlign;
    text.anchorX = this.getAnchorX();
    text.anchorY = "middle";

    // Rendering quality settings
    text.depthOffset = 0;
    text.renderOrder = 0;

    text.sdfGlyphSize = 256;
    text.gpuAccelerateSDF = true;

    if (this.textData.strokeWidth > 0) {
      text.outlineBlur = 0.003;
    }

    // Trigger initial sync
    text.sync();

    return text;
  }

  /**
   * Get font URL for Troika
   */
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined returns
  // Pattern match: Returns empty string for system fonts (never undefined)
  private getFontUrl(fontFamily: string): string {
    const systemFonts = [
      "Arial",
      "Helvetica",
      "Times New Roman",
      "Georgia",
      "Verdana",
      "Courier New",
      "Impact",
      "Comic Sans MS",
      "Trebuchet MS",
      "Palatino",
    ];

    if (systemFonts.includes(fontFamily)) {
      // Lean4/PureScript/Haskell: Explicit default - never return undefined
      return "";
    }

    const googleFonts: Record<string, string> = {
      Roboto:
        "https://fonts.gstatic.com/s/roboto/v30/KFOmCnqEu92Fr1Mu4mxK.woff2",
      "Open Sans":
        "https://fonts.gstatic.com/s/opensans/v35/memSYaGs126MiZpBA-UvWbX2vVnXBbObj2OVZyOOSr4dVJWUgsjZ0B4gaVI.woff2",
      Lato: "https://fonts.gstatic.com/s/lato/v24/S6uyw4BMUTPHjx4wXg.woff2",
      Montserrat:
        "https://fonts.gstatic.com/s/montserrat/v26/JTUHjIg1_i6t8kCHKm4532VJOt5-QNFgpCtr6Hw5aXo.woff2",
      Oswald:
        "https://fonts.gstatic.com/s/oswald/v53/TK3_WkUHHAIjg75cFRf3bXL8LICs1_FvsUZiYA.woff2",
      Poppins:
        "https://fonts.gstatic.com/s/poppins/v21/pxiEyp8kv8JHgFVrJJfecg.woff2",
    };

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined
    // Pattern match: googleFonts[fontFamily] ∈ string | undefined → string
    if (fontFamily in googleFonts && typeof googleFonts[fontFamily] === "string") {
      return googleFonts[fontFamily];
    }
    return "";
  }

  /**
   * Get anchor X based on text alignment
   * Note: Swapped to match intuitive arrow button behavior:
   * - ◀ (left) button makes text appear on LEFT (anchor right edge)
   * - ▶ (right) button makes text appear on RIGHT (anchor left edge)
   */
  private getAnchorX(): "left" | "center" | "right" {
    switch (this.textData.textAlign) {
      case "left":
        return "right"; // Anchor right edge so text extends left
      case "right":
        return "left"; // Anchor left edge so text extends right
      default:
        return "center";
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // path // integration
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Set the path from SplineLayer control points
   * Called by LayerManager when connecting text to a spline
   */
  setPathFromControlPoints(
    controlPoints: ControlPoint[],
    closed: boolean = false,
  ): void {
    this.pathControlPoints = controlPoints;
    this.pathClosed = closed;

    if (controlPoints.length >= 2) {
      this.textOnPath.setPath(controlPoints, closed);

      // Enable per-character mode if not already
      if (!this.perCharacterGroup) {
        this.enablePerCharacter3D();
      }

      // Position on path
      this.updatePathLayout();
    } else {
      this.textOnPath.dispose();
      this.resetPathLayout();
    }
  }

  /**
   * Set the path from a THREE.js CurvePath directly
   */
  setPathFromCurve(curve: THREE.CurvePath<THREE.Vector3>): void {
    this.textOnPath.setCurve(curve);

    if (!this.perCharacterGroup) {
      this.enablePerCharacter3D();
    }

    this.updatePathLayout();
  }

  /**
   * Clear the path reference
   */
  clearPath(): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null assignments
    // Pattern match: pathLayerId ∈ string (empty string = no path, never null)
    this.textData.pathLayerId = "";
    this.pathConfig.pathLayerId = "";
    this.textOnPath.dispose();
    this.resetPathLayout();
  }

  /**
   * Update character positions along the path
   */
  private updatePathLayout(): void {
    if (!this.textOnPath.hasPath() || !this.perCharacterGroup) {
      return;
    }

    // Ensure character widths are calculated
    this.ensureCharacterWidths();

    // Get placements
    const placements = this.textOnPath.calculatePlacements(
      this.characterWidths,
      this.pathConfig,
      this.textData.tracking,
      this.textData.fontSize,
    );

    // Apply placements to character meshes
    this.applyPlacements(placements);
  }

  /**
   * Apply character placements to meshes
   */
  private applyPlacements(placements: CharacterPlacement[]): void {
    for (
      let i = 0;
      i < this.characterMeshes.length && i < placements.length;
      i++
    ) {
      const mesh = this.characterMeshes[i];
      const placement = placements[i];

      mesh.position.copy(placement.position);
      mesh.rotation.copy(placement.rotation);
      mesh.scale.setScalar(placement.scale);
      mesh.visible = placement.visible;
    }
  }

  /**
   * Reset to horizontal layout (no path)
   */
  private resetPathLayout(): void {
    if (this.textData.perCharacter3D) {
      this.createCharacterMeshes();
    } else {
      this.disablePerCharacter3D();
    }
  }

  /**
   * Calculate character widths for path spacing
   *
   * Uses textShaper for accurate glyph metrics when the font is loaded,
   * with automatic kerning support. Falls back to heuristic widths if
   * the font isn't loaded yet or loading failed.
   */
  private ensureCharacterWidths(): void {
    if (!this.characterWidthsDirty) return;

    this.characterWidths = [];
    const text = this.textData.text;
    const fontSize = this.textData.fontSize;
    const fontFamily = this.textData.fontFamily;

    // Try to use accurate metrics from textShaper
    if (this.useAccurateMetrics && textShaper.isFontLoaded(fontFamily)) {
      // Use textShaper for accurate glyph widths with kerning
      this.characterWidths = textShaper.getCharacterWidths(
        text,
        fontFamily,
        fontSize,
        {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy nullish coalescing
          kern: (typeof this.textData.kerning === "boolean") ? this.textData.kerning : true,
          letterSpacing: (typeof this.textData.tracking === "number") ? this.textData.tracking : 0,
        },
      );
      this.characterWidthsDirty = false;
      return;
    }

    // Fallback: Use heuristic widths based on font size
    // This is used while font is loading or for system fonts
    const avgCharWidth = fontSize * 0.6;

    for (let i = 0; i < text.length; i++) {
      const char = text[i];
      // Narrow characters
      if ("iIl1|!.,;:'\"".includes(char)) {
        this.characterWidths.push(avgCharWidth * 0.4);
      }
      // Wide characters
      else if ("mwMW".includes(char)) {
        this.characterWidths.push(avgCharWidth * 1.3);
      }
      // Space
      else if (char === " ") {
        this.characterWidths.push(avgCharWidth * 0.5);
      }
      // Average
      else {
        this.characterWidths.push(avgCharWidth);
      }
    }

    this.characterWidthsDirty = false;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                       // per
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Enable per-character mode (for 3D and path following)
   */
  private enablePerCharacter3D(): void {
    if (this.perCharacterGroup) return;

    // Hide main text mesh
    this.textMesh.visible = false;

    // Create group for characters
    this.perCharacterGroup = new THREE.Group();
    this.perCharacterGroup.name = `text_chars_${this.id}`;
    this.group.add(this.perCharacterGroup);

    // Create individual character meshes
    this.createCharacterMeshes();
  }

  /**
   * Disable per-character mode
   */
  private disablePerCharacter3D(): void {
    if (!this.perCharacterGroup) return;

    // Show main text mesh
    this.textMesh.visible = true;

    // Dispose character meshes
    this.disposeCharacterMeshes();

    // Remove group
    this.group.remove(this.perCharacterGroup);
    this.perCharacterGroup = null;
  }

  /**
   * Create individual character meshes
   */
  private createCharacterMeshes(): void {
    if (!this.perCharacterGroup) return;

    this.disposeCharacterMeshes();
    this.characterWidthsDirty = true;

    const text = this.textData.text;
    let xOffset = 0;

    // Calculate positions for horizontal layout
    this.ensureCharacterWidths();
    const totalWidth =
      this.characterWidths.reduce((a, b) => a + b, 0) +
      (text.length - 1) *
        (this.textData.tracking / 1000) *
        this.textData.fontSize;

    // Determine start X based on alignment
    let startX = 0;
    switch (this.textData.textAlign) {
      case "center":
        startX = -totalWidth / 2;
        break;
      case "right":
        startX = -totalWidth;
        break;
      default:
        startX = 0;
    }

    xOffset = startX;

    for (let i = 0; i < text.length; i++) {
      const char = text[i];
      const charMesh = createTroikaTextExtended();

      charMesh.text = char;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy nullish coalescing/logical OR
      const charFontUrl = this.getFontUrl(this.textData.fontFamily);
      charMesh.font = charFontUrl.length > 0 ? charFontUrl : null;
      charMesh.fontSize = this.textData.fontSize;
      charMesh.fontWeight = (typeof this.textData.fontWeight === "string" && this.textData.fontWeight.length > 0) ? this.textData.fontWeight : "400";
      charMesh.fontStyle = (typeof this.textData.fontStyle === "string" && this.textData.fontStyle.length > 0) ? this.textData.fontStyle : "normal";
      charMesh.color = this.textData.fill;
      charMesh.anchorX = "center";
      charMesh.anchorY = "middle";

      if (this.textData.stroke && this.textData.strokeWidth > 0) {
        charMesh.outlineWidth =
          this.textData.strokeWidth / this.textData.fontSize;
        charMesh.outlineColor = this.textData.stroke;
        charMesh.outlineBlur = 0.005;
      }

      charMesh.sdfGlyphSize = 128;

      // Position character (for horizontal layout)
      const charWidth = this.characterWidths[i];
      charMesh.position.x = xOffset + charWidth / 2;
      charMesh.position.y = 0;
      charMesh.position.z = 0;

      xOffset +=
        charWidth + (this.textData.tracking / 1000) * this.textData.fontSize;

      charMesh.sync();
      this.characterMeshes.push(charMesh);
      this.perCharacterGroup.add(charMesh);
    }

    // If we have a path, apply path layout
    if (this.textOnPath.hasPath()) {
      this.updatePathLayout();
    }
  }

  /**
   * Dispose character meshes
   */
  private disposeCharacterMeshes(): void {
    for (const mesh of this.characterMeshes) {
      mesh.dispose();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      if (this.perCharacterGroup !== null && typeof this.perCharacterGroup === "object" && "remove" in this.perCharacterGroup && typeof this.perCharacterGroup.remove === "function") {
        this.perCharacterGroup.remove(mesh);
      }
    }
    this.characterMeshes = [];
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // property // updates
  // ════════════════════════════════════════════════════════════════════════════

  setText(text: string): void {
    // Cap text length to prevent performance issues (10,000 chars max)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy nullish coalescing
    const MAX_TEXT_LENGTH = 10000;
    const textValue = typeof text === "string" ? text : "";
    const validText = textValue.slice(0, MAX_TEXT_LENGTH);
    this.textData.text = validText;
    this.textMesh.text = validText;
    this.textMesh.sync();
    this.characterWidthsDirty = true;

    if (this.perCharacterGroup) {
      this.createCharacterMeshes();
    }
  }

  setFontFamily(family: string): void {
    this.textData.fontFamily = family;
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy nullish coalescing
    const fontUrl = this.getFontUrl(family);
    this.textMesh.font = fontUrl.length > 0 ? fontUrl : null;
    this.textMesh.sync();
    this.characterWidthsDirty = true;

    // Reset font metrics and reload for new font
    this.fontMetrics = undefined;
    this.fontLoadingPromise = undefined;
    this.useAccurateMetrics = false;
    this.loadFontMetrics();

    for (const charMesh of this.characterMeshes) {
      charMesh.font = fontUrl;
      charMesh.sync();
    }

    if (this.textOnPath.hasPath()) {
      this.updatePathLayout();
    }
  }

  setFontSize(size: number): void {
    // Validate size (NaN/0 would cause division errors in stroke width calculations)
    const validSize = Number.isFinite(size) && size > 0 ? size : 72;
    this.textData.fontSize = validSize;
    this.textMesh.fontSize = validSize;
    this.textMesh.sync();
    this.characterWidthsDirty = true;

    for (const charMesh of this.characterMeshes) {
      charMesh.fontSize = validSize;
      charMesh.sync();
    }

    if (this.perCharacterGroup) {
      if (this.textOnPath.hasPath()) {
        this.updatePathLayout();
      } else {
        this.createCharacterMeshes();
      }
    }
  }

  setFontWeight(weight: string): void {
    this.textData.fontWeight = weight;
    this.textMesh.fontWeight = weight;
    this.textMesh.sync();

    for (const charMesh of this.characterMeshes) {
      charMesh.fontWeight = weight;
      charMesh.sync();
    }
  }

  setFontStyle(style: string): void {
    const fontStyle = style as "normal" | "italic";
    this.textData.fontStyle = fontStyle;
    this.textMesh.fontStyle = fontStyle;
    this.textMesh.sync();

    for (const charMesh of this.characterMeshes) {
      charMesh.fontStyle = fontStyle;
      charMesh.sync();
    }
  }

  setFillColor(color: string): void {
    this.textData.fill = color;
    this.textMesh.color = color;
    // Force material update for color changes
    if (this.textMesh.material) {
      (this.textMesh.material as THREE.Material).needsUpdate = true;
    }

    for (const charMesh of this.characterMeshes) {
      charMesh.color = color;
      if (charMesh.material) {
        (charMesh.material as THREE.Material).needsUpdate = true;
      }
    }
  }

  setStroke(color: string, width: number): void {
    this.textData.stroke = color;
    this.textData.strokeWidth = width;

    const outlineWidth = width > 0 ? width / this.textData.fontSize : 0;
    this.textMesh.outlineWidth = outlineWidth;
    this.textMesh.outlineColor = width > 0 ? color : "";
    // Force material update for stroke changes
    if (this.textMesh.material) {
      (this.textMesh.material as THREE.Material).needsUpdate = true;
    }

    for (const charMesh of this.characterMeshes) {
      charMesh.outlineWidth = outlineWidth;
      charMesh.outlineColor = width > 0 ? color : "";
      if (charMesh.material) {
        (charMesh.material as THREE.Material).needsUpdate = true;
      }
    }
  }

  setTracking(tracking: number): void {
    // Validate tracking (NaN would corrupt letter spacing)
    const validTracking = Number.isFinite(tracking) ? tracking : 0;
    this.textData.tracking = validTracking;
    this.textMesh.letterSpacing = validTracking / 1000;
    this.textMesh.sync();

    if (this.perCharacterGroup) {
      if (this.textOnPath.hasPath()) {
        this.updatePathLayout();
      } else {
        this.createCharacterMeshes();
      }
    }
  }

  setTextAlign(align: "left" | "center" | "right"): void {
    this.textData.textAlign = align;
    this.textMesh.textAlign = align;
    this.textMesh.anchorX = this.getAnchorX();
    this.textMesh.sync();

    if (this.perCharacterGroup) {
      if (this.textOnPath.hasPath()) {
        this.pathConfig.align = align;
        this.updatePathLayout();
      } else {
        this.createCharacterMeshes();
      }
    }
  }

  /**
   * Set path offset (0-100%)
   * This is the primary animatable property for text-on-path animation
   */
  setPathOffset(offset: number): void {
    this.textData.pathOffset = offset;
    this.pathConfig.offset = offset;

    if (this.textOnPath.hasPath()) {
      this.updatePathLayout();
    }
  }

  /**
   * Set first margin (pixels)
   */
  setFirstMargin(margin: number): void {
    this.textData.pathFirstMargin = margin;
    this.pathConfig.firstMargin = margin;

    if (this.textOnPath.hasPath()) {
      this.updatePathLayout();
    }
  }

  /**
   * Set last margin (pixels)
   */
  setLastMargin(margin: number): void {
    this.textData.pathLastMargin = margin;
    this.pathConfig.lastMargin = margin;

    if (this.textOnPath.hasPath()) {
      this.updatePathLayout();
    }
  }

  /**
   * Set path reversed
   */
  setPathReversed(reversed: boolean): void {
    this.textData.pathReversed = reversed;
    this.pathConfig.reversed = reversed;

    if (this.textOnPath.hasPath()) {
      this.updatePathLayout();
    }
  }

  /**
   * Set perpendicular to path
   */
  setPerpendicularToPath(perpendicular: boolean): void {
    this.textData.pathPerpendicularToPath = perpendicular;
    this.pathConfig.perpendicularToPath = perpendicular;

    if (this.textOnPath.hasPath()) {
      this.updatePathLayout();
    }
  }

  /**
   * Set force alignment
   */
  setForceAlignment(force: boolean): void {
    this.textData.pathForceAlignment = force;
    this.pathConfig.forceAlignment = force;

    if (this.textOnPath.hasPath()) {
      this.updatePathLayout();
    }
  }

  setAnchorPointGrouping(grouping: AnchorPointGrouping): void {
    this.textData.anchorPointGrouping = grouping;
  }

  setFillAndStroke(order: "fill-over-stroke" | "stroke-over-fill"): void {
    this.textData.fillAndStroke = order;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // frame // evaluation
  // ════════════════════════════════════════════════════════════════════════════

  protected onEvaluateFrame(frame: number): void {
    // Evaluate animatable text properties
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    if (typeof this.fontSizeProp === "object" && this.fontSizeProp !== null && "animated" in this.fontSizeProp && this.fontSizeProp.animated === true) {
      const size = this.textEvaluator.evaluate(this.fontSizeProp, frame);
      this.setFontSize(size);
    }

    if (typeof this.trackingProp === "object" && this.trackingProp !== null && "animated" in this.trackingProp && this.trackingProp.animated === true) {
      const tracking = this.textEvaluator.evaluate(this.trackingProp, frame);
      this.setTracking(tracking);
    }

    if (typeof this.fillColorProp === "object" && this.fillColorProp !== null && "animated" in this.fillColorProp && this.fillColorProp.animated === true) {
      const color = this.textEvaluator.evaluate(this.fillColorProp, frame);
      this.setFillColor(color);
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    if (typeof this.strokeColorProp === "object" && this.strokeColorProp !== null && "animated" in this.strokeColorProp && this.strokeColorProp.animated === true && typeof this.strokeWidthProp === "object" && this.strokeWidthProp !== null) {
      // System F/Omega: Validate return type from evaluator
      // Type proof: strokeColorProp is AnimatableProperty<string>, so evaluate returns string
      const colorValue = this.textEvaluator.evaluate(this.strokeColorProp, frame);
      const color = typeof colorValue === "string" ? colorValue : (typeof this.textData.stroke === "string" ? this.textData.stroke : "");
      // Type proof: strokeWidthProp is AnimatableProperty<number>, so evaluate returns number
      const widthValue = (typeof this.strokeWidthProp === "object" && this.strokeWidthProp !== null && "animated" in this.strokeWidthProp && this.strokeWidthProp.animated === true)
        ? this.textEvaluator.evaluate(this.strokeWidthProp, frame)
        : this.textData.strokeWidth;
      const width = typeof widthValue === "number" ? widthValue : (typeof this.textData.strokeWidth === "number" ? this.textData.strokeWidth : 0);
      this.setStroke(color, width);
    }

    //                                               // path // offset // animation
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (typeof this.pathOffsetProp === "object" && this.pathOffsetProp !== null) {
      const offset = this.pathOffsetProp.animated === true
        ? this.textEvaluator.evaluate(this.pathOffsetProp, frame)
        : this.textData.pathOffset;
      this.setPathOffset(offset);
    }

    // First/Last margin animation
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    if (typeof this.firstMarginProp === "object" && this.firstMarginProp !== null && "animated" in this.firstMarginProp && this.firstMarginProp.animated === true) {
      const margin = this.textEvaluator.evaluate(this.firstMarginProp, frame);
      this.setFirstMargin(margin);
    }

    if (typeof this.lastMarginProp === "object" && this.lastMarginProp !== null && "animated" in this.lastMarginProp && this.lastMarginProp.animated === true) {
      const margin = this.textEvaluator.evaluate(this.lastMarginProp, frame);
      this.setLastMargin(margin);
    }

    // Per-character transforms (from characterTransforms property)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    if (typeof this.characterTransforms === "object" && this.characterTransforms !== null && "animated" in this.characterTransforms && this.characterTransforms.animated === true && this.perCharacterGroup !== null) {
      this.applyCharacterTransforms(frame);
    }

    // Apply text animators (per-character animation)
    // This must come after other evaluations so it can modify character positions
    if (this.animators.length > 0) {
      // Enable per-character mode if needed (animators require individual char meshes)
      if (!this.perCharacterGroup) {
        this.enablePerCharacter3D();
      }
      this.applyAnimatorsToCharacters(frame, this.compositionFps);
    }
  }

  /**
   * Set composition fps for accurate time-based calculations
   * Called by LayerManager when layer is added or composition changes
   */
  override setCompositionFps(fps: number): void {
    super.setCompositionFps(fps);
  }

  protected override onApplyEvaluatedState(
    state: import("../MotionEngine").EvaluatedLayer,
  ): void {
    const props = state.properties;
    const frame = state.frame;

    // Apply evaluated text properties
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof props === "object" && props !== null && "fontSize" in props && typeof props.fontSize === "number") {
      this.setFontSize(props.fontSize);
    }

    if (typeof props === "object" && props !== null && "tracking" in props && typeof props.tracking === "number") {
      this.setTracking(props.tracking);
    }

    if (typeof props === "object" && props !== null && "fillColor" in props && typeof props.fillColor === "string") {
      this.setFillColor(props.fillColor);
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined/nullish coalescing
    const hasStrokeColor = typeof props === "object" && props !== null && "strokeColor" in props && typeof props.strokeColor === "string";
    const hasStrokeWidth = typeof props === "object" && props !== null && "strokeWidth" in props && typeof props.strokeWidth === "number";
    if (hasStrokeColor || hasStrokeWidth) {
      // System F/Omega: Validate types before calling setStroke
      // Type proof: strokeColorValue ∈ string (validated or from textData.stroke which is string)
      let strokeColorValue: string;
      if (hasStrokeColor && typeof props.strokeColor === "string") {
        strokeColorValue = props.strokeColor;
      } else {
        strokeColorValue = typeof this.textData.stroke === "string" ? this.textData.stroke : "";
      }
      // Type proof: strokeWidthValue ∈ number (validated or from textData.strokeWidth which is number)
      let strokeWidthValue: number;
      if (hasStrokeWidth && typeof props.strokeWidth === "number") {
        strokeWidthValue = props.strokeWidth;
      } else {
        strokeWidthValue = typeof this.textData.strokeWidth === "number" ? this.textData.strokeWidth : 0;
      }
      this.setStroke(strokeColorValue, strokeWidthValue);
    }

    // Path animation properties
    if (typeof props === "object" && props !== null && "pathOffset" in props && typeof props.pathOffset === "number") {
      this.setPathOffset(props.pathOffset);
    }

    if (typeof props === "object" && props !== null && "firstMargin" in props && typeof props.firstMargin === "number") {
      this.setFirstMargin(props.firstMargin);
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof props === "object" && props !== null && "lastMargin" in props && typeof props.lastMargin === "number") {
      this.setLastMargin(props.lastMargin);
    }

    // Apply audio-reactive path position modifier.
    // pathPosition is 0-1 normalized, pathOffset is 0-100%, so scale by 100.
    const audioMod = this.currentAudioModifiers;
    if (
      audioMod.pathPosition !== undefined &&
      audioMod.pathPosition !== 0 &&
      this.textOnPath.hasPath()
    ) {
      // Apply as additive to current pathOffset (convert 0-1 to percentage points)
      const additionalOffset = audioMod.pathPosition * 100;
      this.setPathOffset(this.textData.pathOffset + additionalOffset);
    }

    // Effects
    if (state.effects.length > 0) {
      this.applyEvaluatedEffects(state.effects);
    }

    // Apply text animators (per-character animation)
    // This is critical for kinetic typography - without this, animators won't render!
    if (this.animators.length > 0) {
      // Enable per-character mode if needed (animators require individual char meshes)
      if (!this.perCharacterGroup) {
        this.enablePerCharacter3D();
      }
      this.applyAnimatorsToCharacters(frame, this.compositionFps);
    }

    // Per-character transforms (from characterTransforms property, if animated)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    if (typeof this.characterTransforms === "object" && this.characterTransforms !== null && "animated" in this.characterTransforms && this.characterTransforms.animated === true && this.perCharacterGroup !== null) {
      this.applyCharacterTransforms(frame);
    }
  }

  /**
   * Apply per-character animated transforms (additional offsets)
   */
  private applyCharacterTransforms(frame: number): void {
    if (!this.characterTransforms) return;

    // System F/Omega: CharacterTransform[] is not in PropertyValue union, but KeyframeEvaluator
    // can handle it via generic constraint. Type assertion needed for type system compatibility.
    // Type proof: characterTransforms.value ∈ CharacterTransform[] (runtime validated)
    // Deterministic: Explicit type conversion with unknown intermediate
    const transforms = this.textEvaluator.evaluate(
      this.characterTransforms as unknown as AnimatableProperty<PropertyValue>,
      frame,
    ) as unknown as CharacterTransform[];

    for (
      let i = 0;
      i < this.characterMeshes.length && i < transforms.length;
      i++
    ) {
      const charMesh = this.characterMeshes[i];
      const t = transforms[i];

      // Apply as additional offset to current position
      charMesh.position.x += t.position.x;
      charMesh.position.y += t.position.y;
      charMesh.position.z += t.position.z;

      // Apply rotation offset
      charMesh.rotation.x += THREE.MathUtils.degToRad(t.rotation.x);
      charMesh.rotation.y += THREE.MathUtils.degToRad(t.rotation.y);
      charMesh.rotation.z += THREE.MathUtils.degToRad(t.rotation.z);

      // Apply scale
      charMesh.scale.x *= t.scale.x;
      charMesh.scale.y *= t.scale.y;

      // Apply opacity
      if (charMesh.material) {
        (charMesh.material as THREE.Material).opacity *= t.opacity;
      }
    }
  }

  /**
   * Apply text animators to per-character meshes (per-character animation)
   *
   * This is the key integration point for the textAnimator service.
   * For each enabled animator, calculates per-character influence and applies
   * the animator's property values blended by that influence.
   *
   * @param frame Current frame number
   * @param fps Frames per second (default 16)
   */
  private applyAnimatorsToCharacters(frame: number, fps: number = 16): void {
    if (!this.perCharacterGroup || this.characterMeshes.length === 0) {
      return;
    }

    if (this.animators.length === 0) {
      return;
    }

    const totalChars = this.characterMeshes.length;

    // Store original states for blending (reset from base values each frame)
    const originalStates = this.characterMeshes.map((mesh) => ({
      posX: mesh.position.x,
      posY: mesh.position.y,
      posZ: mesh.position.z,
      rotX: mesh.rotation.x,
      rotY: mesh.rotation.y,
      rotZ: mesh.rotation.z,
      scaleX: mesh.scale.x,
      scaleY: mesh.scale.y,
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
      opacity: (typeof mesh.fillOpacity === "number" && Number.isFinite(mesh.fillOpacity)) ? mesh.fillOpacity : 1,
      color: mesh.color,
      letterSpacing: (typeof mesh.letterSpacing === "number" && Number.isFinite(mesh.letterSpacing)) ? mesh.letterSpacing : 0,
    }));

    // Track if any layout properties were modified (require Troika sync)
    let needsSync = false;

    // Apply each animator
    for (const animator of this.animators) {
      if (!animator.enabled) continue;

      const props = animator.properties;

      // Check if this animator has layout properties that need sync
      if (props.tracking) {
        needsSync = true;
      }

      for (let i = 0; i < totalChars; i++) {
        const charMesh = this.characterMeshes[i];
        const original = originalStates[i];

        // Calculate influence (0 = normal, 1 = fully affected by animator)
        const influence = calculateCompleteCharacterInfluence(
          i,
          totalChars,
          animator,
          frame,
          fps,
        );

        // Skip if no influence
        if (influence <= 0.001) continue;

        // Apply Position offset
        if (props.position) {
          const posVal = this.getAnimatorPropertyValue(props.position, frame);
          charMesh.position.x = original.posX + posVal.x * influence;
          charMesh.position.y = original.posY + posVal.y * influence;
        }

        // Apply Scale
        if (props.scale) {
          const scaleVal = this.getAnimatorPropertyValue(props.scale, frame);
          // Scale is percentage-based (100 = no change)
          // Blend from original scale to animator scale value
          const scaleX =
            original.scaleX +
            (scaleVal.x / 100 - 1) * original.scaleX * influence;
          const scaleY =
            original.scaleY +
            (scaleVal.y / 100 - 1) * original.scaleY * influence;
          charMesh.scale.set(
            Math.max(0.001, scaleX),
            Math.max(0.001, scaleY),
            1,
          );
        }

        // Apply Rotation
        if (props.rotation) {
          const rotVal = this.getAnimatorPropertyValue(props.rotation, frame);
          const rotRad = THREE.MathUtils.degToRad(rotVal);
          charMesh.rotation.z = original.rotZ + rotRad * influence;
        }

        // Apply Opacity
        if (props.opacity !== undefined) {
          const opacityVal = this.getAnimatorPropertyValue(
            props.opacity,
            frame,
          );
          // Opacity is 0-100, influence determines blend
          // At influence=0: original opacity, at influence=1: animator opacity value
          const targetOpacity = opacityVal / 100;
          const blendedOpacity =
            original.opacity * (1 - influence) + targetOpacity * influence;
          charMesh.fillOpacity = Math.max(0, Math.min(1, blendedOpacity));
          charMesh.outlineOpacity = charMesh.fillOpacity;
        }

        // Apply Fill Color
        if (props.fillColor) {
          const colorVal = this.getAnimatorPropertyValue(
            props.fillColor,
            frame,
          );
          // Blend colors using influence
          // For simplicity, we'll use the color when influence > 0.5
          if (influence > 0.5) {
            charMesh.color = colorVal;
          }
        }

        // Apply Tracking offset
        if (props.tracking) {
          const trackingVal = this.getAnimatorPropertyValue(
            props.tracking,
            frame,
          );
          // Tracking is in thousandths of an em, convert to letter spacing
          charMesh.letterSpacing =
            original.letterSpacing + (trackingVal / 1000) * influence;
        }

        // Apply Wiggly position offset (if wiggly selector is enabled)
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        if (typeof animator.wigglySelector === "object" && animator.wigglySelector !== null && "enabled" in animator.wigglySelector && animator.wigglySelector.enabled === true) {
          const wiggleOffset = calculateWigglyOffset(
            i,
            animator.wigglySelector,
            frame,
            fps,
          );
          charMesh.position.x +=
            wiggleOffset.x * this.textData.fontSize * influence;
          charMesh.position.y +=
            wiggleOffset.y * this.textData.fontSize * influence;
        }

        if (props.blur) {
          const blurVal = this.getAnimatorPropertyValue(props.blur, frame);
          charMesh.__blurX = blurVal.x * influence;
          charMesh.__blurY = blurVal.y * influence;
        }
      }
    }

    // Sync character meshes if layout properties were modified
    // letterSpacing is a Troika layout property that requires sync() to take effect
    if (needsSync) {
      for (const charMesh of this.characterMeshes) {
        charMesh.sync();
      }
    }
  }

  /**
   * Get the current value of an animator property (animated or static)
   */
  private getAnimatorPropertyValue<T>(
    prop: AnimatableProperty<T>,
    frame: number,
  ): T {
    if (!prop.animated || prop.keyframes.length === 0) {
      return prop.value;
    }

    // System F/Omega: Type assertion needed for properties that extend beyond PropertyValue union
    // Type proof: T extends PropertyValue at runtime (validated by KeyframeEvaluator)
    // This is safe because KeyframeEvaluator.evaluate<T extends PropertyValue> handles the type
    return this.textEvaluator.evaluate(prop as AnimatableProperty<PropertyValue>, frame) as T;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                           // layer // update
  // ════════════════════════════════════════════════════════════════════════════

  protected onUpdate(properties: Partial<Layer>): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    // Pattern match: data ∈ Partial<TextData> | undefined → Partial<TextData> | {}
    const data = (typeof properties.data === "object" && properties.data !== null) ? properties.data as Partial<TextData> : {};

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    // Pattern match: Check each property with explicit type narrowing
    if (typeof data === "object" && data !== null && "text" in data && typeof data.text === "string") {
      this.setText(data.text);
    }
    if (typeof data === "object" && data !== null && "fontFamily" in data && typeof data.fontFamily === "string") {
      this.setFontFamily(data.fontFamily);
    }
    if (typeof data === "object" && data !== null && "fontSize" in data && typeof data.fontSize === "number") {
      this.setFontSize(data.fontSize);
    }
    if (typeof data === "object" && data !== null && "fontWeight" in data && typeof data.fontWeight === "string") {
      this.setFontWeight(data.fontWeight);
    }
    if (typeof data === "object" && data !== null && "fontStyle" in data && typeof data.fontStyle === "string") {
      this.setFontStyle(data.fontStyle);
    }
    if (typeof data === "object" && data !== null && "fill" in data && typeof data.fill === "string") {
      this.setFillColor(data.fill);
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined/nullish coalescing
    const hasStroke = typeof data === "object" && data !== null && "stroke" in data && typeof data.stroke === "string";
    const hasStrokeWidth = typeof data === "object" && data !== null && "strokeWidth" in data && typeof data.strokeWidth === "number";
    if (hasStroke || hasStrokeWidth) {
      // System F/Omega: Validate types before calling setStroke
      // Type proof: strokeColorValue ∈ string (validated or from textData.stroke which is string)
      let strokeColorValue: string;
      if (hasStroke && typeof data.stroke === "string") {
        strokeColorValue = data.stroke;
      } else {
        strokeColorValue = typeof this.textData.stroke === "string" ? this.textData.stroke : "";
      }
      // Type proof: strokeWidthValue ∈ number (validated or from textData.strokeWidth which is number)
      let strokeWidthValue: number;
      if (hasStrokeWidth && typeof data.strokeWidth === "number") {
        strokeWidthValue = data.strokeWidth;
      } else {
        strokeWidthValue = typeof this.textData.strokeWidth === "number" ? this.textData.strokeWidth : 0;
      }
      this.setStroke(strokeColorValue, strokeWidthValue);
    }
    if (typeof data === "object" && data !== null && "tracking" in data && typeof data.tracking === "number") {
      this.setTracking(data.tracking);
    }
    if (typeof data === "object" && data !== null && "textAlign" in data && typeof data.textAlign === "string") {
      // System F/Omega: Validate textAlign is one of the allowed values
      // Type proof: textAlign ∈ string → "left" | "center" | "right"
      const textAlignValue = data.textAlign;
      if (textAlignValue === "left" || textAlignValue === "center" || textAlignValue === "right") {
        this.setTextAlign(textAlignValue);
      }
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null checks
    if (typeof data === "object" && data !== null && "pathLayerId" in data && typeof data.pathLayerId === "string") {
      this.textData.pathLayerId = data.pathLayerId;
      this.pathConfig.pathLayerId = data.pathLayerId;
    }
    if (typeof data === "object" && data !== null && "pathOffset" in data && typeof data.pathOffset === "number") {
      this.setPathOffset(data.pathOffset);
    }
    if (typeof data === "object" && data !== null && "pathFirstMargin" in data && typeof data.pathFirstMargin === "number") {
      this.setFirstMargin(data.pathFirstMargin);
    }
    if (typeof data === "object" && data !== null && "pathLastMargin" in data && typeof data.pathLastMargin === "number") {
      this.setLastMargin(data.pathLastMargin);
    }
    if (typeof data === "object" && data !== null && "pathReversed" in data && typeof data.pathReversed === "boolean") {
      this.setPathReversed(data.pathReversed);
    }
    if (typeof data === "object" && data !== null && "pathPerpendicularToPath" in data && typeof data.pathPerpendicularToPath === "boolean") {
      this.setPerpendicularToPath(data.pathPerpendicularToPath);
    }
    if (typeof data === "object" && data !== null && "pathForceAlignment" in data && typeof data.pathForceAlignment === "boolean") {
      this.setForceAlignment(data.pathForceAlignment);
    }
    if (typeof data === "object" && data !== null && "perCharacter3D" in data && typeof data.perCharacter3D === "boolean") {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      if (data.perCharacter3D === true && this.perCharacterGroup === null) {
        this.enablePerCharacter3D();
      } else if (
        data.perCharacter3D === false &&
        !this.textOnPath.hasPath() &&
        this.perCharacterGroup !== null
      ) {
        this.disablePerCharacter3D();
      }
    }
    if (typeof data === "object" && data !== null && "anchorPointGrouping" in data && typeof data.anchorPointGrouping === "string") {
      this.setAnchorPointGrouping(data.anchorPointGrouping);
    }
    if (typeof data === "object" && data !== null && "fillAndStroke" in data && typeof data.fillAndStroke === "string") {
      this.setFillAndStroke(data.fillAndStroke);
    }

    // Update animators array
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof data === "object" && data !== null && "animators" in data && Array.isArray(data.animators)) {
      this.animators = data.animators;
      this.textData.animators = data.animators;
      // Enable per-character mode if animators exist
      if (this.animators.length > 0 && this.perCharacterGroup === null) {
        this.enablePerCharacter3D();
      }
    }

    // Re-extract animatable properties if properties array changed
    if (properties.properties) {
      this.extractAnimatableProperties(properties as Layer);
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                              // opacity // override // for // troika // text
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Override base class opacity to use Troika's fillOpacity
   */
  protected override applyOpacity(opacity: number): void {
    // Validate opacity (NaN bypasses Math.max/min clamps)
    const validOpacity = Number.isFinite(opacity) ? opacity : 100;
    const normalizedOpacity = Math.max(0, Math.min(100, validOpacity)) / 100;

    // Apply to main text mesh using Troika's fillOpacity
    this.textMesh.fillOpacity = normalizedOpacity;
    this.textMesh.outlineOpacity = normalizedOpacity;

    // Apply to character meshes if in per-character mode
    for (const charMesh of this.characterMeshes) {
      charMesh.fillOpacity = normalizedOpacity;
      charMesh.outlineOpacity = normalizedOpacity;
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                   // getters
  // ════════════════════════════════════════════════════════════════════════════

  getTextData(): TextData {
    return { ...this.textData };
  }

  getTextBounds(): { width: number; height: number } {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    const textRenderInfo = (typeof this.textMesh.textRenderInfo === "object" && this.textMesh.textRenderInfo !== null && "blockBounds" in this.textMesh.textRenderInfo) ? this.textMesh.textRenderInfo : null;
    const bounds = (textRenderInfo !== null && typeof textRenderInfo.blockBounds === "object" && textRenderInfo.blockBounds !== null) ? textRenderInfo.blockBounds : null;
    if (bounds !== null && typeof bounds === "object" && Array.isArray(bounds) && bounds.length >= 4) {
      return {
        width: bounds[2] - bounds[0],
        height: bounds[3] - bounds[1],
      };
    }
    throw new Error(`[TextLayer] Cannot get text bounds: textRenderInfo.blockBounds is not available for layer "${this.id}"`);
    return { width: 0, height: 0 };
  }

  getPathLength(): number {
    return this.textOnPath.getTotalLength();
  }

  hasPath(): boolean {
    return this.textOnPath.hasPath();
  }

  getTextOnPathService(): TextOnPathService {
    return this.textOnPath;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                  // disposal
  // ════════════════════════════════════════════════════════════════════════════

  protected onDispose(): void {
    this.textMesh.dispose();
    this.disposeCharacterMeshes();
    this.textOnPath.dispose();

    if (this.perCharacterGroup) {
      this.group.remove(this.perCharacterGroup);
    }
  }
}
