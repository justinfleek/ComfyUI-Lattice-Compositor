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

import * as THREE from 'three';
import { Text as TroikaText } from 'troika-three-text';
import type { Layer, TextData, AnimatableProperty, ControlPoint } from '@/types/project';
import type { ResourceManager } from '../core/ResourceManager';
import { BaseLayer } from './BaseLayer';
import { KeyframeEvaluator } from '../animation/KeyframeEvaluator';
import {
  TextOnPathService,
  createDefaultPathConfig,
  type TextOnPathConfig,
  type CharacterPlacement,
} from '@/services/textOnPath';
import {
  calculateCompleteCharacterInfluence,
  calculateWigglyOffset,
} from '@/services/textAnimator';
import type { TextAnimator } from '@/types/project';

// ============================================================================
// TYPES
// ============================================================================

/** Anchor point grouping mode for text animation */
export type AnchorPointGrouping = 'character' | 'word' | 'line' | 'all';

/** Fill and stroke rendering order */
export type FillStrokeOrder = 'perCharacter' | 'fillOverStroke' | 'strokeOverFill';

/** Inter-character blending mode */
export type InterCharacterBlending = 'normal' | 'multiply' | 'screen' | 'overlay';

/** Per-character transform for animation */
export interface CharacterTransform {
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  scale: { x: number; y: number };
  opacity: number;
}

// ============================================================================
// TEXT LAYER
// ============================================================================

export class TextLayer extends BaseLayer {
  private readonly resources: ResourceManager;

  // Text rendering
  private textMesh: InstanceType<typeof TroikaText>;
  private perCharacterGroup: THREE.Group | null = null;
  private characterMeshes: InstanceType<typeof TroikaText>[] = [];

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

  // Path following service
  private textOnPath: TextOnPathService;
  private pathConfig: TextOnPathConfig;
  private pathControlPoints: ControlPoint[] = [];
  private pathClosed: boolean = false;

  // Character width cache (recalculated when text/font changes)
  private characterWidths: number[] = [];
  private characterWidthsDirty: boolean = true;

  // Text animators (After Effects-style per-character animation)
  private animators: TextAnimator[] = [];

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

    // Extract animatable properties
    this.extractAnimatableProperties(layerData);

    // Create text mesh
    this.textMesh = this.createTextMesh();
    this.group.add(this.textMesh);

    // If per-character 3D or path following is enabled, use character mode
    if (this.textData.perCharacter3D || this.textData.pathLayerId) {
      this.enablePerCharacter3D();
    }

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  // ============================================================================
  // INITIALIZATION
  // ============================================================================

  /**
   * Extract text data from layer, with defaults matching AE
   */
  private extractTextData(layerData: Layer): TextData {
    const data = layerData.data as TextData | null;

    return {
      text: data?.text ?? 'Text',
      fontFamily: data?.fontFamily ?? 'Impact',
      fontSize: data?.fontSize ?? 72,
      fontWeight: data?.fontWeight ?? '400',
      fontStyle: data?.fontStyle ?? 'normal',
      fill: data?.fill ?? '#ffffff',
      stroke: data?.stroke ?? '',
      strokeWidth: data?.strokeWidth ?? 0,

      // Character properties
      tracking: data?.tracking ?? 0,
      lineSpacing: data?.lineSpacing ?? 0,
      lineAnchor: data?.lineAnchor ?? 50,
      characterOffset: data?.characterOffset ?? 0,
      characterValue: data?.characterValue ?? 0,
      blur: data?.blur ?? { x: 0, y: 0 },

      // Paragraph (aliases)
      letterSpacing: data?.letterSpacing ?? data?.tracking ?? 0,
      lineHeight: data?.lineHeight ?? data?.lineSpacing ?? 1.2,
      textAlign: data?.textAlign ?? 'left',

      // Path options (full AE parity)
      pathLayerId: data?.pathLayerId ?? null,
      pathReversed: data?.pathReversed ?? false,
      pathPerpendicularToPath: data?.pathPerpendicularToPath ?? true,
      pathForceAlignment: data?.pathForceAlignment ?? false,
      pathFirstMargin: data?.pathFirstMargin ?? 0,
      pathLastMargin: data?.pathLastMargin ?? 0,
      pathOffset: data?.pathOffset ?? 0,
      pathAlign: data?.pathAlign ?? 'left',

      // More Options
      anchorPointGrouping: data?.anchorPointGrouping ?? 'character',
      groupingAlignment: data?.groupingAlignment ?? { x: 0, y: 0 },
      fillAndStroke: data?.fillAndStroke ?? 'fill-over-stroke',
      interCharacterBlending: data?.interCharacterBlending ?? 'normal',

      // 3D
      perCharacter3D: data?.perCharacter3D ?? false,

      // Text animators
      animators: data?.animators ?? [],
    };

    // Also store animators separately for quick access
    this.animators = data?.animators ?? [];
  }

  /**
   * Extract animatable properties from layer.properties array
   */
  private extractAnimatableProperties(layerData: Layer): void {
    if (!layerData.properties) return;

    for (const prop of layerData.properties) {
      switch (prop.name) {
        case 'Font Size':
          this.fontSizeProp = prop as AnimatableProperty<number>;
          break;
        case 'Tracking':
          this.trackingProp = prop as AnimatableProperty<number>;
          break;
        case 'Line Spacing':
          this.lineSpacingProp = prop as AnimatableProperty<number>;
          break;
        case 'Fill Color':
          this.fillColorProp = prop as AnimatableProperty<string>;
          break;
        case 'Stroke Color':
          this.strokeColorProp = prop as AnimatableProperty<string>;
          break;
        case 'Stroke Width':
          this.strokeWidthProp = prop as AnimatableProperty<number>;
          break;
        case 'Path Offset':
          this.pathOffsetProp = prop as AnimatableProperty<number>;
          break;
        case 'First Margin':
          this.firstMarginProp = prop as AnimatableProperty<number>;
          break;
        case 'Last Margin':
          this.lastMarginProp = prop as AnimatableProperty<number>;
          break;
        case 'Character Offset':
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

  // ============================================================================
  // TEXT MESH CREATION
  // ============================================================================

  /**
   * Create Troika text mesh with current settings
   */
  private createTextMesh(): InstanceType<typeof TroikaText> {
    const text = new TroikaText();

    // Core text content
    text.text = this.textData.text;

    // Font settings
    text.font = this.getFontUrl(this.textData.fontFamily) ?? null;
    text.fontSize = this.textData.fontSize;

    // Font weight and style (using type assertions - Troika supports these but types are incomplete)
    (text as any).fontWeight = this.textData.fontWeight || '400';
    (text as any).fontStyle = this.textData.fontStyle || 'normal';

    // Colors
    text.color = this.textData.fill;
    if (this.textData.stroke && this.textData.strokeWidth > 0) {
      text.outlineWidth = this.textData.strokeWidth / this.textData.fontSize;
      text.outlineColor = this.textData.stroke;
    }

    // Spacing - Troika uses em units for letter spacing
    text.letterSpacing = (this.textData.tracking || 0) / 1000;
    text.lineHeight = this.textData.lineHeight || 1.2;

    // Alignment
    text.textAlign = this.textData.textAlign;
    text.anchorX = this.getAnchorX();
    text.anchorY = 'middle';

    // Rendering quality settings
    text.depthOffset = 0;
    text.renderOrder = 0;

    // Improve text rendering quality - higher SDF glyph size for sharper edges
    // Max useful value is around 256 (higher = better quality but more memory)
    (text as any).sdfGlyphSize = 256; // Default is 64, higher = sharper text

    // GPU texture precision for better rendering
    (text as any).gpuAccelerateSDF = true;

    // Enable smooth outline edges
    if (this.textData.strokeWidth > 0) {
      (text as any).outlineBlur = 0.003; // Slight blur for smoother outline edges
    }

    // Trigger initial sync
    text.sync();

    return text;
  }

  /**
   * Get font URL for Troika
   */
  private getFontUrl(fontFamily: string): string | undefined {
    const systemFonts = [
      'Arial', 'Helvetica', 'Times New Roman', 'Georgia', 'Verdana',
      'Courier New', 'Impact', 'Comic Sans MS', 'Trebuchet MS', 'Palatino',
    ];

    if (systemFonts.includes(fontFamily)) {
      return undefined;
    }

    const googleFonts: Record<string, string> = {
      'Roboto': 'https://fonts.gstatic.com/s/roboto/v30/KFOmCnqEu92Fr1Mu4mxK.woff2',
      'Open Sans': 'https://fonts.gstatic.com/s/opensans/v35/memSYaGs126MiZpBA-UvWbX2vVnXBbObj2OVZyOOSr4dVJWUgsjZ0B4gaVI.woff2',
      'Lato': 'https://fonts.gstatic.com/s/lato/v24/S6uyw4BMUTPHjx4wXg.woff2',
      'Montserrat': 'https://fonts.gstatic.com/s/montserrat/v26/JTUHjIg1_i6t8kCHKm4532VJOt5-QNFgpCtr6Hw5aXo.woff2',
      'Oswald': 'https://fonts.gstatic.com/s/oswald/v53/TK3_WkUHHAIjg75cFRf3bXL8LICs1_FvsUZiYA.woff2',
      'Poppins': 'https://fonts.gstatic.com/s/poppins/v21/pxiEyp8kv8JHgFVrJJfecg.woff2',
    };

    return googleFonts[fontFamily];
  }

  /**
   * Get anchor X based on text alignment
   * Note: Swapped to match intuitive arrow button behavior:
   * - ◀ (left) button makes text appear on LEFT (anchor right edge)
   * - ▶ (right) button makes text appear on RIGHT (anchor left edge)
   */
  private getAnchorX(): 'left' | 'center' | 'right' {
    switch (this.textData.textAlign) {
      case 'left': return 'right';  // Anchor right edge so text extends left
      case 'right': return 'left';  // Anchor left edge so text extends right
      default: return 'center';
    }
  }

  // ============================================================================
  // PATH INTEGRATION
  // ============================================================================

  /**
   * Set the path from SplineLayer control points
   * Called by LayerManager when connecting text to a spline
   */
  setPathFromControlPoints(controlPoints: ControlPoint[], closed: boolean = false): void {
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
    this.textData.pathLayerId = null;
    this.pathConfig.pathLayerId = null;
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
      this.textData.fontSize
    );

    // Apply placements to character meshes
    this.applyPlacements(placements);
  }

  /**
   * Apply character placements to meshes
   */
  private applyPlacements(placements: CharacterPlacement[]): void {
    for (let i = 0; i < this.characterMeshes.length && i < placements.length; i++) {
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
   */
  private ensureCharacterWidths(): void {
    if (!this.characterWidthsDirty) return;

    this.characterWidths = [];
    const text = this.textData.text;

    // Use approximate width based on font size
    // A more accurate method would measure actual glyph widths from Troika
    const avgCharWidth = this.textData.fontSize * 0.6;

    for (let i = 0; i < text.length; i++) {
      const char = text[i];
      // Narrow characters
      if ('iIl1|!.,;:\'"'.includes(char)) {
        this.characterWidths.push(avgCharWidth * 0.4);
      }
      // Wide characters
      else if ('mwMW'.includes(char)) {
        this.characterWidths.push(avgCharWidth * 1.3);
      }
      // Space
      else if (char === ' ') {
        this.characterWidths.push(avgCharWidth * 0.5);
      }
      // Average
      else {
        this.characterWidths.push(avgCharWidth);
      }
    }

    this.characterWidthsDirty = false;
  }

  // ============================================================================
  // PER-CHARACTER 3D MODE
  // ============================================================================

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
    const totalWidth = this.characterWidths.reduce((a, b) => a + b, 0) +
      (text.length - 1) * (this.textData.tracking / 1000) * this.textData.fontSize;

    // Determine start X based on alignment
    let startX = 0;
    switch (this.textData.textAlign) {
      case 'center':
        startX = -totalWidth / 2;
        break;
      case 'right':
        startX = -totalWidth;
        break;
      default:
        startX = 0;
    }

    xOffset = startX;

    for (let i = 0; i < text.length; i++) {
      const char = text[i];
      const charMesh = new TroikaText();

      charMesh.text = char;
      charMesh.font = this.getFontUrl(this.textData.fontFamily) ?? null;
      charMesh.fontSize = this.textData.fontSize;
      (charMesh as any).fontWeight = this.textData.fontWeight || '400';
      (charMesh as any).fontStyle = this.textData.fontStyle || 'normal';
      charMesh.color = this.textData.fill;
      charMesh.anchorX = 'center';
      charMesh.anchorY = 'middle';

      if (this.textData.stroke && this.textData.strokeWidth > 0) {
        charMesh.outlineWidth = this.textData.strokeWidth / this.textData.fontSize;
        charMesh.outlineColor = this.textData.stroke;
        (charMesh as any).outlineBlur = 0.005;
      }

      // Quality settings for character mesh
      (charMesh as any).sdfGlyphSize = 128;

      // Position character (for horizontal layout)
      const charWidth = this.characterWidths[i];
      charMesh.position.x = xOffset + charWidth / 2;
      charMesh.position.y = 0;
      charMesh.position.z = 0;

      xOffset += charWidth + (this.textData.tracking / 1000) * this.textData.fontSize;

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
      this.perCharacterGroup?.remove(mesh);
    }
    this.characterMeshes = [];
  }

  // ============================================================================
  // PROPERTY UPDATES
  // ============================================================================

  setText(text: string): void {
    this.textData.text = text;
    this.textMesh.text = text;
    this.textMesh.sync();
    this.characterWidthsDirty = true;

    if (this.perCharacterGroup) {
      this.createCharacterMeshes();
    }
  }

  setFontFamily(family: string): void {
    this.textData.fontFamily = family;
    const fontUrl = this.getFontUrl(family) ?? null;
    this.textMesh.font = fontUrl;
    this.textMesh.sync();
    this.characterWidthsDirty = true;

    for (const charMesh of this.characterMeshes) {
      charMesh.font = fontUrl;
      charMesh.sync();
    }

    if (this.textOnPath.hasPath()) {
      this.updatePathLayout();
    }
  }

  setFontSize(size: number): void {
    this.textData.fontSize = size;
    this.textMesh.fontSize = size;
    this.textMesh.sync();
    this.characterWidthsDirty = true;

    for (const charMesh of this.characterMeshes) {
      charMesh.fontSize = size;
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
    (this.textMesh as any).fontWeight = weight;
    this.textMesh.sync();

    for (const charMesh of this.characterMeshes) {
      (charMesh as any).fontWeight = weight;
      charMesh.sync();
    }
  }

  setFontStyle(style: string): void {
    this.textData.fontStyle = style as 'normal' | 'italic';
    (this.textMesh as any).fontStyle = style;
    this.textMesh.sync();

    for (const charMesh of this.characterMeshes) {
      (charMesh as any).fontStyle = style;
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
    this.textMesh.outlineColor = width > 0 ? color : '';
    // Force material update for stroke changes
    if (this.textMesh.material) {
      (this.textMesh.material as THREE.Material).needsUpdate = true;
    }

    for (const charMesh of this.characterMeshes) {
      charMesh.outlineWidth = outlineWidth;
      charMesh.outlineColor = width > 0 ? color : '';
      if (charMesh.material) {
        (charMesh.material as THREE.Material).needsUpdate = true;
      }
    }
  }

  setTracking(tracking: number): void {
    this.textData.tracking = tracking;
    this.textMesh.letterSpacing = tracking / 1000;
    this.textMesh.sync();

    if (this.perCharacterGroup) {
      if (this.textOnPath.hasPath()) {
        this.updatePathLayout();
      } else {
        this.createCharacterMeshes();
      }
    }
  }

  setTextAlign(align: 'left' | 'center' | 'right'): void {
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

  setFillAndStroke(order: 'fill-over-stroke' | 'stroke-over-fill'): void {
    this.textData.fillAndStroke = order;
  }

  // ============================================================================
  // FRAME EVALUATION
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Evaluate animatable text properties
    if (this.fontSizeProp?.animated) {
      const size = this.textEvaluator.evaluate(this.fontSizeProp, frame);
      this.setFontSize(size);
    }

    if (this.trackingProp?.animated) {
      const tracking = this.textEvaluator.evaluate(this.trackingProp, frame);
      this.setTracking(tracking);
    }

    if (this.fillColorProp?.animated) {
      const color = this.textEvaluator.evaluate(this.fillColorProp, frame);
      this.setFillColor(color);
    }

    if (this.strokeColorProp?.animated && this.strokeWidthProp) {
      const color = this.textEvaluator.evaluate(this.strokeColorProp, frame);
      const width = this.strokeWidthProp.animated
        ? this.textEvaluator.evaluate(this.strokeWidthProp, frame)
        : this.textData.strokeWidth;
      this.setStroke(color, width);
    }

    // PATH OFFSET ANIMATION - The key animatable property for text-on-path
    if (this.pathOffsetProp) {
      const offset = this.pathOffsetProp.animated
        ? this.textEvaluator.evaluate(this.pathOffsetProp, frame)
        : this.textData.pathOffset;
      this.setPathOffset(offset);
    }

    // First/Last margin animation
    if (this.firstMarginProp?.animated) {
      const margin = this.textEvaluator.evaluate(this.firstMarginProp, frame);
      this.setFirstMargin(margin);
    }

    if (this.lastMarginProp?.animated) {
      const margin = this.textEvaluator.evaluate(this.lastMarginProp, frame);
      this.setLastMargin(margin);
    }

    // Per-character transforms (from characterTransforms property)
    if (this.characterTransforms?.animated && this.perCharacterGroup) {
      this.applyCharacterTransforms(frame);
    }

    // Apply text animators (After Effects-style per-character animation)
    // This must come after other evaluations so it can modify character positions
    if (this.animators.length > 0) {
      // Enable per-character mode if needed (animators require individual char meshes)
      if (!this.perCharacterGroup) {
        this.enablePerCharacter3D();
      }
      this.applyAnimatorsToCharacters(frame, 16); // TODO: get fps from composition
    }
  }

  protected override onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    const props = state.properties;

    // Apply evaluated text properties
    if (props['fontSize'] !== undefined) {
      this.setFontSize(props['fontSize'] as number);
    }

    if (props['tracking'] !== undefined) {
      this.setTracking(props['tracking'] as number);
    }

    if (props['fillColor'] !== undefined) {
      this.setFillColor(props['fillColor'] as string);
    }

    if (props['strokeColor'] !== undefined || props['strokeWidth'] !== undefined) {
      this.setStroke(
        (props['strokeColor'] as string) ?? this.textData.stroke,
        (props['strokeWidth'] as number) ?? this.textData.strokeWidth
      );
    }

    // Path animation properties
    if (props['pathOffset'] !== undefined) {
      this.setPathOffset(props['pathOffset'] as number);
    }

    if (props['firstMargin'] !== undefined) {
      this.setFirstMargin(props['firstMargin'] as number);
    }

    if (props['lastMargin'] !== undefined) {
      this.setLastMargin(props['lastMargin'] as number);
    }

    // Effects
    if (state.effects.length > 0) {
      this.applyEvaluatedEffects(state.effects);
    }
  }

  /**
   * Apply per-character animated transforms (additional offsets)
   */
  private applyCharacterTransforms(frame: number): void {
    if (!this.characterTransforms) return;

    const transforms = this.textEvaluator.evaluate(this.characterTransforms, frame);

    for (let i = 0; i < this.characterMeshes.length && i < transforms.length; i++) {
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
   * Apply text animators to per-character meshes (After Effects-style animation)
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
      opacity: mesh.fillOpacity ?? 1,
      color: mesh.color,
      letterSpacing: mesh.letterSpacing ?? 0,
    }));

    // Apply each animator
    for (const animator of this.animators) {
      if (!animator.enabled) continue;

      const props = animator.properties;

      for (let i = 0; i < totalChars; i++) {
        const charMesh = this.characterMeshes[i];
        const original = originalStates[i];

        // Calculate influence (0 = normal, 1 = fully affected by animator)
        const influence = calculateCompleteCharacterInfluence(
          i,
          totalChars,
          animator,
          frame,
          fps
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
          const scaleX = original.scaleX + ((scaleVal.x / 100) - 1) * original.scaleX * influence;
          const scaleY = original.scaleY + ((scaleVal.y / 100) - 1) * original.scaleY * influence;
          charMesh.scale.set(Math.max(0.001, scaleX), Math.max(0.001, scaleY), 1);
        }

        // Apply Rotation
        if (props.rotation) {
          const rotVal = this.getAnimatorPropertyValue(props.rotation, frame);
          const rotRad = THREE.MathUtils.degToRad(rotVal);
          charMesh.rotation.z = original.rotZ + rotRad * influence;
        }

        // Apply Opacity
        if (props.opacity !== undefined) {
          const opacityVal = this.getAnimatorPropertyValue(props.opacity, frame);
          // Opacity is 0-100, influence determines blend
          // At influence=0: original opacity, at influence=1: animator opacity value
          const targetOpacity = opacityVal / 100;
          const blendedOpacity = original.opacity * (1 - influence) + targetOpacity * influence;
          charMesh.fillOpacity = Math.max(0, Math.min(1, blendedOpacity));
          charMesh.outlineOpacity = charMesh.fillOpacity;
        }

        // Apply Fill Color
        if (props.fillColor) {
          const colorVal = this.getAnimatorPropertyValue(props.fillColor, frame);
          // Blend colors using influence
          // For simplicity, we'll use the color when influence > 0.5
          if (influence > 0.5) {
            charMesh.color = colorVal;
          }
        }

        // Apply Tracking offset
        if (props.tracking) {
          const trackingVal = this.getAnimatorPropertyValue(props.tracking, frame);
          // Tracking is in thousandths of an em, convert to letter spacing
          charMesh.letterSpacing = original.letterSpacing + (trackingVal / 1000) * influence;
        }

        // Apply Wiggly position offset (if wiggly selector is enabled)
        if (animator.wigglySelector?.enabled) {
          const wiggleOffset = calculateWigglyOffset(
            i,
            animator.wigglySelector,
            frame,
            fps
          );
          charMesh.position.x += wiggleOffset.x * this.textData.fontSize * influence;
          charMesh.position.y += wiggleOffset.y * this.textData.fontSize * influence;
        }

        // Apply Blur (if supported via material)
        if (props.blur) {
          // Blur requires special handling - Troika doesn't support per-character blur
          // Store blur value for potential post-processing
          const blurVal = this.getAnimatorPropertyValue(props.blur, frame);
          (charMesh as any).__blurX = blurVal.x * influence;
          (charMesh as any).__blurY = blurVal.y * influence;
        }
      }
    }
  }

  /**
   * Get the current value of an animator property (animated or static)
   */
  private getAnimatorPropertyValue<T>(prop: AnimatableProperty<T>, frame: number): T {
    if (!prop.animated || prop.keyframes.length === 0) {
      return prop.value;
    }

    // Use the text evaluator to interpolate keyframes
    return this.textEvaluator.evaluate(prop, frame);
  }

  // ============================================================================
  // LAYER UPDATE
  // ============================================================================

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<TextData> | undefined;

    if (data) {
      if (data.text !== undefined) {
        this.setText(data.text);
      }
      if (data.fontFamily !== undefined) {
        this.setFontFamily(data.fontFamily);
      }
      if (data.fontSize !== undefined) {
        this.setFontSize(data.fontSize);
      }
      if (data.fontWeight !== undefined) {
        this.setFontWeight(data.fontWeight);
      }
      if (data.fontStyle !== undefined) {
        this.setFontStyle(data.fontStyle);
      }
      if (data.fill !== undefined) {
        this.setFillColor(data.fill);
      }
      if (data.stroke !== undefined || data.strokeWidth !== undefined) {
        this.setStroke(
          data.stroke ?? this.textData.stroke,
          data.strokeWidth ?? this.textData.strokeWidth
        );
      }
      if (data.tracking !== undefined) {
        this.setTracking(data.tracking);
      }
      if (data.textAlign !== undefined) {
        this.setTextAlign(data.textAlign);
      }
      if (data.pathLayerId !== undefined) {
        this.textData.pathLayerId = data.pathLayerId;
        this.pathConfig.pathLayerId = data.pathLayerId;
      }
      if (data.pathOffset !== undefined) {
        this.setPathOffset(data.pathOffset);
      }
      if (data.pathFirstMargin !== undefined) {
        this.setFirstMargin(data.pathFirstMargin);
      }
      if (data.pathLastMargin !== undefined) {
        this.setLastMargin(data.pathLastMargin);
      }
      if (data.pathReversed !== undefined) {
        this.setPathReversed(data.pathReversed);
      }
      if (data.pathPerpendicularToPath !== undefined) {
        this.setPerpendicularToPath(data.pathPerpendicularToPath);
      }
      if (data.pathForceAlignment !== undefined) {
        this.setForceAlignment(data.pathForceAlignment);
      }
      if (data.perCharacter3D !== undefined) {
        if (data.perCharacter3D && !this.perCharacterGroup) {
          this.enablePerCharacter3D();
        } else if (!data.perCharacter3D && !this.textOnPath.hasPath() && this.perCharacterGroup) {
          this.disablePerCharacter3D();
        }
      }
      if (data.anchorPointGrouping !== undefined) {
        this.setAnchorPointGrouping(data.anchorPointGrouping);
      }
      if (data.fillAndStroke !== undefined) {
        this.setFillAndStroke(data.fillAndStroke);
      }

      // Update animators array
      if (data.animators !== undefined) {
        this.animators = data.animators;
        this.textData.animators = data.animators;
        // Enable per-character mode if animators exist
        if (this.animators.length > 0 && !this.perCharacterGroup) {
          this.enablePerCharacter3D();
        }
      }
    }

    // Re-extract animatable properties if properties array changed
    if (properties.properties) {
      this.extractAnimatableProperties(properties as Layer);
    }
  }

  // ============================================================================
  // OPACITY OVERRIDE FOR TROIKA TEXT
  // ============================================================================

  /**
   * Override base class opacity to use Troika's fillOpacity
   */
  protected override applyOpacity(opacity: number): void {
    const normalizedOpacity = Math.max(0, Math.min(100, opacity)) / 100;

    // Apply to main text mesh using Troika's fillOpacity
    this.textMesh.fillOpacity = normalizedOpacity;
    this.textMesh.outlineOpacity = normalizedOpacity;

    // Apply to character meshes if in per-character mode
    for (const charMesh of this.characterMeshes) {
      charMesh.fillOpacity = normalizedOpacity;
      charMesh.outlineOpacity = normalizedOpacity;
    }
  }

  // ============================================================================
  // GETTERS
  // ============================================================================

  getTextData(): TextData {
    return { ...this.textData };
  }

  getTextBounds(): { width: number; height: number } {
    const bounds = this.textMesh.textRenderInfo?.blockBounds;
    if (bounds) {
      return {
        width: bounds[2] - bounds[0],
        height: bounds[3] - bounds[1],
      };
    }
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

  // ============================================================================
  // DISPOSAL
  // ============================================================================

  protected onDispose(): void {
    this.textMesh.dispose();
    this.disposeCharacterMeshes();
    this.textOnPath.dispose();

    if (this.perCharacterGroup) {
      this.group.remove(this.perCharacterGroup);
    }
  }
}
