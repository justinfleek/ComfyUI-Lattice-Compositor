/**
 * Text Animator Store
 *
 * Domain store for text animator operations including CRUD,
 * selector configuration, computed character transforms, and text-on-path.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { defineStore } from "pinia";
import {
  calculateCharacterInfluence,
  calculateCompleteCharacterInfluence,
  createExpressionSelector,
  createTextAnimator,
  createWigglySelector,
  getAnimatableValue,
} from "@/services/textAnimator";
import { isExpressionSafe } from "@/services/expressions/expressionValidator";
import {
  type CharacterPlacement,
  type TextOnPathConfig,
  TextOnPathService,
} from "@/services/textOnPath";
import { createAnimatableProperty } from "@/types/animation";
import type { Composition, ControlPoint, Layer, TextData } from "@/types/project";
import type { TextAnimator, TextAnimatorProperties } from "@/types/text";
import { hexToRgba, rgbToHex } from "@/utils/colorUtils";

// ============================================================================
// TYPES
// ============================================================================

export interface TextAnimatorStoreAccess {
  project: { meta: { modified: string } };
  currentFrame: number;
  getActiveCompLayers(): Layer[];
  getActiveComp(): Composition | null;
  pushHistory(): void;
}

export interface CharacterTransform {
  index: number;
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  scale: { x: number; y: number };
  opacity: number;
  tracking: number;
  fillColor?: { r: number; g: number; b: number; a: number };
  strokeWidth?: number;
}

export interface AddTextAnimatorConfig {
  name?: string;
  properties?: Partial<TextAnimatorProperties>;
}

export interface RangeSelectorConfig {
  start?: number;
  end?: number;
  offset?: number;
  shape?: "square" | "ramp_up" | "ramp_down" | "triangle" | "round" | "smooth";
  amount?: number;
  smoothness?: number;
  basedOn?: "characters" | "words" | "lines";
  randomizeOrder?: boolean;
}

export interface ExpressionSelectorConfig {
  expression?: string;
  mode?: "add" | "subtract" | "intersect" | "min" | "max" | "difference";
  basedOn?: "characters" | "words" | "lines";
}

export interface WigglySelectorConfig {
  mode?: "add" | "subtract" | "intersect" | "min" | "max" | "difference";
  maxAmount?: number;
  minAmount?: number;
  wigglesPerSecond?: number;
  correlation?: number;
  lockDimensions?: boolean;
  randomSeed?: number;
}

export interface TextPathConfig {
  pathPoints: ControlPoint[];
  closed?: boolean;
  reversed?: boolean;
  perpendicularToPath?: boolean;
  forceAlignment?: boolean;
  firstMargin?: number;
  lastMargin?: number;
  offset?: number;
  align?: "left" | "center" | "right";
}

interface TextDataWithPath extends TextData {
  pathConfig?: TextPathConfig;
}

// ============================================================================
// HELPERS
// ============================================================================

function getTextLayer(store: TextAnimatorStoreAccess, layerId: string): Layer | undefined {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  return layer?.type === "text" ? layer : undefined;
}

function getTextData(layer: Layer): TextData | undefined {
  return layer.data as TextData | undefined;
}

function ensureAnimatorsArray(textData: TextData): void {
  if (!textData.animators) textData.animators = [];
}

function updateModified(store: TextAnimatorStoreAccess): void {
  store.project.meta.modified = new Date().toISOString();
}

function rgbaObjectToHex(rgba: { r: number; g: number; b: number; a?: number }): string {
  const r = Math.max(0, Math.min(255, Math.round(rgba.r)));
  const g = Math.max(0, Math.min(255, Math.round(rgba.g)));
  const b = Math.max(0, Math.min(255, Math.round(rgba.b)));
  return rgbToHex(r, g, b);
}

function hexToRgbaObject(hex: string): { r: number; g: number; b: number; a: number } {
  const rgba = hexToRgba(hex);
  return rgba ? { r: rgba[0], g: rgba[1], b: rgba[2], a: Math.round(rgba[3] * 255) } : { r: 0, g: 0, b: 0, a: 255 };
}

function isRgbaObject(value: unknown): value is { r: number; g: number; b: number; a?: number } {
  return (
    typeof value === "object" &&
    value !== null &&
    typeof (value as Record<string, unknown>).r === "number" &&
    typeof (value as Record<string, unknown>).g === "number" &&
    typeof (value as Record<string, unknown>).b === "number"
  );
}

// Path service singletons
const pathServices = new Map<string, TextOnPathService>();

function getPathService(layerId: string): TextOnPathService {
  let service = pathServices.get(layerId);
  if (!service) {
    service = new TextOnPathService();
    pathServices.set(layerId, service);
  }
  return service;
}

// ============================================================================
// PINIA STORE
// ============================================================================

export const useTextAnimatorStore = defineStore("textAnimator", {
  state: () => ({}),

  getters: {},

  actions: {
    // ========================================================================
    // CRUD OPERATIONS
    // ========================================================================

    addTextAnimator(store: TextAnimatorStoreAccess, layerId: string, config: AddTextAnimatorConfig = {}): TextAnimator | null {
      const layer = getTextLayer(store, layerId);
      if (!layer) return null;

      const textData = getTextData(layer);
      if (!textData) return null;

      store.pushHistory();
      ensureAnimatorsArray(textData);

      const animator = createTextAnimator(config.name);

      if (config.properties) {
        const p = config.properties;
        if (p.position) animator.properties.position = createAnimatableProperty("Position", p.position.value, "position");
        if (p.scale) animator.properties.scale = createAnimatableProperty("Scale", p.scale.value, "position");
        if (p.rotation !== undefined) animator.properties.rotation = createAnimatableProperty("Rotation", p.rotation.value, "number");
        if (p.opacity !== undefined) animator.properties.opacity = createAnimatableProperty("Opacity", p.opacity.value, "number");
        if (p.tracking !== undefined) animator.properties.tracking = createAnimatableProperty("Tracking", p.tracking.value, "number");
        if (p.fillColor) animator.properties.fillColor = createAnimatableProperty("Fill Color", p.fillColor.value, "color");
        if (p.strokeColor) animator.properties.strokeColor = createAnimatableProperty("Stroke Color", p.strokeColor.value, "color");
        if (p.strokeWidth !== undefined) animator.properties.strokeWidth = createAnimatableProperty("Stroke Width", p.strokeWidth.value, "number");
        if (p.blur) animator.properties.blur = createAnimatableProperty("Blur", p.blur.value, "position");
      }

      textData.animators?.push(animator);
      updateModified(store);
      return animator;
    },

    removeTextAnimator(store: TextAnimatorStoreAccess, layerId: string, animatorId: string): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      if (!textData?.animators) return false;

      const index = textData.animators.findIndex((a) => a.id === animatorId);
      if (index === -1) return false;

      store.pushHistory();
      textData.animators.splice(index, 1);
      updateModified(store);
      return true;
    },

    updateTextAnimator(store: TextAnimatorStoreAccess, layerId: string, animatorId: string, updates: Partial<TextAnimator>): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      if (!textData?.animators) return false;

      const animator = textData.animators.find((a) => a.id === animatorId);
      if (!animator) return false;

      store.pushHistory();
      if (updates.name !== undefined) animator.name = updates.name;
      if (updates.enabled !== undefined) animator.enabled = updates.enabled;
      if (updates.properties) Object.assign(animator.properties, updates.properties);
      if (updates.rangeSelector) Object.assign(animator.rangeSelector, updates.rangeSelector);
      updateModified(store);
      return true;
    },

    getTextAnimator(store: TextAnimatorStoreAccess, layerId: string, animatorId: string): TextAnimator | null {
      const layer = getTextLayer(store, layerId);
      if (!layer) return null;
      const textData = getTextData(layer);
      return textData?.animators?.find((a) => a.id === animatorId) ?? null;
    },

    getTextAnimators(store: TextAnimatorStoreAccess, layerId: string): TextAnimator[] {
      const layer = getTextLayer(store, layerId);
      if (!layer) return [];
      return getTextData(layer)?.animators ?? [];
    },

    // ========================================================================
    // SELECTOR OPERATIONS
    // ========================================================================

    configureRangeSelector(store: TextAnimatorStoreAccess, layerId: string, animatorId: string, config: RangeSelectorConfig): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      if (!textData?.animators) return false;

      const animator = textData.animators.find((a) => a.id === animatorId);
      if (!animator) return false;

      store.pushHistory();
      const s = animator.rangeSelector;
      if (config.start !== undefined) s.start.value = config.start;
      if (config.end !== undefined) s.end.value = config.end;
      if (config.offset !== undefined) s.offset.value = config.offset;
      if (config.shape !== undefined) s.shape = config.shape;
      if (config.amount !== undefined) s.amount = config.amount;
      if (config.smoothness !== undefined) s.smoothness = config.smoothness;
      if (config.basedOn !== undefined) s.basedOn = config.basedOn;
      if (config.randomizeOrder !== undefined) s.randomizeOrder = config.randomizeOrder;
      updateModified(store);
      return true;
    },

    async configureExpressionSelector(store: TextAnimatorStoreAccess, layerId: string, animatorId: string, config: ExpressionSelectorConfig): Promise<boolean> {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      if (!textData?.animators) return false;

      const animator = textData.animators.find((a) => a.id === animatorId);
      if (!animator) return false;

      if (config.expression && typeof config.expression === "string" && config.expression.trim()) {
        const safe = await isExpressionSafe(config.expression);
        if (!safe) {
          console.error("[SECURITY] Expression blocked - timeout detected");
          return false;
        }
      }

      store.pushHistory();
      if (!animator.expressionSelector) animator.expressionSelector = createExpressionSelector(config.expression || "selectorValue");
      const s = animator.expressionSelector;
      s.enabled = true;
      if (config.expression !== undefined) s.amountExpression = config.expression;
      if (config.mode !== undefined) s.mode = config.mode;
      if (config.basedOn !== undefined) s.basedOn = config.basedOn;
      updateModified(store);
      return true;
    },

    removeExpressionSelector(store: TextAnimatorStoreAccess, layerId: string, animatorId: string): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      if (!textData?.animators) return false;

      const animator = textData.animators.find((a) => a.id === animatorId);
      if (!animator?.expressionSelector) return false;

      store.pushHistory();
      animator.expressionSelector.enabled = false;
      updateModified(store);
      return true;
    },

    configureWigglySelector(store: TextAnimatorStoreAccess, layerId: string, animatorId: string, config: WigglySelectorConfig): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      if (!textData?.animators) return false;

      const animator = textData.animators.find((a) => a.id === animatorId);
      if (!animator) return false;

      store.pushHistory();
      if (!animator.wigglySelector) animator.wigglySelector = createWigglySelector({ enabled: true });
      const s = animator.wigglySelector;
      s.enabled = true;
      if (config.mode !== undefined) s.mode = config.mode;
      if (config.maxAmount !== undefined) s.maxAmount = config.maxAmount;
      if (config.minAmount !== undefined) s.minAmount = config.minAmount;
      if (config.wigglesPerSecond !== undefined) s.wigglesPerSecond = config.wigglesPerSecond;
      if (config.correlation !== undefined) s.correlation = config.correlation;
      if (config.lockDimensions !== undefined) s.lockDimensions = config.lockDimensions;
      if (config.randomSeed !== undefined) s.randomSeed = config.randomSeed;
      updateModified(store);
      return true;
    },

    removeWigglySelector(store: TextAnimatorStoreAccess, layerId: string, animatorId: string): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      if (!textData?.animators) return false;

      const animator = textData.animators.find((a) => a.id === animatorId);
      if (!animator?.wigglySelector) return false;

      store.pushHistory();
      animator.wigglySelector.enabled = false;
      updateModified(store);
      return true;
    },

    // ========================================================================
    // COMPUTED VALUES
    // ========================================================================

    getCharacterTransforms(store: TextAnimatorStoreAccess, layerId: string, frame: number): CharacterTransform[] {
      const layer = getTextLayer(store, layerId);
      if (!layer) return [];

      const textData = getTextData(layer);
      if (!textData) return [];

      const text = textData.text || "";
      const totalChars = text.length;
      if (totalChars === 0) return [];

      const animators = textData.animators || [];
      const fps = store.getActiveComp()?.settings?.fps || 16;

      const transforms: CharacterTransform[] = [];
      for (let i = 0; i < totalChars; i++) {
        transforms.push({
          index: i,
          position: { x: 0, y: 0, z: 0 },
          rotation: { x: 0, y: 0, z: 0 },
          scale: { x: 100, y: 100 },
          opacity: 100,
          tracking: 0,
        });
      }

      for (const animator of animators) {
        if (!animator.enabled) continue;
        const props = animator.properties;

        for (let i = 0; i < totalChars; i++) {
          const influence = calculateCompleteCharacterInfluence(i, totalChars, animator, frame, fps);
          if (influence <= 0.001) continue;

          if (props.position) {
            const v = getAnimatableValue(props.position, frame);
            transforms[i].position.x += v.x * influence;
            transforms[i].position.y += v.y * influence;
          }
          if (props.scale) {
            const v = getAnimatableValue(props.scale, frame);
            transforms[i].scale.x += (v.x - 100) * influence;
            transforms[i].scale.y += (v.y - 100) * influence;
          }
          if (props.rotation) {
            const v = getAnimatableValue(props.rotation, frame);
            transforms[i].rotation.z += v * influence;
          }
          if (props.opacity !== undefined) {
            const v = getAnimatableValue(props.opacity, frame);
            transforms[i].opacity += (v - 100) * influence;
          }
          if (props.tracking) {
            const v = getAnimatableValue(props.tracking, frame);
            transforms[i].tracking += v * influence;
          }
          if (props.fillColor) {
            const hex = getAnimatableValue(props.fillColor, frame) as string;
            const rgba = hexToRgbaObject(hex);
            if (!transforms[i].fillColor) transforms[i].fillColor = { r: 0, g: 0, b: 0, a: 255 };
            const fc = transforms[i].fillColor!;
            fc.r += rgba.r * influence;
            fc.g += rgba.g * influence;
            fc.b += rgba.b * influence;
            fc.a = Math.round(255 - (255 - rgba.a) * influence);
          }
          if (props.strokeWidth !== undefined) {
            const v = getAnimatableValue(props.strokeWidth, frame) as number;
            transforms[i].strokeWidth = (transforms[i].strokeWidth ?? 0) + v * influence;
          }
        }
      }

      for (const t of transforms) {
        t.opacity = Math.max(0, Math.min(100, t.opacity));
        t.scale.x = Math.max(0, t.scale.x);
        t.scale.y = Math.max(0, t.scale.y);
        if (t.fillColor) {
          t.fillColor.r = Math.max(0, Math.min(255, Math.round(t.fillColor.r)));
          t.fillColor.g = Math.max(0, Math.min(255, Math.round(t.fillColor.g)));
          t.fillColor.b = Math.max(0, Math.min(255, Math.round(t.fillColor.b)));
          t.fillColor.a = Math.max(0, Math.min(255, Math.round(t.fillColor.a)));
        }
        if (t.strokeWidth !== undefined) t.strokeWidth = Math.max(0, t.strokeWidth);
      }

      return transforms;
    },

    getSelectionValues(store: TextAnimatorStoreAccess, layerId: string, animatorId: string, frame: number): number[] {
      const layer = getTextLayer(store, layerId);
      if (!layer) return [];

      const textData = getTextData(layer);
      if (!textData) return [];

      const text = textData.text || "";
      const totalChars = text.length;
      if (totalChars === 0) return [];

      const animator = textData.animators?.find((a) => a.id === animatorId);
      if (!animator) return [];

      const fps = store.getActiveComp()?.settings?.fps || 16;
      const values: number[] = [];

      for (let i = 0; i < totalChars; i++) {
        const influence = calculateCompleteCharacterInfluence(i, totalChars, animator, frame, fps);
        values.push(influence * 100);
      }

      return values;
    },

    getRangeSelectionValue(store: TextAnimatorStoreAccess, layerId: string, animatorId: string, charIndex: number, frame: number): number {
      const layer = getTextLayer(store, layerId);
      if (!layer) return 0;

      const textData = getTextData(layer);
      if (!textData) return 0;

      const text = textData.text || "";
      const totalChars = text.length;
      if (totalChars === 0 || charIndex < 0 || charIndex >= totalChars) return 0;

      const animator = textData.animators?.find((a) => a.id === animatorId);
      if (!animator) return 0;

      return calculateCharacterInfluence(charIndex, totalChars, animator.rangeSelector, frame) * 100;
    },

    // ========================================================================
    // UTILITY FUNCTIONS
    // ========================================================================

    setAnimatorPropertyValue(store: TextAnimatorStoreAccess, layerId: string, animatorId: string, propertyName: keyof TextAnimatorProperties, value: unknown): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      if (!textData?.animators) return false;

      const animator = textData.animators.find((a) => a.id === animatorId);
      if (!animator) return false;

      store.pushHistory();

      let normalizedValue = value;
      let valueType: "number" | "position" | "color" = "number";

      if (isRgbaObject(value)) {
        normalizedValue = rgbaObjectToHex(value);
        valueType = "color";
      } else if (typeof value === "object" && value !== null && "x" in value && "y" in value) {
        valueType = "position";
      } else if (typeof value === "string") {
        valueType = "color";
      }

      const props = animator.properties as Record<string, unknown>;
      const propName = String(propertyName);

      if (!props[propName]) {
        props[propName] = createAnimatableProperty(propName, normalizedValue, valueType);
      } else {
        (props[propName] as { value: unknown }).value = normalizedValue;
      }

      updateModified(store);
      return true;
    },

    hasTextAnimators(store: TextAnimatorStoreAccess, layerId: string): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;
      const textData = getTextData(layer);
      return !!(textData?.animators && textData.animators.length > 0);
    },

    getTextContent(store: TextAnimatorStoreAccess, layerId: string): string | null {
      const layer = getTextLayer(store, layerId);
      if (!layer) return null;
      return getTextData(layer)?.text ?? null;
    },

    setTextContent(store: TextAnimatorStoreAccess, layerId: string, text: string): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      if (!textData) return false;

      store.pushHistory();
      textData.text = text;
      updateModified(store);
      return true;
    },

    // ========================================================================
    // TEXT ON PATH OPERATIONS
    // ========================================================================

    setTextPath(store: TextAnimatorStoreAccess, layerId: string, config: TextPathConfig): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer) as TextDataWithPath | undefined;
      if (!textData) return false;

      store.pushHistory();
      textData.pathConfig = {
        pathPoints: config.pathPoints,
        closed: config.closed ?? false,
        reversed: config.reversed ?? false,
        perpendicularToPath: config.perpendicularToPath ?? true,
        forceAlignment: config.forceAlignment ?? false,
        firstMargin: config.firstMargin ?? 0,
        lastMargin: config.lastMargin ?? 0,
        offset: config.offset ?? 0,
        align: config.align ?? "left",
      };

      const service = getPathService(layerId);
      service.setPath(config.pathPoints, config.closed ?? false);
      updateModified(store);
      return true;
    },

    getTextPathConfig(store: TextAnimatorStoreAccess, layerId: string): TextPathConfig | null {
      const layer = getTextLayer(store, layerId);
      if (!layer) return null;
      return (getTextData(layer) as TextDataWithPath | undefined)?.pathConfig ?? null;
    },

    updateTextPath(store: TextAnimatorStoreAccess, layerId: string, updates: Partial<TextPathConfig>): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer) as TextDataWithPath | undefined;
      if (!textData?.pathConfig) return false;

      store.pushHistory();
      Object.assign(textData.pathConfig, updates);

      if (updates.pathPoints || updates.closed !== undefined) {
        const service = getPathService(layerId);
        service.setPath(textData.pathConfig.pathPoints, textData.pathConfig.closed ?? false);
      }

      updateModified(store);
      return true;
    },

    getCharacterPathPlacements(store: TextAnimatorStoreAccess, layerId: string, _frame: number): CharacterPlacement[] {
      const layer = getTextLayer(store, layerId);
      if (!layer) return [];

      const textData = getTextData(layer) as TextDataWithPath | undefined;
      if (!textData?.pathConfig?.pathPoints || textData.pathConfig.pathPoints.length < 2) return [];

      const text = textData.text || "";
      if (text.length === 0) return [];

      const service = getPathService(layerId);
      if (!service.hasPath()) service.setPath(textData.pathConfig.pathPoints, textData.pathConfig.closed ?? false);

      const fontSize = textData.fontSize || 72;
      const charWidth = fontSize * 0.6;
      const characterWidths = Array(text.length).fill(charWidth);

      const config: TextOnPathConfig = {
        pathLayerId: layerId,
        reversed: textData.pathConfig.reversed ?? false,
        perpendicularToPath: textData.pathConfig.perpendicularToPath ?? true,
        forceAlignment: textData.pathConfig.forceAlignment ?? false,
        firstMargin: textData.pathConfig.firstMargin ?? 0,
        lastMargin: textData.pathConfig.lastMargin ?? 0,
        offset: textData.pathConfig.offset ?? 0,
        align: textData.pathConfig.align ?? "left",
      };

      return service.calculatePlacements(characterWidths, config, textData.tracking || 0, fontSize);
    },

    getPathLength(store: TextAnimatorStoreAccess, layerId: string): number {
      const layer = getTextLayer(store, layerId);
      if (!layer) return 0;

      const textData = getTextData(layer) as TextDataWithPath | undefined;
      if (!textData?.pathConfig?.pathPoints || textData.pathConfig.pathPoints.length < 2) return 0;

      const service = getPathService(layerId);
      if (!service.hasPath()) service.setPath(textData.pathConfig.pathPoints, textData.pathConfig.closed ?? false);

      return service.getTotalLength();
    },

    hasTextPath(store: TextAnimatorStoreAccess, layerId: string): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer) as TextDataWithPath | undefined;
      return !!(textData?.pathConfig?.pathPoints && textData.pathConfig.pathPoints.length >= 2);
    },

    clearTextPath(store: TextAnimatorStoreAccess, layerId: string): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer) as TextDataWithPath | undefined;
      if (!textData) return false;

      store.pushHistory();
      delete textData.pathConfig;

      const service = pathServices.get(layerId);
      if (service) {
        service.dispose();
        pathServices.delete(layerId);
      }

      updateModified(store);
      return true;
    },
  },
});
