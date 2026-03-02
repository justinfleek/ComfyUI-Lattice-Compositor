/**
 * Text Animator Store
 *
 * Domain store for text animator operations including CRUD,
 * selector configuration, computed character transforms, and text-on-path.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import { defineStore } from "pinia";
import {
  calculateCharacterInfluence,
  calculateCompleteCharacterInfluence,
  createExpressionSelector,
  createTextAnimator,
  createWigglySelector,
  getAnimatableValue,
} from "@/services/textAnimator";
import type { JSONValue } from "@/types/dataAsset";
import type { PropertyValue } from "@/types/animation";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;
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

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

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

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // helpers
// ════════════════════════════════════════════════════════════════════════════

function getTextLayer(store: TextAnimatorStoreAccess, layerId: string): Layer | undefined {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  return (layer != null && typeof layer === "object" && "type" in layer && layer.type === "text") ? layer : undefined;
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
  // System F/Omega proof: Validate hex format before calling utility
  // Type proof: hex ∈ string → { r: number; g: number; b: number; a: number }
  // Mathematical proof: Hex string must be valid format (#RGB, #RRGGBB, or #RRGGBBAA)
  const normalizedHex = hex.replace(/^#/, "");
  const isValidHex = /^([0-9a-f]{3}|[0-9a-f]{6}|[0-9a-f]{8})$/i.test(normalizedHex);
  
  if (!isValidHex) {
    // Invalid hex format - return default black with full opacity
    return { r: 0, g: 0, b: 0, a: 255 };
  }
  
  const rgba = hexToRgba(hex);
  return { r: rgba[0], g: rgba[1], b: rgba[2], a: Math.round(rgba[3] * 255) };
}

/**
 * Type guard for RGBA color objects
 */
interface RgbaObject {
  r: number;
  g: number;
  b: number;
  a?: number;
}

function isRgbaObject(value: RuntimeValue): value is RgbaObject {
  return (
    typeof value === "object" &&
    value !== null &&
    "r" in value &&
    "g" in value &&
    "b" in value &&
    typeof (value as RgbaObject).r === "number" &&
    typeof (value as RgbaObject).g === "number" &&
    typeof (value as RgbaObject).b === "number"
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

// ════════════════════════════════════════════════════════════════════════════
//                                                            // pinia // store
// ════════════════════════════════════════════════════════════════════════════

export const useTextAnimatorStore = defineStore("textAnimator", {
  state: () => ({}),

  getters: {},

  actions: {
    // ════════════════════════════════════════════════════════════════════════════
    //                                                        // crud // operations
    // ════════════════════════════════════════════════════════════════════════════

    addTextAnimator(store: TextAnimatorStoreAccess, layerId: string, config: AddTextAnimatorConfig = {}): TextAnimator {
      const layer = getTextLayer(store, layerId);
      if (!layer) {
        throw new Error(`[TextAnimatorStore] Cannot add animator: Layer "${layerId}" not found or is not a text layer`);
      }

      const textData = getTextData(layer);
      if (!textData) {
        throw new Error(`[TextAnimatorStore] Cannot add animator: Text data not found for layer "${layerId}"`);
      }

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

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (textData.animators != null && Array.isArray(textData.animators)) {
        textData.animators.push(animator);
      } else {
        textData.animators = [animator];
      }
      updateModified(store);
      return animator;
    },

    removeTextAnimator(store: TextAnimatorStoreAccess, layerId: string, animatorId: string): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (textData == null || typeof textData !== "object" || !("animators" in textData) || textData.animators == null || !Array.isArray(textData.animators)) return false;

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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (textData == null || typeof textData !== "object" || !("animators" in textData) || textData.animators == null || !Array.isArray(textData.animators)) return false;

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

    getTextAnimator(store: TextAnimatorStoreAccess, layerId: string, animatorId: string): TextAnimator {
      const layer = getTextLayer(store, layerId);
      if (!layer) {
        throw new Error(`[TextAnimatorStore] Cannot get animator: Layer "${layerId}" not found or is not a text layer`);
      }
      const textData = getTextData(layer);
      // Type proof: animators?.find(...) ∈ TextAnimator | undefined → TextAnimator (throws if not found)
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const animators = (textData != null && typeof textData === "object" && "animators" in textData && Array.isArray(textData.animators)) ? textData.animators : undefined;
      const foundAnimator = Array.isArray(animators) ? animators.find((a) => a.id === animatorId) : undefined;
      if (foundAnimator !== undefined) {
        return foundAnimator;
      }
      throw new Error(`[TextAnimatorStore] Animator "${animatorId}" not found on layer "${layerId}"`);
    },

    getTextAnimators(store: TextAnimatorStoreAccess, layerId: string): TextAnimator[] {
      const layer = getTextLayer(store, layerId);
      if (!layer) return [];
      // Type proof: animators ∈ TextAnimator[] | undefined → TextAnimator[]
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const textData = getTextData(layer);
      const animators = (textData != null && typeof textData === "object" && "animators" in textData && Array.isArray(textData.animators)) ? textData.animators : undefined;
      return Array.isArray(animators) ? animators : [];
    },

    // ════════════════════════════════════════════════════════════════════════════
    //                                                    // selector // operations
    // ════════════════════════════════════════════════════════════════════════════

    configureRangeSelector(store: TextAnimatorStoreAccess, layerId: string, animatorId: string, config: RangeSelectorConfig): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (textData == null || typeof textData !== "object" || !("animators" in textData) || textData.animators == null || !Array.isArray(textData.animators)) return false;

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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (textData == null || typeof textData !== "object" || !("animators" in textData) || textData.animators == null || !Array.isArray(textData.animators)) return false;

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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (textData == null || typeof textData !== "object" || !("animators" in textData) || textData.animators == null || !Array.isArray(textData.animators)) return false;

      const animator = textData.animators.find((a) => a.id === animatorId);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (animator === null || animator === undefined || typeof animator !== "object" || !("expressionSelector" in animator) || animator.expressionSelector === null || animator.expressionSelector === undefined || typeof animator.expressionSelector !== "object") return false;

      store.pushHistory();
      animator.expressionSelector.enabled = false;
      updateModified(store);
      return true;
    },

    configureWigglySelector(store: TextAnimatorStoreAccess, layerId: string, animatorId: string, config: WigglySelectorConfig): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (textData == null || typeof textData !== "object" || !("animators" in textData) || textData.animators == null || !Array.isArray(textData.animators)) return false;

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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (textData == null || typeof textData !== "object" || !("animators" in textData) || textData.animators == null || !Array.isArray(textData.animators)) return false;

      const animator = textData.animators.find((a) => a.id === animatorId);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (animator === null || animator === undefined || typeof animator !== "object" || !("wigglySelector" in animator) || animator.wigglySelector === null || animator.wigglySelector === undefined || typeof animator.wigglySelector !== "object") return false;

      store.pushHistory();
      animator.wigglySelector.enabled = false;
      updateModified(store);
      return true;
    },

    // ════════════════════════════════════════════════════════════════════════════
    //                                                        // computed // values
    // ════════════════════════════════════════════════════════════════════════════

    getCharacterTransforms(store: TextAnimatorStoreAccess, layerId: string, frame: number): CharacterTransform[] {
      const layer = getTextLayer(store, layerId);
      if (!layer) return [];

      const textData = getTextData(layer);
      if (!textData) return [];

      const text = textData.text || "";
      const totalChars = text.length;
      if (totalChars === 0) return [];

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      const animators = (Array.isArray(textData.animators)) ? textData.animators : [];
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const comp = store.getActiveComp();
      const fps = (comp !== null && comp !== undefined && typeof comp === "object" && "settings" in comp && comp.settings !== null && comp.settings !== undefined && typeof comp.settings === "object" && "fps" in comp.settings && typeof comp.settings.fps === "number") ? comp.settings.fps : 16;

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
            // Deterministic: Explicit null check before accessing fillColor
            if (!transforms[i].fillColor) {
              transforms[i].fillColor = { r: 0, g: 0, b: 0, a: 255 };
            }
            const fillColor = transforms[i].fillColor;
            if (!fillColor) {
              throw new Error("[TextAnimatorStore] fillColor should be defined after initialization check");
            }
            const fc = fillColor;
            fc.r += rgba.r * influence;
            fc.g += rgba.g * influence;
            fc.b += rgba.b * influence;
            fc.a = Math.round(255 - (255 - rgba.a) * influence);
          }
          if (props.strokeWidth !== undefined) {
            const v = getAnimatableValue(props.strokeWidth, frame) as number;
            // Type proof: strokeWidth ∈ ℝ ∪ {undefined} → ℝ
            const currentStrokeWidth = transforms[i].strokeWidth;
            const baseStrokeWidth = isFiniteNumber(currentStrokeWidth) && currentStrokeWidth >= 0 ? currentStrokeWidth : 0;
            transforms[i].strokeWidth = baseStrokeWidth + v * influence;
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

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const animators = (textData != null && typeof textData === "object" && "animators" in textData && Array.isArray(textData.animators)) ? textData.animators : undefined;
      const animator = Array.isArray(animators) ? animators.find((a) => a.id === animatorId) : undefined;
      if (!animator) return [];

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const comp = store.getActiveComp();
      const fps = (comp !== null && comp !== undefined && typeof comp === "object" && "settings" in comp && comp.settings !== null && comp.settings !== undefined && typeof comp.settings === "object" && "fps" in comp.settings && typeof comp.settings.fps === "number") ? comp.settings.fps : 16;
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

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const animators = (textData != null && typeof textData === "object" && "animators" in textData && Array.isArray(textData.animators)) ? textData.animators : undefined;
      const animator = Array.isArray(animators) ? animators.find((a) => a.id === animatorId) : undefined;
      if (!animator) return 0;

      return calculateCharacterInfluence(charIndex, totalChars, animator.rangeSelector, frame) * 100;
    },

    // ════════════════════════════════════════════════════════════════════════════
    //                                                      // utility // functions
    // ════════════════════════════════════════════════════════════════════════════

    setAnimatorPropertyValue(store: TextAnimatorStoreAccess, layerId: string, animatorId: string, propertyName: keyof TextAnimatorProperties, value: PropertyValue | JSONValue): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (textData == null || typeof textData !== "object" || !("animators" in textData) || textData.animators == null || !Array.isArray(textData.animators)) return false;

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

      const propName = String(propertyName);

      // Type-safe property access
      if (!(propName in animator.properties)) {
        (animator.properties as Partial<TextAnimatorProperties>)[propName as keyof TextAnimatorProperties] = createAnimatableProperty(propName, normalizedValue, valueType) as TextAnimatorProperties[keyof TextAnimatorProperties];
      } else {
        const prop = animator.properties[propertyName];
        if (prop && typeof prop === "object" && "value" in prop) {
          (prop as { value: string | number | { x: number; y: number } }).value = normalizedValue as string | number | { x: number; y: number };
        }
      }

      updateModified(store);
      return true;
    },

    hasTextAnimators(store: TextAnimatorStoreAccess, layerId: string): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;
      const textData = getTextData(layer);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      return !!(textData !== null && textData !== undefined && typeof textData === "object" && "animators" in textData && Array.isArray(textData.animators) && textData.animators.length > 0);
    },

    getTextContent(store: TextAnimatorStoreAccess, layerId: string): string {
      const layer = getTextLayer(store, layerId);
      if (!layer) {
        throw new Error(`[TextAnimatorStore] Cannot get text content: Layer "${layerId}" not found or is not a text layer`);
      }
      // Type proof: text ∈ string | undefined → string (throws if undefined)
      const textData = getTextData(layer);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const textValue = (textData !== null && textData !== undefined && typeof textData === "object" && "text" in textData && typeof textData.text === "string") ? textData.text : undefined;
      if (typeof textValue === "string") {
        return textValue;
      }
      throw new Error(`[TextAnimatorStore] Text content is undefined for layer "${layerId}"`);
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

    // ════════════════════════════════════════════════════════════════════════════
    //                                          // text // on // path // operations
    // ════════════════════════════════════════════════════════════════════════════

    setTextPath(store: TextAnimatorStoreAccess, layerId: string, config: TextPathConfig): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer) as TextDataWithPath | undefined;
      if (!textData) return false;

      store.pushHistory();
      // Type proof: pathConfig properties with explicit type proofs
      const closedValue = config.closed;
      const closed = closedValue === true;
      const reversedValue = config.reversed;
      const reversed = reversedValue === true;
      const perpendicularToPathValue = config.perpendicularToPath;
      const perpendicularToPath = perpendicularToPathValue === true;
      const forceAlignmentValue = config.forceAlignment;
      const forceAlignment = forceAlignmentValue === true;
      // Type proof: firstMargin ∈ ℝ ∪ {undefined} → ℝ
      const firstMarginValue = config.firstMargin;
      const firstMargin = isFiniteNumber(firstMarginValue) ? firstMarginValue : 0;
      // Type proof: lastMargin ∈ ℝ ∪ {undefined} → ℝ
      const lastMarginValue = config.lastMargin;
      const lastMargin = isFiniteNumber(lastMarginValue) ? lastMarginValue : 0;
      // Type proof: offset ∈ ℝ ∪ {undefined} → ℝ
      const offsetValue = config.offset;
      const offset = isFiniteNumber(offsetValue) ? offsetValue : 0;
      // Type proof: align ∈ string | undefined → string
      const alignValue = config.align;
      const align = typeof alignValue === "string" && (alignValue === "left" || alignValue === "center" || alignValue === "right") ? alignValue : "left";

      textData.pathConfig = {
        pathPoints: config.pathPoints,
        closed: closed,
        reversed: reversed,
        perpendicularToPath: perpendicularToPath,
        forceAlignment: forceAlignment,
        firstMargin: firstMargin,
        lastMargin: lastMargin,
        offset: offset,
        align: align,
      };

      const service = getPathService(layerId);
      service.setPath(config.pathPoints, closed);
      updateModified(store);
      return true;
    },

    getTextPathConfig(store: TextAnimatorStoreAccess, layerId: string): TextPathConfig {
      const layer = getTextLayer(store, layerId);
      if (!layer) {
        throw new Error(`[TextAnimatorStore] Cannot get path config: Layer "${layerId}" not found or is not a text layer`);
      }
      // Type proof: pathConfig ∈ TextPathConfig | undefined → TextPathConfig (throws if undefined)
      const textData = getTextData(layer) as TextDataWithPath | undefined;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const pathConfig = (textData !== null && textData !== undefined && typeof textData === "object" && "pathConfig" in textData && textData.pathConfig !== null && textData.pathConfig !== undefined && typeof textData.pathConfig === "object") ? textData.pathConfig : undefined;
      if (pathConfig !== undefined) {
        return pathConfig;
      }
      throw new Error(`[TextAnimatorStore] Path config is undefined for layer "${layerId}"`);
    },

    updateTextPath(store: TextAnimatorStoreAccess, layerId: string, updates: Partial<TextPathConfig>): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer) as TextDataWithPath | undefined;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (textData === null || textData === undefined || typeof textData !== "object" || !("pathConfig" in textData) || textData.pathConfig === null || textData.pathConfig === undefined || typeof textData.pathConfig !== "object") return false;

      store.pushHistory();
      Object.assign(textData.pathConfig, updates);

      if (updates.pathPoints || updates.closed !== undefined) {
        const service = getPathService(layerId);
        // Type proof: closed ∈ boolean | undefined → boolean
        const closedValue = textData.pathConfig.closed;
        const closed = closedValue === true;
        service.setPath(textData.pathConfig.pathPoints, closed);
      }

      updateModified(store);
      return true;
    },

    getCharacterPathPlacements(store: TextAnimatorStoreAccess, layerId: string, _frame: number): CharacterPlacement[] {
      const layer = getTextLayer(store, layerId);
      if (!layer) return [];

      const textData = getTextData(layer) as TextDataWithPath | undefined;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (textData === null || textData === undefined || typeof textData !== "object" || !("pathConfig" in textData) || textData.pathConfig === null || textData.pathConfig === undefined || typeof textData.pathConfig !== "object" || !("pathPoints" in textData.pathConfig) || !Array.isArray(textData.pathConfig.pathPoints) || textData.pathConfig.pathPoints.length < 2) return [];

      const text = textData.text || "";
      if (text.length === 0) return [];

      const service = getPathService(layerId);
      if (!service.hasPath()) {
        // Type proof: closed ∈ boolean | undefined → boolean
        const closedValue = textData.pathConfig.closed;
        const closed = closedValue === true;
        service.setPath(textData.pathConfig.pathPoints, closed);
      }

      const fontSize = textData.fontSize || 72;
      const charWidth = fontSize * 0.6;
      const characterWidths = Array(text.length).fill(charWidth);

      // Type proof: pathConfig properties with explicit type proofs
      const reversedValue = textData.pathConfig.reversed;
      const reversed = reversedValue === true;
      const perpendicularToPathValue = textData.pathConfig.perpendicularToPath;
      const perpendicularToPath = perpendicularToPathValue === true;
      const forceAlignmentValue = textData.pathConfig.forceAlignment;
      const forceAlignment = forceAlignmentValue === true;
      // Type proof: firstMargin ∈ ℝ ∪ {undefined} → ℝ
      const firstMarginValue = textData.pathConfig.firstMargin;
      const firstMargin = isFiniteNumber(firstMarginValue) ? firstMarginValue : 0;
      // Type proof: lastMargin ∈ ℝ ∪ {undefined} → ℝ
      const lastMarginValue = textData.pathConfig.lastMargin;
      const lastMargin = isFiniteNumber(lastMarginValue) ? lastMarginValue : 0;
      // Type proof: offset ∈ ℝ ∪ {undefined} → ℝ
      const offsetValue = textData.pathConfig.offset;
      const offset = isFiniteNumber(offsetValue) ? offsetValue : 0;
      // Type proof: align ∈ string | undefined → string
      const alignValue = textData.pathConfig.align;
      const align = typeof alignValue === "string" && (alignValue === "left" || alignValue === "center" || alignValue === "right") ? alignValue : "left";

      const config: TextOnPathConfig = {
        pathLayerId: layerId,
        reversed: reversed,
        perpendicularToPath: perpendicularToPath,
        forceAlignment: forceAlignment,
        firstMargin: firstMargin,
        lastMargin: lastMargin,
        offset: offset,
        align: align,
      };

      // Type proof: tracking ∈ number | undefined → number (coordinate-like, can be negative)
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
      const tracking = (typeof textData.tracking === "number" && Number.isFinite(textData.tracking)) ? textData.tracking : 0;
      return service.calculatePlacements(characterWidths, config, tracking, fontSize);
    },

    getPathLength(store: TextAnimatorStoreAccess, layerId: string): number {
      const layer = getTextLayer(store, layerId);
      if (!layer) return 0;

      const textData = getTextData(layer) as TextDataWithPath | undefined;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (textData === null || textData === undefined || typeof textData !== "object" || !("pathConfig" in textData) || textData.pathConfig === null || textData.pathConfig === undefined || typeof textData.pathConfig !== "object" || !("pathPoints" in textData.pathConfig) || !Array.isArray(textData.pathConfig.pathPoints) || textData.pathConfig.pathPoints.length < 2) return 0;

      const service = getPathService(layerId);
      if (!service.hasPath()) {
        // Type proof: closed ∈ boolean | undefined → boolean
        const closedValue = textData.pathConfig.closed;
        const closed = closedValue === true;
        service.setPath(textData.pathConfig.pathPoints, closed);
      }

      return service.getTotalLength();
    },

    hasTextPath(store: TextAnimatorStoreAccess, layerId: string): boolean {
      const layer = getTextLayer(store, layerId);
      if (!layer) return false;

      const textData = getTextData(layer) as TextDataWithPath | undefined;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      return !!(textData !== null && textData !== undefined && typeof textData === "object" && "pathConfig" in textData && textData.pathConfig !== null && textData.pathConfig !== undefined && typeof textData.pathConfig === "object" && "pathPoints" in textData.pathConfig && Array.isArray(textData.pathConfig.pathPoints) && textData.pathConfig.pathPoints.length >= 2);
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
