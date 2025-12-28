/**
 * Text Animator Actions
 *
 * Store actions for managing text animators, selectors, and computing
 * per-character transforms. Provides the public API for Tutorial 06
 * text animation features.
 */

import type { Layer, TextData, Composition, ControlPoint } from '@/types/project';
import type {
  TextAnimator,
  TextRangeSelector,
  TextWigglySelector,
  TextExpressionSelector,
  TextAnimatorProperties,
} from '@/types/text';
import {
  createTextAnimator,
  createWigglySelector,
  createExpressionSelector,
  calculateCompleteCharacterInfluence,
  calculateCharacterInfluence,
  getAnimatableValue,
  DEFAULT_RANGE_SELECTOR,
} from '@/services/textAnimator';
import { isExpressionSafe } from '@/services/expressions/expressionValidator';
import {
  TextOnPathService,
  createDefaultPathConfig,
  type TextOnPathConfig,
  type CharacterPlacement,
} from '@/services/textOnPath';
import { createAnimatableProperty } from '@/types/animation';

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface TextAnimatorStore {
  project: {
    meta: { modified: string };
  };
  currentFrame: number;
  getActiveCompLayers(): Layer[];
  getActiveComp(): Composition | null;
  pushHistory(): void;
}

// ============================================================================
// TYPES
// ============================================================================

export interface CharacterTransform {
  index: number;
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  scale: { x: number; y: number };
  opacity: number;
  tracking: number;
}

export interface AddTextAnimatorConfig {
  name?: string;
  properties?: Partial<TextAnimatorProperties>;
}

export interface RangeSelectorConfig {
  start?: number;
  end?: number;
  offset?: number;
  shape?: 'square' | 'ramp_up' | 'ramp_down' | 'triangle' | 'round' | 'smooth';
  amount?: number;
  smoothness?: number;
  basedOn?: 'characters' | 'words' | 'lines';
  randomizeOrder?: boolean;
}

export interface ExpressionSelectorConfig {
  expression?: string;
  mode?: 'add' | 'subtract' | 'intersect' | 'min' | 'max' | 'difference';
  basedOn?: 'characters' | 'words' | 'lines';
}

export interface WigglySelectorConfig {
  mode?: 'add' | 'subtract' | 'intersect' | 'min' | 'max' | 'difference';
  maxAmount?: number;
  minAmount?: number;
  wigglesPerSecond?: number;
  correlation?: number;
  lockDimensions?: boolean;
  randomSeed?: number;
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/**
 * Get a text layer by ID and validate it's a text layer
 */
function getTextLayer(store: TextAnimatorStore, layerId: string): Layer | null {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'text') return null;
  return layer;
}

/**
 * Get text data from layer
 */
function getTextData(layer: Layer): TextData | null {
  return layer.data as TextData | null;
}

/**
 * Ensure animators array exists on text data
 */
function ensureAnimatorsArray(textData: TextData): void {
  if (!textData.animators) {
    textData.animators = [];
  }
}

/**
 * Generate unique ID
 */
function generateId(prefix: string = 'ta'): string {
  return `${prefix}_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
}

// ============================================================================
// TEXT ANIMATOR CRUD OPERATIONS
// ============================================================================

/**
 * Add a text animator to a text layer
 */
export function addTextAnimator(
  store: TextAnimatorStore,
  layerId: string,
  config: AddTextAnimatorConfig = {}
): TextAnimator | null {
  const layer = getTextLayer(store, layerId);
  if (!layer) return null;

  const textData = getTextData(layer);
  if (!textData) return null;

  store.pushHistory();
  ensureAnimatorsArray(textData);

  // Create new animator
  const animator = createTextAnimator(config.name);

  // Apply property configuration if provided
  if (config.properties) {
    if (config.properties.position) {
      animator.properties.position = createAnimatableProperty(
        'Position',
        config.properties.position.value,
        'position'
      );
    }
    if (config.properties.scale) {
      animator.properties.scale = createAnimatableProperty(
        'Scale',
        config.properties.scale.value,
        'position'
      );
    }
    if (config.properties.rotation !== undefined) {
      animator.properties.rotation = createAnimatableProperty(
        'Rotation',
        config.properties.rotation.value,
        'number'
      );
    }
    if (config.properties.opacity !== undefined) {
      animator.properties.opacity = createAnimatableProperty(
        'Opacity',
        config.properties.opacity.value,
        'number'
      );
    }
    if (config.properties.tracking !== undefined) {
      animator.properties.tracking = createAnimatableProperty(
        'Tracking',
        config.properties.tracking.value,
        'number'
      );
    }
    if (config.properties.fillColor) {
      animator.properties.fillColor = createAnimatableProperty(
        'Fill Color',
        config.properties.fillColor.value,
        'color'
      );
    }
    if (config.properties.strokeColor) {
      animator.properties.strokeColor = createAnimatableProperty(
        'Stroke Color',
        config.properties.strokeColor.value,
        'color'
      );
    }
    if (config.properties.strokeWidth !== undefined) {
      animator.properties.strokeWidth = createAnimatableProperty(
        'Stroke Width',
        config.properties.strokeWidth.value,
        'number'
      );
    }
    if (config.properties.blur) {
      animator.properties.blur = createAnimatableProperty(
        'Blur',
        config.properties.blur.value,
        'position'
      );
    }
  }

  textData.animators!.push(animator);
  store.project.meta.modified = new Date().toISOString();

  return animator;
}

/**
 * Remove a text animator from a text layer
 */
export function removeTextAnimator(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const index = textData.animators.findIndex(a => a.id === animatorId);
  if (index === -1) return false;

  store.pushHistory();
  textData.animators.splice(index, 1);
  store.project.meta.modified = new Date().toISOString();

  return true;
}

/**
 * Update a text animator's properties
 */
export function updateTextAnimator(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  updates: Partial<TextAnimator>
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find(a => a.id === animatorId);
  if (!animator) return false;

  store.pushHistory();

  // Apply updates
  if (updates.name !== undefined) animator.name = updates.name;
  if (updates.enabled !== undefined) animator.enabled = updates.enabled;
  if (updates.properties) {
    Object.assign(animator.properties, updates.properties);
  }
  if (updates.rangeSelector) {
    Object.assign(animator.rangeSelector, updates.rangeSelector);
  }

  store.project.meta.modified = new Date().toISOString();
  return true;
}

/**
 * Get a text animator by ID
 */
export function getTextAnimator(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string
): TextAnimator | null {
  const layer = getTextLayer(store, layerId);
  if (!layer) return null;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return null;

  return textData.animators.find(a => a.id === animatorId) || null;
}

/**
 * Get all text animators for a layer
 */
export function getTextAnimators(
  store: TextAnimatorStore,
  layerId: string
): TextAnimator[] {
  const layer = getTextLayer(store, layerId);
  if (!layer) return [];

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return [];

  return textData.animators;
}

// ============================================================================
// RANGE SELECTOR OPERATIONS
// ============================================================================

/**
 * Configure the range selector for a text animator
 */
export function configureRangeSelector(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  config: RangeSelectorConfig
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find(a => a.id === animatorId);
  if (!animator) return false;

  store.pushHistory();

  const selector = animator.rangeSelector;

  if (config.start !== undefined) selector.start.value = config.start;
  if (config.end !== undefined) selector.end.value = config.end;
  if (config.offset !== undefined) selector.offset.value = config.offset;
  if (config.shape !== undefined) selector.shape = config.shape;
  if (config.amount !== undefined) selector.amount = config.amount;
  if (config.smoothness !== undefined) selector.smoothness = config.smoothness;
  if (config.basedOn !== undefined) selector.basedOn = config.basedOn;
  if (config.randomizeOrder !== undefined) selector.randomizeOrder = config.randomizeOrder;

  store.project.meta.modified = new Date().toISOString();
  return true;
}

// ============================================================================
// EXPRESSION SELECTOR OPERATIONS
// ============================================================================

/**
 * Add or configure an expression selector for a text animator
 * SECURITY: Validates expressions before applying (DoS protection)
 */
export async function configureExpressionSelector(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  config: ExpressionSelectorConfig
): Promise<boolean> {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find(a => a.id === animatorId);
  if (!animator) return false;

  // SECURITY: Validate expression before applying
  if (config.expression !== undefined && typeof config.expression === 'string' && config.expression.trim()) {
    const safe = await isExpressionSafe(config.expression);
    if (!safe) {
      console.error('[SECURITY] Expression blocked - timeout detected (possible infinite loop)');
      return false;
    }
  }

  store.pushHistory();

  // Create expression selector if doesn't exist
  if (!animator.expressionSelector) {
    animator.expressionSelector = createExpressionSelector(
      config.expression || 'selectorValue'
    );
  }

  const selector = animator.expressionSelector;
  selector.enabled = true;

  if (config.expression !== undefined) selector.amountExpression = config.expression;
  if (config.mode !== undefined) selector.mode = config.mode;
  if (config.basedOn !== undefined) selector.basedOn = config.basedOn;

  store.project.meta.modified = new Date().toISOString();
  return true;
}

/**
 * Remove expression selector from animator
 */
export function removeExpressionSelector(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find(a => a.id === animatorId);
  if (!animator || !animator.expressionSelector) return false;

  store.pushHistory();
  animator.expressionSelector.enabled = false;
  store.project.meta.modified = new Date().toISOString();
  return true;
}

// ============================================================================
// WIGGLY SELECTOR OPERATIONS
// ============================================================================

/**
 * Add or configure a wiggly selector for a text animator
 */
export function configureWigglySelector(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  config: WigglySelectorConfig
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find(a => a.id === animatorId);
  if (!animator) return false;

  store.pushHistory();

  // Create wiggly selector if doesn't exist
  if (!animator.wigglySelector) {
    animator.wigglySelector = createWigglySelector({ enabled: true });
  }

  const selector = animator.wigglySelector;
  selector.enabled = true;

  if (config.mode !== undefined) selector.mode = config.mode;
  if (config.maxAmount !== undefined) selector.maxAmount = config.maxAmount;
  if (config.minAmount !== undefined) selector.minAmount = config.minAmount;
  if (config.wigglesPerSecond !== undefined) selector.wigglesPerSecond = config.wigglesPerSecond;
  if (config.correlation !== undefined) selector.correlation = config.correlation;
  if (config.lockDimensions !== undefined) selector.lockDimensions = config.lockDimensions;
  if (config.randomSeed !== undefined) selector.randomSeed = config.randomSeed;

  store.project.meta.modified = new Date().toISOString();
  return true;
}

/**
 * Remove wiggly selector from animator
 */
export function removeWigglySelector(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find(a => a.id === animatorId);
  if (!animator || !animator.wigglySelector) return false;

  store.pushHistory();
  animator.wigglySelector.enabled = false;
  store.project.meta.modified = new Date().toISOString();
  return true;
}

// ============================================================================
// COMPUTED VALUES
// ============================================================================

/**
 * Get computed transforms for all characters at a specific frame
 *
 * This is the KEY function for testing - it returns the exact transform
 * values that would be applied to each character mesh at the given frame.
 */
export function getCharacterTransforms(
  store: TextAnimatorStore,
  layerId: string,
  frame: number
): CharacterTransform[] {
  const layer = getTextLayer(store, layerId);
  if (!layer) return [];

  const textData = getTextData(layer);
  if (!textData) return [];

  const text = textData.text || '';
  const totalChars = text.length;
  if (totalChars === 0) return [];

  const animators = textData.animators || [];
  const comp = store.getActiveComp();
  const fps = comp?.settings?.fps || 16;

  // Initialize transforms with base values
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

  // Apply each animator
  for (const animator of animators) {
    if (!animator.enabled) continue;

    const props = animator.properties;

    for (let i = 0; i < totalChars; i++) {
      // Calculate influence (0-1) for this character
      const influence = calculateCompleteCharacterInfluence(
        i,
        totalChars,
        animator,
        frame,
        fps
      );

      // Skip if no influence
      if (influence <= 0.001) continue;

      // Apply position offset (with keyframe interpolation)
      if (props.position) {
        const posVal = getAnimatableValue(props.position, frame);
        transforms[i].position.x += posVal.x * influence;
        transforms[i].position.y += posVal.y * influence;
      }

      // Apply scale (with keyframe interpolation)
      if (props.scale) {
        const scaleVal = getAnimatableValue(props.scale, frame);
        // Scale is additive offset from 100%
        // At influence=1, full offset applied; at influence=0, no change
        transforms[i].scale.x += (scaleVal.x - 100) * influence;
        transforms[i].scale.y += (scaleVal.y - 100) * influence;
      }

      // Apply rotation (with keyframe interpolation)
      if (props.rotation) {
        const rotVal = getAnimatableValue(props.rotation, frame);
        transforms[i].rotation.z += rotVal * influence;
      }

      // Apply opacity (with keyframe interpolation)
      if (props.opacity !== undefined) {
        const opacityVal = getAnimatableValue(props.opacity, frame);
        // Opacity offset: at influence=1, opacity moves toward animator value
        // Formula: current + (target - 100) * influence
        transforms[i].opacity += (opacityVal - 100) * influence;
      }

      // Apply tracking (with keyframe interpolation)
      if (props.tracking) {
        const trackingVal = getAnimatableValue(props.tracking, frame);
        transforms[i].tracking += trackingVal * influence;
      }
    }
  }

  // Clamp final values
  for (const t of transforms) {
    t.opacity = Math.max(0, Math.min(100, t.opacity));
    t.scale.x = Math.max(0, t.scale.x);
    t.scale.y = Math.max(0, t.scale.y);
  }

  return transforms;
}

/**
 * Get selection values (influence 0-100) for each character from a specific animator
 *
 * This exposes the raw selector calculation for testing selector math.
 */
export function getSelectionValues(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  frame: number
): number[] {
  const layer = getTextLayer(store, layerId);
  if (!layer) return [];

  const textData = getTextData(layer);
  if (!textData) return [];

  const text = textData.text || '';
  const totalChars = text.length;
  if (totalChars === 0) return [];

  const animator = textData.animators?.find(a => a.id === animatorId);
  if (!animator) return [];

  const comp = store.getActiveComp();
  const fps = comp?.settings?.fps || 16;

  const values: number[] = [];
  for (let i = 0; i < totalChars; i++) {
    const influence = calculateCompleteCharacterInfluence(
      i,
      totalChars,
      animator,
      frame,
      fps
    );
    // Return as percentage (0-100)
    values.push(influence * 100);
  }

  return values;
}

/**
 * Get raw range selector value for a specific character
 * (without wiggly/expression modifiers)
 */
export function getRangeSelectionValue(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  charIndex: number,
  frame: number
): number {
  const layer = getTextLayer(store, layerId);
  if (!layer) return 0;

  const textData = getTextData(layer);
  if (!textData) return 0;

  const text = textData.text || '';
  const totalChars = text.length;
  if (totalChars === 0 || charIndex < 0 || charIndex >= totalChars) return 0;

  const animator = textData.animators?.find(a => a.id === animatorId);
  if (!animator) return 0;

  const influence = calculateCharacterInfluence(
    charIndex,
    totalChars,
    animator.rangeSelector,
    frame
  );

  // Return as percentage (0-100)
  return influence * 100;
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/**
 * Set animator property value
 */
export function setAnimatorPropertyValue(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  propertyName: keyof TextAnimatorProperties,
  value: any
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find(a => a.id === animatorId);
  if (!animator) return false;

  store.pushHistory();

  // Create property if doesn't exist
  const valueType = typeof value === 'object' ? 'position' : typeof value === 'number' ? 'number' : 'color';
  const propName = String(propertyName);

  const props = animator.properties as Record<string, any>;
  if (!props[propName]) {
    props[propName] = createAnimatableProperty(
      propName,
      value,
      valueType as any
    );
  } else {
    props[propName].value = value;
  }

  store.project.meta.modified = new Date().toISOString();
  return true;
}

/**
 * Check if a layer has any text animators
 */
export function hasTextAnimators(
  store: TextAnimatorStore,
  layerId: string
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  return !!(textData?.animators && textData.animators.length > 0);
}

/**
 * Get text content from a text layer
 */
export function getTextContent(
  store: TextAnimatorStore,
  layerId: string
): string {
  const layer = getTextLayer(store, layerId);
  if (!layer) return '';

  const textData = getTextData(layer);
  return textData?.text || '';
}

/**
 * Set text content on a text layer
 */
export function setTextContent(
  store: TextAnimatorStore,
  layerId: string,
  text: string
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData) return false;

  store.pushHistory();
  textData.text = text;
  store.project.meta.modified = new Date().toISOString();
  return true;
}

// ============================================================================
// TEXT ON PATH OPERATIONS
// ============================================================================

// Singleton path service instances per layer
const pathServices = new Map<string, TextOnPathService>();

/**
 * Get or create a TextOnPath service instance for a layer
 */
function getPathService(layerId: string): TextOnPathService {
  let service = pathServices.get(layerId);
  if (!service) {
    service = new TextOnPathService();
    pathServices.set(layerId, service);
  }
  return service;
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
  align?: 'left' | 'center' | 'right';
}

/**
 * Configure text on path for a text layer
 */
export function setTextPath(
  store: TextAnimatorStore,
  layerId: string,
  config: TextPathConfig
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData) return false;

  store.pushHistory();

  // Store path config on layer data
  (textData as any).pathConfig = {
    pathPoints: config.pathPoints,
    closed: config.closed ?? false,
    reversed: config.reversed ?? false,
    perpendicularToPath: config.perpendicularToPath ?? true,
    forceAlignment: config.forceAlignment ?? false,
    firstMargin: config.firstMargin ?? 0,
    lastMargin: config.lastMargin ?? 0,
    offset: config.offset ?? 0,
    align: config.align ?? 'left',
  };

  // Set path on service
  const service = getPathService(layerId);
  service.setPath(config.pathPoints, config.closed ?? false);

  store.project.meta.modified = new Date().toISOString();
  return true;
}

/**
 * Get text path config from a text layer
 */
export function getTextPathConfig(
  store: TextAnimatorStore,
  layerId: string
): TextPathConfig | null {
  const layer = getTextLayer(store, layerId);
  if (!layer) return null;

  const textData = getTextData(layer);
  if (!textData) return null;

  return (textData as any).pathConfig || null;
}

/**
 * Update specific path properties
 */
export function updateTextPath(
  store: TextAnimatorStore,
  layerId: string,
  updates: Partial<TextPathConfig>
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData) return false;

  const currentConfig = (textData as any).pathConfig;
  if (!currentConfig) return false;

  store.pushHistory();

  // Apply updates
  Object.assign(currentConfig, updates);

  // Rebuild path if points changed
  if (updates.pathPoints || updates.closed !== undefined) {
    const service = getPathService(layerId);
    service.setPath(currentConfig.pathPoints, currentConfig.closed ?? false);
  }

  store.project.meta.modified = new Date().toISOString();
  return true;
}

/**
 * Get character placements along the path
 *
 * Returns detailed placement info including:
 * - position (x, y, z)
 * - rotation (for perpendicular to path)
 * - distance along path
 * - visibility
 */
export function getCharacterPathPlacements(
  store: TextAnimatorStore,
  layerId: string,
  frame: number
): CharacterPlacement[] {
  const layer = getTextLayer(store, layerId);
  if (!layer) return [];

  const textData = getTextData(layer);
  if (!textData) return [];

  const pathConfig = (textData as any).pathConfig;
  if (!pathConfig || !pathConfig.pathPoints || pathConfig.pathPoints.length < 2) {
    return [];
  }

  const text = textData.text || '';
  if (text.length === 0) return [];

  const service = getPathService(layerId);

  // Ensure path is set
  if (!service.hasPath()) {
    service.setPath(pathConfig.pathPoints, pathConfig.closed ?? false);
  }

  // Estimate character widths (assume monospace for simplicity - could be enhanced)
  const fontSize = (textData as any).fontSize || 72;
  const charWidth = fontSize * 0.6; // Approximate character width
  const characterWidths = Array(text.length).fill(charWidth);

  // Build config
  const config: TextOnPathConfig = {
    pathLayerId: layerId,
    reversed: pathConfig.reversed ?? false,
    perpendicularToPath: pathConfig.perpendicularToPath ?? true,
    forceAlignment: pathConfig.forceAlignment ?? false,
    firstMargin: pathConfig.firstMargin ?? 0,
    lastMargin: pathConfig.lastMargin ?? 0,
    offset: pathConfig.offset ?? 0,
    align: pathConfig.align ?? 'left',
  };

  const tracking = (textData as any).tracking || 0;
  return service.calculatePlacements(characterWidths, config, tracking, fontSize);
}

/**
 * Get total path length in pixels
 */
export function getPathLength(
  store: TextAnimatorStore,
  layerId: string
): number {
  const layer = getTextLayer(store, layerId);
  if (!layer) return 0;

  const textData = getTextData(layer);
  if (!textData) return 0;

  const pathConfig = (textData as any).pathConfig;
  if (!pathConfig || !pathConfig.pathPoints || pathConfig.pathPoints.length < 2) {
    return 0;
  }

  const service = getPathService(layerId);
  if (!service.hasPath()) {
    service.setPath(pathConfig.pathPoints, pathConfig.closed ?? false);
  }

  return service.getTotalLength();
}

/**
 * Clear text path (return to normal text layout)
 */
export function clearTextPath(
  store: TextAnimatorStore,
  layerId: string
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData) return false;

  store.pushHistory();

  delete (textData as any).pathConfig;

  // Clean up service
  const service = pathServices.get(layerId);
  if (service) {
    service.dispose();
    pathServices.delete(layerId);
  }

  store.project.meta.modified = new Date().toISOString();
  return true;
}

/**
 * Check if text layer has path configured
 */
export function hasTextPath(
  store: TextAnimatorStore,
  layerId: string
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData) return false;

  const pathConfig = (textData as any).pathConfig;
  return !!(pathConfig && pathConfig.pathPoints && pathConfig.pathPoints.length >= 2);
}
