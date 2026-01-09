/**
 * Test Fixtures
 *
 * Provides properly typed factory functions for creating test data.
 * 
 * CRITICAL: These fixtures REUSE production helpers to ensure exact match.
 * Do NOT duplicate logic - import from production code.
 * 
 * PRODUCTION CODE REFERENCES:
 * - Layer creation: @/stores/actions/layerActions.ts createLayer()
 * - Transform creation: @/types/transform.ts createDefaultTransform()
 * - Property creation: @/types/animation.ts createAnimatableProperty()
 * - Keyframe creation: @/types/animation.ts createKeyframe()
 * - Composition creation: @/stores/actions/compositionActions.ts createComposition()
 *
 * USAGE:
 *   import { createTestLayer, createTestComposition } from '../fixtures';
 *   const layer = createTestLayer('solid');
 *   const comp = createTestComposition({ name: 'Test' });
 *
 * CONTRACT:
 * - All fixtures wrap production helpers where they exist
 * - Only create new helpers when production code lacks them
 * - All fixtures produce type-safe, complete objects matching production patterns
 */

// ============================================================================
// REUSE EXISTING PRODUCTION HELPERS
// These are the authoritative sources - do NOT duplicate their logic
// ============================================================================
import {
  createAnimatableProperty,
  createKeyframe,
  type AnimatableProperty,
  type Keyframe,
} from '@/types/animation';

import {
  createDefaultTransform,
  type LayerTransform,
} from '@/types/transform';

import type {
  CompositionSettings,
  Layer,
  EffectInstance,
  LatticeProject,
  Composition,
} from '@/types/project';

import { getDefaultLayerData } from '@/stores/actions/layer/layerDefaults';

// ============================================================================
// ID GENERATION (for test isolation)
// ============================================================================

let idCounter = 0;

/**
 * Generate a unique test ID
 * Uses counter + timestamp to ensure uniqueness across test runs
 * 
 * PRODUCTION PATTERN: `layer_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`
 * We use a simpler pattern for tests but maintain uniqueness.
 */
export function generateTestId(prefix: string = 'test'): string {
  return `${prefix}_${++idCounter}_${Date.now().toString(36)}`;
}

/**
 * Reset ID counter (call in beforeEach if needed for deterministic IDs)
 */
export function resetTestIdCounter(): void {
  idCounter = 0;
}

// ============================================================================
// COMPOSITION SETTINGS
// Based on: @/stores/actions/compositionActions.ts createComposition()
// ============================================================================

/**
 * Create a complete CompositionSettings object for testing.
 * 
 * DEFAULTS match production code in createComposition():
 * - 1024x1024 resolution (production default)
 * - 81 frames (production default)
 * - DEFAULT_FPS (16 for Phase 1, see @/utils/fpsUtils)
 * - "#050505" background (production default)
 * - autoResizeToContent: true (production default)
 * - frameBlendingEnabled: false (production default)
 * 
 * @see createComposition in @/stores/actions/compositionActions.ts lines 68-78
 */
export function createTestCompositionSettings(
  overrides: Partial<CompositionSettings> = {}
): CompositionSettings {
  const fps = overrides.fps ?? 16; // DEFAULT_FPS from production
  const frameCount = overrides.frameCount ?? 81; // Production default
  
  return {
    width: overrides.width ?? 1024, // Production default
    height: overrides.height ?? 1024, // Production default
    frameCount,
    fps,
    duration: frameCount / fps, // Computed from frameCount/fps (production pattern)
    backgroundColor: overrides.backgroundColor ?? "#050505", // Production default
    autoResizeToContent: overrides.autoResizeToContent ?? true, // Production default
    frameBlendingEnabled: overrides.frameBlendingEnabled ?? false, // Production default
    ...overrides,
  };
}

// ============================================================================
// ANIMATABLE PROPERTY
// REUSE: createAnimatableProperty from @/types/animation
// ============================================================================

/**
 * Create an AnimatableProperty for testing.
 * WRAPS the production helper to ensure exact match.
 * 
 * @see createAnimatableProperty in @/types/animation.ts
 */
export function createTestAnimatableProperty<T>(
  name: string,
  value: T,
  type: 'number' | 'position' | 'color' | 'enum' | 'vector3' = 'number',
  group?: string
): AnimatableProperty<T> {
  return createAnimatableProperty(name, value, type, group);
}

/**
 * Create an animated property with keyframes for testing.
 * REUSES the production createKeyframe helper.
 * 
 * BEZIER HANDLE DEFAULTS (from production createKeyframe):
 * - inHandle: { frame: -5, value: 0, enabled: true }
 * - outHandle: { frame: 5, value: 0, enabled: true }
 * 
 * The ±5 frame offset creates a gentle ease curve by default.
 * At 30fps: 5 frames = ~0.167 seconds of influence
 * At 16fps: 5 frames = ~0.313 seconds of influence
 * 
 * @see createKeyframe in @/types/animation.ts lines 158-180
 */
export function createTestAnimatedProperty<T>(
  name: string,
  keyframes: Array<{ frame: number; value: T }>,
  type: 'number' | 'position' | 'color' | 'enum' | 'vector3' = 'number'
): AnimatableProperty<T> {
  if (keyframes.length === 0) {
    throw new Error('createTestAnimatedProperty requires at least one keyframe');
  }
  
  // Use production createKeyframe helper - preserves exact handle defaults
  const fullKeyframes: Keyframe<T>[] = keyframes.map((kf) => 
    createKeyframe(kf.frame, kf.value, 'linear')
  );
  
  const baseProp = createAnimatableProperty(name, keyframes[0].value, type);
  return {
    ...baseProp,
    animated: true,
    keyframes: fullKeyframes,
  };
}

// ============================================================================
// KEYFRAME
// REUSE: createKeyframe from @/types/animation
// ============================================================================

/**
 * Create a complete Keyframe for testing.
 * WRAPS the production helper.
 * 
 * NOTE: Default bezier handles are { frame: ±5, value: 0, enabled: true }
 * This creates 5-frame influence in each direction (gentle ease).
 * 
 * @see createKeyframe in @/types/animation.ts lines 158-180
 */
export function createTestKeyframe<T>(
  frame: number,
  value: T,
  interpolation: 'linear' | 'bezier' | 'hold' = 'linear'
): Keyframe<T> {
  return createKeyframe(frame, value, interpolation);
}

// ============================================================================
// LAYER TRANSFORM
// REUSE: createDefaultTransform from @/types/transform
// ============================================================================

/**
 * Create a complete LayerTransform for testing.
 * WRAPS the production helper.
 * 
 * PRODUCTION DEFAULTS (from createDefaultTransform):
 * - position: { x: 0, y: 0, z: 0 } (vector3)
 * - origin: { x: 0, y: 0, z: 0 } (vector3)
 * - scale: { x: 100, y: 100, z: 100 } (vector3)
 * - rotation: 0 (number)
 * - orientation: { x: 0, y: 0, z: 0 } (vector3)
 * - rotationX/Y/Z: 0 (number)
 * 
 * @see createDefaultTransform in @/types/transform.ts lines 178-208
 */
export function createTestTransform(
  overrides: Partial<LayerTransform> = {}
): LayerTransform {
  const base = createDefaultTransform();
  return {
    ...base,
    ...overrides,
  };
}

// ============================================================================
// EFFECT INSTANCE
// ============================================================================

/**
 * Create a complete EffectInstance for testing.
 * 
 * DEFAULTS match production patterns:
 * - enabled: true
 * - category: 'stylize'
 * - expanded: false
 * - parameters: {}
 */
export function createTestEffectInstance(
  effectKey: string,
  overrides: Partial<EffectInstance> = {}
): EffectInstance {
  return {
    id: generateTestId('effect'),
    name: overrides.name ?? effectKey.replace(/-/g, ' ').replace(/\b\w/g, c => c.toUpperCase()),
    effectKey,
    enabled: true,
    category: 'stylize',
    expanded: false,
    parameters: {},
    ...overrides,
  };
}

// ============================================================================
// LAYER
// Based on: @/stores/actions/layerActions.ts createLayer()
// ============================================================================

/**
 * Create a complete Layer for testing.
 * 
 * DEFAULTS match production code in createLayer():
 * - visible: true
 * - locked: false
 * - isolate: false
 * - threeD: false
 * - motionBlur: false
 * - startFrame: 0
 * - endFrame: (comp.frameCount || 81) - 1
 * - parentId: null
 * - blendMode: "normal"
 * - opacity: createAnimatableProperty("opacity", 100, "number")
 * - transform: createDefaultTransform() (centered in comp)
 * - properties: [] (type-specific properties added by getDefaultLayerData)
 * - effects: []
 * 
 * @see createLayer in @/stores/actions/layerActions.ts lines 81-171
 */
export function createTestLayer(
  type: Layer['type'] = 'solid',
  overrides: Partial<Layer> & {
    compositionContext?: { width: number; height: number; frameCount?: number };
  } = {}
): Layer {
  const compContext = overrides.compositionContext ?? { width: 1920, height: 1080 };
  const frameCount = overrides.compositionContext?.frameCount ?? 81;
  
  // Get type-specific data from production helper
  const layerData = getDefaultLayerData(type, compContext);
  
  // Create transform using production helper
  const transform = createDefaultTransform();
  // Center the layer in composition (production pattern)
  transform.position.value = { 
    x: compContext.width / 2, 
    y: compContext.height / 2 
  };
  
  return {
    id: generateTestId('layer'),
    type,
    name: overrides.name ?? `${type.charAt(0).toUpperCase() + type.slice(1)} 1`,
    visible: true,
    locked: false,
    isolate: false,
    threeD: false,
    motionBlur: false,
    startFrame: 0,
    endFrame: frameCount - 1,
    // Backwards compatibility aliases (production pattern)
    inPoint: 0,
    outPoint: frameCount - 1,
    parentId: null,
    blendMode: 'normal',
    opacity: createAnimatableProperty('opacity', 100, 'number'),
    transform,
    properties: [],
    effects: [],
    data: layerData as Layer['data'],
    ...overrides,
  };
}

// ============================================================================
// COMPOSITION
// Based on: @/stores/actions/compositionActions.ts createComposition()
// ============================================================================

/**
 * Create a complete Composition for testing.
 * 
 * DEFAULTS match production code in createComposition():
 * - layers: []
 * - currentFrame: 0
 * - isNestedComp: false
 * 
 * @see createComposition in @/stores/actions/compositionActions.ts lines 53-88
 */
export function createTestComposition(
  overrides: {
    id?: string;
    name?: string;
    layers?: Layer[];
    settings?: Partial<CompositionSettings>;
    currentFrame?: number;
    isNestedComp?: boolean;
  } = {}
): Composition {
  const id = overrides.id ?? generateTestId('comp');
  const settingsOverrides = overrides.settings ?? {};
  return {
    id,
    name: overrides.name ?? 'Test Composition',
    settings: createTestCompositionSettings(settingsOverrides),
    layers: overrides.layers ?? [],
    currentFrame: overrides.currentFrame ?? 0,
    isNestedComp: overrides.isNestedComp ?? false,
  };
}

// ============================================================================
// PROJECT
// Based on: @/types/project.ts LatticeProject interface
// ============================================================================

/**
 * Create a complete LatticeProject for testing.
 * 
 * DEFAULTS match production patterns:
 * - version: "1.0.0"
 * - assets: {}
 * - layers: [] (legacy)
 * - currentFrame: 0
 */
export function createTestProject(
  overrides: {
    composition?: Partial<CompositionSettings>;
    layers?: Layer[];
    compositions?: Record<string, Composition>;
  } = {}
): LatticeProject {
  const mainCompId = generateTestId('comp');
  const compOverrides: Parameters<typeof createTestComposition>[0] = {
    id: mainCompId,
    name: 'Main',
  };
  if (overrides.composition) {
    compOverrides.settings = overrides.composition;
  }
  if (overrides.layers) {
    compOverrides.layers = overrides.layers;
  }
  const mainComp = createTestComposition(compOverrides);
  
  return {
    version: '1.0.0',
    mainCompositionId: mainCompId,
    meta: {
      name: 'Test Project',
      created: new Date().toISOString(),
      modified: new Date().toISOString(),
    },
    composition: mainComp.settings,
    compositions: {
      [mainCompId]: mainComp,
      ...overrides.compositions,
    },
    assets: {},
    layers: overrides.layers ?? [],
    currentFrame: 0,
  };
}
