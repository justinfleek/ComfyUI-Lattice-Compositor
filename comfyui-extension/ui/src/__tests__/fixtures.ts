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
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  const fps = (overrides.fps !== null && overrides.fps !== undefined && typeof overrides.fps === "number" && Number.isFinite(overrides.fps) && overrides.fps > 0) ? overrides.fps : 16; // DEFAULT_FPS from production
  const frameCount = (overrides.frameCount !== null && overrides.frameCount !== undefined && typeof overrides.frameCount === "number" && Number.isFinite(overrides.frameCount) && overrides.frameCount > 0) ? overrides.frameCount : 81; // Production default
  
  const width = (overrides.width !== null && overrides.width !== undefined && typeof overrides.width === "number" && Number.isFinite(overrides.width) && overrides.width > 0) ? overrides.width : 1024; // Production default
  const height = (overrides.height !== null && overrides.height !== undefined && typeof overrides.height === "number" && Number.isFinite(overrides.height) && overrides.height > 0) ? overrides.height : 1024; // Production default
  const backgroundColor = (overrides.backgroundColor !== null && overrides.backgroundColor !== undefined && typeof overrides.backgroundColor === "string" && overrides.backgroundColor.length > 0) ? overrides.backgroundColor : "#050505"; // Production default
  const autoResizeToContent = (overrides.autoResizeToContent !== null && overrides.autoResizeToContent !== undefined && typeof overrides.autoResizeToContent === "boolean") ? overrides.autoResizeToContent : true; // Production default
  const frameBlendingEnabled = (overrides.frameBlendingEnabled !== null && overrides.frameBlendingEnabled !== undefined && typeof overrides.frameBlendingEnabled === "boolean") ? overrides.frameBlendingEnabled : false; // Production default
  
  return {
    width,
    height,
    frameCount,
    fps,
    duration: frameCount / fps, // Computed from frameCount/fps (production pattern)
    backgroundColor,
    autoResizeToContent,
    frameBlendingEnabled,
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
  // Deterministic: Provide layerId and propertyPath for keyframe ID generation
  const testLayerId = 'test-layer';
  const testPropertyPath = `transform.${name}`;
  const fullKeyframes: Keyframe<T>[] = keyframes.map((kf) => 
    createKeyframe(testLayerId, testPropertyPath, kf.frame, kf.value, 'linear')
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
/**
 * Create a test keyframe with default layer/property IDs
 * Deterministic: Uses test IDs for consistent keyframe ID generation
 */
export function createTestKeyframe<T>(
  frame: number,
  value: T,
  interpolation: 'linear' | 'bezier' | 'hold' = 'linear'
): Keyframe<T> {
  // Use test IDs for deterministic keyframe ID generation
  const testLayerId = 'test-layer';
  const testPropertyPath = 'test.property';
  return createKeyframe(testLayerId, testPropertyPath, frame, value, interpolation);
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
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  const name = (overrides.name !== null && overrides.name !== undefined && typeof overrides.name === "string" && overrides.name.length > 0) ? overrides.name : effectKey.replace(/-/g, ' ').replace(/\b\w/g, c => c.toUpperCase());
  return {
    id: generateTestId('effect'),
    name,
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
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
  const compContext = (overrides.compositionContext !== null && overrides.compositionContext !== undefined && typeof overrides.compositionContext === "object") ? overrides.compositionContext : { width: 1920, height: 1080 };
  const compContextFrameCount = (overrides.compositionContext !== null && overrides.compositionContext !== undefined && typeof overrides.compositionContext === "object" && "frameCount" in overrides.compositionContext && typeof overrides.compositionContext.frameCount === "number" && Number.isFinite(overrides.compositionContext.frameCount) && overrides.compositionContext.frameCount > 0) ? overrides.compositionContext.frameCount : undefined;
  const frameCount = compContextFrameCount !== undefined ? compContextFrameCount : 81;
  
  // Get type-specific data from production helper
  const layerData = getDefaultLayerData(type, compContext);
  
  // Create transform using production helper
  const transform = createDefaultTransform();
  // Center the layer in composition (production pattern)
  transform.position.value = { 
    x: compContext.width / 2, 
    y: compContext.height / 2 
  };
  
  const name = (overrides.name !== null && overrides.name !== undefined && typeof overrides.name === "string" && overrides.name.length > 0) ? overrides.name : `${type.charAt(0).toUpperCase() + type.slice(1)} 1`;
  return {
    id: generateTestId('layer'),
    type,
    name,
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
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  const id = (overrides.id !== null && overrides.id !== undefined && typeof overrides.id === "string" && overrides.id.length > 0) ? overrides.id : generateTestId('comp');
  const settingsOverrides = (overrides.settings !== null && overrides.settings !== undefined && typeof overrides.settings === "object" && overrides.settings !== null) ? overrides.settings : {};
  const name = (overrides.name !== null && overrides.name !== undefined && typeof overrides.name === "string" && overrides.name.length > 0) ? overrides.name : 'Test Composition';
  const layers = (Array.isArray(overrides.layers)) ? overrides.layers : [];
  const currentFrame = (overrides.currentFrame !== null && overrides.currentFrame !== undefined && typeof overrides.currentFrame === "number" && Number.isFinite(overrides.currentFrame) && overrides.currentFrame >= 0) ? overrides.currentFrame : 0;
  const isNestedComp = (overrides.isNestedComp !== null && overrides.isNestedComp !== undefined && typeof overrides.isNestedComp === "boolean") ? overrides.isNestedComp : false;
  return {
    id,
    name,
    settings: createTestCompositionSettings(settingsOverrides),
    layers,
    currentFrame,
    isNestedComp,
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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    layers: (Array.isArray(overrides.layers)) ? overrides.layers : [],
    currentFrame: 0,
  };
}
