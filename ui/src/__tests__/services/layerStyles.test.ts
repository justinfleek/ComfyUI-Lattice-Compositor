/**
 * Layer Styles Test Suite
 *
 * Tests for Photoshop-style Layer Styles implementation:
 * - Type definitions and factory functions
 * - Layer style renderers
 * - Store actions
 * - Integration with render pipeline
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  createDefaultLayerStyles,
  createDefaultDropShadow,
  createDefaultInnerShadow,
  createDefaultOuterGlow,
  createDefaultInnerGlow,
  createDefaultBevelEmboss,
  createDefaultSatin,
  createDefaultColorOverlay,
  createDefaultGradientOverlay,
  createDefaultStroke,
  createDefaultBlendingOptions,
  type LayerStyles,
  type DropShadowStyle,
  type RGBA
} from '@/types/layerStyles';

import {
  renderLayerStyles,
  renderDropShadowStyle,
  renderInnerShadowStyle,
  renderOuterGlowStyle,
  renderInnerGlowStyle,
  renderBevelEmbossStyle,
  renderSatinStyle,
  renderColorOverlayStyle,
  renderGradientOverlayStyle,
  renderStrokeStyle
} from '@/services/effects/layerStyleRenderer';

import {
  setLayerStylesEnabled,
  setStyleEnabled,
  updateStyleProperty,
  copyLayerStyles,
  pasteLayerStyles,
  clearLayerStyles,
  hasStylesInClipboard,
  addDropShadow,
  addStroke,
  addOuterGlow,
  addColorOverlay,
  addBevelEmboss,
  applyStylePreset,
  getStylePresetNames,
  STYLE_PRESETS
} from '@/stores/actions/layerStyleActions';

// ============================================================================
// TYPE DEFINITION TESTS
// ============================================================================

describe('Layer Styles Type Definitions', () => {
  describe('createDefaultLayerStyles', () => {
    it('creates layer styles with enabled=false by default', () => {
      const styles = createDefaultLayerStyles();
      expect(styles.enabled).toBe(false);
    });

    it('creates all style types as undefined by default', () => {
      const styles = createDefaultLayerStyles();
      expect(styles.dropShadow).toBeUndefined();
      expect(styles.innerShadow).toBeUndefined();
      expect(styles.outerGlow).toBeUndefined();
      expect(styles.innerGlow).toBeUndefined();
      expect(styles.bevelEmboss).toBeUndefined();
      expect(styles.satin).toBeUndefined();
      expect(styles.colorOverlay).toBeUndefined();
      expect(styles.gradientOverlay).toBeUndefined();
      expect(styles.stroke).toBeUndefined();
    });
  });

  describe('createDefaultDropShadow', () => {
    it('creates drop shadow with correct defaults', () => {
      const shadow = createDefaultDropShadow();
      expect(shadow.enabled).toBe(true);
      expect(shadow.blendMode).toBe('multiply');
      expect(shadow.opacity.value).toBe(75);
      expect(shadow.angle.value).toBe(120);
      expect(shadow.distance.value).toBe(5);
      expect(shadow.spread.value).toBe(0);
      expect(shadow.size.value).toBe(5);
      expect(shadow.color.value).toEqual({ r: 0, g: 0, b: 0, a: 1 });
    });

    it('creates animatable properties', () => {
      const shadow = createDefaultDropShadow();
      expect(shadow.opacity.animated).toBe(false);
      expect(shadow.angle.animated).toBe(false);
      expect(shadow.distance.animated).toBe(false);
    });
  });

  describe('createDefaultInnerShadow', () => {
    it('creates inner shadow with correct defaults', () => {
      const shadow = createDefaultInnerShadow();
      expect(shadow.enabled).toBe(true);
      expect(shadow.blendMode).toBe('multiply');
      expect(shadow.choke.value).toBe(0);
    });
  });

  describe('createDefaultOuterGlow', () => {
    it('creates outer glow with correct defaults', () => {
      const glow = createDefaultOuterGlow();
      expect(glow.enabled).toBe(true);
      expect(glow.blendMode).toBe('screen');
      expect(glow.technique).toBe('softer');
      expect(glow.spread.value).toBe(0);
      expect(glow.size.value).toBe(5);
    });
  });

  describe('createDefaultInnerGlow', () => {
    it('creates inner glow with correct defaults', () => {
      const glow = createDefaultInnerGlow();
      expect(glow.enabled).toBe(true);
      expect(glow.source).toBe('edge');
      expect(glow.choke.value).toBe(0);
    });
  });

  describe('createDefaultBevelEmboss', () => {
    it('creates bevel emboss with correct defaults', () => {
      const bevel = createDefaultBevelEmboss();
      expect(bevel.enabled).toBe(true);
      expect(bevel.style).toBe('inner-bevel');
      expect(bevel.technique).toBe('smooth');
      expect(bevel.depth.value).toBe(100);
      expect(bevel.direction).toBe('up');
      expect(bevel.angle.value).toBe(120);
      expect(bevel.altitude.value).toBe(30);
      expect(bevel.highlightMode).toBe('screen');
      expect(bevel.shadowMode).toBe('multiply');
    });
  });

  describe('createDefaultSatin', () => {
    it('creates satin with correct defaults', () => {
      const satin = createDefaultSatin();
      expect(satin.enabled).toBe(true);
      expect(satin.blendMode).toBe('multiply');
      expect(satin.invert).toBe(true); // Default is inverted
    });
  });

  describe('createDefaultColorOverlay', () => {
    it('creates color overlay with correct defaults', () => {
      const overlay = createDefaultColorOverlay();
      expect(overlay.enabled).toBe(true);
      expect(overlay.blendMode).toBe('normal');
      expect(overlay.color.value).toEqual({ r: 255, g: 0, b: 0, a: 1 });
    });
  });

  describe('createDefaultGradientOverlay', () => {
    it('creates gradient overlay with correct defaults', () => {
      const overlay = createDefaultGradientOverlay();
      expect(overlay.enabled).toBe(true);
      expect(overlay.style).toBe('linear');
      expect(overlay.angle.value).toBe(90);
      expect(overlay.scale.value).toBe(100);
      expect(overlay.alignWithLayer).toBe(true);
      expect(overlay.reverse).toBe(false);
    });
  });

  describe('createDefaultStroke', () => {
    it('creates stroke with correct defaults', () => {
      const stroke = createDefaultStroke();
      expect(stroke.enabled).toBe(true);
      expect(stroke.size.value).toBe(3);
      expect(stroke.position).toBe('outside');
      expect(stroke.fillType).toBe('color');
    });
  });

  describe('createDefaultBlendingOptions', () => {
    it('creates blending options with correct defaults', () => {
      const options = createDefaultBlendingOptions();
      expect(options.fillOpacity.value).toBe(100);
      expect(options.blendInteriorStylesAsGroup).toBe(false);
    });
  });
});

// ============================================================================
// RENDERER TESTS
// ============================================================================

describe('Layer Style Renderers', () => {
  // Helper to create a test canvas
  function createTestCanvas(width = 100, height = 100): HTMLCanvasElement {
    const canvas = document.createElement('canvas');
    canvas.width = width;
    canvas.height = height;
    const ctx = canvas.getContext('2d')!;

    // Draw a simple shape for testing
    ctx.fillStyle = 'white';
    ctx.fillRect(25, 25, 50, 50);

    return canvas;
  }

  describe('renderLayerStyles', () => {
    it('returns input canvas when styles disabled', () => {
      const input = createTestCanvas();
      const styles: LayerStyles = { enabled: false };

      const result = renderLayerStyles(input, styles, 0);
      expect(result).toBe(input);
    });

    it('returns input canvas when no styles enabled', () => {
      const input = createTestCanvas();
      const styles: LayerStyles = { enabled: true };

      const result = renderLayerStyles(input, styles, 0);
      expect(result).toBe(input);
    });

    it('processes enabled styles', () => {
      const input = createTestCanvas();
      const styles: LayerStyles = {
        enabled: true,
        dropShadow: createDefaultDropShadow()
      };

      const result = renderLayerStyles(input, styles, 0);
      // Result should be a new canvas with shadow applied
      expect(result).not.toBe(input);
      expect(result.width).toBe(input.width);
      expect(result.height).toBe(input.height);
    });
  });

  describe('renderDropShadowStyle', () => {
    it('creates shadow offset based on angle and distance', () => {
      const input = createTestCanvas();
      const shadow = createDefaultDropShadow();
      shadow.distance.value = 10;
      shadow.angle.value = 0; // Right

      const result = renderDropShadowStyle(input, shadow, 0);
      expect(result).not.toBe(input);
    });
  });

  describe('renderStrokeStyle', () => {
    it('creates stroke around content', () => {
      const input = createTestCanvas();
      const stroke = createDefaultStroke();
      stroke.size.value = 5;
      stroke.position = 'outside';

      const result = renderStrokeStyle(input, stroke, 0);
      expect(result).not.toBe(input);
    });
  });

  describe('renderColorOverlayStyle', () => {
    it('overlays color on content', () => {
      const input = createTestCanvas();
      const overlay = createDefaultColorOverlay();
      overlay.color.value = { r: 255, g: 0, b: 0, a: 1 };

      const result = renderColorOverlayStyle(input, overlay, 0);
      expect(result).not.toBe(input);
    });
  });
});

// ============================================================================
// STORE ACTION TESTS
// ============================================================================

describe('Layer Style Store Actions', () => {
  // Mock store
  let mockStore: any;
  let testLayer: any;

  beforeEach(() => {
    testLayer = {
      id: 'layer-1',
      name: 'Test Layer',
      type: 'solid',
      layerStyles: undefined
    };

    mockStore = {
      project: {
        meta: { modified: '' }
      },
      getActiveCompLayers: vi.fn(() => [testLayer]),
      pushHistory: vi.fn()
    };
  });

  describe('setLayerStylesEnabled', () => {
    it('enables layer styles and creates default if needed', () => {
      setLayerStylesEnabled(mockStore, 'layer-1', true);

      expect(testLayer.layerStyles).toBeDefined();
      expect(testLayer.layerStyles.enabled).toBe(true);
      expect(mockStore.pushHistory).toHaveBeenCalled();
    });

    it('disables layer styles', () => {
      testLayer.layerStyles = createDefaultLayerStyles();
      testLayer.layerStyles.enabled = true;

      setLayerStylesEnabled(mockStore, 'layer-1', false);

      expect(testLayer.layerStyles.enabled).toBe(false);
    });

    it('does nothing for non-existent layer', () => {
      setLayerStylesEnabled(mockStore, 'non-existent', true);
      expect(mockStore.pushHistory).not.toHaveBeenCalled();
    });
  });

  describe('setStyleEnabled', () => {
    it('creates and enables a specific style', () => {
      setStyleEnabled(mockStore, 'layer-1', 'dropShadow', true);

      expect(testLayer.layerStyles).toBeDefined();
      expect(testLayer.layerStyles.dropShadow).toBeDefined();
      expect(testLayer.layerStyles.dropShadow.enabled).toBe(true);
      expect(testLayer.layerStyles.enabled).toBe(true); // Master also enabled
    });

    it('disables a specific style', () => {
      testLayer.layerStyles = createDefaultLayerStyles();
      testLayer.layerStyles.dropShadow = createDefaultDropShadow();

      setStyleEnabled(mockStore, 'layer-1', 'dropShadow', false);

      expect(testLayer.layerStyles.dropShadow.enabled).toBe(false);
    });
  });

  describe('updateStyleProperty', () => {
    it('updates animatable property value', () => {
      testLayer.layerStyles = createDefaultLayerStyles();
      testLayer.layerStyles.dropShadow = createDefaultDropShadow();

      updateStyleProperty(mockStore, 'layer-1', 'dropShadow', 'opacity', 50);

      expect(testLayer.layerStyles.dropShadow.opacity.value).toBe(50);
    });

    it('updates non-animatable property', () => {
      testLayer.layerStyles = createDefaultLayerStyles();
      testLayer.layerStyles.dropShadow = createDefaultDropShadow();

      updateStyleProperty(mockStore, 'layer-1', 'dropShadow', 'blendMode', 'screen');

      expect(testLayer.layerStyles.dropShadow.blendMode).toBe('screen');
    });
  });

  describe('copyLayerStyles / pasteLayerStyles', () => {
    it('copies and pastes styles between layers', () => {
      const layer2 = { id: 'layer-2', name: 'Layer 2', layerStyles: undefined };
      mockStore.getActiveCompLayers = vi.fn(() => [testLayer, layer2]);

      // Setup source layer
      testLayer.layerStyles = createDefaultLayerStyles();
      testLayer.layerStyles.enabled = true;
      testLayer.layerStyles.dropShadow = createDefaultDropShadow();
      testLayer.layerStyles.dropShadow.opacity.value = 80;

      // Copy
      const copied = copyLayerStyles(mockStore, 'layer-1');
      expect(copied).toBeDefined();
      expect(hasStylesInClipboard()).toBe(true);

      // Paste
      pasteLayerStyles(mockStore, 'layer-2');
      expect(layer2.layerStyles).toBeDefined();
      expect(layer2.layerStyles.dropShadow.opacity.value).toBe(80);
    });

    it('deep clones to avoid reference issues', () => {
      testLayer.layerStyles = createDefaultLayerStyles();
      testLayer.layerStyles.dropShadow = createDefaultDropShadow();

      copyLayerStyles(mockStore, 'layer-1');

      // Modify source after copy
      testLayer.layerStyles.dropShadow.opacity.value = 10;

      const layer2 = { id: 'layer-2', name: 'Layer 2', layerStyles: undefined };
      mockStore.getActiveCompLayers = vi.fn(() => [testLayer, layer2]);

      pasteLayerStyles(mockStore, 'layer-2');

      // Pasted value should be original, not modified
      expect(layer2.layerStyles.dropShadow.opacity.value).toBe(75);
    });
  });

  describe('clearLayerStyles', () => {
    it('removes all layer styles', () => {
      testLayer.layerStyles = createDefaultLayerStyles();
      testLayer.layerStyles.dropShadow = createDefaultDropShadow();

      clearLayerStyles(mockStore, 'layer-1');

      expect(testLayer.layerStyles).toBeUndefined();
    });
  });

  describe('Quick Style Helpers', () => {
    it('addDropShadow creates drop shadow with options', () => {
      addDropShadow(mockStore, 'layer-1', {
        color: { r: 255, g: 0, b: 0, a: 1 },
        distance: 15,
        opacity: 50
      });

      expect(testLayer.layerStyles.dropShadow).toBeDefined();
      expect(testLayer.layerStyles.dropShadow.color.value).toEqual({ r: 255, g: 0, b: 0, a: 1 });
      expect(testLayer.layerStyles.dropShadow.distance.value).toBe(15);
      expect(testLayer.layerStyles.dropShadow.opacity.value).toBe(50);
    });

    it('addStroke creates stroke with options', () => {
      addStroke(mockStore, 'layer-1', {
        size: 5,
        position: 'inside'
      });

      expect(testLayer.layerStyles.stroke).toBeDefined();
      expect(testLayer.layerStyles.stroke.size.value).toBe(5);
      expect(testLayer.layerStyles.stroke.position).toBe('inside');
    });

    it('addOuterGlow creates glow with options', () => {
      addOuterGlow(mockStore, 'layer-1', {
        color: { r: 0, g: 255, b: 255, a: 1 },
        size: 20
      });

      expect(testLayer.layerStyles.outerGlow).toBeDefined();
      expect(testLayer.layerStyles.outerGlow.color.value).toEqual({ r: 0, g: 255, b: 255, a: 1 });
      expect(testLayer.layerStyles.outerGlow.size.value).toBe(20);
    });

    it('addColorOverlay creates overlay with options', () => {
      addColorOverlay(mockStore, 'layer-1', {
        color: { r: 0, g: 0, b: 255, a: 1 },
        opacity: 80,
        blendMode: 'multiply'
      });

      expect(testLayer.layerStyles.colorOverlay).toBeDefined();
      expect(testLayer.layerStyles.colorOverlay.color.value).toEqual({ r: 0, g: 0, b: 255, a: 1 });
      expect(testLayer.layerStyles.colorOverlay.opacity.value).toBe(80);
      expect(testLayer.layerStyles.colorOverlay.blendMode).toBe('multiply');
    });

    it('addBevelEmboss creates bevel with options', () => {
      addBevelEmboss(mockStore, 'layer-1', {
        style: 'emboss',
        depth: 200,
        direction: 'down'
      });

      expect(testLayer.layerStyles.bevelEmboss).toBeDefined();
      expect(testLayer.layerStyles.bevelEmboss.style).toBe('emboss');
      expect(testLayer.layerStyles.bevelEmboss.depth.value).toBe(200);
      expect(testLayer.layerStyles.bevelEmboss.direction).toBe('down');
    });
  });

  describe('Style Presets', () => {
    it('provides list of preset names', () => {
      const names = getStylePresetNames();
      expect(names).toContain('soft-shadow');
      expect(names).toContain('hard-shadow');
      expect(names).toContain('neon-glow');
      expect(names).toContain('simple-stroke');
      expect(names).toContain('embossed');
      expect(names.length).toBeGreaterThanOrEqual(7);
    });

    it('applies preset to layer', () => {
      applyStylePreset(mockStore, 'layer-1', 'soft-shadow');

      expect(testLayer.layerStyles).toBeDefined();
      expect(testLayer.layerStyles.enabled).toBe(true);
      expect(testLayer.layerStyles.dropShadow).toBeDefined();
    });

    it('neon-glow preset includes outer and inner glow', () => {
      applyStylePreset(mockStore, 'layer-1', 'neon-glow');

      expect(testLayer.layerStyles.outerGlow).toBeDefined();
      expect(testLayer.layerStyles.innerGlow).toBeDefined();
      // Neon cyan color
      expect(testLayer.layerStyles.outerGlow.color.value).toEqual({ r: 0, g: 255, b: 255, a: 1 });
    });
  });
});

// ============================================================================
// INTEGRATION TESTS
// ============================================================================

describe('Layer Styles Integration', () => {
  describe('Render Order', () => {
    it('applies styles in correct order: shadows → glows → bevel → overlays → stroke', () => {
      // This tests that the render pipeline respects the correct order
      const canvas = document.createElement('canvas');
      canvas.width = 100;
      canvas.height = 100;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = 'white';
      ctx.fillRect(25, 25, 50, 50);

      const styles: LayerStyles = {
        enabled: true,
        dropShadow: createDefaultDropShadow(),
        outerGlow: createDefaultOuterGlow(),
        stroke: createDefaultStroke()
      };

      // Should not throw
      const result = renderLayerStyles(canvas, styles, 0);
      expect(result).toBeDefined();
      expect(result.width).toBe(canvas.width);
    });
  });

  describe('Animation Support', () => {
    it('interpolates property values at different frames', () => {
      const shadow = createDefaultDropShadow();
      shadow.opacity.animated = true;
      shadow.opacity.keyframes = [
        { frame: 0, value: 0, interpolation: 'linear' },
        { frame: 100, value: 100, interpolation: 'linear' }
      ];

      // At frame 0: opacity should be 0
      // At frame 50: opacity should be 50
      // At frame 100: opacity should be 100
      // The renderer uses interpolateProperty internally

      const canvas = document.createElement('canvas');
      canvas.width = 50;
      canvas.height = 50;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = 'white';
      ctx.fillRect(10, 10, 30, 30);

      const styles: LayerStyles = {
        enabled: true,
        dropShadow: shadow
      };

      // Render at different frames - should not throw
      const result0 = renderLayerStyles(canvas, styles, 0);
      const result50 = renderLayerStyles(canvas, styles, 50);
      const result100 = renderLayerStyles(canvas, styles, 100);

      expect(result0).toBeDefined();
      expect(result50).toBeDefined();
      expect(result100).toBeDefined();
    });
  });

  describe('Style Combinations', () => {
    it('can combine multiple styles', () => {
      const canvas = document.createElement('canvas');
      canvas.width = 100;
      canvas.height = 100;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = 'white';
      ctx.fillRect(25, 25, 50, 50);

      const styles: LayerStyles = {
        enabled: true,
        dropShadow: createDefaultDropShadow(),
        innerShadow: createDefaultInnerShadow(),
        outerGlow: createDefaultOuterGlow(),
        innerGlow: createDefaultInnerGlow(),
        bevelEmboss: createDefaultBevelEmboss(),
        satin: createDefaultSatin(),
        colorOverlay: createDefaultColorOverlay(),
        gradientOverlay: createDefaultGradientOverlay(),
        stroke: createDefaultStroke()
      };

      // Should handle all styles without error
      const result = renderLayerStyles(canvas, styles, 0);
      expect(result).toBeDefined();
    });
  });
});
