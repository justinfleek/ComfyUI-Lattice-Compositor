/**
 * REGRESSION TEST: Viewport Controls NaN/Infinity Validation
 *
 * @fixed 2026-01-10
 * @file composables/useViewportControls.ts
 * @rootCause setZoom() and screenToScene() could receive invalid values (NaN, Infinity, <= 0)
 *            which would corrupt viewport state and cause coordinate misalignment
 * @fix Added validation guards that reject invalid input with warnings instead of
 *      silently corrupting state
 * @counterexample setZoom(NaN) would set zoom.value = NaN, breaking all coordinate math
 */

import { describe, test, expect, vi, beforeEach } from 'vitest';
import { ref, shallowRef } from 'vue';
import { useViewportControls } from '@/composables/useViewportControls';
import type { LatticeEngine } from '@/engine/LatticeEngine';

// Mock console.warn to capture validation warnings
const warnSpy = vi.spyOn(console, 'warn').mockImplementation(() => {});

describe('Viewport Controls NaN Validation Regression', () => {
  beforeEach(() => {
    warnSpy.mockClear();
  });

  function createTestControls() {
    // Create partial mock engine matching the interface used by useViewportControls
    // Only include methods actually used by the composable
    const mockEngine: Pick<LatticeEngine, "setViewportTransform" | "getCameraController" | "resetCameraToDefault"> = {
      setViewportTransform: vi.fn(),
      getCameraController: () => ({
        setZoom: vi.fn(),
        setPan: vi.fn(),
      }),
      resetCameraToDefault: vi.fn(),
    };

    return useViewportControls({
      engine: shallowRef(mockEngine as LatticeEngine),
      compositionWidth: ref(1920),
      compositionHeight: ref(1080),
      canvasWidth: ref(800),
      canvasHeight: ref(600),
    });
  }

  describe('setZoom() validation', () => {
    /**
     * Original bug: setZoom(NaN) would set zoom.value = NaN
     * Fix: Reject with warning, preserve previous valid state
     */
    test('rejects NaN zoom value', () => {
      const controls = createTestControls();
      const initialZoom = controls.zoom.value;

      controls.setZoom(NaN);

      // Zoom should remain unchanged
      expect(controls.zoom.value).toBe(initialZoom);
      expect(warnSpy).toHaveBeenCalledWith(
        expect.stringContaining('Invalid zoom value')
      );
    });

    test('rejects Infinity zoom value', () => {
      const controls = createTestControls();
      const initialZoom = controls.zoom.value;

      controls.setZoom(Infinity);

      expect(controls.zoom.value).toBe(initialZoom);
      expect(warnSpy).toHaveBeenCalled();
    });

    test('rejects -Infinity zoom value', () => {
      const controls = createTestControls();
      const initialZoom = controls.zoom.value;

      controls.setZoom(-Infinity);

      expect(controls.zoom.value).toBe(initialZoom);
      expect(warnSpy).toHaveBeenCalled();
    });

    test('rejects zero zoom value', () => {
      const controls = createTestControls();
      const initialZoom = controls.zoom.value;

      controls.setZoom(0);

      expect(controls.zoom.value).toBe(initialZoom);
      expect(warnSpy).toHaveBeenCalled();
    });

    test('rejects negative zoom value', () => {
      const controls = createTestControls();
      const initialZoom = controls.zoom.value;

      controls.setZoom(-1);

      expect(controls.zoom.value).toBe(initialZoom);
      expect(warnSpy).toHaveBeenCalled();
    });

    test('accepts valid positive zoom values', () => {
      const controls = createTestControls();

      controls.setZoom(2);
      expect(controls.zoom.value).toBe(2);
      expect(warnSpy).not.toHaveBeenCalled();

      controls.setZoom(0.5);
      expect(controls.zoom.value).toBe(0.5);
      expect(warnSpy).not.toHaveBeenCalled();
    });

    test('clamps zoom to valid range [0.1, 10]', () => {
      const controls = createTestControls();

      // Below minimum should clamp to 0.1
      controls.setZoom(0.001);
      expect(controls.zoom.value).toBe(0.1);

      // Above maximum should clamp to 10
      controls.setZoom(100);
      expect(controls.zoom.value).toBe(10);
    });
  });

  describe('screenToScene() coordinate conversion', () => {
    /**
     * Original bug: Division by zero if viewportTransform scale was 0 or NaN
     * Fix: Guard against invalid scale values, return (0, 0) with warning
     */
    test('handles zero scaleX in viewportTransform', () => {
      const controls = createTestControls();

      // Corrupt the viewport transform with zero scale
      controls.viewportTransform.value = [0, 0, 0, 1, 0, 0];

      const result = controls.screenToScene(100, 100);

      // Should return safe fallback instead of Infinity/NaN
      expect(Number.isFinite(result.x)).toBe(true);
      expect(Number.isFinite(result.y)).toBe(true);
      expect(warnSpy).toHaveBeenCalledWith(
        expect.stringContaining('Invalid scaleX')
      );
    });

    test('handles zero scaleY in viewportTransform', () => {
      const controls = createTestControls();

      controls.viewportTransform.value = [1, 0, 0, 0, 0, 0];

      const result = controls.screenToScene(100, 100);

      expect(Number.isFinite(result.x)).toBe(true);
      expect(Number.isFinite(result.y)).toBe(true);
      expect(warnSpy).toHaveBeenCalledWith(
        expect.stringContaining('Invalid scaleY')
      );
    });

    test('handles NaN scale values in viewportTransform', () => {
      const controls = createTestControls();

      controls.viewportTransform.value = [NaN, 0, 0, 1, 0, 0];

      const result = controls.screenToScene(100, 100);

      expect(Number.isFinite(result.x)).toBe(true);
      expect(result.x).toBe(0);
      expect(warnSpy).toHaveBeenCalled();
    });

    test('handles NaN pan offset values', () => {
      const controls = createTestControls();

      // Valid scale but NaN pan offsets
      controls.viewportTransform.value = [1, 0, 0, 1, NaN, NaN];

      const result = controls.screenToScene(100, 100);

      // Should use 0 for pan offsets and produce valid result
      expect(Number.isFinite(result.x)).toBe(true);
      expect(Number.isFinite(result.y)).toBe(true);
      // With pan = 0 and scale = 1, screen coords equal scene coords
      expect(result.x).toBe(100);
      expect(result.y).toBe(100);
    });

    test('correctly converts screen coordinates with valid transform', () => {
      const controls = createTestControls();

      // Set zoom = 2, pan = (100, 50)
      controls.viewportTransform.value = [2, 0, 0, 2, 100, 50];

      const result = controls.screenToScene(200, 150);

      // scene = (screen - pan) / scale
      // x = (200 - 100) / 2 = 50
      // y = (150 - 50) / 2 = 50
      expect(result.x).toBe(50);
      expect(result.y).toBe(50);
      expect(warnSpy).not.toHaveBeenCalled();
    });
  });

  describe('zoomIn/zoomOut operations', () => {
    test('zoomIn increases zoom by 20%', () => {
      const controls = createTestControls();
      controls.setZoom(1);

      controls.zoomIn();

      expect(controls.zoom.value).toBeCloseTo(1.2);
    });

    test('zoomOut decreases zoom by 20%', () => {
      const controls = createTestControls();
      controls.setZoom(1);

      controls.zoomOut();

      expect(controls.zoom.value).toBeCloseTo(0.8);
    });

    test('zoomIn respects maximum zoom limit', () => {
      const controls = createTestControls();
      controls.setZoom(10);

      controls.zoomIn();

      // Should not exceed max zoom of 10
      expect(controls.zoom.value).toBe(10);
    });

    test('zoomOut respects minimum zoom limit', () => {
      const controls = createTestControls();
      controls.setZoom(0.1);

      controls.zoomOut();

      // Should not go below min zoom of 0.1
      expect(controls.zoom.value).toBe(0.1);
    });
  });
});
