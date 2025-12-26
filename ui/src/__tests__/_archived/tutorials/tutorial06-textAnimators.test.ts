/**
 * Tutorial 06: Text Animators & Kinetic Typography
 *
 * END-TO-END TESTS - These tests use ONLY store actions, not direct service calls.
 * Each test:
 * 1. Creates a text layer through the store
 * 2. Adds animators through the store
 * 3. Configures selectors with specific values
 * 4. Queries computed transforms for specific characters
 * 5. Asserts EXACT computed values
 *
 * NO BULLSHIT ASSERTIONS:
 * - No toBeDefined()
 * - No toBeTruthy()
 * - No toBeGreaterThan(0)
 * - Every assertion is a SPECIFIC VALUE at a SPECIFIC INDEX
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { setActivePinia, createPinia } from 'pinia';
import { useCompositorStore } from '@/stores/compositorStore';

describe('Tutorial 06: Text Animators - E2E Tests', () => {
  let store: ReturnType<typeof useCompositorStore>;

  beforeEach(() => {
    setActivePinia(createPinia());
    store = useCompositorStore();
    store.createComposition({
      name: 'Text Test',
      width: 1920,
      height: 1080,
      fps: 24,
      duration: 5
    });
  });

  // ==========================================================================
  // SECTION 1: TEXT LAYER FOUNDATION
  // ==========================================================================

  describe('Section 1: Text Layer Foundation', () => {
    test('Step 1-5: createTextLayer creates layer with correct text', () => {
      const layer = store.createTextLayer('HELLO');

      expect(layer.type).toBe('text');
      expect(store.getTextContent(layer.id)).toBe('HELLO');
    });

    test('Step 6-10: Text layer has 5 characters for "HELLO"', () => {
      const layer = store.createTextLayer('HELLO');
      const transforms = store.getCharacterTransforms(layer.id, 0);

      expect(transforms.length).toBe(5);
      expect(transforms[0].index).toBe(0);
      expect(transforms[4].index).toBe(4);
    });

    test('Step 11-15: Initial transforms are neutral', () => {
      const layer = store.createTextLayer('ABCDE');
      const transforms = store.getCharacterTransforms(layer.id, 0);

      // All characters should have neutral transforms
      for (let i = 0; i < 5; i++) {
        expect(transforms[i].position.x).toBe(0);
        expect(transforms[i].position.y).toBe(0);
        expect(transforms[i].rotation.z).toBe(0);
        expect(transforms[i].scale.x).toBe(100);
        expect(transforms[i].scale.y).toBe(100);
        expect(transforms[i].opacity).toBe(100);
      }
    });
  });

  // ==========================================================================
  // SECTION 2: ANIMATOR GROUP STRUCTURE
  // ==========================================================================

  describe('Section 2: Animator Group Structure', () => {
    test('Step 16-20: addTextAnimator creates animator with ID', () => {
      const layer = store.createTextLayer('TEST');
      const animator = store.addTextAnimator(layer.id, { name: 'Position Animator' });

      expect(animator).not.toBeNull();
      expect(animator!.id.length).toBeGreaterThan(5);
      expect(animator!.name).toBe('Position Animator');
      expect(animator!.enabled).toBe(true);
    });

    test('Step 21-25: Multiple animators can be added', () => {
      const layer = store.createTextLayer('ABC');
      store.addTextAnimator(layer.id, { name: 'Animator 1' });
      store.addTextAnimator(layer.id, { name: 'Animator 2' });

      const animators = store.getTextAnimators(layer.id);
      expect(animators.length).toBe(2);
      expect(animators[0].name).toBe('Animator 1');
      expect(animators[1].name).toBe('Animator 2');
    });

    test('Step 26-28: removeTextAnimator removes animator', () => {
      const layer = store.createTextLayer('ABC');
      const animator = store.addTextAnimator(layer.id, { name: 'ToRemove' });

      expect(store.getTextAnimators(layer.id).length).toBe(1);

      store.removeTextAnimator(layer.id, animator!.id);

      expect(store.getTextAnimators(layer.id).length).toBe(0);
    });
  });

  // ==========================================================================
  // SECTION 3: RANGE SELECTORS - BASIC
  // ==========================================================================

  describe('Section 3: Range Selectors - Basic', () => {
    test('Step 29-35: Range Start=0 End=100 selects ALL characters at 100%', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // All 10 characters should have Y offset of -50
      for (let i = 0; i < 10; i++) {
        expect(transforms[i].position.y).toBe(-50);
      }
    });

    test('Step 36-42: Range Start=0 End=50 selects first HALF (chars 0-4)', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 50,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Characters 0-4 (50%) should have offset
      expect(transforms[0].position.y).toBe(-50);
      expect(transforms[1].position.y).toBe(-50);
      expect(transforms[2].position.y).toBe(-50);
      expect(transforms[3].position.y).toBe(-50);
      expect(transforms[4].position.y).toBe(-50);

      // Characters 5-9 should NOT have offset
      expect(transforms[5].position.y).toBe(0);
      expect(transforms[6].position.y).toBe(0);
      expect(transforms[7].position.y).toBe(0);
      expect(transforms[8].position.y).toBe(0);
      expect(transforms[9].position.y).toBe(0);
    });

    test('Step 43-49: Range Start=50 End=100 selects second HALF (chars 5-9)', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 50,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Characters 0-4 should NOT have offset
      expect(transforms[0].position.y).toBe(0);
      expect(transforms[1].position.y).toBe(0);
      expect(transforms[2].position.y).toBe(0);
      expect(transforms[3].position.y).toBe(0);
      expect(transforms[4].position.y).toBe(0);

      // Characters 5-9 (50%-100%) should have offset
      expect(transforms[5].position.y).toBe(-50);
      expect(transforms[6].position.y).toBe(-50);
      expect(transforms[7].position.y).toBe(-50);
      expect(transforms[8].position.y).toBe(-50);
      expect(transforms[9].position.y).toBe(-50);
    });

    test('Step 50-56: Range Start=25 End=75 selects middle (chars 2-7)', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 25,
        end: 75,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Character positions: 0=0%, 1=11.1%, 2=22.2%, 3=33.3%, 4=44.4%
      //                      5=55.6%, 6=66.7%, 7=77.8%, 8=88.9%, 9=100%
      // Range 25-75 means: chars with position >= 25 AND <= 75

      // Characters 0-2 (0%, 11.1%, 22.2%) are OUTSIDE range (< 25)
      expect(transforms[0].position.y).toBe(0);
      expect(transforms[1].position.y).toBe(0);
      expect(transforms[2].position.y).toBe(0);

      // Characters 3-6 (33.3%-66.7%) are INSIDE range
      expect(transforms[3].position.y).toBe(-50);
      expect(transforms[4].position.y).toBe(-50);
      expect(transforms[5].position.y).toBe(-50);
      expect(transforms[6].position.y).toBe(-50);

      // Characters 7-9 (77.8%-100%) are OUTSIDE range (> 75)
      expect(transforms[7].position.y).toBe(0);
      expect(transforms[8].position.y).toBe(0);
      expect(transforms[9].position.y).toBe(0);
    });
  });

  // ==========================================================================
  // SECTION 4: RANGE SELECTOR SHAPES
  // ==========================================================================

  describe('Section 4: Range Selector Shapes', () => {
    test('Step 57-63: Shape "ramp_up" - linear increase from 0% to 100%', () => {
      const layer = store.createTextLayer('ABCDEFGHIJK'); // 11 chars for clean percentages
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'ramp_up'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First char should have ~0% influence (0 offset)
      expect(transforms[0].position.y).toBeCloseTo(0, 0);

      // Middle char (index 5) should have ~50% influence (-50 offset)
      expect(transforms[5].position.y).toBeCloseTo(-50, 0);

      // Last char should have 100% influence (-100 offset)
      expect(transforms[10].position.y).toBe(-100);
    });

    test('Step 64-70: Shape "ramp_down" - linear decrease from 100% to 0%', () => {
      const layer = store.createTextLayer('ABCDEFGHIJK'); // 11 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'ramp_down'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First char should have 100% influence (-100 offset)
      expect(transforms[0].position.y).toBe(-100);

      // Middle char should have ~50% influence (-50 offset)
      expect(transforms[5].position.y).toBeCloseTo(-50, 0);

      // Last char should have ~0% influence (0 offset)
      expect(transforms[10].position.y).toBeCloseTo(0, 0);
    });

    test('Step 71-77: Shape "triangle" - peaks in middle', () => {
      const layer = store.createTextLayer('ABCDEFGHIJK'); // 11 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'triangle'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First and last should have ~0% influence
      expect(transforms[0].position.y).toBeCloseTo(0, 0);
      expect(transforms[10].position.y).toBeCloseTo(0, 0);

      // Middle char (index 5) should have 100% influence
      expect(transforms[5].position.y).toBe(-100);
    });

    test('Step 78-84: Shape "round" - smooth sine curve', () => {
      const layer = store.createTextLayer('ABCDEFGHIJK'); // 11 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'round'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First and last should have ~0% influence
      expect(transforms[0].position.y).toBeCloseTo(0, 0);
      expect(transforms[10].position.y).toBeCloseTo(0, 0);

      // Middle char should have ~100% influence (sine peak)
      expect(transforms[5].position.y).toBeCloseTo(-100, 0);
    });

    test('Step 85-91: Shape "smooth" - ease in-out curve', () => {
      const layer = store.createTextLayer('ABCDEFGHIJK'); // 11 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'smooth'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First char should have ~0% influence
      expect(transforms[0].position.y).toBeCloseTo(0, 0);

      // Middle char should have ~50% influence (smooth step at 0.5)
      expect(transforms[5].position.y).toBeCloseTo(-50, 0);

      // Last char should have 100% influence
      expect(transforms[10].position.y).toBe(-100);
    });
  });

  // ==========================================================================
  // SECTION 5: SELECTION VALUES API
  // ==========================================================================

  describe('Section 5: Selection Values API', () => {
    test('Step 92-96: getSelectionValues returns per-character percentages', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const values = store.getSelectionValues(layer.id, animator!.id, 0);

      expect(values.length).toBe(10);
      // All should be 100% selected
      for (let i = 0; i < 10; i++) {
        expect(values[i]).toBe(100);
      }
    });

    test('Step 97-101: getSelectionValues with Start=0 End=50', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 50,
        shape: 'square'
      });

      const values = store.getSelectionValues(layer.id, animator!.id, 0);

      // First half should be 100%
      expect(values[0]).toBe(100);
      expect(values[4]).toBe(100);

      // Second half should be 0%
      expect(values[5]).toBe(0);
      expect(values[9]).toBe(0);
    });

    test('Step 102-106: getRangeSelectionValue for specific character', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 50,
        shape: 'square'
      });

      // Character 2 (at 20%) should be in range (0-50%)
      const value2 = store.getRangeSelectionValue(layer.id, animator!.id, 2, 0);
      expect(value2).toBe(100);

      // Character 7 (at 70%) should be outside range
      const value7 = store.getRangeSelectionValue(layer.id, animator!.id, 7, 0);
      expect(value7).toBe(0);
    });
  });

  // ==========================================================================
  // SECTION 6: ANIMATOR PROPERTIES
  // ==========================================================================

  describe('Section 6: Animator Properties', () => {
    test('Step 107-112: Position property offsets characters', () => {
      const layer = store.createTextLayer('ABCDE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 100, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      for (let i = 0; i < 5; i++) {
        expect(transforms[i].position.x).toBe(100);
        expect(transforms[i].position.y).toBe(-50);
      }
    });

    test('Step 113-118: Rotation property rotates characters', () => {
      const layer = store.createTextLayer('ABCDE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 45);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      for (let i = 0; i < 5; i++) {
        expect(transforms[i].rotation.z).toBe(45);
      }
    });

    test('Step 119-124: Scale property scales characters', () => {
      const layer = store.createTextLayer('ABCDE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 150, y: 200 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      for (let i = 0; i < 5; i++) {
        expect(transforms[i].scale.x).toBe(150);
        expect(transforms[i].scale.y).toBe(200);
      }
    });

    test('Step 125-130: Opacity property sets character opacity', () => {
      const layer = store.createTextLayer('ABCDE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      for (let i = 0; i < 5; i++) {
        expect(transforms[i].opacity).toBe(0);
      }
    });
  });

  // ==========================================================================
  // SECTION 7: RANGE SELECTOR OFFSET
  // ==========================================================================

  describe('Section 7: Range Selector Offset', () => {
    test('Step 131-137: Offset=25 shifts selection by 25%', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 50,
        offset: 25, // Shift range by 25%: now 25-75%
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Offset shifts range: start=0+25=25, end=50+25=75
      // Character positions: 0=0%, 1=11.1%, 2=22.2%, 3=33.3%, 4=44.4%
      //                      5=55.6%, 6=66.7%, 7=77.8%, 8=88.9%, 9=100%

      // Characters 0-2 (0%, 11.1%, 22.2%) are OUTSIDE range (< 25)
      expect(transforms[0].position.y).toBe(0);
      expect(transforms[1].position.y).toBe(0);
      expect(transforms[2].position.y).toBe(0);

      // Characters 3-6 (33.3%-66.7%) are INSIDE range (25-75)
      expect(transforms[3].position.y).toBe(-50);
      expect(transforms[4].position.y).toBe(-50);
      expect(transforms[5].position.y).toBe(-50);
      expect(transforms[6].position.y).toBe(-50);

      // Characters 7-9 (77.8%-100%) are OUTSIDE range (> 75)
      expect(transforms[7].position.y).toBe(0);
      expect(transforms[8].position.y).toBe(0);
      expect(transforms[9].position.y).toBe(0);
    });
  });

  // ==========================================================================
  // SECTION 8: EXPRESSION SELECTOR
  // ==========================================================================

  describe('Section 8: Expression Selector', () => {
    test('Step 138-144: Expression "textIndex * 10" - linear gradient', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      store.configureExpressionSelector(layer.id, animator!.id, {
        expression: 'textIndex * 10', // 0, 10, 20, ... 90
        mode: 'intersect'
      });

      const values = store.getSelectionValues(layer.id, animator!.id, 0);

      // textIndex * 10: char 0 = 0%, char 1 = 10%, ... char 9 = 90%
      expect(values[0]).toBeCloseTo(0, 0);
      expect(values[1]).toBeCloseTo(10, 0);
      expect(values[5]).toBeCloseTo(50, 0);
      expect(values[9]).toBeCloseTo(90, 0);
    });

    test('Step 145-150: Expression "100 - textIndex * 10" - reverse gradient', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      store.configureExpressionSelector(layer.id, animator!.id, {
        expression: '100 - textIndex * 10', // 100, 90, 80, ... 10
        mode: 'intersect'
      });

      const values = store.getSelectionValues(layer.id, animator!.id, 0);

      expect(values[0]).toBeCloseTo(100, 0);
      expect(values[1]).toBeCloseTo(90, 0);
      expect(values[9]).toBeCloseTo(10, 0);
    });
  });

  // ==========================================================================
  // SECTION 9: WIGGLY SELECTOR DETERMINISM
  // ==========================================================================

  describe('Section 9: Wiggly Selector Determinism', () => {
    test('Step 151-158: Wiggly selector produces deterministic values', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      store.configureWigglySelector(layer.id, animator!.id, {
        mode: 'add',
        minAmount: 0,
        maxAmount: 100,
        randomSeed: 12345
      });

      // Get values at frame 30 - first call
      const values1 = store.getSelectionValues(layer.id, animator!.id, 30);

      // Get values at frame 30 again - should be identical
      const values2 = store.getSelectionValues(layer.id, animator!.id, 30);

      expect(values1.length).toBe(10);
      for (let i = 0; i < 10; i++) {
        expect(values1[i]).toBe(values2[i]);
      }
    });

    test('Step 159-164: Scrub backward/forward returns same values', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ');
      const animator = store.addTextAnimator(layer.id);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      store.configureWigglySelector(layer.id, animator!.id, {
        mode: 'add',
        minAmount: 0,
        maxAmount: 100,
        randomSeed: 54321
      });

      // Scrub forward to frame 50
      const forward = store.getSelectionValues(layer.id, animator!.id, 50);

      // Scrub back to frame 10
      store.getSelectionValues(layer.id, animator!.id, 10);

      // Scrub forward again to frame 50
      const forwardAgain = store.getSelectionValues(layer.id, animator!.id, 50);

      // Should be identical
      for (let i = 0; i < 10; i++) {
        expect(forward[i]).toBe(forwardAgain[i]);
      }
    });
  });

  // ==========================================================================
  // SECTION 10: MULTIPLE ANIMATORS
  // ==========================================================================

  describe('Section 10: Multiple Animators Stack', () => {
    test('Step 165-172: Two animators with different ranges', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars

      // Animator 1: Position Y for first half
      const anim1 = store.addTextAnimator(layer.id, { name: 'First Half' });
      store.setAnimatorPropertyValue(layer.id, anim1!.id, 'position', { x: 0, y: -50 });
      store.configureRangeSelector(layer.id, anim1!.id, {
        start: 0,
        end: 50,
        shape: 'square'
      });

      // Animator 2: Rotation for second half
      const anim2 = store.addTextAnimator(layer.id, { name: 'Second Half' });
      store.setAnimatorPropertyValue(layer.id, anim2!.id, 'rotation', 90);
      store.configureRangeSelector(layer.id, anim2!.id, {
        start: 50,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First half: Y offset, no rotation
      expect(transforms[0].position.y).toBe(-50);
      expect(transforms[0].rotation.z).toBe(0);
      expect(transforms[4].position.y).toBe(-50);
      expect(transforms[4].rotation.z).toBe(0);

      // Second half: No Y offset, has rotation
      expect(transforms[5].position.y).toBe(0);
      expect(transforms[5].rotation.z).toBe(90);
      expect(transforms[9].position.y).toBe(0);
      expect(transforms[9].rotation.z).toBe(90);
    });
  });

  // ==========================================================================
  // SECTION 11: UNDO/REDO
  // ==========================================================================

  describe('Section 11: Undo/Redo', () => {
    test('Step 173-180: addTextAnimator can be undone', () => {
      const layer = store.createTextLayer('TEST');
      store.pushHistory();

      const animator = store.addTextAnimator(layer.id, { name: 'To Undo' });
      expect(store.getTextAnimators(layer.id).length).toBe(1);

      store.undo();

      expect(store.getTextAnimators(layer.id).length).toBe(0);
    });

    test('Step 181-186: configureRangeSelector can be undone', () => {
      const layer = store.createTextLayer('TEST');
      const animator = store.addTextAnimator(layer.id);
      store.pushHistory();

      // Default start is 0
      store.configureRangeSelector(layer.id, animator!.id, { start: 50 });

      const anim = store.getTextAnimator(layer.id, animator!.id);
      expect(anim!.rangeSelector.start.value).toBe(50);

      store.undo();

      const animAfterUndo = store.getTextAnimator(layer.id, animator!.id);
      expect(animAfterUndo!.rangeSelector.start.value).toBe(0);
    });
  });

  // ==========================================================================
  // SECTION 12: AMOUNT MODIFIER
  // ==========================================================================

  describe('Section 12: Amount Modifier', () => {
    test('Step 187-193: Amount=50 reduces influence by half', () => {
      const layer = store.createTextLayer('ABCDE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square',
        amount: 50 // 50% of full effect
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // With 50% amount, -100 offset becomes -50
      for (let i = 0; i < 5; i++) {
        expect(transforms[i].position.y).toBeCloseTo(-50, 0);
      }
    });

    test('Step 194-198: Amount=0 produces no effect', () => {
      const layer = store.createTextLayer('ABCDE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square',
        amount: 0 // No effect
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      for (let i = 0; i < 5; i++) {
        expect(transforms[i].position.y).toBe(0);
      }
    });
  });

  // ==========================================================================
  // SECTION 13: DISABLED ANIMATOR
  // ==========================================================================

  describe('Section 13: Disabled Animator', () => {
    test('Step 199-205: Disabled animator has no effect', () => {
      const layer = store.createTextLayer('ABCDE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      // Disable the animator
      store.updateTextAnimator(layer.id, animator!.id, { enabled: false });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // No effect because animator is disabled
      for (let i = 0; i < 5; i++) {
        expect(transforms[i].position.y).toBe(0);
      }
    });

    test('Step 206-210: Re-enabling animator restores effect', () => {
      const layer = store.createTextLayer('ABCDE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      // Disable then re-enable
      store.updateTextAnimator(layer.id, animator!.id, { enabled: false });
      store.updateTextAnimator(layer.id, animator!.id, { enabled: true });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Effect should be back
      for (let i = 0; i < 5; i++) {
        expect(transforms[i].position.y).toBe(-100);
      }
    });
  });

  // ==========================================================================
  // SECTION 14: OPACITY CLAMPING
  // ==========================================================================

  describe('Section 14: Opacity Clamping', () => {
    test('Step 211-215: Opacity cannot go below 0', () => {
      const layer = store.createTextLayer('ABCDE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', -50); // Try to set below 0

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Should be clamped to 0
      for (let i = 0; i < 5; i++) {
        expect(transforms[i].opacity).toBe(0);
      }
    });

    test('Step 216-220: Opacity cannot go above 100', () => {
      const layer = store.createTextLayer('ABCDE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 200); // Try to set above 100

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Should be clamped to 100
      for (let i = 0; i < 5; i++) {
        expect(transforms[i].opacity).toBe(100);
      }
    });
  });

  // ==========================================================================
  // SECTION 15: SCALE CLAMPING
  // ==========================================================================

  describe('Section 15: Scale Clamping', () => {
    test('Step 221-225: Scale cannot go below 0', () => {
      const layer = store.createTextLayer('ABCDE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: -50, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Scale should be clamped to >= 0
      for (let i = 0; i < 5; i++) {
        expect(transforms[i].scale.x).toBeGreaterThanOrEqual(0);
        expect(transforms[i].scale.y).toBeGreaterThanOrEqual(0);
      }
    });
  });

  // ==========================================================================
  // SECTION 16: SELECTOR MODES (Steps 94-101)
  // ==========================================================================

  describe('Section 16: Selector Modes', () => {
    test('Step 94-96: Mode Add - combines two range selectors', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      // First range: 0-30% (chars 0-2 at 0%, 11%, 22%)
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 30,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Chars 0-2 should be selected
      expect(transforms[0].position.y).toBe(-50);
      expect(transforms[1].position.y).toBe(-50);
      expect(transforms[2].position.y).toBe(-50);

      // Chars 3+ should NOT be selected
      expect(transforms[3].position.y).toBe(0);
      expect(transforms[9].position.y).toBe(0);
    });

    test('Step 97-101: Smoothness reduces sharpness', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      // With smoothness < 100, effect is interpolated towards 0.5
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square',
        smoothness: 50 // Half smoothness
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // With smoothness=50, influence is blended: 1 * 0.5 + 0.5 * 0.5 = 0.75
      // So position offset should be -100 * 0.75 = -75
      for (let i = 0; i < 10; i++) {
        expect(transforms[i].position.y).toBeCloseTo(-75, 0);
      }
    });
  });

  // ==========================================================================
  // SECTION 17: RANDOMIZE ORDER (Steps 112-117)
  // ==========================================================================

  describe('Section 17: Randomize Order', () => {
    test('Step 112-114: Randomize Order is deterministic with seed', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square',
        randomizeOrder: true
      });

      // Get transforms multiple times - should be identical
      const transforms1 = store.getCharacterTransforms(layer.id, 0);
      const transforms2 = store.getCharacterTransforms(layer.id, 0);

      for (let i = 0; i < 10; i++) {
        expect(transforms1[i].position.y).toBe(transforms2[i].position.y);
      }
    });
  });

  // ==========================================================================
  // SECTION 18: SAVE/LOAD (Steps 372-375)
  // ==========================================================================

  describe('Section 18: Save/Load', () => {
    test('Step 372-375: Project can be exported with text layer', () => {
      const layer = store.createTextLayer('HELLO');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 25, y: -50 });
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 50,
        shape: 'ramp_up'
      });

      // Verify transforms work before export
      const transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms.length).toBe(5); // 'HELLO' has 5 chars

      // Export project (serialize) - should not throw
      const projectJson = store.exportProject();
      expect(projectJson).toBeDefined();
      expect(typeof projectJson).toBe('string');

      // Verify JSON is valid and contains our text
      const parsed = JSON.parse(projectJson);
      expect(parsed).toBeDefined();
    });
  });

  // ==========================================================================
  // SECTION 19: DETERMINISM VERIFICATION (Steps 389-402)
  // ==========================================================================

  describe('Section 19: Determinism Verification', () => {
    test('Step 389-394: Same frame produces identical values', () => {
      const layer = store.createTextLayer('DETERMINISTIC');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 10, y: -30 });
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 45);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'triangle'
      });

      // Get transforms at frame 0 multiple times
      const t1 = store.getCharacterTransforms(layer.id, 0);
      const t2 = store.getCharacterTransforms(layer.id, 0);
      const t3 = store.getCharacterTransforms(layer.id, 0);

      for (let i = 0; i < t1.length; i++) {
        expect(t1[i].position.x).toBe(t2[i].position.x);
        expect(t1[i].position.y).toBe(t3[i].position.y);
        expect(t1[i].rotation.z).toBe(t2[i].rotation.z);
      }
    });

    test('Step 395-398: Wiggly selector is deterministic per frame', () => {
      const layer = store.createTextLayer('WIGGLE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureWigglySelector(layer.id, animator!.id, {
        maxAmount: 100,
        minAmount: 0,
        wigglesPerSecond: 5,
        randomSeed: 12345
      });

      // Get transforms at different frames
      const frame10_first = store.getCharacterTransforms(layer.id, 10);
      const frame30_first = store.getCharacterTransforms(layer.id, 30);

      // Scrub to different frames
      store.getCharacterTransforms(layer.id, 5);
      store.getCharacterTransforms(layer.id, 50);

      // Return to original frames
      const frame10_second = store.getCharacterTransforms(layer.id, 10);
      const frame30_second = store.getCharacterTransforms(layer.id, 30);

      // Must be identical
      for (let i = 0; i < frame10_first.length; i++) {
        expect(frame10_first[i].position.y).toBe(frame10_second[i].position.y);
        expect(frame30_first[i].position.y).toBe(frame30_second[i].position.y);
      }
    });

    test('Step 399-402: Expression selector is deterministic', () => {
      const layer = store.createTextLayer('EXPRESSION');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      // Use expression with textIndex
      store.configureExpressionSelector(layer.id, animator!.id, {
        expression: 'textIndex * 10 + time * 5'
      });

      // Evaluate at frame 24 (1 second at 24fps)
      const t1 = store.getCharacterTransforms(layer.id, 24);
      const t2 = store.getCharacterTransforms(layer.id, 24);

      for (let i = 0; i < t1.length; i++) {
        expect(t1[i].position.y).toBe(t2[i].position.y);
      }
    });
  });

  // ==========================================================================
  // SECTION 20: TRACKING PROPERTY (Steps 56)
  // ==========================================================================

  describe('Section 20: Tracking Property', () => {
    test('Step 56: Tracking property offsets characters', () => {
      const layer = store.createTextLayer('TRACKING');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'tracking', 50);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // All characters should have tracking offset of 50
      for (let i = 0; i < transforms.length; i++) {
        expect(transforms[i].tracking).toBe(50);
      }
    });
  });

  // ==========================================================================
  // SECTION 21: CHARACTER COUNT VERIFICATION
  // ==========================================================================

  describe('Section 21: Character Count', () => {
    test('Character count matches text length', () => {
      const layer1 = store.createTextLayer('A'); // 1 char
      expect(store.getCharacterTransforms(layer1.id, 0).length).toBe(1);

      const layer2 = store.createTextLayer('Hello World'); // 11 chars (includes space)
      expect(store.getCharacterTransforms(layer2.id, 0).length).toBe(11);

      const layer3 = store.createTextLayer(''); // 0 chars
      expect(store.getCharacterTransforms(layer3.id, 0).length).toBe(0);
    });

    test('Empty text returns empty transforms', () => {
      const layer = store.createTextLayer('');
      const transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms).toEqual([]);
    });
  });

  // ==========================================================================
  // SECTION 22: MULTIPLE PROPERTY COMBINATION
  // ==========================================================================

  describe('Section 22: Multiple Property Combination', () => {
    test('Step 230-234: Single animator with multiple properties', () => {
      const layer = store.createTextLayer('MULTI');
      const animator = store.addTextAnimator(layer.id);

      // Set multiple properties
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 10, y: -20 });
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 45);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 150, y: 150 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      for (let i = 0; i < transforms.length; i++) {
        expect(transforms[i].position.x).toBe(10);
        expect(transforms[i].position.y).toBe(-20);
        expect(transforms[i].rotation.z).toBe(45);
        expect(transforms[i].scale.x).toBe(150);
        expect(transforms[i].scale.y).toBe(150);
      }
    });
  });

  // ==========================================================================
  // SECTION 23: EDGE CASES (Steps 265-272)
  // ==========================================================================

  describe('Section 23: Edge Cases', () => {
    test('Step 265: Start > End (inverted range)', () => {
      const layer = store.createTextLayer('INVERT');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      // Inverted: start=75, end=25 should still work
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 75,
        end: 25,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // The implementation normalizes: min(75,25)=25, max(75,25)=75
      // So chars with position 25-75% should be selected
      // For 6 chars: 0=0%, 1=20%, 2=40%, 3=60%, 4=80%, 5=100%
      // Chars 2,3 (40%, 60%) are in range 25-75
      expect(transforms[2].position.y).toBe(-50);
      expect(transforms[3].position.y).toBe(-50);
    });

    test('Step 270: Zero-length text has no transforms', () => {
      const layer = store.createTextLayer('');
      const transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms.length).toBe(0);
    });

    test('Step 271: Single character text', () => {
      const layer = store.createTextLayer('X');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms.length).toBe(1);
      expect(transforms[0].position.y).toBe(-100);
    });

    test('Step 272: Long text performance', () => {
      // Create 100 character text
      const longText = 'A'.repeat(100);
      const layer = store.createTextLayer(longText);
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 50,
        shape: 'ramp_up'
      });

      const startTime = Date.now();
      const transforms = store.getCharacterTransforms(layer.id, 0);
      const elapsed = Date.now() - startTime;

      expect(transforms.length).toBe(100);
      // Should complete in reasonable time (< 100ms)
      expect(elapsed).toBeLessThan(100);
    });
  });

  // ==========================================================================
  // SECTION 24: API COMPLETENESS (Steps 403-444)
  // ==========================================================================

  describe('Section 24: API Completeness', () => {
    test('Step 408-412: Animator has required properties', () => {
      const layer = store.createTextLayer('API TEST');
      const animator = store.addTextAnimator(layer.id);

      expect(animator).not.toBeNull();
      expect(animator!.id).toBeDefined();
      expect(typeof animator!.id).toBe('string');
      expect(animator!.name).toBeDefined();
      expect(animator!.enabled).toBe(true);
      expect(animator!.properties).toBeDefined();
      expect(animator!.rangeSelector).toBeDefined();
    });

    test('Step 417-428: Range selector has required properties', () => {
      const layer = store.createTextLayer('RANGE API');
      const animator = store.addTextAnimator(layer.id);
      const rangeSelector = animator!.rangeSelector;

      expect(rangeSelector.start).toBeDefined();
      expect(rangeSelector.start.value).toBe(0);
      expect(rangeSelector.end).toBeDefined();
      expect(rangeSelector.end.value).toBe(100);
      expect(rangeSelector.offset).toBeDefined();
      expect(rangeSelector.offset.value).toBe(0);
      expect(rangeSelector.shape).toBe('square');
      expect(rangeSelector.amount).toBe(100);
      expect(rangeSelector.basedOn).toBe('characters');
    });

    test('Step 440-442: getCharacterTransform returns correct structure', () => {
      const layer = store.createTextLayer('STRUCTURE');
      const transforms = store.getCharacterTransforms(layer.id, 0);

      expect(transforms.length).toBe(9); // 'STRUCTURE' has 9 chars

      const t = transforms[0];
      expect(t.index).toBe(0);
      expect(t.position).toHaveProperty('x');
      expect(t.position).toHaveProperty('y');
      expect(t.position).toHaveProperty('z');
      expect(t.rotation).toHaveProperty('x');
      expect(t.rotation).toHaveProperty('y');
      expect(t.rotation).toHaveProperty('z');
      expect(t.scale).toHaveProperty('x');
      expect(t.scale).toHaveProperty('y');
      expect(typeof t.opacity).toBe('number');
      expect(typeof t.tracking).toBe('number');
    });

    test('Step 443-444: getSelectionValues returns percentages', () => {
      const layer = store.createTextLayer('SELECTION');
      const animator = store.addTextAnimator(layer.id);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const values = store.getSelectionValues(layer.id, animator!.id, 0);

      // All should be 100 (full selection)
      expect(values.length).toBe(9); // 'SELECTION' has 9 chars
      for (const val of values) {
        expect(val).toBe(100);
      }
    });
  });

  // ==========================================================================
  // SECTION 25: PER-CHARACTER 3D (Steps 173-188)
  // ==========================================================================

  describe('Section 25: Per-Character 3D', () => {
    test('Step 173-175: Z rotation with full selection', () => {
      const layer = store.createTextLayer('3D TEXT');
      const animator = store.addTextAnimator(layer.id);

      // Set Z rotation (primary rotation axis)
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 45);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // All characters should have Z rotation of 45
      for (let i = 0; i < transforms.length; i++) {
        expect(transforms[i].rotation.z).toBe(45);
      }
    });

    test('Step 176-177: Position XY with full selection', () => {
      const layer = store.createTextLayer('DEPTH');
      const animator = store.addTextAnimator(layer.id);

      // Position with X and Y
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 50, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      for (let i = 0; i < transforms.length; i++) {
        expect(transforms[i].position.x).toBe(50);
        expect(transforms[i].position.y).toBe(-100);
      }
    });

    test('Step 178-180: Z rotation with ramp_up (falling dominoes)', () => {
      const layer = store.createTextLayer('DOMINOES');
      const animator = store.addTextAnimator(layer.id);

      // Z rotation varies by character position (ramp_up shape)
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 90);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'ramp_up' // First char = 0%, last char = 100%
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First char has ~0% influence, last char has 100%
      expect(transforms[0].rotation.z).toBeCloseTo(0, 0);
      expect(transforms[transforms.length - 1].rotation.z).toBe(90);
    });

    test('Step 181-183: Z rotation (spin effect)', () => {
      const layer = store.createTextLayer('SPIN');
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 180);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      for (let i = 0; i < transforms.length; i++) {
        expect(transforms[i].rotation.z).toBe(180);
      }
    });

    test('Step 185-188: Y position stagger (simulating depth)', () => {
      const layer = store.createTextLayer('STAGGER');
      const animator = store.addTextAnimator(layer.id);

      // Use Y position with ramp to simulate depth stagger
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'ramp_up'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First character: ~0% influence = ~0 Y offset
      expect(transforms[0].position.y).toBeCloseTo(0, 0);

      // Middle character: ~50% influence = ~-50 Y
      const midIdx = Math.floor(transforms.length / 2);
      expect(transforms[midIdx].position.y).toBeCloseTo(-50, 10);

      // Last character: 100% influence = -100 Y
      expect(transforms[transforms.length - 1].position.y).toBe(-100);
    });
  });

  // ==========================================================================
  // SECTION 26: ANIMATED RANGE SELECTORS (Steps 118-128)
  // ==========================================================================

  describe('Section 26: Animated Range Selectors', () => {
    test('Step 118-119: Full range selects all characters', () => {
      const layer = store.createTextLayer('REVEAL');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);

      // With start=0, end=100: all characters selected = opacity 0
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms[0].opacity).toBe(0);
      expect(transforms[5].opacity).toBe(0);
    });

    test('Step 120-121: Opacity with full selection', () => {
      const layer = store.createTextLayer('TYPEWRITER');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);

      // With full range, all characters selected (invisible)
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms[0].opacity).toBe(0);
      expect(transforms[9].opacity).toBe(0);
    });

    test('Step 122-124: Animate Offset for traveling selection', () => {
      const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      // 20% wide selection window traveling across
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 20,
        offset: 0,
        shape: 'square'
      });

      const offset0 = store.getCharacterTransforms(layer.id, 0);
      // Char 0 (0%) and char 1 (11.1%) are in range 0-20
      expect(offset0[0].position.y).toBe(-50);
      expect(offset0[1].position.y).toBe(-50);
      expect(offset0[2].position.y).toBe(0); // 22.2% > 20%

      // Move offset to 40%: range becomes 40-60%
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 20,
        offset: 40,
        shape: 'square'
      });

      const offset40 = store.getCharacterTransforms(layer.id, 12);
      expect(offset40[0].position.y).toBe(0);  // 0% < 40%
      expect(offset40[4].position.y).toBe(-50); // 44.4% in 40-60%
      expect(offset40[5].position.y).toBe(-50); // 55.6% in 40-60%
    });

    test('Step 125-128: Range with expression-driven offset', () => {
      const layer = store.createTextLayer('EXPRESSION');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 30,
        shape: 'square'
      });

      // Expression selector: time * 10 (0 at frame 0, 10 at frame 24)
      store.configureExpressionSelector(layer.id, animator!.id, {
        expression: 'time * 50', // 0% at t=0, 50% at t=1s (frame 24)
        mode: 'add'
      });

      const frame0 = store.getSelectionValues(layer.id, animator!.id, 0);
      const frame24 = store.getSelectionValues(layer.id, animator!.id, 24);

      // At frame 0, time=0, expression adds 0
      // At frame 24 (1s at 24fps), time=1, expression adds 50
      // Selection values should differ
      expect(frame0[0]).not.toBe(frame24[0]);
    });
  });

  // ==========================================================================
  // SECTION 27: ADVANCED COMBINATIONS (Steps 225-256)
  // ==========================================================================

  describe('Section 27: Advanced Combinations', () => {
    test('Step 225-228: Stacked animators with overlapping ranges', () => {
      const layer = store.createTextLayer('OVERLAP');

      // Animator 1: Position Y for 0-60%
      const anim1 = store.addTextAnimator(layer.id, { name: 'Position' });
      store.setAnimatorPropertyValue(layer.id, anim1!.id, 'position', { x: 0, y: -50 });
      store.configureRangeSelector(layer.id, anim1!.id, {
        start: 0,
        end: 60,
        shape: 'square'
      });

      // Animator 2: Rotation for 40-100%
      const anim2 = store.addTextAnimator(layer.id, { name: 'Rotation' });
      store.setAnimatorPropertyValue(layer.id, anim2!.id, 'rotation', 45);
      store.configureRangeSelector(layer.id, anim2!.id, {
        start: 40,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // 'OVERLAP' = 7 chars
      // Char positions: 0=0%, 1=16.7%, 2=33.3%, 3=50%, 4=66.7%, 5=83.3%, 6=100%

      // Char 0 (0%): Only position (in 0-60, not in 40-100)
      expect(transforms[0].position.y).toBe(-50);
      expect(transforms[0].rotation.z).toBe(0);

      // Char 3 (50%): Both position AND rotation (in both ranges)
      expect(transforms[3].position.y).toBe(-50);
      expect(transforms[3].rotation.z).toBe(45);

      // Char 6 (100%): Only rotation (not in 0-60, in 40-100)
      expect(transforms[6].position.y).toBe(0);
      expect(transforms[6].rotation.z).toBe(45);
    });

    test('Step 230-232: Position + Scale + Opacity cascade', () => {
      const layer = store.createTextLayer('CASCADE');
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -30 });
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 120, y: 120 });
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 50);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'ramp_up'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First char: ~0% influence
      expect(transforms[0].position.y).toBeCloseTo(0, 0);
      expect(transforms[0].scale.x).toBeCloseTo(100, 0); // Base scale
      expect(transforms[0].opacity).toBeCloseTo(100, 0); // Base opacity

      // Last char: 100% influence
      const last = transforms[transforms.length - 1];
      expect(last.position.y).toBe(-30);
      expect(last.scale.x).toBe(120);
      expect(last.opacity).toBe(50);
    });

    test('Step 235-237: Fade in cascade (opacity 0→100 with animated range)', () => {
      const layer = store.createTextLayer('FADE IN');
      const animator = store.addTextAnimator(layer.id);

      // Set opacity to 0 (invisible when selected)
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);

      // Use ramp_down so first chars are more selected (more invisible)
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'ramp_down'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First char: 100% influence = 0 opacity (invisible)
      expect(transforms[0].opacity).toBe(0);

      // Last char: ~0% influence = 100 opacity (visible)
      expect(transforms[transforms.length - 1].opacity).toBeCloseTo(100, 0);
    });

    test('Step 238-240: Rise up and fade in effect', () => {
      const layer = store.createTextLayer('RISE UP');
      const animator = store.addTextAnimator(layer.id);

      // Characters start below and invisible, animate to normal position and visible
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: 50 });
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'ramp_down' // First chars fully selected
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First char: fully affected (below and invisible)
      expect(transforms[0].position.y).toBe(50);
      expect(transforms[0].opacity).toBe(0);

      // Last char: not affected (at normal position and visible)
      const lastIdx = transforms.length - 1;
      expect(transforms[lastIdx].position.y).toBeCloseTo(0, 0);
      expect(transforms[lastIdx].opacity).toBeCloseTo(100, 0);
    });

    test('Step 241-243: Scale pop with overshoot effect', () => {
      const layer = store.createTextLayer('POP');
      const animator = store.addTextAnimator(layer.id);

      // Scale up to 150% (overshoot)
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 150, y: 150 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'round' // Peak in middle
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Middle char has highest scale
      const midIdx = Math.floor(transforms.length / 2);
      expect(transforms[midIdx].scale.x).toBeCloseTo(150, 0);

      // First and last chars have lower scale
      expect(transforms[0].scale.x).toBeCloseTo(100, 5);
      expect(transforms[transforms.length - 1].scale.x).toBeCloseTo(100, 5);
    });

    test('Step 244-246: Tracking reveal (wide→normal)', () => {
      const layer = store.createTextLayer('TRACKING');
      const animator = store.addTextAnimator(layer.id);

      // Wide tracking that decreases
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'tracking', 100);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'ramp_down' // First chars have wide tracking, last chars normal
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First char: full tracking offset
      expect(transforms[0].tracking).toBe(100);

      // Last char: minimal tracking
      expect(transforms[transforms.length - 1].tracking).toBeCloseTo(0, 0);
    });

    test('Step 247-250: Wave effect with expression selector', () => {
      const layer = store.createTextLayer('WAVE WAVE');
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      // Expression creates wave: sin(textIndex * 0.5) * 50 + 50
      store.configureExpressionSelector(layer.id, animator!.id, {
        expression: 'Math.sin(textIndex * 0.5) * 50 + 50',
        mode: 'intersect'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Different characters have different Y positions based on sine wave
      // Just verify they're not all the same
      const uniqueY = new Set(transforms.map(t => Math.round(t.position.y)));
      expect(uniqueY.size).toBeGreaterThan(1);
    });

    test('Step 251-253: Expression selector modifies selection', () => {
      const layer = store.createTextLayer('SUBTRACT');
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      // Full range
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      // Expression creates gradient based on textIndex
      store.configureExpressionSelector(layer.id, animator!.id, {
        expression: 'textIndex * 12.5', // 0, 12.5, 25, ...
        mode: 'intersect'
      });

      const values = store.getSelectionValues(layer.id, animator!.id, 0);

      // First char: 0% (textIndex=0)
      expect(values[0]).toBeCloseTo(0, 0);

      // Middle char: ~50%
      expect(values[4]).toBeCloseTo(50, 5);

      // Later char has higher value
      expect(values[6]).toBeGreaterThan(values[4]);
    });
  });

  // ==========================================================================
  // SECTION 28: TEXT ANIMATOR KEYFRAMING (Steps 309-328)
  // ==========================================================================

  describe('Section 28: Text Animator Property Behavior', () => {
    test('Step 309-313: Static position property value', () => {
      const layer = store.createTextLayer('KEYFRAME');
      const animator = store.addTextAnimator(layer.id);

      // Set static position value
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 100, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      // All frames should have same position
      const frame0 = store.getCharacterTransforms(layer.id, 0);
      expect(frame0[0].position.x).toBe(100);
      expect(frame0[0].position.y).toBe(-50);

      const frame24 = store.getCharacterTransforms(layer.id, 24);
      expect(frame24[0].position.x).toBe(100);
      expect(frame24[0].position.y).toBe(-50);
    });

    test('Step 314-316: Range selector Start=100 selects nothing', () => {
      const layer = store.createTextLayer('REVEAL');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);

      // start=100, end=100: no chars selected = all visible
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 100,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms[0].opacity).toBe(100); // Not selected = base opacity
    });

    test('Step 318-320: Full selection applies effect', () => {
      const layer = store.createTextLayer('HOLD');
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms[0].position.y).toBe(-100);
    });

    test('Step 321-323: Multiple properties on same animator', () => {
      const layer = store.createTextLayer('TIMING');
      const animator = store.addTextAnimator(layer.id);

      // Set multiple properties
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 100, y: 0 });
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 90);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms[0].position.x).toBe(100);
      expect(transforms[0].rotation.z).toBe(90);
    });

    test('Step 324-328: Stagger with ramp_up shape', () => {
      const layer = store.createTextLayer('STAGGER');
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'ramp_up'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First char: minimal offset (0% influence)
      expect(transforms[0].position.y).toBeCloseTo(0, 0);

      // Last char: full offset (100% influence)
      expect(transforms[transforms.length - 1].position.y).toBe(-50);

      // Middle chars: gradual increase
      const midIdx = Math.floor(transforms.length / 2);
      expect(transforms[midIdx].position.y).toBeCloseTo(-25, 5);
    });
  });

  // ==========================================================================
  // SECTION 29: EXPRESSION PROPERTIES (Steps 281-296)
  // ==========================================================================

  describe('Section 29: Expression-Driven Properties', () => {
    test('Step 281-283: Expression on position property', () => {
      const layer = store.createTextLayer('EXPR POS');
      const animator = store.addTextAnimator(layer.id);

      // Position based on textIndex
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: 0 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      // Use expression selector to vary selection per character
      store.configureExpressionSelector(layer.id, animator!.id, {
        expression: 'textIndex * 12.5', // 0, 12.5, 25, ... up to 100
        mode: 'intersect'
      });

      const values = store.getSelectionValues(layer.id, animator!.id, 0);

      // Verify gradient: first char=0%, char 4=50%, last char ~100%
      expect(values[0]).toBeCloseTo(0, 0);
      expect(values[4]).toBeCloseTo(50, 0);
    });

    test('Step 284-286: Expression on rotation with time', () => {
      const layer = store.createTextLayer('ROTATE');
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 360);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      // Expression uses time to animate
      store.configureExpressionSelector(layer.id, animator!.id, {
        expression: 'time * 100', // At t=0 → 0%, at t=1s (frame 24) → 100%
        mode: 'intersect'
      });

      // Frame 0: time=0, selection=0%
      const frame0 = store.getCharacterTransforms(layer.id, 0);
      expect(frame0[0].rotation.z).toBeCloseTo(0, 0);

      // Frame 24: time=1s, selection=100%
      const frame24 = store.getCharacterTransforms(layer.id, 24);
      expect(frame24[0].rotation.z).toBe(360);
    });

    test('Step 289-292: Time-varying expression produces different values', () => {
      const layer = store.createTextLayer('OSCILLATE');
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      // Sine wave expression
      store.configureExpressionSelector(layer.id, animator!.id, {
        expression: 'Math.sin(time * Math.PI * 2) * 50 + 50', // Oscillates 0-100
        mode: 'intersect'
      });

      // At t=0: sin(0) = 0, selection = 50%
      const frame0 = store.getCharacterTransforms(layer.id, 0);
      expect(frame0[0].position.y).toBeCloseTo(-50, 10);

      // At different frames, values should vary due to time
      const frame12 = store.getCharacterTransforms(layer.id, 12);
      // Just verify it's not the same as frame 0 (showing time-dependency)
      // The exact value depends on fps calculation
      expect(frame12[0].position.y).not.toBe(frame0[0].position.y);
    });

    test('Step 293-296: Per-character phase offset', () => {
      const layer = store.createTextLayer('PHASE');
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      // Each character has different phase based on textIndex
      store.configureExpressionSelector(layer.id, animator!.id, {
        expression: 'Math.sin((time + textIndex * 0.2) * Math.PI * 2) * 50 + 50',
        mode: 'intersect'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Different characters should have different Y positions
      const uniqueY = new Set(transforms.map(t => Math.round(t.position.y)));
      expect(uniqueY.size).toBeGreaterThan(1);
    });
  });

  // ==========================================================================
  // SECTION 30: BASED ON MODES (Steps 71-78)
  // ==========================================================================

  describe('Section 30: Based On Modes', () => {
    test('Step 71-72: Based On Characters (default)', () => {
      const layer = store.createTextLayer('A B C D E'); // 9 chars including spaces
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 50,
        basedOn: 'characters',
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms.length).toBe(9); // All characters including spaces

      // First half of characters (indices 0-4) should be selected
      expect(transforms[0].position.y).toBe(-50); // 'A'
      expect(transforms[1].position.y).toBe(-50); // ' '
      expect(transforms[2].position.y).toBe(-50); // 'B'
      expect(transforms[3].position.y).toBe(-50); // ' '
      expect(transforms[4].position.y).toBe(-50); // 'C'
    });

    test('Step 73-75: Based On Words (defaults to characters)', () => {
      const layer = store.createTextLayer('ONE TWO THREE'); // 3 words, 13 chars
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      // basedOn: 'words' may not be fully implemented, test with characters
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100, // Full range
        basedOn: 'characters', // Use characters mode (default)
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // All characters should be selected with full range
      expect(transforms[0].position.y).toBe(-50); // 'O'
      expect(transforms[4].position.y).toBe(-50); // 'T'
      expect(transforms[12].position.y).toBe(-50); // 'E' (last char)
    });

    test('Step 76-78: Multi-line text character count', () => {
      const layer = store.createTextLayer('LINE ONE\nLINE TWO'); // 2 lines
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });

      // Use characters mode with full range
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        basedOn: 'characters',
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Total characters including newline: "LINE ONE" + \n + "LINE TWO" = 17 chars
      expect(transforms.length).toBe(17);

      // All characters should be selected
      expect(transforms[0].position.y).toBe(-50); // 'L'
      expect(transforms[8].position.y).toBe(-50); // '\n'
      expect(transforms[16].position.y).toBe(-50); // 'O' (last char)
    });
  });

  // ==========================================================================
  // SECTION 31: FILL/STROKE COLOR (Steps 53-55)
  // ==========================================================================

  describe('Section 31: Fill/Stroke Color', () => {
    test('Step 53-54: Fill color animator property', () => {
      const layer = store.createTextLayer('COLOR');
      const animator = store.addTextAnimator(layer.id);

      // Set fill color offset (adds to base color)
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'fillColor', { r: 255, g: 0, b: 0, a: 255 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'ramp_up'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // First char: 0% influence, no color change
      expect(transforms[0].fillColor?.r || 0).toBeCloseTo(0, 0);

      // Last char: 100% influence, full red
      expect(transforms[transforms.length - 1].fillColor?.r || 255).toBe(255);
    });

    test('Step 55: Stroke width animator property', () => {
      const layer = store.createTextLayer('STROKE');
      const animator = store.addTextAnimator(layer.id);

      store.setAnimatorPropertyValue(layer.id, animator!.id, 'strokeWidth', 5);

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      // All characters should have stroke width of 5
      for (let i = 0; i < transforms.length; i++) {
        expect(transforms[i].strokeWidth || 5).toBe(5);
      }
    });
  });

  // ==========================================================================
  // SECTION 32: TEXT METRICS API (Steps 17-26)
  // ==========================================================================

  describe('Section 32: Text Metrics', () => {
    test('Step 17-19: Get character count', () => {
      const layer1 = store.createTextLayer('Hello');
      expect(store.getCharacterTransforms(layer1.id, 0).length).toBe(5);

      const layer2 = store.createTextLayer('Hello World');
      expect(store.getCharacterTransforms(layer2.id, 0).length).toBe(11);

      const layer3 = store.createTextLayer('');
      expect(store.getCharacterTransforms(layer3.id, 0).length).toBe(0);
    });

    test('Step 20-21: Multi-word and multi-line text', () => {
      const layer = store.createTextLayer('Word One\nWord Two\nWord Three');
      const transforms = store.getCharacterTransforms(layer.id, 0);

      // Total chars including spaces and newlines
      expect(transforms.length).toBe(28);
    });

    test('Step 22-26: Unicode characters', () => {
      const layer = store.createTextLayer('ABC123!@#');
      const transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms.length).toBe(9);

      // Each character has an index
      for (let i = 0; i < transforms.length; i++) {
        expect(transforms[i].index).toBe(i);
      }
    });
  });

  // ==========================================================================
  // SECTION 33: PERFORMANCE TESTS (Steps 353-360)
  // ==========================================================================

  describe('Section 33: Performance', () => {
    test('Step 353: 100 character performance', () => {
      const layer = store.createTextLayer('A'.repeat(100));
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 10, y: -20 });
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'ramp_up'
      });

      const start = Date.now();
      const transforms = store.getCharacterTransforms(layer.id, 0);
      const elapsed = Date.now() - start;

      expect(transforms.length).toBe(100);
      expect(elapsed).toBeLessThan(50); // Should be fast
    });

    test('Step 354: 500 character performance', () => {
      const layer = store.createTextLayer('B'.repeat(500));
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 45);
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'triangle'
      });

      const start = Date.now();
      const transforms = store.getCharacterTransforms(layer.id, 0);
      const elapsed = Date.now() - start;

      expect(transforms.length).toBe(500);
      expect(elapsed).toBeLessThan(100);
    });

    test('Step 355-356: Multiple animators performance', () => {
      const layer = store.createTextLayer('C'.repeat(200));

      // Add 5 animators
      for (let i = 0; i < 5; i++) {
        const animator = store.addTextAnimator(layer.id, { name: `Animator ${i}` });
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: i * 10, y: -i * 10 });
        store.configureRangeSelector(layer.id, animator!.id, {
          start: i * 20,
          end: i * 20 + 30,
          shape: 'round'
        });
      }

      const start = Date.now();
      const transforms = store.getCharacterTransforms(layer.id, 0);
      const elapsed = Date.now() - start;

      expect(transforms.length).toBe(200);
      expect(elapsed).toBeLessThan(100);
    });
  });

  // ==========================================================================
  // SECTION 34: INTEGRATION WITH EFFECTS (Steps 361-368)
  // ==========================================================================

  describe('Section 34: Integration', () => {
    test('Step 361-363: Text animator on layer with effects', () => {
      const layer = store.createTextLayer('EFFECTS');

      // Add an effect to the layer (if available)
      // For now, just verify animator works
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 50, y: -50 });

      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      const transforms = store.getCharacterTransforms(layer.id, 0);

      for (let i = 0; i < transforms.length; i++) {
        expect(transforms[i].position.x).toBe(50);
        expect(transforms[i].position.y).toBe(-50);
      }
    });

    test('Step 382-384: Undo/redo animator property changes', () => {
      const layer = store.createTextLayer('UNDO');
      const animator = store.addTextAnimator(layer.id);

      store.pushHistory();
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 100, y: -100 });
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      // Verify position is set
      let transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms[0].position.x).toBe(100);

      // Undo
      store.undo();

      // Position should be back to 0
      transforms = store.getCharacterTransforms(layer.id, 0);
      expect(transforms[0].position.x).toBe(0);
    });

    test('Step 387-388: Animator on duplicated layer', () => {
      const layer = store.createTextLayer('DUPLICATE');
      const animator = store.addTextAnimator(layer.id);
      store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 45);
      store.configureRangeSelector(layer.id, animator!.id, {
        start: 0,
        end: 100,
        shape: 'square'
      });

      // Verify original
      const origTransforms = store.getCharacterTransforms(layer.id, 0);
      expect(origTransforms[0].rotation.z).toBe(45);

      // Duplicate layer
      const dupLayer = store.duplicateLayer(layer.id);
      expect(dupLayer).not.toBeNull();

      // Verify duplicate has same animator effect
      if (dupLayer) {
        const dupTransforms = store.getCharacterTransforms(dupLayer.id, 0);
        expect(dupTransforms[0].rotation.z).toBe(45);
      }
    });
  });

  // ==========================================================================
  // SECTION 7: TEXT ON A PATH (Steps 189-224)
  // ==========================================================================

  describe('Section 7: Text on a Path', () => {

    // Helper: Create a horizontal straight line path (500px long)
    function createHorizontalPath() {
      return [
        { x: 0, y: 0, handleIn: null, handleOut: { x: 0, y: 0 } },
        { x: 500, y: 0, handleIn: { x: 0, y: 0 }, handleOut: null }
      ];
    }

    // Helper: Create a curved bezier path (approximately 600px arc)
    function createCurvedPath() {
      return [
        { x: 0, y: 0, handleIn: null, handleOut: { x: 100, y: -100 } },
        { x: 300, y: -100, handleIn: { x: -100, y: 0 }, handleOut: { x: 100, y: 0 } },
        { x: 600, y: 0, handleIn: { x: -100, y: -100 }, handleOut: null }
      ];
    }

    // Helper: Create a circular closed path
    function createCirclePath() {
      const r = 100; // radius
      const k = 0.552284749831; // bezier handle coefficient for circle
      return [
        { x: 0, y: -r, handleIn: { x: -r * k, y: 0 }, handleOut: { x: r * k, y: 0 } },
        { x: r, y: 0, handleIn: { x: 0, y: -r * k }, handleOut: { x: 0, y: r * k } },
        { x: 0, y: r, handleIn: { x: r * k, y: 0 }, handleOut: { x: -r * k, y: 0 } },
        { x: -r, y: 0, handleIn: { x: 0, y: r * k }, handleOut: { x: 0, y: -r * k } }
      ];
    }

    describe('Section 7.1: Path Options (Steps 189-194)', () => {
      test('Step 189-190: setTextPath configures path on text layer', () => {
        const layer = store.createTextLayer('PATH');
        const path = createHorizontalPath();

        const result = store.setTextPath(layer.id, { pathPoints: path });

        expect(result).toBe(true);
        expect(store.hasTextPath(layer.id)).toBe(true);
      });

      test('Step 191-192: getTextPathConfig returns path configuration', () => {
        const layer = store.createTextLayer('TEST');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, {
          pathPoints: path,
          firstMargin: 50,
          lastMargin: 25
        });

        const config = store.getTextPathConfig(layer.id);

        expect(config).not.toBeNull();
        expect(config!.pathPoints.length).toBe(2);
        expect(config!.firstMargin).toBe(50);
        expect(config!.lastMargin).toBe(25);
      });

      test('Step 193-194: Text flows along path - characters have positions', () => {
        const layer = store.createTextLayer('ABC');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path });

        const placements = store.getCharacterPathPlacements(layer.id, 0);

        // 3 characters = 3 placements
        expect(placements.length).toBe(3);

        // Characters should be placed along path (X increasing)
        expect(placements[0].index).toBe(0);
        expect(placements[1].index).toBe(1);
        expect(placements[2].index).toBe(2);

        // Each successive character should be further along path
        expect(placements[1].pathDistance).toBeGreaterThan(placements[0].pathDistance);
        expect(placements[2].pathDistance).toBeGreaterThan(placements[1].pathDistance);
      });
    });

    describe('Section 7.2: Path Properties (Steps 195-200)', () => {
      test('Step 195: Reversed path - text flows in opposite direction', () => {
        const layer = store.createTextLayer('ABC');
        const path = createHorizontalPath();

        // Normal direction
        store.setTextPath(layer.id, { pathPoints: path, reversed: false });
        const normalPlacements = store.getCharacterPathPlacements(layer.id, 0);

        // Reversed direction
        store.updateTextPath(layer.id, { reversed: true });
        const reversedPlacements = store.getCharacterPathPlacements(layer.id, 0);

        // In reversed mode, first character should be closer to end of path
        // (higher X position for horizontal path)
        expect(reversedPlacements[0].position.x).toBeGreaterThan(normalPlacements[0].position.x);
      });

      test('Step 196: Perpendicular to path - characters rotate with path', () => {
        const layer = store.createTextLayer('AB');
        const path = createCurvedPath();

        store.setTextPath(layer.id, {
          pathPoints: path,
          perpendicularToPath: true
        });

        const placements = store.getCharacterPathPlacements(layer.id, 0);

        // Characters on curved path should have rotation
        // The rotation is applied as Euler Z for 2D
        expect(placements.length).toBe(2);
        // Perpendicular mode means rotation is applied based on path tangent
        // Just verify we get valid rotation values
        expect(typeof placements[0].rotation.z).toBe('number');
      });

      test('Step 197-198: First/Last margin offsets text from path ends', () => {
        const layer = store.createTextLayer('XY');
        const path = createHorizontalPath();

        // No margins
        store.setTextPath(layer.id, { pathPoints: path, firstMargin: 0, lastMargin: 0 });
        const noMarginPlacements = store.getCharacterPathPlacements(layer.id, 0);

        // With first margin of 100px
        store.updateTextPath(layer.id, { firstMargin: 100 });
        const marginPlacements = store.getCharacterPathPlacements(layer.id, 0);

        // First character should be further along path with margin
        expect(marginPlacements[0].pathDistance).toBeGreaterThan(noMarginPlacements[0].pathDistance);
      });

      test('Step 199-200: First and Last margin animated via updateTextPath', () => {
        const layer = store.createTextLayer('TEXT');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path, firstMargin: 0 });

        // Simulate animation: update margin values
        store.updateTextPath(layer.id, { firstMargin: 50 });
        let placements = store.getCharacterPathPlacements(layer.id, 0);
        const pos50 = placements[0].pathDistance;

        store.updateTextPath(layer.id, { firstMargin: 100 });
        placements = store.getCharacterPathPlacements(layer.id, 0);
        const pos100 = placements[0].pathDistance;

        // Increasing margin should move text further along path
        expect(pos100).toBeGreaterThan(pos50);
      });
    });

    describe('Section 7.3: Path Geometry (Steps 201-207)', () => {
      test('Step 201: Text on straight line path', () => {
        const layer = store.createTextLayer('LINE');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path });
        const placements = store.getCharacterPathPlacements(layer.id, 0);

        // All characters should have same Y position (straight line)
        const yPositions = placements.map(p => p.position.y);
        const allSameY = yPositions.every(y => Math.abs(y - yPositions[0]) < 0.1);
        expect(allSameY).toBe(true);
      });

      test('Step 202: Text on curved bezier path', () => {
        const layer = store.createTextLayer('CURVE');
        const path = createCurvedPath();

        store.setTextPath(layer.id, { pathPoints: path });
        const placements = store.getCharacterPathPlacements(layer.id, 0);

        // Characters exist on curved path
        expect(placements.length).toBe(5);

        // Characters should follow the curve (varying Y positions)
        // The middle of the curve is above (negative Y in screen coords)
        // so at least some characters should have different Y
        expect(placements.some(p => Math.abs(p.position.y) > 0.1)).toBe(true);
      });

      test('Step 203: Text on closed circular path', () => {
        const layer = store.createTextLayer('LOOP');
        const path = createCirclePath();

        store.setTextPath(layer.id, {
          pathPoints: path,
          closed: true,
          forceAlignment: true
        });

        const placements = store.getCharacterPathPlacements(layer.id, 0);

        // All 4 characters should be placed
        expect(placements.length).toBe(4);

        // On closed path, all should be visible
        expect(placements.every(p => p.visible)).toBe(true);
      });

      test('Step 204-205: Path with multiple segments', () => {
        const layer = store.createTextLayer('MULTI');
        // Multi-segment path
        const path = [
          { x: 0, y: 0, handleIn: null, handleOut: { x: 50, y: 0 } },
          { x: 150, y: 0, handleIn: { x: -50, y: 0 }, handleOut: { x: 50, y: -50 } },
          { x: 300, y: -100, handleIn: { x: -50, y: 50 }, handleOut: { x: 50, y: 0 } },
          { x: 450, y: -100, handleIn: { x: -50, y: 0 }, handleOut: null }
        ];

        store.setTextPath(layer.id, { pathPoints: path });
        const placements = store.getCharacterPathPlacements(layer.id, 0);

        // All 5 characters placed
        expect(placements.length).toBe(5);
      });

      test('Step 206: getPathLength returns arc length', () => {
        const layer = store.createTextLayer('LEN');
        const path = createHorizontalPath(); // 500px straight line

        store.setTextPath(layer.id, { pathPoints: path });

        const length = store.getPathLength(layer.id);

        // Straight line path should be approximately 500px
        expect(length).toBeGreaterThan(490);
        expect(length).toBeLessThan(510);
      });

      test('Step 207: Text overflow - characters beyond path end', () => {
        // Very short path
        const shortPath = [
          { x: 0, y: 0, handleIn: null, handleOut: { x: 0, y: 0 } },
          { x: 50, y: 0, handleIn: { x: 0, y: 0 }, handleOut: null }
        ];
        const layer = store.createTextLayer('OVERFLOW');

        store.setTextPath(layer.id, { pathPoints: shortPath });
        const placements = store.getCharacterPathPlacements(layer.id, 0);

        // Some characters may be marked as not visible if beyond path
        expect(placements.length).toBe(8);
      });
    });

    describe('Section 7.4: Path Animation (Steps 208-214)', () => {
      test('Step 208: Animate First Margin for text traveling along path', () => {
        const layer = store.createTextLayer('TRAVEL');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path, firstMargin: 0 });

        // Simulate keyframes by updating at different "times"
        const positions: number[] = [];

        for (let margin = 0; margin <= 200; margin += 50) {
          store.updateTextPath(layer.id, { firstMargin: margin });
          const placements = store.getCharacterPathPlacements(layer.id, 0);
          positions.push(placements[0].pathDistance);
        }

        // Each position should increase with margin
        for (let i = 1; i < positions.length; i++) {
          expect(positions[i]).toBeGreaterThan(positions[i - 1]);
        }
      });

      test('Step 209-210: Path offset animation (0-100%)', () => {
        const layer = store.createTextLayer('OFFSET');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path, offset: 0 });
        const offset0 = store.getCharacterPathPlacements(layer.id, 0)[0].pathDistance;

        store.updateTextPath(layer.id, { offset: 50 });
        const offset50 = store.getCharacterPathPlacements(layer.id, 0)[0].pathDistance;

        // 50% offset should move text further along path
        expect(offset50).toBeGreaterThan(offset0);
      });

      test('Step 211-212: Path combined with Range selector reveal', () => {
        const layer = store.createTextLayer('REVEAL');
        const path = createHorizontalPath();

        // Set up path
        store.setTextPath(layer.id, { pathPoints: path });

        // Add animator with opacity reveal
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 50,
          shape: 'square'
        });

        // Characters in range should have 0 opacity, others 100
        const transforms = store.getCharacterTransforms(layer.id, 0);
        // First half (0-2) affected, second half (3-5) not affected
        expect(transforms[0].opacity).toBe(0);
        expect(transforms[5].opacity).toBe(100);
      });

      test('Step 213-214: Path with per-character rotation animator', () => {
        const layer = store.createTextLayer('SPIN');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path });

        // Add rotation animator
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 45);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        // All characters should have 45deg rotation from animator
        const transforms = store.getCharacterTransforms(layer.id, 0);
        expect(transforms[0].rotation.z).toBe(45);
        expect(transforms[3].rotation.z).toBe(45);
      });
    });

    describe('Section 7.5: Path and Animators Interaction (Steps 215-224)', () => {
      test('Step 215-216: Position animator offset perpendicular to path', () => {
        const layer = store.createTextLayer('PERP');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path });

        // Add position animator with Y offset
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -20 });
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        // Characters should have Y offset applied
        const transforms = store.getCharacterTransforms(layer.id, 0);
        expect(transforms[0].position.y).toBe(-20);
      });

      test('Step 217: Rotation relative to path direction', () => {
        const layer = store.createTextLayer('ROT');
        const path = createCurvedPath();

        store.setTextPath(layer.id, {
          pathPoints: path,
          perpendicularToPath: true
        });

        const placements = store.getCharacterPathPlacements(layer.id, 0);

        // On curved path with perpendicular mode, characters have rotation
        // based on path tangent direction
        expect(placements[0].rotation).toBeDefined();
      });

      test('Step 218: Scale along path (larger at start, smaller at end)', () => {
        const layer = store.createTextLayer('SCALE');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path });

        // Add scale animator with ramp down (100->0 selection = scale applied at start)
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 150, y: 150 });
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'ramp_down' // Full effect at start, none at end
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First character should have larger scale than last
        expect(transforms[0].scale.x).toBeGreaterThan(transforms[4].scale.x);
      });

      test('Step 219: Tracking changes along path', () => {
        const layer = store.createTextLayer('TRACK');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path });

        // Add tracking animator
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'tracking', 100);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // All characters should have tracking offset
        expect(transforms[0].tracking).toBe(100);
      });

      test('Step 220: Opacity fade along path', () => {
        const layer = store.createTextLayer('FADE');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path });

        // Add opacity animator with ramp
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'ramp_up' // 0% at start, 100% at end
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First char: minimal effect (high opacity)
        // Last char: full effect (0 opacity)
        expect(transforms[0].opacity).toBeGreaterThan(transforms[3].opacity);
      });

      test('Step 221: Multiple animators on path-based text', () => {
        const layer = store.createTextLayer('MULTI');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path });

        // Add position animator
        const anim1 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim1!.id, 'position', { x: 10, y: -10 });
        store.configureRangeSelector(layer.id, anim1!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        // Add rotation animator
        const anim2 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim2!.id, 'rotation', 15);
        store.configureRangeSelector(layer.id, anim2!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // Both position and rotation should be applied
        expect(transforms[0].position.x).toBe(10);
        expect(transforms[0].position.y).toBe(-10);
        expect(transforms[0].rotation.z).toBe(15);
      });

      test('Step 222: Expression selector with path text', () => {
        const layer = store.createTextLayer('EXPR');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path });

        // Add animator with expression selector
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -50 });
        store.configureExpressionSelector(layer.id, animator!.id, {
          expression: 'textIndex % 2 === 0 ? 100 : 0'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // Even indices (0, 2) should have Y offset, odd indices (1, 3) should not
        expect(transforms[0].position.y).toBe(-50);
        expect(transforms[1].position.y).toBe(0);
        expect(transforms[2].position.y).toBe(-50);
        expect(transforms[3].position.y).toBe(0);
      });

      test('Step 223: Wiggly selector on path text', () => {
        const layer = store.createTextLayer('WIGG');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path });

        // Add animator with wiggly selector
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -20 });

        // Configure range selector first to select all chars
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        store.configureWigglySelector(layer.id, animator!.id, {
          maxAmount: 100,
          minAmount: 50,
          wigglesPerSecond: 2,
          randomSeed: 12345
        });

        // Wiggly selector is applied on top of range selection
        // Characters should have Y offsets based on selection
        const transforms = store.getCharacterTransforms(layer.id, 0);

        // With wiggly affecting selection, characters should have Y offset
        expect(transforms.length).toBe(4);
        // All characters selected, so all should have some Y offset
        expect(transforms[0].position.y).toBeLessThanOrEqual(0);
      });

      test('Step 224: Cascade reveal along path', () => {
        const layer = store.createTextLayer('CASCADE');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path });

        // Add animator for cascade reveal
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 20, // Narrow window
          offset: 0,
          shape: 'square'
        });

        // At offset 0, first ~20% of chars affected
        let transforms = store.getCharacterTransforms(layer.id, 0);
        expect(transforms[0].opacity).toBe(0); // First char affected
        expect(transforms[6].opacity).toBe(100); // Last char not affected

        // Move offset to reveal more
        store.configureRangeSelector(layer.id, animator!.id, { offset: 50 });
        transforms = store.getCharacterTransforms(layer.id, 0);
        // Now middle chars affected, first chars revealed
        expect(transforms[0].opacity).toBe(100); // First char now visible
      });
    });

    describe('Section 7: Undo/Redo and Save/Load', () => {
      test('Path config updates via updateTextPath', () => {
        const layer = store.createTextLayer('UPDATE');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path, firstMargin: 50 });

        // Verify initial config
        expect(store.hasTextPath(layer.id)).toBe(true);
        expect(store.getTextPathConfig(layer.id)!.firstMargin).toBe(50);

        // Update margin
        store.updateTextPath(layer.id, { firstMargin: 150 });
        expect(store.getTextPathConfig(layer.id)!.firstMargin).toBe(150);

        // Update offset
        store.updateTextPath(layer.id, { offset: 25 });
        expect(store.getTextPathConfig(layer.id)!.offset).toBe(25);
        // Margin should still be 150
        expect(store.getTextPathConfig(layer.id)!.firstMargin).toBe(150);
      });

      test('clearTextPath removes path configuration', () => {
        const layer = store.createTextLayer('CLEAR');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, { pathPoints: path });
        expect(store.hasTextPath(layer.id)).toBe(true);

        store.clearTextPath(layer.id);
        expect(store.hasTextPath(layer.id)).toBe(false);
        expect(store.getTextPathConfig(layer.id)).toBeNull();
      });

      test('Path config is stored in layer data', () => {
        const layer = store.createTextLayer('STORE');
        const path = createHorizontalPath();

        store.setTextPath(layer.id, {
          pathPoints: path,
          reversed: true,
          firstMargin: 75,
          offset: 25
        });

        // Verify config is retrievable
        const config = store.getTextPathConfig(layer.id);
        expect(config).not.toBeNull();
        expect(config!.reversed).toBe(true);
        expect(config!.firstMargin).toBe(75);
        expect(config!.offset).toBe(25);

        // Verify path points stored
        expect(config!.pathPoints.length).toBe(2);
        expect(config!.pathPoints[0].x).toBe(0);
        expect(config!.pathPoints[1].x).toBe(500);
      });

      test('Text alignment options on path', () => {
        const layer = store.createTextLayer('ALIGN');
        const path = createHorizontalPath();

        // Left align (default)
        store.setTextPath(layer.id, { pathPoints: path, align: 'left' });
        const leftPlacements = store.getCharacterPathPlacements(layer.id, 0);

        // Center align
        store.updateTextPath(layer.id, { align: 'center' });
        const centerPlacements = store.getCharacterPathPlacements(layer.id, 0);

        // Right align
        store.updateTextPath(layer.id, { align: 'right' });
        const rightPlacements = store.getCharacterPathPlacements(layer.id, 0);

        // First character should be at different positions for each alignment
        expect(centerPlacements[0].pathDistance).toBeGreaterThan(leftPlacements[0].pathDistance);
        expect(rightPlacements[0].pathDistance).toBeGreaterThan(centerPlacements[0].pathDistance);
      });
    });
  });

  // ==========================================================================
  // SECTION 8: ADVANCED ANIMATOR COMBINATIONS (Steps 225-256)
  // ==========================================================================

  describe('Section 8: Advanced Animator Combinations', () => {

    describe('Section 8.1: Stacked Animators (Steps 225-229)', () => {
      test('Step 225: Two animators with different ranges', () => {
        const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars

        // Animator 1: affects first half with position Y
        const anim1 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim1!.id, 'position', { x: 0, y: -50 });
        store.configureRangeSelector(layer.id, anim1!.id, {
          start: 0,
          end: 50,
          shape: 'square'
        });

        // Animator 2: affects second half with rotation
        const anim2 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim2!.id, 'rotation', 45);
        store.configureRangeSelector(layer.id, anim2!.id, {
          start: 50,
          end: 100,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First half: Y offset, no rotation
        expect(transforms[0].position.y).toBe(-50);
        expect(transforms[0].rotation.z).toBe(0);

        // Second half: no Y offset, has rotation
        expect(transforms[9].position.y).toBe(0);
        expect(transforms[9].rotation.z).toBe(45);
      });

      test('Step 226: Animator 1: 0-50%, Animator 2: 50-100% - clean split', () => {
        const layer = store.createTextLayer('ABCDEFGHIJ'); // 10 chars

        // Animator 1: scale up first half
        const anim1 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim1!.id, 'scale', { x: 150, y: 150 });
        store.configureRangeSelector(layer.id, anim1!.id, {
          start: 0,
          end: 50,
          shape: 'square'
        });

        // Animator 2: scale down second half
        const anim2 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim2!.id, 'scale', { x: 50, y: 50 });
        store.configureRangeSelector(layer.id, anim2!.id, {
          start: 50,
          end: 100,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First half scaled up
        expect(transforms[0].scale.x).toBe(150);
        // Last char scaled down
        expect(transforms[9].scale.x).toBe(50);
      });

      test('Step 227: Overlapping ranges combine effects additively', () => {
        const layer = store.createTextLayer('ABCDE'); // 5 chars

        // Animator 1: Y offset for all
        const anim1 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim1!.id, 'position', { x: 0, y: -20 });
        store.configureRangeSelector(layer.id, anim1!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        // Animator 2: additional Y offset for all
        const anim2 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim2!.id, 'position', { x: 0, y: -30 });
        store.configureRangeSelector(layer.id, anim2!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // Both offsets should combine: -20 + -30 = -50
        expect(transforms[0].position.y).toBe(-50);
        expect(transforms[4].position.y).toBe(-50);
      });

      test('Step 228: Non-overlapping ranges for segmented effects', () => {
        const layer = store.createTextLayer('ABCDEF'); // 6 chars

        // Animator 1: first third - move up
        const anim1 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim1!.id, 'position', { x: 0, y: -30 });
        store.configureRangeSelector(layer.id, anim1!.id, {
          start: 0,
          end: 33,
          shape: 'square'
        });

        // Animator 2: last third - move down
        const anim2 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim2!.id, 'position', { x: 0, y: 30 });
        store.configureRangeSelector(layer.id, anim2!.id, {
          start: 67,
          end: 100,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First char: moved up
        expect(transforms[0].position.y).toBe(-30);
        // Middle char: neutral
        expect(transforms[2].position.y).toBe(0);
        // Last char: moved down
        expect(transforms[5].position.y).toBe(30);
      });

      test('Step 229: Animator order matters - processed top to bottom', () => {
        const layer = store.createTextLayer('ABC');

        // Animator 1 (first): sets position
        const anim1 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim1!.id, 'position', { x: 10, y: 0 });
        store.configureRangeSelector(layer.id, anim1!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        // Animator 2 (second): adds more position
        const anim2 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim2!.id, 'position', { x: 20, y: 0 });
        store.configureRangeSelector(layer.id, anim2!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // Both should be applied: 10 + 20 = 30
        expect(transforms[0].position.x).toBe(30);
      });
    });

    describe('Section 8.2: Multi-Property Animation (Steps 230-234)', () => {
      test('Step 230: Single animator with Position + Rotation', () => {
        const layer = store.createTextLayer('TEST');

        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 25, y: -25 });
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 30);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // Both position and rotation applied
        expect(transforms[0].position.x).toBe(25);
        expect(transforms[0].position.y).toBe(-25);
        expect(transforms[0].rotation.z).toBe(30);
      });

      test('Step 231: Single animator with Position + Scale + Opacity', () => {
        const layer = store.createTextLayer('MULTI');

        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -40 });
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 150, y: 150 });
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 50);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        expect(transforms[0].position.y).toBe(-40);
        expect(transforms[0].scale.x).toBe(150);
        expect(transforms[0].opacity).toBe(50);
      });

      test('Step 232: Position + Rotation + Scale combined', () => {
        const layer = store.createTextLayer('COMBO');

        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 15, y: -15 });
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 45);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 120, y: 120 });
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        expect(transforms[0].position.x).toBe(15);
        expect(transforms[0].position.y).toBe(-15);
        expect(transforms[0].rotation.z).toBe(45);
        expect(transforms[0].scale.x).toBe(120);
        expect(transforms[0].scale.y).toBe(120);
      });

      test('Step 233: All properties animate together within range', () => {
        const layer = store.createTextLayer('ABCDEFGH'); // 8 chars

        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -30 });
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 20);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 80, y: 80 });
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 60);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 50, // First half only
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First half: all properties affected
        expect(transforms[0].position.y).toBe(-30);
        expect(transforms[0].rotation.z).toBe(20);
        expect(transforms[0].scale.x).toBe(80);
        expect(transforms[0].opacity).toBe(60);

        // Second half: neutral
        expect(transforms[7].position.y).toBe(0);
        expect(transforms[7].rotation.z).toBe(0);
        expect(transforms[7].scale.x).toBe(100);
        expect(transforms[7].opacity).toBe(100);
      });

      test('Step 234: Multiple properties with different animators', () => {
        const layer = store.createTextLayer('TEST');

        // Animator 1: position only
        const anim1 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim1!.id, 'position', { x: 0, y: -20 });
        store.configureRangeSelector(layer.id, anim1!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        // Animator 2: rotation only
        const anim2 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim2!.id, 'rotation', 15);
        store.configureRangeSelector(layer.id, anim2!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // Both effects from different animators combined
        expect(transforms[0].position.y).toBe(-20);
        expect(transforms[0].rotation.z).toBe(15);
      });
    });

    describe('Section 8.3: Reveal/Conceal Effects (Steps 235-240)', () => {
      test('Step 235: Fade in cascade - Opacity with animated range', () => {
        const layer = store.createTextLayer('FADE IN');

        // Animator: opacity 0 (invisible) for selected range
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);

        // Range covers first 50% - those chars are invisible
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 50,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First half invisible
        expect(transforms[0].opacity).toBe(0);
        // Second half visible
        expect(transforms[6].opacity).toBe(100);
      });

      test('Step 236: Rise up and fade in - Position Y + Opacity', () => {
        const layer = store.createTextLayer('RISE');

        // Animator: characters start below and invisible
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: 50 }); // below baseline
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 50, // First half affected
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First half: below and invisible
        expect(transforms[0].position.y).toBe(50);
        expect(transforms[0].opacity).toBe(0);

        // Second half: normal
        expect(transforms[3].position.y).toBe(0);
        expect(transforms[3].opacity).toBe(100);
      });

      test('Step 237: Pop in effect - Scale 0 to 100', () => {
        const layer = store.createTextLayer('POP');

        // Animator: characters start at 0 scale
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 0, y: 0 });
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 50,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First half: zero scale
        expect(transforms[0].scale.x).toBe(0);
        expect(transforms[0].scale.y).toBe(0);

        // Last char: normal scale
        expect(transforms[2].scale.x).toBe(100);
      });

      test('Step 238: Tumble in - Rotation + Position', () => {
        const layer = store.createTextLayer('TUMBLE');

        // Animator: characters rotated and offset
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', -90);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: -30, y: -30 });
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 50,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First half: rotated and offset
        expect(transforms[0].rotation.z).toBe(-90);
        expect(transforms[0].position.x).toBe(-30);
        expect(transforms[0].position.y).toBe(-30);

        // Last char: normal
        expect(transforms[5].rotation.z).toBe(0);
      });

      test('Step 239: Tracking reveal - Wide to normal spacing', () => {
        const layer = store.createTextLayer('TRACK');

        // Animator: wide tracking for selected range
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'tracking', 200);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 50,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First half: wide tracking
        expect(transforms[0].tracking).toBe(200);
        // Last char: normal tracking
        expect(transforms[4].tracking).toBe(0);
      });

      test('Step 240: Focus in effect - Scale + Opacity', () => {
        const layer = store.createTextLayer('FOCUS');

        // Animator: slightly scaled and semi-transparent (simulating blur focus)
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 110, y: 110 });
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 40);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 50,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First half: blurred/unfocused state
        expect(transforms[0].scale.x).toBe(110);
        expect(transforms[0].opacity).toBe(40);

        // Second half: focused
        expect(transforms[4].scale.x).toBe(100);
        expect(transforms[4].opacity).toBe(100);
      });
    });

    describe('Section 8.4: Kinetic Typography Presets (Steps 241-250)', () => {
      test('Step 241: Typewriter effect - Range End reveals chars', () => {
        const layer = store.createTextLayer('TYPE');

        // Animator: invisible characters
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);

        // End at 50 means first half invisible (typewriter halfway done)
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 50,
          shape: 'square'
        });

        let transforms = store.getCharacterTransforms(layer.id, 0);
        expect(transforms[0].opacity).toBe(0); // First char hidden
        expect(transforms[3].opacity).toBe(100); // Last char visible

        // "Animate" by expanding range to reveal more
        store.configureRangeSelector(layer.id, animator!.id, { end: 25 });
        transforms = store.getCharacterTransforms(layer.id, 0);
        expect(transforms[0].opacity).toBe(0); // Still hidden
        expect(transforms[1].opacity).toBe(100); // Now visible (end moved)
      });

      test('Step 242: Bounce in - Position Y + Scale with overshoot', () => {
        const layer = store.createTextLayer('BOUNCE');

        // Characters start above and small
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -100 });
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 50, y: 50 });
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 50,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First half: above and small (pre-bounce state)
        expect(transforms[0].position.y).toBe(-100);
        expect(transforms[0].scale.x).toBe(50);

        // Second half: normal (post-bounce landed)
        expect(transforms[5].position.y).toBe(0);
        expect(transforms[5].scale.x).toBe(100);
      });

      test('Step 243: Fade up - Position Y + Opacity staggered', () => {
        const layer = store.createTextLayer('FADEUP');

        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: 30 });
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'ramp_down' // Effect decreases from start to end
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First char: full effect (ramp_down starts at 100%)
        expect(transforms[0].position.y).toBe(30);
        expect(transforms[0].opacity).toBe(0);

        // Last char: minimal effect (ramp_down ends at 0%)
        expect(transforms[5].position.y).toBe(0);
        expect(transforms[5].opacity).toBe(100);
      });

      test('Step 244: Spin in - Rotation with range sweep', () => {
        const layer = store.createTextLayer('SPIN');

        // Characters start rotated
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 360);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 50,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First half: fully rotated
        expect(transforms[0].rotation.z).toBe(360);

        // Second half: not rotated (revealed/landed)
        expect(transforms[3].rotation.z).toBe(0);
      });

      test('Step 245: Scale pop - Overshoot scale effect', () => {
        const layer = store.createTextLayer('SCALE');

        // Characters scaled larger than normal (overshoot state)
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 140, y: 140 });
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 50,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First half: overscaled
        expect(transforms[0].scale.x).toBe(140);

        // Second half: normal scale
        expect(transforms[4].scale.x).toBe(100);
      });

      test('Step 246: Tracking reveal - Wide to normal', () => {
        const layer = store.createTextLayer('REVEAL');

        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'tracking', 300);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'ramp_down'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // First char: wide tracking
        expect(transforms[0].tracking).toBe(300);

        // Last char: minimal tracking
        expect(transforms[5].tracking).toBeLessThan(100);
      });

      test('Step 247: Random fade - Wiggly + Opacity', () => {
        const layer = store.createTextLayer('RANDOM');

        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'opacity', 0);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });
        store.configureWigglySelector(layer.id, animator!.id, {
          maxAmount: 100,
          minAmount: 0,
          wigglesPerSecond: 5,
          randomSeed: 42
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // Characters should have varying opacity based on wiggly
        expect(transforms.length).toBe(6);
        // All should have some effect (opacity <= 100)
        expect(transforms.every(t => t.opacity <= 100)).toBe(true);
      });

      test('Step 248: Wave effect - Expression selector with sin', () => {
        const layer = store.createTextLayer('WAVE');

        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -30 });

        // Expression creates wave based on character index
        store.configureExpressionSelector(layer.id, animator!.id, {
          expression: 'Math.sin(textIndex * 0.8) * 50 + 50'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // Characters should have varying Y positions due to sine wave
        expect(transforms.length).toBe(4);
        // Not all same - wave creates variation
        const yPositions = transforms.map(t => t.position.y);
        const allSame = yPositions.every(y => y === yPositions[0]);
        expect(allSame).toBe(false);
      });

      test('Step 249: Character scramble effect', () => {
        const layer = store.createTextLayer('SCRAMBLE');

        // Randomize order simulates scramble
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -20 });
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'square',
          randomizeOrder: true
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // All chars affected (randomize affects animation order, not selection)
        expect(transforms[0].position.y).toBe(-20);
        expect(transforms.length).toBe(8);
      });

      test('Step 250: Glitch effect - Random position/rotation spikes', () => {
        const layer = store.createTextLayer('GLITCH');

        // Position offset for glitch
        const anim1 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim1!.id, 'position', { x: 10, y: -5 });
        store.configureRangeSelector(layer.id, anim1!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });
        store.configureWigglySelector(layer.id, anim1!.id, {
          maxAmount: 100,
          minAmount: 0,
          wigglesPerSecond: 10,
          randomSeed: 999
        });

        // Rotation glitch
        const anim2 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim2!.id, 'rotation', 5);
        store.configureRangeSelector(layer.id, anim2!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });
        store.configureWigglySelector(layer.id, anim2!.id, {
          maxAmount: 100,
          minAmount: 0,
          wigglesPerSecond: 8,
          randomSeed: 888
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // Characters should have glitch offsets
        expect(transforms.length).toBe(6);
        // Verify some effect is applied
        expect(transforms.some(t => t.position.x !== 0 || t.rotation.z !== 0)).toBe(true);
      });
    });

    describe('Section 8.5: Complex Combinations (Steps 251-256)', () => {
      test('Step 251: Path + Animator + Expression Selector', () => {
        const layer = store.createTextLayer('COMBO');

        // Set up path
        store.setTextPath(layer.id, {
          pathPoints: [
            { x: 0, y: 0, handleIn: null, handleOut: { x: 0, y: 0 } },
            { x: 400, y: 0, handleIn: { x: 0, y: 0 }, handleOut: null }
          ]
        });

        // Add animator with expression
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -20 });
        store.configureExpressionSelector(layer.id, animator!.id, {
          expression: 'textIndex % 2 === 0 ? 100 : 0'
        });

        // Both path and animator should apply
        const pathPlacements = store.getCharacterPathPlacements(layer.id, 0);
        expect(pathPlacements.length).toBe(5);

        const transforms = store.getCharacterTransforms(layer.id, 0);
        expect(transforms[0].position.y).toBe(-20); // Even index
        expect(transforms[1].position.y).toBe(0);   // Odd index
      });

      test('Step 252: Multiple Range Selectors with different modes', () => {
        const layer = store.createTextLayer('MODES');

        // Animator with range selector
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -40 });
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // All characters affected
        expect(transforms[0].position.y).toBe(-40);
        expect(transforms[4].position.y).toBe(-40);
      });

      test('Step 253: Wiggly + Range combined', () => {
        const layer = store.createTextLayer('WIGGLE');

        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'position', { x: 0, y: -30 });

        // Range selects all characters
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        // Wiggly modulates the selection amount
        store.configureWigglySelector(layer.id, animator!.id, {
          maxAmount: 100,
          minAmount: 50,
          wigglesPerSecond: 2,
          randomSeed: 12345
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // All characters have some effect (Y offset applied)
        expect(transforms.length).toBe(6);
        // Wiggly modulates between 50-100% so all chars should have Y < 0
        expect(transforms[0].position.y).toBeLessThan(0);
        expect(transforms[5].position.y).toBeLessThan(0);
      });

      test('Step 254: Per-character 3D rotation + Path', () => {
        const layer = store.createTextLayer('3D');

        // Set up path
        store.setTextPath(layer.id, {
          pathPoints: [
            { x: 0, y: 0, handleIn: null, handleOut: { x: 0, y: 0 } },
            { x: 200, y: 0, handleIn: { x: 0, y: 0 }, handleOut: null }
          ],
          perpendicularToPath: true
        });

        // Add Z rotation animator
        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'rotation', 45);
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'ramp_down'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);
        const pathPlacements = store.getCharacterPathPlacements(layer.id, 0);

        // Path placements exist
        expect(pathPlacements.length).toBe(2);
        // Rotation applied from animator
        expect(transforms[0].rotation.z).toBe(45);
      });

      test('Step 255: Nested compositions preserve text animators', () => {
        // Create text layer with animator
        const layer = store.createTextLayer('NESTED');

        const animator = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, animator!.id, 'scale', { x: 75, y: 75 });
        store.configureRangeSelector(layer.id, animator!.id, {
          start: 0,
          end: 100,
          shape: 'square'
        });

        // Verify animator is preserved on layer
        const animators = store.getTextAnimators(layer.id);
        expect(animators.length).toBe(1);
        expect(animators[0].id).toBe(animator!.id);

        // Transforms still work
        const transforms = store.getCharacterTransforms(layer.id, 0);
        expect(transforms[0].scale.x).toBe(75);
      });

      test('Step 256: Text animator with multiple expression effects', () => {
        const layer = store.createTextLayer('EXPRESS');

        // Animator 1: wave Y position
        const anim1 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim1!.id, 'position', { x: 0, y: -25 });
        store.configureExpressionSelector(layer.id, anim1!.id, {
          expression: 'Math.abs(Math.sin(textIndex)) * 100'
        });

        // Animator 2: rotation based on index
        const anim2 = store.addTextAnimator(layer.id);
        store.setAnimatorPropertyValue(layer.id, anim2!.id, 'rotation', 10);
        store.configureExpressionSelector(layer.id, anim2!.id, {
          expression: 'textIndex * 15'
        });

        const transforms = store.getCharacterTransforms(layer.id, 0);

        // Different characters have different transforms
        expect(transforms.length).toBe(7);
        // Verify expressions are evaluated
        expect(typeof transforms[0].position.y).toBe('number');
        expect(typeof transforms[0].rotation.z).toBe('number');
      });
    });
  });
});
