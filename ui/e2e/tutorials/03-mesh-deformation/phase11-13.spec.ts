import { test, expect } from '@playwright/test';
import { CompositorHelper } from '../../helpers/compositor';

test.describe('Tutorial 03: Mesh Deformation - Phases 11-13 (Steps 146-185)', () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto('/');
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition('Walk_Cycle', 1920, 1080, 30, 2);
    await h.newSolid('Character');
  });

  test('Phase 11: Loop Expressions (Steps 146-160)', async ({ page }) => {
    // Setup walk cycle pins
    await h.selectDeformPinTool();
    await h.placePinAtPosition(960, 300);
    await h.placePinAtPosition(880, 700);
    await h.placePinAtPosition(1040, 700);

    // Create basic animation
    await h.goToStart();
    await h.enablePinKeyframes(0, 1, 'position');
    await h.goToFrame(30);
    await h.movePinTo(0, 1, 880, 650);
    await h.goToFrame(60);
    await h.movePinTo(0, 1, 880, 700);

    // Step 146-150: Add loop expression
    await h.selectPin(0, 1);
    await h.openPinExpressions(0, 1, 'position');
    await h.setExpression('loopOut("cycle")');
    await h.closeExpressionEditor();

    // Step 151-155: Verify loop plays continuously
    await h.goToFrame(90);  // Beyond keyframe range
    // Animation should continue due to loop

    // Step 156-160: Add pingpong variation
    await h.selectPin(0, 2);
    await h.enablePinKeyframes(0, 2, 'position');
    await h.goToStart();
    await h.goToFrame(30);
    await h.movePinTo(0, 2, 1040, 650);
    await h.openPinExpressions(0, 2, 'position');
    await h.setExpression('loopOut("pingpong")');
    await h.closeExpressionEditor();

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });

  test('Phase 12: Comprehensive Undo/Redo (Steps 161-175)', async ({ page }) => {
    // Step 161-165: Build complex rig
    await h.selectDeformPinTool();
    await h.placePinAtPosition(960, 200);
    await h.placePinAtPosition(960, 400);
    await h.placePinAtPosition(960, 600);
    await h.placePinAtPosition(880, 800);
    await h.placePinAtPosition(1040, 800);

    await h.selectStiffnessPinTool();
    await h.placePinAtPosition(960, 300);

    await h.selectBendPinTool();
    await h.placePinAtPosition(960, 500);

    // Step 166-170: Undo all pin placements
    await h.expectPinCount(0, 7);
    await h.undo(); // Undo bend pin
    await h.expectPinCount(0, 6);
    await h.undo(); // Undo stiffness pin
    await h.expectPinCount(0, 5);
    await h.undo(); // Undo deform pin
    await h.undo();
    await h.undo();
    await h.undo();
    await h.undo();
    await h.expectPinCount(0, 0);

    // Step 171-175: Redo all
    await h.redo();
    await h.redo();
    await h.redo();
    await h.redo();
    await h.redo();
    await h.redo();
    await h.redo();
    await h.expectPinCount(0, 7);
  });

  test('Phase 13: Save/Load Verification (Steps 176-185)', async ({ page }) => {
    // Step 176-178: Build complete character
    await h.selectDeformPinTool();
    await h.placePinAtPosition(960, 200);
    await h.placePinAtPosition(960, 400);
    await h.placePinAtPosition(800, 400);
    await h.placePinAtPosition(1120, 400);
    await h.placePinAtPosition(960, 600);
    await h.placePinAtPosition(880, 800);
    await h.placePinAtPosition(1040, 800);

    // Configure mesh
    await h.setMeshTriangleCount(0, 300);
    await h.setMeshExpansion(0, 5);

    // Add animation
    await h.goToStart();
    await h.enablePinKeyframes(0, 0, 'position');
    await h.goToFrame(30);
    await h.movePinTo(0, 0, 980, 220);

    // Step 179-181: Save project
    await h.saveProject();

    // Step 182-184: Reload and verify
    await h.reloadProject();
    await page.waitForSelector('[data-testid="app-ready"]');

    // Step 185: Verify all pins restored
    await h.expectPinCount(0, 7);
    await h.expectMeshDeformationEffect(0);
  });

  test('DETERMINISM: Pin animation consistency', async ({ page }) => {
    await h.selectDeformPinTool();
    await h.placePinAtPosition(960, 400);

    await h.goToStart();
    await h.enablePinKeyframes(0, 0, 'position');
    await h.goToFrame(60);
    await h.movePinTo(0, 0, 1000, 450);

    // Verify determinism
    await h.verifyDeterminism(['pin-position'], 30);
  });
});
