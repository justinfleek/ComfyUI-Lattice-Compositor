import { test, expect } from '@playwright/test';
import { CompositorHelper } from '../../helpers/compositor';

test.describe('Tutorial 03: Mesh Deformation - Phases 3-4 (Steps 23-50)', () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto('/');
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition('Test', 1920, 1080, 30, 10);
    await h.newSolid('Character');
    await h.selectDeformPinTool();
  });

  test('Phase 3: Deform Pin Placement (Steps 23-38)', async ({ page }) => {
    // Step 23-34: Place pins at joint locations
    await h.placePinAtPosition(960, 200);  // Head
    await h.placePinAtPosition(960, 280);  // Neck
    await h.placePinAtPosition(800, 400);  // Left elbow
    await h.placePinAtPosition(700, 500);  // Left wrist
    await h.placePinAtPosition(1120, 400); // Right elbow
    await h.placePinAtPosition(1220, 500); // Right wrist
    await h.placePinAtPosition(960, 450);  // Torso
    await h.placePinAtPosition(960, 600);  // Hip
    await h.placePinAtPosition(880, 750);  // Left knee
    await h.placePinAtPosition(880, 900);  // Left ankle
    await h.placePinAtPosition(1040, 750); // Right knee
    await h.placePinAtPosition(1040, 900); // Right ankle

    // Verify 12 pins placed
    await h.expectPinCount(0, 12);

    // Step 35-36: Rename pins
    await h.renamePin(0, 0, 'Head');
    await h.renamePin(0, 1, 'Neck');
    await h.renamePin(0, 2, 'L_Elbow');
    await h.renamePin(0, 3, 'L_Wrist');

    // Step 37-38: Pin count undo/redo
    await h.undo();
    await h.undo();
    await h.undo();
    await h.expectPinCount(0, 9);
    await h.redo();
    await h.redo();
    await h.redo();
    await h.expectPinCount(0, 12);
  });

  test('Phase 4: Stiffness Pins (Steps 39-50)', async ({ page }) => {
    // Place initial deform pins
    await h.placePinAtPosition(960, 300);  // Head area
    await h.placePinAtPosition(960, 500);  // Torso
    await h.placePinAtPosition(880, 900);  // Left foot
    await h.placePinAtPosition(1040, 900); // Right foot

    // Step 39-40: Switch to stiffness tool
    await h.selectStiffnessPinTool();

    // Step 41-44: Place stiffness pins
    await h.placePinAtPosition(960, 250);  // Head stiffness
    await h.placePinAtPosition(960, 480);  // Torso stiffness
    await h.placePinAtPosition(860, 920);  // Left foot stiffness
    await h.placePinAtPosition(1060, 920); // Right foot stiffness

    // Step 45-47: Adjust stiffness parameters
    await h.selectPin(0, 4);
    await h.setStiffnessAmount(0, 4, 75);
    await h.setStiffnessExtent(0, 4, 50);

    // Step 48-50: Test stiffness effect
    await h.selectDeformPinTool();
    await h.selectPin(0, 0);
    await h.movePinTo(0, 0, 980, 320);

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });
});
