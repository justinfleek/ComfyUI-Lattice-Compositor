import { test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 03: Mesh Deformation - Phases 5-6 (Steps 51-76)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Test", 1920, 1080, 30, 10);
    await h.newSolid("Character");
    await h.selectDeformPinTool();
    // Place base deform pins
    await h.placePinAtPosition(960, 300);
    await h.placePinAtPosition(960, 500);
    await h.placePinAtPosition(880, 700);
    await h.placePinAtPosition(1040, 700);
  });

  test("Phase 5: Overlap Pins (Steps 51-62)", async ({ page }) => {
    // Step 51-52: Switch to overlap tool
    await h.selectOverlapPinTool();

    // Step 53-56: Place overlap pins
    await h.placePinAtPosition(880, 400); // Left arm overlap
    await h.placePinAtPosition(1040, 400); // Right arm overlap

    // Step 57-60: Configure overlap settings
    await h.selectPin(0, 4);
    await h.setOverlapInFront(0, 4, true);
    await h.setOverlapExtent(0, 4, 80);

    await h.selectPin(0, 5);
    await h.setOverlapInFront(0, 5, false);
    await h.setOverlapExtent(0, 5, 60);

    // Step 61-62: Verify overlap effect
    await h.selectDeformPinTool();
    await h.selectPin(0, 0);
    await h.movePinTo(0, 0, 900, 280);

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });

  test("Phase 6: Bend Pins (Steps 63-76)", async ({ page }) => {
    // Step 63-64: Switch to bend tool
    await h.selectBendPinTool();

    // Step 65-68: Place bend pins at joints
    await h.placePinAtPosition(960, 400); // Torso bend
    await h.placePinAtPosition(880, 600); // Left hip bend
    await h.placePinAtPosition(1040, 600); // Right hip bend

    // Step 69-72: Configure bend parameters
    await h.selectPin(0, 4);
    await h.setBendAngle(0, 4, 45);
    await h.setBendLength(0, 4, 100);

    // Step 73-74: Animate bend
    await h.goToStart();
    await h.enableBendKeyframes(0, 4, "angle");
    await h.goToFrame(30);
    await h.setBendAngle(0, 4, -30);

    // Step 75-76: Verify bend animation
    await h.goToStart();
    await h.goToFrame(15);

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });
});
