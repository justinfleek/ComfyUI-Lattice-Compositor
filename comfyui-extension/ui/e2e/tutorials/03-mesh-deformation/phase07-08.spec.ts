import { test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 03: Mesh Deformation - Phases 7-8 (Steps 77-115)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Walk_Cycle", 1920, 1080, 30, 2);
    await h.newSolid("Character");
    await h.selectDeformPinTool();
  });

  test("Phase 7: Advanced Pins (Steps 77-95)", async ({ page }) => {
    // Step 77-80: Place skeleton pins
    await h.placePinAtPosition(960, 200); // Head
    await h.placePinAtPosition(960, 350); // Torso
    await h.placePinAtPosition(960, 550); // Hip

    // Step 81-82: Switch to advanced pin tool
    await h.selectAdvancedPinTool();

    // Step 83-86: Place advanced pins
    await h.placePinAtPosition(960, 280); // Neck advanced
    await h.placePinAtPosition(800, 350); // Left shoulder
    await h.placePinAtPosition(1120, 350); // Right shoulder

    // Step 87-90: Configure advanced parameters
    await h.selectPin(0, 3);
    await h.setAdvancedPinScale(0, 3, 1.2);
    await h.setAdvancedPinRotation(0, 3, 15);
    await h.setAdvancedPinPosition(0, 3, 960, 275);

    // Step 91-95: Link pins
    await h.linkPins(0, 3, 0); // Link neck to head
    await h.linkPins(0, 4, 1); // Link left shoulder to torso
    await h.linkPins(0, 5, 1); // Link right shoulder to torso

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });

  test("Phase 8: Walk Cycle Animation (Steps 96-115)", async ({ page }) => {
    // Step 96-100: Setup character rig
    await h.placePinAtPosition(960, 200); // Head
    await h.placePinAtPosition(960, 400); // Torso
    await h.placePinAtPosition(960, 550); // Hip
    await h.placePinAtPosition(880, 750); // Left knee
    await h.placePinAtPosition(880, 900); // Left foot
    await h.placePinAtPosition(1040, 750); // Right knee
    await h.placePinAtPosition(1040, 900); // Right foot

    // Step 101-104: Contact pose (frame 0)
    await h.goToStart();
    await h.enablePinKeyframes(0, 3, "position");
    await h.enablePinKeyframes(0, 4, "position");
    await h.enablePinKeyframes(0, 5, "position");
    await h.enablePinKeyframes(0, 6, "position");

    // Step 105-108: Passing pose (frame 15)
    await h.goToFrame(15);
    await h.movePinTo(0, 3, 880, 700);
    await h.movePinTo(0, 4, 880, 850);
    await h.movePinTo(0, 5, 1040, 800);
    await h.movePinTo(0, 6, 1040, 950);

    // Step 109-112: Contact pose opposite (frame 30)
    await h.goToFrame(30);
    await h.movePinTo(0, 3, 880, 750);
    await h.movePinTo(0, 4, 880, 900);
    await h.movePinTo(0, 5, 1040, 750);
    await h.movePinTo(0, 6, 1040, 900);

    // Step 113-115: Passing pose opposite (frame 45)
    await h.goToFrame(45);
    await h.movePinTo(0, 3, 880, 800);
    await h.movePinTo(0, 4, 880, 950);
    await h.movePinTo(0, 5, 1040, 700);
    await h.movePinTo(0, 6, 1040, 850);

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });
});
