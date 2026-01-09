import { expect, test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 03: Mesh Deformation - Phases 9-10 (Steps 116-145)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Test", 1920, 1080, 30, 5);
    await h.newSolid("Character");
    await h.selectDeformPinTool();
    // Setup basic rig
    await h.placePinAtPosition(960, 300);
    await h.placePinAtPosition(960, 500);
    await h.placePinAtPosition(880, 800);
    await h.placePinAtPosition(1040, 800);
  });

  test("Phase 9: Motion Recording (Steps 116-130)", async ({ page }) => {
    // Step 116-118: Enable motion recording
    await h.enableMotionRecording(0);
    await expect(
      page.locator('[data-testid="motion-recording-active"]'),
    ).toBeVisible();

    // Step 119-122: Record motion for head
    await h.selectPin(0, 0);
    await h.startRecording();

    // Simulate recording movements
    await h.recordPinMovement(0, 0, [
      { frame: 0, x: 960, y: 300 },
      { frame: 10, x: 980, y: 290 },
      { frame: 20, x: 960, y: 300 },
      { frame: 30, x: 940, y: 310 },
      { frame: 40, x: 960, y: 300 },
    ]);

    await h.stopRecording();

    // Step 123-126: Verify recorded keyframes
    await h.goToStart();
    await h.selectPin(0, 0);
    await h.expectKeyframeCount(0, 0, "position", 5);

    // Step 127-130: Smooth recorded animation
    await h.selectAllKeyframes(0, 0, "position");
    await h.smoothEase();

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });

  test("Phase 10: Troubleshooting Common Issues (Steps 131-145)", async ({
    page,
  }) => {
    // Step 131-135: Mesh tearing fix
    await h.movePinTo(0, 0, 1200, 100); // Extreme position causing tear
    await expect(page.locator('[data-testid="mesh-warning"]')).toBeVisible();

    // Increase mesh density
    await h.setMeshTriangleCount(0, 500);
    await expect(
      page.locator('[data-testid="mesh-warning"]'),
    ).not.toBeVisible();

    // Step 136-138: Reset to fix issues
    await h.resetPinPosition(0, 0);

    // Step 139-142: Stiffness adjustment for jitter
    await h.selectStiffnessPinTool();
    await h.placePinAtPosition(960, 400);
    await h.setStiffnessAmount(0, 4, 100);

    // Step 143-145: Performance optimization
    await h.setMeshTriangleCount(0, 200); // Reduce for performance
    await h.toggleMeshVisibility(0);
    await expect(
      page.locator('[data-testid="layer-0-mesh-overlay"]'),
    ).toBeVisible();

    // UNDO/REDO
    await h.undo();
    await h.redo();
  });
});
