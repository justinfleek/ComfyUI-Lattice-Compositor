import { expect, test } from "@playwright/test";
import { CompositorHelper } from "../../helpers/compositor";

test.describe("Tutorial 04: Time Remapping - Phases 7-8 (Steps 136-180)", () => {
  let h: CompositorHelper;

  test.beforeEach(async ({ page }) => {
    h = new CompositorHelper(page);
    await page.goto("/");
    await page.waitForSelector('[data-testid="app-ready"]');
    await h.newProject();
    await h.newComposition("Time_Test", 1920, 1080, 24, 10);
    await h.newSolid("Footage");
    await h.setLayerEndFrame(0, 240);
    await h.setTimeStretch(0, 200); // Slow motion
  });

  test("Phase 7: Frame Blending (Steps 136-162)", async ({ page }) => {
    // Step 136-140: Frame blending modes
    await h.setFrameBlending(0, "none");
    await h.setFrameBlending(0, "mix");
    await h.setFrameBlending(0, "motion");

    // Step 141-145: Frame Mix mode
    await h.setFrameBlending(0, "mix");
    // Frames crossfade/dissolve

    // Step 146-150: Pixel Motion mode
    await h.setFrameBlending(0, "motion");
    // Optical flow synthesis

    // Step 151-154: Compare modes
    await h.duplicateLayer();
    await h.setFrameBlending(0, "motion");
    await h.setFrameBlending(1, "mix");

    // Step 155-157: Composition frame blending
    await h.enableCompFrameBlending();

    // Step 158-162: Frame blending determinism
    await h.goToFrame(75);
    const pixels1 = await h.captureFramePixels();

    await h.goToFrame(0);
    await h.goToFrame(150);
    await h.goToFrame(75);

    const pixels2 = await h.captureFramePixels();
    expect(pixels2).toBe(pixels1);

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });

  test("Phase 8: Posterize Time Effect (Steps 163-180)", async ({ page }) => {
    // Step 163-168: Add PosterizeTime effect
    await h.addPosterizeTimeEffect(0);

    // Step 169-171: Stop motion look
    await h.setPosterizeTimeFrameRate(0, 8);
    // Layer plays at 8fps (choppy)

    // Step 172-173: Retro look
    await h.setPosterizeTimeFrameRate(0, 12);
    // Classic animation frame rate

    // Step 174-177: Animate posterize rate
    await h.goToStart();
    await h.setPosterizeTimeFrameRate(0, 24);
    // Add keyframes...
    await h.goToFrame(48);
    await h.setPosterizeTimeFrameRate(0, 8);
    await h.goToFrame(96);
    await h.setPosterizeTimeFrameRate(0, 24);

    // Step 178-180: Posterize on EffectLayer
    await h.newEffectLayer();
    await h.addPosterizeTimeEffect(0);
    await h.setPosterizeTimeFrameRate(0, 12);
    // All layers below affected

    //                                                                      // undo
    await h.undo();
    await h.redo();
  });
});
