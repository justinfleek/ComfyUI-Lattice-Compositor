/**
 * Property tests for ui/src/types/camera.ts
 * Tests: createDefaultCamera, createDefaultViewportState, createDefaultViewOptions
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  createDefaultCamera,
  createDefaultViewportState,
  createDefaultViewOptions,
  CAMERA_PRESETS,
  type Camera3D,
  type ViewportState,
  type ViewOptions,
} from "@/types/camera";

// ============================================================
// ARBITRARIES
// ============================================================

// Composition dimensions (must be positive)
const compWidthArb = fc.integer({ min: 1, max: 8192 });
const compHeightArb = fc.integer({ min: 1, max: 8192 });

// Camera ID
const cameraIdArb = fc.string({ minLength: 1, maxLength: 50 });

// ============================================================
// createDefaultCamera TESTS
// ============================================================

describe("PROPERTY: createDefaultCamera", () => {
  it("returns object with all required Camera3D fields", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);

        // Core fields
        expect(camera).toHaveProperty("id");
        expect(camera).toHaveProperty("name");
        expect(camera).toHaveProperty("type");

        // Transform
        expect(camera).toHaveProperty("position");
        expect(camera).toHaveProperty("pointOfInterest");
        expect(camera).toHaveProperty("orientation");
        expect(camera).toHaveProperty("xRotation");
        expect(camera).toHaveProperty("yRotation");
        expect(camera).toHaveProperty("zRotation");

        // Lens
        expect(camera).toHaveProperty("zoom");
        expect(camera).toHaveProperty("focalLength");
        expect(camera).toHaveProperty("angleOfView");
        expect(camera).toHaveProperty("filmSize");
        expect(camera).toHaveProperty("measureFilmSize");

        // DOF
        expect(camera).toHaveProperty("depthOfField");

        // Iris
        expect(camera).toHaveProperty("iris");

        // Highlight
        expect(camera).toHaveProperty("highlight");

        // Other
        expect(camera).toHaveProperty("autoOrient");
        expect(camera).toHaveProperty("nearClip");
        expect(camera).toHaveProperty("farClip");
      })
    );
  });

  it("id matches input", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.id).toBe(id);
      })
    );
  });

  it("name is 'Camera 1'", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.name).toBe("Camera 1");
      })
    );
  });

  it("type is 'two-node'", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.type).toBe("two-node");
      })
    );
  });

  it("position.x is compWidth / 2", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.position.x).toBe(width / 2);
      })
    );
  });

  it("position.y is compHeight / 2", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.position.y).toBe(height / 2);
      })
    );
  });

  it("position.z is -1500", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.position.z).toBe(-1500);
      })
    );
  });

  it("pointOfInterest is centered at z=0", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.pointOfInterest.x).toBe(width / 2);
        expect(camera.pointOfInterest.y).toBe(height / 2);
        expect(camera.pointOfInterest.z).toBe(0);
      })
    );
  });

  it("orientation is (0, 0, 0)", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.orientation).toEqual({ x: 0, y: 0, z: 0 });
      })
    );
  });

  it("individual rotations are 0", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.xRotation).toBe(0);
        expect(camera.yRotation).toBe(0);
        expect(camera.zRotation).toBe(0);
      })
    );
  });

  it("zoom is 1778 (50mm equivalent)", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.zoom).toBe(1778);
      })
    );
  });

  it("focalLength is 50mm", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.focalLength).toBe(50);
      })
    );
  });

  it("angleOfView is 39.6 degrees", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.angleOfView).toBe(39.6);
      })
    );
  });

  it("filmSize is 36mm (full frame)", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.filmSize).toBe(36);
      })
    );
  });

  it("measureFilmSize is 'horizontal'", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.measureFilmSize).toBe("horizontal");
      })
    );
  });

  it("depthOfField has correct defaults", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.depthOfField.enabled).toBe(false);
        expect(camera.depthOfField.focusDistance).toBe(1500);
        expect(camera.depthOfField.aperture).toBe(50);
        expect(camera.depthOfField.fStop).toBe(2.8);
        expect(camera.depthOfField.blurLevel).toBe(1);
        expect(camera.depthOfField.lockToZoom).toBe(false);
      })
    );
  });

  it("iris has correct defaults", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.iris.shape).toBe(7);
        expect(camera.iris.rotation).toBe(0);
        expect(camera.iris.roundness).toBe(0);
        expect(camera.iris.aspectRatio).toBe(1);
        expect(camera.iris.diffractionFringe).toBe(0);
      })
    );
  });

  it("highlight has correct defaults", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.highlight.gain).toBe(0);
        expect(camera.highlight.threshold).toBe(1);
        expect(camera.highlight.saturation).toBe(1);
      })
    );
  });

  it("autoOrient is 'off'", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.autoOrient).toBe("off");
      })
    );
  });

  it("clip planes are valid (near < far)", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera = createDefaultCamera(id, width, height);
        expect(camera.nearClip).toBe(1);
        expect(camera.farClip).toBe(10000);
        expect(camera.nearClip).toBeLessThan(camera.farClip);
      })
    );
  });

  it("is deterministic (same inputs = same output)", () => {
    fc.assert(
      fc.property(cameraIdArb, compWidthArb, compHeightArb, (id, width, height) => {
        const camera1 = createDefaultCamera(id, width, height);
        const camera2 = createDefaultCamera(id, width, height);
        expect(camera1).toEqual(camera2);
      })
    );
  });
});

// ============================================================
// createDefaultViewportState TESTS
// ============================================================

describe("PROPERTY: createDefaultViewportState", () => {
  it("returns object with all required ViewportState fields", () => {
    const state = createDefaultViewportState();

    expect(state).toHaveProperty("layout");
    expect(state).toHaveProperty("views");
    expect(state).toHaveProperty("customViews");
    expect(state).toHaveProperty("activeViewIndex");
  });

  it("layout is '1-view'", () => {
    const state = createDefaultViewportState();
    expect(state.layout).toBe("1-view");
  });

  it("views contains 'active-camera'", () => {
    const state = createDefaultViewportState();
    expect(state.views).toContain("active-camera");
  });

  it("all 3 custom views exist", () => {
    const state = createDefaultViewportState();
    expect(state.customViews).toHaveProperty("custom-1");
    expect(state.customViews).toHaveProperty("custom-2");
    expect(state.customViews).toHaveProperty("custom-3");
  });

  it("custom-1 has correct defaults", () => {
    const state = createDefaultViewportState();
    expect(state.customViews["custom-1"].orbitCenter).toEqual({ x: 0, y: 0, z: 0 });
    expect(state.customViews["custom-1"].orbitDistance).toBe(2000);
    expect(state.customViews["custom-1"].orbitPhi).toBe(60);
    expect(state.customViews["custom-1"].orbitTheta).toBe(45);
    expect(state.customViews["custom-1"].orthoZoom).toBe(1);
    expect(state.customViews["custom-1"].orthoOffset).toEqual({ x: 0, y: 0 });
  });

  it("custom-2 has correct defaults", () => {
    const state = createDefaultViewportState();
    expect(state.customViews["custom-2"].orbitPhi).toBe(90);
    expect(state.customViews["custom-2"].orbitTheta).toBe(0);
  });

  it("custom-3 has correct defaults", () => {
    const state = createDefaultViewportState();
    expect(state.customViews["custom-3"].orbitPhi).toBe(0);
    expect(state.customViews["custom-3"].orbitTheta).toBe(0);
  });

  it("activeViewIndex is 0", () => {
    const state = createDefaultViewportState();
    expect(state.activeViewIndex).toBe(0);
  });

  it("is deterministic", () => {
    const state1 = createDefaultViewportState();
    const state2 = createDefaultViewportState();
    expect(state1).toEqual(state2);
  });
});

// ============================================================
// createDefaultViewOptions TESTS
// ============================================================

describe("PROPERTY: createDefaultViewOptions", () => {
  it("returns object with all required ViewOptions fields", () => {
    const options = createDefaultViewOptions();

    expect(options).toHaveProperty("cameraWireframes");
    expect(options).toHaveProperty("lightWireframes");
    expect(options).toHaveProperty("showMotionPaths");
    expect(options).toHaveProperty("showLayerPaths");
    expect(options).toHaveProperty("showLayerHandles");
    expect(options).toHaveProperty("showSafeZones");
    expect(options).toHaveProperty("showGrid");
    expect(options).toHaveProperty("showRulers");
    expect(options).toHaveProperty("show3DReferenceAxes");
    expect(options).toHaveProperty("showCompositionBounds");
    expect(options).toHaveProperty("showFocalPlane");
  });

  it("cameraWireframes is 'selected'", () => {
    const options = createDefaultViewOptions();
    expect(options.cameraWireframes).toBe("selected");
  });

  it("lightWireframes is 'selected'", () => {
    const options = createDefaultViewOptions();
    expect(options.lightWireframes).toBe("selected");
  });

  it("showMotionPaths is true", () => {
    const options = createDefaultViewOptions();
    expect(options.showMotionPaths).toBe(true);
  });

  it("showLayerPaths is true", () => {
    const options = createDefaultViewOptions();
    expect(options.showLayerPaths).toBe(true);
  });

  it("showLayerHandles is true", () => {
    const options = createDefaultViewOptions();
    expect(options.showLayerHandles).toBe(true);
  });

  it("showSafeZones is false", () => {
    const options = createDefaultViewOptions();
    expect(options.showSafeZones).toBe(false);
  });

  it("showGrid is false", () => {
    const options = createDefaultViewOptions();
    expect(options.showGrid).toBe(false);
  });

  it("showRulers is true", () => {
    const options = createDefaultViewOptions();
    expect(options.showRulers).toBe(true);
  });

  it("show3DReferenceAxes is true", () => {
    const options = createDefaultViewOptions();
    expect(options.show3DReferenceAxes).toBe(true);
  });

  it("showCompositionBounds is true", () => {
    const options = createDefaultViewOptions();
    expect(options.showCompositionBounds).toBe(true);
  });

  it("showFocalPlane is false", () => {
    const options = createDefaultViewOptions();
    expect(options.showFocalPlane).toBe(false);
  });

  it("is deterministic", () => {
    const options1 = createDefaultViewOptions();
    const options2 = createDefaultViewOptions();
    expect(options1).toEqual(options2);
  });
});

// ============================================================
// CAMERA_PRESETS TESTS
// ============================================================

describe("PROPERTY: CAMERA_PRESETS", () => {
  it("has 8 presets", () => {
    expect(CAMERA_PRESETS).toHaveLength(8);
  });

  it("all presets have required fields", () => {
    for (const preset of CAMERA_PRESETS) {
      expect(preset).toHaveProperty("name");
      expect(preset).toHaveProperty("focalLength");
      expect(preset).toHaveProperty("angleOfView");
      expect(preset).toHaveProperty("zoom");
    }
  });

  it("focalLength is positive for all presets", () => {
    for (const preset of CAMERA_PRESETS) {
      expect(preset.focalLength).toBeGreaterThan(0);
    }
  });

  it("angleOfView is positive for all presets", () => {
    for (const preset of CAMERA_PRESETS) {
      expect(preset.angleOfView).toBeGreaterThan(0);
    }
  });

  it("zoom is positive for all presets", () => {
    for (const preset of CAMERA_PRESETS) {
      expect(preset.zoom).toBeGreaterThan(0);
    }
  });

  it("focalLength increases as name suggests wider to telephoto", () => {
    const focalLengths = CAMERA_PRESETS.map((p) => p.focalLength);
    for (let i = 1; i < focalLengths.length; i++) {
      expect(focalLengths[i]).toBeGreaterThan(focalLengths[i - 1]);
    }
  });

  it("angleOfView decreases as focalLength increases", () => {
    const angles = CAMERA_PRESETS.map((p) => p.angleOfView);
    for (let i = 1; i < angles.length; i++) {
      expect(angles[i]).toBeLessThan(angles[i - 1]);
    }
  });

  it("zoom increases as focalLength increases", () => {
    const zooms = CAMERA_PRESETS.map((p) => p.zoom);
    for (let i = 1; i < zooms.length; i++) {
      expect(zooms[i]).toBeGreaterThan(zooms[i - 1]);
    }
  });
});
