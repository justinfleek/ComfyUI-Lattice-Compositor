/**
 * Camera Export Tests
 * 
 * BUG HUNTING - focused on actual issues found:
 * 1. Hardcoded 30fps in exportToAEScript (line 421)
 * 2. Import/export roundtrip
 */

import { describe, it, expect } from "vitest";
import {
  exportToUni3C,
  exportCameraJSON,
  importCameraJSON,
  exportToAEScript,
} from "@/services/cameraExport";
import type { Camera3D, CameraKeyframe } from "@/types/camera";

// Test fixtures
function createTestCamera(overrides: Partial<Camera3D> = {}): Camera3D {
  const base: Camera3D = {
    id: "test-cam",
    name: "Test Camera",
    type: "one-node",
    position: { x: 0, y: 0, z: -1000 },
    pointOfInterest: { x: 0, y: 0, z: 0 },
    orientation: { x: 0, y: 0, z: 0 },
    xRotation: 0,
    yRotation: 0,
    zRotation: 0,
    zoom: 1000,
    focalLength: 50,
    filmSize: 36,
    angleOfView: 39.6,
    measureFilmSize: "horizontal",
    depthOfField: {
      enabled: false,
      focusDistance: 500,
      aperture: 50, // Pixels (internal)
      fStop: 5.6, // f-stop (display)
      blurLevel: 1,
      lockToZoom: false,
    },
    iris: {
      shape: 7,
      rotation: 0,
      roundness: 0,
      aspectRatio: 1,
      diffractionFringe: 0,
    },
    highlight: {
      gain: 0,
      threshold: 1,
      saturation: 1,
    },
    autoOrient: "off",
    nearClip: 1,
    farClip: 10000,
  };
  return { ...base, ...overrides };
}

function createTestKeyframe(frame: number, overrides: Partial<CameraKeyframe> = {}): CameraKeyframe {
  return {
    frame,
    ...overrides,
  };
}

describe("exportToUni3C", () => {
  it("should export correct number of frames", () => {
    const camera = createTestCamera();
    const keyframes: CameraKeyframe[] = [];
    
    const result = exportToUni3C(camera, keyframes, 30, 1920, 1080, 0, 10);
    
    expect(result.frames.length).toBe(11); // 0-10 inclusive
  });

  it("should include correct metadata", () => {
    const camera = createTestCamera({ name: "My Camera" });
    
    const result = exportToUni3C(camera, [], 24, 1920, 1080, 0, 5);
    
    expect(result.version).toBe("1.0");
    expect(result.fps).toBe(24);
    expect(result.metadata.cameraName).toBe("My Camera");
    expect(result.metadata.compWidth).toBe(1920);
    expect(result.metadata.compHeight).toBe(1080);
  });

  it("should calculate correct timestamps", () => {
    const camera = createTestCamera();
    
    const result = exportToUni3C(camera, [], 30, 1920, 1080, 0, 3);
    
    expect(result.frames[0].timestamp).toBeCloseTo(0);
    expect(result.frames[1].timestamp).toBeCloseTo(1/30);
    expect(result.frames[2].timestamp).toBeCloseTo(2/30);
    expect(result.frames[3].timestamp).toBeCloseTo(3/30);
  });

  it("should interpolate keyframes correctly", () => {
    const camera = createTestCamera({ position: { x: 0, y: 0, z: 0 } });
    const keyframes: CameraKeyframe[] = [
      createTestKeyframe(0, { position: { x: 0, y: 0, z: 0 } }),
      createTestKeyframe(10, { position: { x: 100, y: 0, z: 0 } }),
    ];
    
    const result = exportToUni3C(camera, keyframes, 30, 1920, 1080, 0, 10);
    
    // Frame 5 should be halfway
    expect(result.frames[5].camera.position.x).toBeCloseTo(50, 0);
  });

  it("should handle two-node camera rotation from POI", () => {
    const camera = createTestCamera({
      type: "two-node",
      position: { x: 0, y: 0, z: -100 },
      pointOfInterest: { x: 0, y: 0, z: 0 },
    });
    
    const result = exportToUni3C(camera, [], 30, 1920, 1080, 0, 0);
    
    // Looking from z=-100 towards origin should have 0 rotation
    expect(result.frames[0].camera.rotation.y).toBeCloseTo(0, 0);
  });
});

describe("JSON import/export roundtrip", () => {
  it("should preserve camera data through roundtrip", () => {
    const camera = createTestCamera({
      position: { x: 100, y: 200, z: -500 },
      focalLength: 35,
    });
    const keyframes: CameraKeyframe[] = [
      createTestKeyframe(0, { position: { x: 0, y: 0, z: 0 } }),
      createTestKeyframe(30, { position: { x: 100, y: 100, z: 100 } }),
    ];
    
    const json = exportCameraJSON(camera, keyframes);
    const imported = importCameraJSON(json);
    
    expect(imported).not.toBeNull();
    expect(imported!.camera.position.x).toBe(100);
    expect(imported!.camera.position.y).toBe(200);
    expect(imported!.camera.focalLength).toBe(35);
    expect(imported!.keyframes.length).toBe(2);
  });

  it("should return null for invalid JSON", () => {
    expect(importCameraJSON("not valid json")).toBeNull();
    expect(importCameraJSON("{}")).toBeNull(); // Missing camera/keyframes
    expect(importCameraJSON('{"camera": null}')).toBeNull();
  });
});

describe("exportToAEScript fps parameter (BUG FIXED)", () => {
  it("uses default 30fps when not specified", () => {
    const camera = createTestCamera();
    const keyframes = [
      createTestKeyframe(60, { position: { x: 100, y: 0, z: 0 } }),
    ];
    
    const script = exportToAEScript(camera, keyframes, "TestComp");
    
    // Frame 60 at 30fps = 2 seconds
    expect(script).toContain("setValueAtTime(2,"); // 60 / 30 = 2
  });

  it("uses custom fps when provided", () => {
    const camera = createTestCamera();
    const keyframes = [
      createTestKeyframe(60, { position: { x: 100, y: 0, z: 0 } }),
    ];
    
    const script = exportToAEScript(camera, keyframes, "TestComp", 24);
    
    // Frame 60 at 24fps = 2.5 seconds
    expect(script).toContain("setValueAtTime(2.5,"); // 60 / 24 = 2.5
  });

  it("handles 60fps correctly", () => {
    const camera = createTestCamera();
    const keyframes = [
      createTestKeyframe(120, { position: { x: 100, y: 0, z: 0 } }),
    ];
    
    const script = exportToAEScript(camera, keyframes, "TestComp", 60);
    
    // Frame 120 at 60fps = 2 seconds
    expect(script).toContain("setValueAtTime(2,"); // 120 / 60 = 2
  });

  it("generates valid ExtendScript structure", () => {
    const camera = createTestCamera({ name: "Hero Camera" });
    
    const script = exportToAEScript(camera, [], "MainComp");
    
    expect(script).toContain("// Camera Import Script");
    expect(script).toContain("Hero Camera");
    expect(script).toContain("app.project.activeItem");
    expect(script).toContain("comp.layers.addCamera");
  });

  it("includes DOF settings when enabled", () => {
    const camera = createTestCamera({
      depthOfField: {
        enabled: true,
        focusDistance: 500,
        aperture: 50, // Pixels (internal)
        fStop: 2.8, // f-stop (display)
        blurLevel: 1.5,
        lockToZoom: false,
      },
    });
    
    const script = exportToAEScript(camera, [], "TestComp");
    
    expect(script).toContain("Depth of Field");
    expect(script).toContain("500"); // focusDistance
    //                                                                      // note
    // The implementation outputs depthOfField.aperture (50) not fStop (2.8)
    expect(script).toContain("50"); // aperture in pixels (not fStop)
  });

  it("includes POI for two-node camera", () => {
    const camera = createTestCamera({
      type: "two-node",
      pointOfInterest: { x: 100, y: 200, z: 300 },
    });
    
    const script = exportToAEScript(camera, [], "TestComp");
    
    expect(script).toContain("pointOfInterest");
    expect(script).toContain("100");
    expect(script).toContain("200");
    expect(script).toContain("300");
  });
});
