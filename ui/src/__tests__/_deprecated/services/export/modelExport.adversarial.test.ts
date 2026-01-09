/**
 * Model Export Adversarial Tests
 *
 * Tests designed to BREAK the model export system and verify it fails gracefully.
 * Focus areas:
 * - NPY binary format generation
 * - Trajectory data validation
 * - Camera matrix computation
 * - TTM mask generation
 *
 * @module ModelExportAdversarialTests
 */

import { describe, expect, it, vi } from "vitest";

// Note: We need to mock THREE.js and canvas for Node environment
// Using proper class constructors instead of arrow functions (TEST-001 fix)
vi.mock("three", () => {
  class MockVector3 {
    constructor(
      public x = 0,
      public y = 0,
      public z = 0,
    ) {}
    set(x: number, y: number, z: number) {
      this.x = x;
      this.y = y;
      this.z = z;
      return this;
    }
    clone() {
      return new MockVector3(this.x, this.y, this.z);
    }
    copy(v: MockVector3) {
      this.x = v.x;
      this.y = v.y;
      this.z = v.z;
      return this;
    }
    add(v: MockVector3) {
      this.x += v.x;
      this.y += v.y;
      this.z += v.z;
      return this;
    }
    sub(v: MockVector3) {
      this.x -= v.x;
      this.y -= v.y;
      this.z -= v.z;
      return this;
    }
    multiplyScalar(s: number) {
      this.x *= s;
      this.y *= s;
      this.z *= s;
      return this;
    }
    length() {
      return Math.sqrt(this.x * this.x + this.y * this.y + this.z * this.z);
    }
    normalize() {
      const l = this.length();
      if (l > 0) {
        this.x /= l;
        this.y /= l;
        this.z /= l;
      }
      return this;
    }
    applyMatrix4(_m: MockMatrix4) {
      return this;
    }
    applyQuaternion(_q: MockQuaternion) {
      return this;
    }
  }

  class MockEuler {
    constructor(
      public x = 0,
      public y = 0,
      public z = 0,
      public order = "XYZ",
    ) {}
    set(x: number, y: number, z: number, order?: string) {
      this.x = x;
      this.y = y;
      this.z = z;
      if (order) this.order = order;
      return this;
    }
    clone() {
      return new MockEuler(this.x, this.y, this.z, this.order);
    }
    setFromQuaternion(_q: MockQuaternion, _order?: string) {
      return this;
    }
  }

  class MockQuaternion {
    constructor(
      public x = 0,
      public y = 0,
      public z = 0,
      public w = 1,
    ) {}
    setFromEuler(_euler: MockEuler) {
      return this;
    }
    clone() {
      return new MockQuaternion(this.x, this.y, this.z, this.w);
    }
    multiply(_q: MockQuaternion) {
      return this;
    }
    invert() {
      return this;
    }
  }

  class MockMatrix4 {
    elements: Float32Array;
    constructor() {
      this.elements = new Float32Array(16);
      this.identity();
    }
    identity() {
      this.elements.fill(0);
      this.elements[0] =
        this.elements[5] =
        this.elements[10] =
        this.elements[15] =
          1;
      return this;
    }
    compose(
      position: MockVector3,
      _quaternion: MockQuaternion,
      _scale: MockVector3,
    ) {
      // Simplified compose - sets translation in last column
      this.identity();
      this.elements[12] = position.x;
      this.elements[13] = position.y;
      this.elements[14] = position.z;
      return this;
    }
    multiply(_m: MockMatrix4) {
      return this;
    }
    invert() {
      return this;
    }
    clone() {
      const m = new MockMatrix4();
      m.elements.set(this.elements);
      return m;
    }
    toArray() {
      return Array.from(this.elements);
    }
  }

  return {
    Vector3: MockVector3,
    Euler: MockEuler,
    Quaternion: MockQuaternion,
    Matrix4: MockMatrix4,
    MathUtils: {
      degToRad: (deg: number) => (deg * Math.PI) / 180,
      radToDeg: (rad: number) => (rad * 180) / Math.PI,
    },
  };
});

import {
  calculatePanSpeed,
  camera3DToMatrix4x4,
  createNpyHeader,
  exportCameraTrajectory,
  exportForModel,
  exportWanMoveTracksForKijai,
  exportWanMoveTrajectories,
  extractLayerTrajectory,
  generateCombinedMotionMask,
  generateMotionMask,
  imageDataToBase64,
  type PointTrajectory,
  trajectoriesToNpy,
} from "@/services/modelExport";
import type { Camera3D } from "@/types/camera";
import type { Layer } from "@/types/project";

// ============================================================================
// Test Fixtures
// ============================================================================

function createValidCamera(overrides: Partial<Camera3D> = {}): Camera3D {
  return {
    id: "test-camera",
    name: "Test Camera",
    type: "perspective",
    position: { x: 0, y: 0, z: -500 },
    orientation: { x: 0, y: 0, z: 0 },
    xRotation: 0,
    yRotation: 0,
    zRotation: 0,
    focalLength: 50,
    angleOfView: 39.6,
    zoom: 1,
    nearClip: 1,
    farClip: 10000,
    filmSize: 36,
    depthOfField: {
      enabled: false,
      focusDistance: 100,
      aperture: 2.8,
      bladeCount: 6,
    },
    ...overrides,
  } as Camera3D;
}

function createValidLayer(overrides: Partial<Layer> = {}): Layer {
  return {
    id: "test-layer",
    name: "Test Layer",
    type: "solid",
    visible: true,
    startFrame: 0,
    endFrame: 100,
    inPoint: 0,
    outPoint: 100,
    transform: {
      position: { value: { x: 0, y: 0 }, animated: false },
      scale: { value: { x: 100, y: 100 }, animated: false },
      rotation: { value: 0, animated: false },
      anchorPoint: { value: { x: 0, y: 0 }, animated: false },
      opacity: { value: 100 },
    },
    ...overrides,
  } as unknown as Layer;
}

function _createValidTrajectory(
  overrides: Partial<PointTrajectory> = {},
): PointTrajectory {
  return {
    id: "test-traj",
    points: [
      { frame: 0, x: 0, y: 0 },
      { frame: 1, x: 10, y: 10 },
      { frame: 2, x: 20, y: 20 },
    ],
    visibility: [true, true, true],
    ...overrides,
  };
}

// Mock document.createElement for canvas operations
const mockCanvas = {
  width: 512,
  height: 512,
  getContext: vi.fn(() => ({
    fillStyle: "",
    fillRect: vi.fn(),
    getImageData: vi.fn(() => new ImageData(512, 512)),
    putImageData: vi.fn(),
  })),
  toDataURL: vi.fn(() => "data:image/png;base64,mock"),
};

vi.stubGlobal("document", {
  createElement: vi.fn(() => mockCanvas),
});

// ============================================================================
// CRITICAL: NPY Binary Format Tests
// ============================================================================

describe("CRITICAL: NPY Binary Format - Header Generation", () => {
  describe("createNpyHeader - Shape Validation", () => {
    it("should throw for empty shape array", () => {
      expect(() => {
        createNpyHeader([]);
      }).toThrow(/empty|undefined/i);
    });

    it("should throw for undefined shape", () => {
      expect(() => {
        createNpyHeader(undefined as any);
      }).toThrow(/empty|undefined/i);
    });

    it("should throw for negative dimensions", () => {
      expect(() => {
        createNpyHeader([-1, 10, 2]);
      }).toThrow(/negative|invalid/i);
    });

    it("should throw for NaN dimensions", () => {
      expect(() => {
        createNpyHeader([NaN, 10, 2]);
      }).toThrow(/NaN|invalid/i);
    });

    it("should throw for Infinity dimensions", () => {
      expect(() => {
        createNpyHeader([Infinity, 10, 2]);
      }).toThrow(/Infinity|invalid/i);
    });

    it("should throw for non-integer dimensions", () => {
      expect(() => {
        createNpyHeader([10.5, 10, 2]);
      }).toThrow(/integer|invalid/i);
    });

    it("should handle valid single-dimension shape", () => {
      const header = createNpyHeader([10]);
      expect(header).toBeInstanceOf(Uint8Array);
      expect(header.length).toBeGreaterThan(10);
    });

    it("should handle zero dimension (valid but empty array)", () => {
      // Note: Shape [0, 10, 2] is valid in NumPy - represents empty array
      const header = createNpyHeader([0, 10, 2]);
      expect(header).toBeInstanceOf(Uint8Array);
    });

    it("should include Python tuple syntax in header", () => {
      const header = createNpyHeader([10, 5, 2]);
      const headerStr = new TextDecoder().decode(header);
      // Should contain Python tuple format: (10, 5, 2)
      expect(headerStr).toContain("(");
      expect(headerStr).toContain(")");
    });

    it("should include trailing comma for single-element tuple", () => {
      const header = createNpyHeader([10]);
      const headerStr = new TextDecoder().decode(header);
      // Python single-element tuple: (10,)
      expect(headerStr).toMatch(/\(10,\)/);
    });
  });
});

describe("CRITICAL: NPY Binary Format - trajectoriesToNpy", () => {
  it("should throw for empty trajectories array", () => {
    expect(() => {
      trajectoriesToNpy([]);
    }).toThrow(/empty/i);
  });

  it("should throw for trajectory with no points", () => {
    expect(() => {
      trajectoriesToNpy([[]]);
    }).toThrow(/no points/i);
  });

  it("should handle NaN values in trajectory points gracefully", () => {
    const trajectories = [
      [
        [NaN, 0],
        [10, NaN],
        [20, 20],
      ],
    ];

    // Should not throw - should replace NaN with 0
    const blob = trajectoriesToNpy(trajectories);
    expect(blob).toBeInstanceOf(Blob);
  });

  it("should warn but not crash for mismatched frame counts", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});

    const trajectories = [
      [
        [0, 0],
        [10, 10],
        [20, 20],
      ], // 3 frames
      [
        [0, 0],
        [10, 10],
      ], // 2 frames
    ];

    const blob = trajectoriesToNpy(trajectories);
    expect(blob).toBeInstanceOf(Blob);
    expect(consoleWarn).toHaveBeenCalled();

    consoleWarn.mockRestore();
  });

  it("should handle undefined points in trajectory", () => {
    const trajectories = [[[0, 0], undefined as any, [20, 20]]];

    // Should not crash - should use fallback
    const blob = trajectoriesToNpy(trajectories);
    expect(blob).toBeInstanceOf(Blob);
  });
});

// ============================================================================
// CRITICAL: Camera Matrix Export
// ============================================================================

describe("CRITICAL: Camera Matrix Export - NaN/Infinity Handling", () => {
  it("should throw for NaN camera position", () => {
    const camera = createValidCamera({
      position: { x: NaN, y: 0, z: 0 },
    });

    expect(() => {
      camera3DToMatrix4x4(camera);
    }).toThrow(/position.*NaN|invalid/i);
  });

  it("should throw for Infinity camera position", () => {
    const camera = createValidCamera({
      position: { x: Infinity, y: 0, z: 0 },
    });

    expect(() => {
      camera3DToMatrix4x4(camera);
    }).toThrow(/position.*Infinity|invalid/i);
  });

  it("should use fallback for NaN orientation (non-critical)", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});

    const camera = createValidCamera({
      orientation: { x: NaN, y: 0, z: 0 },
    });

    // Should not throw - orientation uses fallback
    const matrix = camera3DToMatrix4x4(camera);
    expect(matrix).toBeDefined();
    expect(matrix.length).toBe(4);
    expect(consoleWarn).toHaveBeenCalled();

    consoleWarn.mockRestore();
  });

  it("should use fallback for NaN rotation values", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});

    const camera = createValidCamera({
      xRotation: NaN,
      yRotation: NaN,
      zRotation: NaN,
    });

    const matrix = camera3DToMatrix4x4(camera);
    expect(matrix).toBeDefined();
    expect(consoleWarn).toHaveBeenCalled();

    consoleWarn.mockRestore();
  });
});

describe("CRITICAL: exportCameraTrajectory - Input Validation", () => {
  it("should return empty result for empty camera array", () => {
    const result = exportCameraTrajectory([], 24, 1920, 1080);

    expect(result.matrices).toEqual([]);
    expect(result.metadata.frameCount).toBe(0);
  });

  it("should throw for invalid fps", () => {
    const cameras = [createValidCamera()];

    expect(() => {
      exportCameraTrajectory(cameras, 0, 1920, 1080);
    }).toThrow(/fps.*0|invalid/i);
  });

  it("should throw for negative fps", () => {
    const cameras = [createValidCamera()];

    expect(() => {
      exportCameraTrajectory(cameras, -24, 1920, 1080);
    }).toThrow(/fps.*-24|invalid/i);
  });

  it("should throw for NaN fps", () => {
    const cameras = [createValidCamera()];

    expect(() => {
      exportCameraTrajectory(cameras, NaN, 1920, 1080);
    }).toThrow(/fps.*NaN|invalid/i);
  });

  it("should use fallback for invalid dimensions", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});
    const cameras = [createValidCamera()];

    const result = exportCameraTrajectory(cameras, 24, NaN, NaN);

    expect(result.metadata.width).toBe(512); // Fallback
    expect(result.metadata.height).toBe(512); // Fallback
    expect(consoleWarn).toHaveBeenCalled();

    consoleWarn.mockRestore();
  });

  it("should provide detailed error if camera at specific frame fails", () => {
    const cameras = [
      createValidCamera(),
      createValidCamera({ position: { x: NaN, y: NaN, z: NaN } }),
    ];

    expect(() => {
      exportCameraTrajectory(cameras, 24, 1920, 1080);
    }).toThrow(/frame 1|camera/i);
  });
});

// ============================================================================
// HIGH: Trajectory Export Tests
// ============================================================================

describe("HIGH: WanMove Trajectory Export", () => {
  it("should return empty result for empty trajectories", () => {
    const result = exportWanMoveTrajectories([], 1920, 1080);

    expect(result.trajectories).toEqual([]);
    expect(result.metadata.numPoints).toBe(0);
    expect(result.metadata.numFrames).toBe(0);
  });

  it("should handle trajectories with no points", () => {
    const trajectories: PointTrajectory[] = [
      {
        id: "empty",
        points: [],
        visibility: [],
      },
    ];

    const result = exportWanMoveTrajectories(trajectories, 1920, 1080);
    expect(result.metadata.numFrames).toBe(0);
  });

  it("should handle mixed 2D/3D trajectories", () => {
    const trajectories: PointTrajectory[] = [
      {
        id: "traj-2d",
        points: [{ frame: 0, x: 0, y: 0 }],
        visibility: [true],
      },
      {
        id: "traj-3d",
        points: [{ frame: 0, x: 0, y: 0, z: 100 }],
        visibility: [true],
      },
    ];

    const result = exportWanMoveTrajectories(trajectories, 1920, 1080);
    expect(result.metadata.is3D).toBe(true);
    // 2D trajectory should have z filled with 0
    expect(result.trajectories[0][0]).toEqual([0, 0, 0]);
  });
});

describe("HIGH: Kijai WanMove Format", () => {
  it("should return empty array for empty trajectories", () => {
    const result = exportWanMoveTracksForKijai([]);
    expect(result).toEqual([]);
  });

  it("should convert to [{x,y}] format correctly", () => {
    const trajectories: PointTrajectory[] = [
      {
        id: "test",
        points: [
          { frame: 0, x: 100, y: 200 },
          { frame: 1, x: 150, y: 250 },
        ],
        visibility: [true, true],
      },
    ];

    const result = exportWanMoveTracksForKijai(trajectories);

    expect(result).toEqual([
      [
        { x: 100, y: 200 },
        { x: 150, y: 250 },
      ],
    ]);
  });
});

// ============================================================================
// HIGH: Pan Speed Calculation
// ============================================================================

describe("HIGH: calculatePanSpeed - Division by Zero", () => {
  const mockGetPosition = (_layer: Layer, frame: number) => {
    return { x: frame * 10, y: frame * 5 };
  };

  it("should return zero speed for equal start/end frames", () => {
    const layer = createValidLayer();
    const result = calculatePanSpeed(layer, 0, 0, mockGetPosition);

    expect(result.x).toBe(0);
    expect(result.y).toBe(0);
  });

  it("should return zero speed for endFrame < startFrame", () => {
    const layer = createValidLayer();
    const result = calculatePanSpeed(layer, 10, 5, mockGetPosition);

    expect(result.x).toBe(0);
    expect(result.y).toBe(0);
  });

  it("should return zero speed for NaN frames", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});
    const layer = createValidLayer();

    const result = calculatePanSpeed(layer, NaN, 10, mockGetPosition);

    expect(result.x).toBe(0);
    expect(result.y).toBe(0);
    expect(consoleWarn).toHaveBeenCalled();

    consoleWarn.mockRestore();
  });

  it("should handle NaN positions from getter", () => {
    const layer = createValidLayer();
    const nanGetter = () => ({ x: NaN, y: NaN });

    const result = calculatePanSpeed(layer, 0, 10, nanGetter);

    // Should use fallback values
    expect(Number.isFinite(result.x)).toBe(true);
    expect(Number.isFinite(result.y)).toBe(true);
  });
});

// ============================================================================
// HIGH: Motion Mask Generation
// ============================================================================

describe("HIGH: generateMotionMask - Dimension Validation", () => {
  const mockGetBounds = () => ({ x: 100, y: 100, width: 200, height: 200 });

  it("should throw for zero width", () => {
    const layer = createValidLayer();

    expect(() => {
      generateMotionMask(layer, 0, 512, mockGetBounds);
    }).toThrow(/width.*0|invalid/i);
  });

  it("should throw for negative height", () => {
    const layer = createValidLayer();

    expect(() => {
      generateMotionMask(layer, 512, -100, mockGetBounds);
    }).toThrow(/height.*-100|invalid/i);
  });

  it("should throw for NaN dimensions", () => {
    const layer = createValidLayer();

    expect(() => {
      generateMotionMask(layer, NaN, 512, mockGetBounds);
    }).toThrow(/NaN|invalid/i);
  });

  it("should throw for dimensions exceeding 8192", () => {
    const layer = createValidLayer();

    expect(() => {
      generateMotionMask(layer, 16384, 512, mockGetBounds);
    }).toThrow(/16384|exceeds|too large/i);
  });

  it("should handle NaN bounds gracefully", () => {
    const layer = createValidLayer();
    const nanBoundsGetter = () => ({ x: NaN, y: NaN, width: NaN, height: NaN });

    // Should use fallback values, not crash
    const result = generateMotionMask(layer, 512, 512, nanBoundsGetter);
    expect(result).toBeInstanceOf(ImageData);
  });
});

describe("HIGH: generateCombinedMotionMask - Multi-Layer", () => {
  const mockGetBounds = () => ({ x: 100, y: 100, width: 200, height: 200 });

  it("should throw for invalid dimensions", () => {
    const layers = [createValidLayer()];

    expect(() => {
      generateCombinedMotionMask(layers, 0, 0, mockGetBounds);
    }).toThrow(/invalid/i);
  });

  it("should handle empty layers array", () => {
    const result = generateCombinedMotionMask([], 512, 512, mockGetBounds);

    // Should return black image (no motion regions)
    expect(result).toBeInstanceOf(ImageData);
    expect(result.width).toBe(512);
    expect(result.height).toBe(512);
  });

  it("should continue if one layer throws", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});

    const layers = [createValidLayer(), createValidLayer()];
    let callCount = 0;
    const throwingGetter = () => {
      callCount++;
      if (callCount === 1) throw new Error("Layer 1 failed");
      return { x: 100, y: 100, width: 200, height: 200 };
    };

    // Should not throw - should skip failed layer
    const result = generateCombinedMotionMask(layers, 512, 512, throwingGetter);
    expect(result).toBeInstanceOf(ImageData);
    expect(consoleWarn).toHaveBeenCalled();

    consoleWarn.mockRestore();
  });
});

// ============================================================================
// HIGH: imageDataToBase64 Validation
// ============================================================================

describe("HIGH: imageDataToBase64 - Input Validation", () => {
  it("should throw for null ImageData", () => {
    expect(() => {
      imageDataToBase64(null as any);
    }).toThrow(/invalid/i);
  });

  it("should throw for ImageData with zero dimensions", () => {
    const badImageData = {
      width: 0,
      height: 0,
      data: new Uint8ClampedArray(0),
    } as ImageData;

    expect(() => {
      imageDataToBase64(badImageData);
    }).toThrow(/invalid|width.*0/i);
  });

  it("should throw for ImageData with missing data", () => {
    const badImageData = { width: 100, height: 100, data: null } as any;

    expect(() => {
      imageDataToBase64(badImageData);
    }).toThrow(/invalid/i);
  });
});

// ============================================================================
// HIGH: exportForModel - Unknown Target
// ============================================================================

describe("HIGH: exportForModel - Unknown Target Handling", () => {
  it("should return error for unknown target", async () => {
    const result = await exportForModel({
      target: "unknown-model" as any,
      layers: [],
      cameras: [],
      compWidth: 1920,
      compHeight: 1080,
      fps: 24,
      startFrame: 0,
      endFrame: 10,
      getPositionAtFrame: () => ({ x: 0, y: 0 }),
      getLayerBounds: () => ({ x: 0, y: 0, width: 100, height: 100 }),
    });

    expect(result.success).toBe(false);
    expect(result.error).toMatch(/unknown.*target|valid targets/i);
  });

  it("should return error for TTM with no animated layers", async () => {
    const result = await exportForModel({
      target: "ttm",
      layers: [
        createValidLayer({
          transform: { position: { animated: false } } as any,
        }),
      ],
      cameras: [],
      compWidth: 1920,
      compHeight: 1080,
      fps: 24,
      startFrame: 0,
      endFrame: 10,
      getPositionAtFrame: () => ({ x: 0, y: 0 }),
      getLayerBounds: () => ({ x: 0, y: 0, width: 100, height: 100 }),
    });

    expect(result.success).toBe(false);
    expect(result.error).toMatch(/no animated layers/i);
  });

  it("should return error for particles with no particle data", async () => {
    const result = await exportForModel({
      target: "particles",
      layers: [],
      cameras: [],
      compWidth: 1920,
      compHeight: 1080,
      fps: 24,
      startFrame: 0,
      endFrame: 10,
      getPositionAtFrame: () => ({ x: 0, y: 0 }),
      getLayerBounds: () => ({ x: 0, y: 0, width: 100, height: 100 }),
    });

    expect(result.success).toBe(false);
    expect(result.error).toMatch(/no particle data/i);
  });
});

// ============================================================================
// MEDIUM: Layer Trajectory Extraction
// ============================================================================

describe("MEDIUM: extractLayerTrajectory - Edge Cases", () => {
  const mockGetPosition = (_layer: Layer, frame: number) => ({
    x: frame * 10,
    y: frame * 5,
  });

  it("should handle layer with no startFrame/endFrame", () => {
    const layer = createValidLayer({
      startFrame: undefined,
      endFrame: undefined,
      inPoint: undefined,
      outPoint: undefined,
    });

    const result = extractLayerTrajectory(layer, 0, 10, mockGetPosition);

    expect(result.points.length).toBe(11);
    // Visibility should use fallback (0 to 80)
  });

  it("should handle invisible layers", () => {
    const layer = createValidLayer({ visible: false });

    const result = extractLayerTrajectory(layer, 0, 10, mockGetPosition);

    // All visibility should be false
    expect(result.visibility.every((v) => v === false)).toBe(true);
  });

  it("should handle single frame range", () => {
    const layer = createValidLayer();

    const result = extractLayerTrajectory(layer, 5, 5, mockGetPosition);

    expect(result.points.length).toBe(1);
    expect(result.points[0].frame).toBe(5);
  });
});
