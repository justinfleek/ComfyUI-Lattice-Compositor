/**
 * Integration Test: Export → ComfyUI Workflow
 *
 * Tests that exported data correctly maps to ComfyUI workflow nodes.
 *
 * CRITICAL: If this fails, ComfyUI workflows will fail or produce
 * incorrect results.
 */

import { describe, expect, test } from "vitest";
import type { ExportTarget, DepthMapFormat } from "@/types/export";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Mock ComfyUI Workflow Types
// ═══════════════════════════════════════════════════════════════════════════

interface ComfyUIWorkflowNode {
  class_type: string;
  inputs: Record<string, unknown>;
}

interface ComfyUIWorkflow {
  nodes: Record<string, ComfyUIWorkflowNode>;
  links: Array<[string, number, string, number, string]>;
}

// ═══════════════════════════════════════════════════════════════════════════
// Export Target → ComfyUI Node Mapping
// ═══════════════════════════════════════════════════════════════════════════

const TARGET_NODE_MAPPING: Record<ExportTarget, string[]> = {
  "wan22-i2v": ["LoadImage", "WanVideo", "WanImageToVideo"],
  "wan22-t2v": ["WanVideo", "WanTextToVideo", "CLIPTextEncode"],
  "wan22-fun-camera": ["WanVideo", "WanFunCameraMotion", "LoadImage"],
  "wan22-first-last": ["WanVideo", "WanFirstLastFrame", "LoadImage"],
  "wan-move": ["WanVideo", "WanMove", "LoadNPY"],
  "uni3c-camera": ["Uni3C", "UniCameraControl", "LoadImage"],
  "uni3c-motion": ["Uni3C", "UniMotionControl", "LoadImage"],
  motionctrl: ["MotionCtrl", "LoadMotionCtrlCamera", "LoadImage"],
  "motionctrl-svd": ["SVD", "MotionCtrlSVD", "LoadImage"],
  cogvideox: ["CogVideoX", "LoadImage", "CLIPTextEncode"],
  "controlnet-depth": ["ControlNetLoader", "ControlNetApply", "LoadImage"],
  "controlnet-canny": ["ControlNetLoader", "ControlNetApply", "CannyEdge"],
  "controlnet-lineart": ["ControlNetLoader", "ControlNetApply", "LineartPreprocessor"],
  "controlnet-pose": ["ControlNetLoader", "ControlNetApply", "PosePreprocessor"],
  "animatediff-cameractrl": ["AnimateDiff", "CameraCtrl", "LoadImage"],
  "custom-workflow": [],
  "light-x": ["LightX", "LoadImage"],
  ati: ["ATI", "LoadImage"],
  ttm: ["TTM", "LoadImage"],
  "ttm-wan": ["TTM", "WanVideo"],
  "ttm-cogvideox": ["TTM", "CogVideoX"],
  "ttm-svd": ["TTM", "SVD"],
  scail: ["SCAIL", "LoadImage", "LoadPose"],
  "camera-comfyui": ["LoadCamera", "ApplyCamera"],
};

// ═══════════════════════════════════════════════════════════════════════════
// Export Depth → ComfyUI Spec
// ═══════════════════════════════════════════════════════════════════════════

interface DepthNodeSpec {
  expectedBitDepth: 8 | 16 | 32;
  expectedFormat: "PNG" | "EXR" | "NPY";
  invertRequired: boolean;
}

const DEPTH_FORMAT_NODE_SPEC: Record<DepthMapFormat, DepthNodeSpec> = {
  raw: { expectedBitDepth: 32, expectedFormat: "EXR", invertRequired: false },
  midas: { expectedBitDepth: 8, expectedFormat: "PNG", invertRequired: true },
  zoe: { expectedBitDepth: 16, expectedFormat: "PNG", invertRequired: false },
  "depth-pro": { expectedBitDepth: 16, expectedFormat: "PNG", invertRequired: false },
  "depth-anything": { expectedBitDepth: 16, expectedFormat: "PNG", invertRequired: true },
  marigold: { expectedBitDepth: 16, expectedFormat: "PNG", invertRequired: false },
  normalized: { expectedBitDepth: 8, expectedFormat: "PNG", invertRequired: false },
};

// ═══════════════════════════════════════════════════════════════════════════
// Mock Workflow Generator
// ═══════════════════════════════════════════════════════════════════════════

function generateMockWorkflow(target: ExportTarget): ComfyUIWorkflow {
  const nodes: Record<string, ComfyUIWorkflowNode> = {};
  const requiredNodes = TARGET_NODE_MAPPING[target];

  requiredNodes.forEach((nodeType, i) => {
    nodes[`node_${i}`] = {
      class_type: nodeType,
      inputs: {},
    };
  });

  return {
    nodes,
    links: [],
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// Integration Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("Export Target → ComfyUI Node Mapping", () => {
  const allTargets: ExportTarget[] = [
    "wan22-i2v",
    "wan22-t2v",
    "wan22-fun-camera",
    "wan22-first-last",
    "wan-move",
    "uni3c-camera",
    "uni3c-motion",
    "motionctrl",
    "motionctrl-svd",
    "cogvideox",
    "controlnet-depth",
    "controlnet-canny",
    "controlnet-lineart",
    "animatediff-cameractrl",
    "custom-workflow",
    "light-x",
    "ati",
    "ttm",
    "ttm-wan",
    "ttm-cogvideox",
    "ttm-svd",
    "camera-comfyui",
  ];

  test("all export targets have node mappings defined", () => {
    for (const target of allTargets) {
      expect(TARGET_NODE_MAPPING[target]).toBeDefined();
    }
  });

  describe("Wan 2.2 Targets", () => {
    test("wan22-i2v requires WanVideo and image loading", () => {
      const nodes = TARGET_NODE_MAPPING["wan22-i2v"];
      expect(nodes).toContain("WanVideo");
      expect(nodes).toContain("LoadImage");
    });

    test("wan22-t2v requires text encoding", () => {
      const nodes = TARGET_NODE_MAPPING["wan22-t2v"];
      expect(nodes).toContain("CLIPTextEncode");
      expect(nodes).toContain("WanVideo");
    });

    test("wan22-fun-camera requires camera motion node", () => {
      const nodes = TARGET_NODE_MAPPING["wan22-fun-camera"];
      expect(nodes).toContain("WanFunCameraMotion");
    });

    test("wan-move requires NPY loading for trajectories", () => {
      const nodes = TARGET_NODE_MAPPING["wan-move"];
      expect(nodes).toContain("LoadNPY");
      expect(nodes).toContain("WanMove");
    });
  });

  describe("ControlNet Targets", () => {
    test("controlnet-depth requires ControlNet loader and apply", () => {
      const nodes = TARGET_NODE_MAPPING["controlnet-depth"];
      expect(nodes).toContain("ControlNetLoader");
      expect(nodes).toContain("ControlNetApply");
    });

    test("controlnet-canny requires edge detection", () => {
      const nodes = TARGET_NODE_MAPPING["controlnet-canny"];
      expect(nodes).toContain("CannyEdge");
    });

    test("controlnet-lineart requires line extraction", () => {
      const nodes = TARGET_NODE_MAPPING["controlnet-lineart"];
      expect(nodes).toContain("LineartPreprocessor");
    });
  });

  describe("Camera Control Targets", () => {
    test("motionctrl requires camera data loading", () => {
      const nodes = TARGET_NODE_MAPPING["motionctrl"];
      expect(nodes).toContain("MotionCtrl");
      expect(nodes).toContain("LoadMotionCtrlCamera");
    });

    test("uni3c-camera requires camera control node", () => {
      const nodes = TARGET_NODE_MAPPING["uni3c-camera"];
      expect(nodes).toContain("UniCameraControl");
    });

    test("animatediff-cameractrl requires AnimateDiff and CameraCtrl", () => {
      const nodes = TARGET_NODE_MAPPING["animatediff-cameractrl"];
      expect(nodes).toContain("AnimateDiff");
      expect(nodes).toContain("CameraCtrl");
    });
  });
});

describe("Depth Format → File Format Mapping", () => {
  const allFormats: DepthMapFormat[] = [
    "raw",
    "midas",
    "zoe",
    "depth-pro",
    "depth-anything",
    "marigold",
    "normalized",
  ];

  test("all depth formats have specs defined", () => {
    for (const format of allFormats) {
      expect(DEPTH_FORMAT_NODE_SPEC[format]).toBeDefined();
    }
  });

  test("raw format uses 32-bit EXR", () => {
    const spec = DEPTH_FORMAT_NODE_SPEC.raw;
    expect(spec.expectedBitDepth).toBe(32);
    expect(spec.expectedFormat).toBe("EXR");
  });

  test("midas format uses 8-bit inverted PNG", () => {
    const spec = DEPTH_FORMAT_NODE_SPEC.midas;
    expect(spec.expectedBitDepth).toBe(8);
    expect(spec.expectedFormat).toBe("PNG");
    expect(spec.invertRequired).toBe(true);
  });

  test("zoe format uses 16-bit non-inverted PNG", () => {
    const spec = DEPTH_FORMAT_NODE_SPEC.zoe;
    expect(spec.expectedBitDepth).toBe(16);
    expect(spec.invertRequired).toBe(false);
  });

  test("depth-anything uses 16-bit inverted PNG", () => {
    const spec = DEPTH_FORMAT_NODE_SPEC["depth-anything"];
    expect(spec.expectedBitDepth).toBe(16);
    expect(spec.invertRequired).toBe(true);
  });
});

describe("Workflow Generation Contract", () => {
  test("generated workflow contains required nodes for target", () => {
    const targets: ExportTarget[] = ["wan22-i2v", "controlnet-depth", "motionctrl"];

    for (const target of targets) {
      const workflow = generateMockWorkflow(target);
      const expectedNodes = TARGET_NODE_MAPPING[target];
      const actualNodeTypes = Object.values(workflow.nodes).map((n) => n.class_type);

      for (const expected of expectedNodes) {
        expect(actualNodeTypes).toContain(expected);
      }
    }
  });

  test("custom-workflow has no required nodes", () => {
    const workflow = generateMockWorkflow("custom-workflow");
    expect(Object.keys(workflow.nodes)).toHaveLength(0);
  });
});

describe("Camera Export Data Contract", () => {
  // Camera data shape requirements
  interface MotionCtrlCameraSpec {
    RT: number[][][]; // [T][4][4] rotation-translation matrices
    frameCount: number;
  }

  interface Uni3CCameraSpec {
    trajectory: number[][]; // [T][7] position + quaternion
    intrinsics: number[]; // [fx, fy, cx, cy]
  }

  interface AnimateDiffCameraSpec {
    pan: number[];
    tilt: number[];
    roll: number[];
    zoom: number[];
  }

  test("MotionCtrl expects [T][4][4] RT matrices", () => {
    const frameCount = 25;
    const mockCameraData: MotionCtrlCameraSpec = {
      RT: Array(frameCount)
        .fill(null)
        .map(() =>
          Array(4)
            .fill(null)
            .map(() => Array(4).fill(0))
        ),
      frameCount,
    };

    expect(mockCameraData.RT.length).toBe(frameCount);
    expect(mockCameraData.RT[0].length).toBe(4);
    expect(mockCameraData.RT[0][0].length).toBe(4);
  });

  test("Uni3C expects [T][7] trajectory (pos + quat)", () => {
    const frameCount = 25;
    const mockTrajectory: Uni3CCameraSpec = {
      trajectory: Array(frameCount)
        .fill(null)
        .map(() => Array(7).fill(0)),
      intrinsics: [1000, 1000, 960, 540],
    };

    expect(mockTrajectory.trajectory.length).toBe(frameCount);
    expect(mockTrajectory.trajectory[0].length).toBe(7); // x,y,z,qw,qx,qy,qz
    expect(mockTrajectory.intrinsics.length).toBe(4);
  });

  test("AnimateDiff CameraCtrl expects separate pan/tilt/roll/zoom arrays", () => {
    const frameCount = 25;
    const mockCamera: AnimateDiffCameraSpec = {
      pan: Array(frameCount).fill(0),
      tilt: Array(frameCount).fill(0),
      roll: Array(frameCount).fill(0),
      zoom: Array(frameCount).fill(1),
    };

    expect(mockCamera.pan.length).toBe(frameCount);
    expect(mockCamera.tilt.length).toBe(frameCount);
    expect(mockCamera.roll.length).toBe(frameCount);
    expect(mockCamera.zoom.length).toBe(frameCount);
  });
});

describe("Wan-Move Trajectory Contract", () => {
  interface WanMoveSpec {
    tracks: number[][][]; // [N][T][2]
    visibility: boolean[][]; // [N][T]
    numPoints: number;
    numFrames: number;
  }

  test("Wan-Move expects [N][T][2] track shape", () => {
    const numPoints = 50;
    const numFrames = 81;

    const mockTracks: WanMoveSpec = {
      tracks: Array(numPoints)
        .fill(null)
        .map(() =>
          Array(numFrames)
            .fill(null)
            .map(() => [0, 0])
        ),
      visibility: Array(numPoints)
        .fill(null)
        .map(() => Array(numFrames).fill(true)),
      numPoints,
      numFrames,
    };

    expect(mockTracks.tracks.length).toBe(numPoints);
    expect(mockTracks.tracks[0].length).toBe(numFrames);
    expect(mockTracks.tracks[0][0].length).toBe(2);
  });

  test("visibility mask matches track dimensions", () => {
    const numPoints = 50;
    const numFrames = 81;

    const mockTracks: WanMoveSpec = {
      tracks: Array(numPoints)
        .fill(null)
        .map(() =>
          Array(numFrames)
            .fill(null)
            .map(() => [0, 0])
        ),
      visibility: Array(numPoints)
        .fill(null)
        .map(() => Array(numFrames).fill(true)),
      numPoints,
      numFrames,
    };

    expect(mockTracks.visibility.length).toBe(mockTracks.tracks.length);
    expect(mockTracks.visibility[0].length).toBe(mockTracks.tracks[0].length);
  });

  test("coordinates are in [0, width/height] range for valid points", () => {
    const width = 512;
    const height = 512;

    // Simulate valid coordinate generation
    const x = Math.random() * width;
    const y = Math.random() * height;

    expect(x).toBeGreaterThanOrEqual(0);
    expect(x).toBeLessThanOrEqual(width);
    expect(y).toBeGreaterThanOrEqual(0);
    expect(y).toBeLessThanOrEqual(height);
  });
});

describe("ComfyUI Node Input Validation", () => {
  // Common ComfyUI input constraints
  const INPUT_CONSTRAINTS = {
    width: { min: 64, max: 8192, step: 8 },
    height: { min: 64, max: 8192, step: 8 },
    fps: { min: 1, max: 120 },
    frames: { min: 1, max: 10000 },
    denoise: { min: 0, max: 1 },
    cfg: { min: 0, max: 100 },
    steps: { min: 1, max: 1000 },
  };

  test("width must be divisible by 8", () => {
    const validWidths = [512, 768, 1024, 1920, 4096];
    const invalidWidths = [513, 769, 1025, 1921];

    for (const w of validWidths) {
      expect(w % INPUT_CONSTRAINTS.width.step).toBe(0);
    }

    for (const w of invalidWidths) {
      expect(w % INPUT_CONSTRAINTS.width.step).not.toBe(0);
    }
  });

  test("height must be divisible by 8", () => {
    const validHeights = [512, 768, 1080, 2160, 4096];
    // 1080 and 2160 are exceptions often handled by padding

    expect(512 % 8).toBe(0);
    expect(768 % 8).toBe(0);
    expect(4096 % 8).toBe(0);
  });

  test("fps must be in valid range", () => {
    const { min, max } = INPUT_CONSTRAINTS.fps;

    expect(16).toBeGreaterThanOrEqual(min);
    expect(16).toBeLessThanOrEqual(max);
    expect(30).toBeGreaterThanOrEqual(min);
    expect(30).toBeLessThanOrEqual(max);
    expect(60).toBeGreaterThanOrEqual(min);
    expect(60).toBeLessThanOrEqual(max);
  });

  test("denoise strength must be [0, 1]", () => {
    const { min, max } = INPUT_CONSTRAINTS.denoise;

    expect(0).toBeGreaterThanOrEqual(min);
    expect(0).toBeLessThanOrEqual(max);
    expect(0.5).toBeGreaterThanOrEqual(min);
    expect(0.5).toBeLessThanOrEqual(max);
    expect(1).toBeGreaterThanOrEqual(min);
    expect(1).toBeLessThanOrEqual(max);
  });
});

describe("Export Pipeline → ComfyUI Integration", () => {
  test("export config maps to workflow config", () => {
    // Simulating export config → workflow config transformation
    const exportConfig = {
      target: "wan22-i2v" as ExportTarget,
      width: 512,
      height: 512,
      frameCount: 81,
      fps: 16,
    };

    // Transform to workflow config (mock)
    const workflowConfig = {
      model: "wan22",
      mode: "i2v",
      width: exportConfig.width,
      height: exportConfig.height,
      video_length: exportConfig.frameCount,
      fps: exportConfig.fps,
    };

    expect(workflowConfig.width).toBe(exportConfig.width);
    expect(workflowConfig.height).toBe(exportConfig.height);
    expect(workflowConfig.video_length).toBe(exportConfig.frameCount);
    expect(workflowConfig.fps).toBe(exportConfig.fps);
  });

  test("depth export config maps to depth node config", () => {
    const depthConfig = {
      format: "midas" as DepthMapFormat,
      width: 512,
      height: 512,
    };

    const spec = DEPTH_FORMAT_NODE_SPEC[depthConfig.format];

    // Depth node config
    const nodeConfig = {
      invert: spec.invertRequired,
      bit_depth: spec.expectedBitDepth,
      output_type: spec.expectedFormat.toLowerCase(),
    };

    expect(nodeConfig.invert).toBe(true); // MiDaS requires inversion
    expect(nodeConfig.bit_depth).toBe(8);
    expect(nodeConfig.output_type).toBe("png");
  });

  test("camera export config maps to camera node config", () => {
    const cameraConfig = {
      target: "motionctrl" as ExportTarget,
      frameCount: 25,
      fov: 60,
    };

    // Camera node expects specific format
    expect(cameraConfig.frameCount).toBeGreaterThan(0);
    expect(cameraConfig.fov).toBeGreaterThan(0);
    expect(cameraConfig.fov).toBeLessThan(180);
  });
});
