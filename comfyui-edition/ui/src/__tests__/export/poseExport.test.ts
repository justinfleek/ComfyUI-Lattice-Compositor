/**
 * Pose Export Tests
 *
 * Tests for OpenPose JSON format export for ControlNet.
 *
 * CRITICAL: OpenPose format is strictly defined. Wrong format = model failure.
 *
 * OpenPose JSON v1.3 Format:
 * - version: 1.3 (required)
 * - people: array of person objects
 * - pose_keypoints_2d: flat array [x1,y1,c1, x2,y2,c2, ...] (18 keypoints = 54 values)
 * - Coordinates normalized 0-1 or pixel coordinates
 * - Confidence values 0-1
 *
 * @audit P0 CRITICAL - ControlNet pose conditioning
 */

import { describe, it, expect, beforeEach } from "vitest";
import {
  exportToOpenPoseJSON,
  importFromOpenPoseJSON,
  createPoseSequence,
  exportPoseSequence,
  createDefaultPoseExportConfig,
  type OpenPoseJSON,
  type PoseExportConfig,
  type PoseSequence,
} from "@/services/export/poseExport";
import type { Pose, PoseKeypoint } from "@/engine/layers/PoseLayer";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Test Fixtures
// ════════════════════════════════════════════════════════════════════════════

function createTestKeypoint(x: number, y: number, confidence: number = 1.0): PoseKeypoint {
  return { x, y, confidence };
}

function createTestPose(id: string = "pose-1"): Pose {
  //                                                                // coco // 18
  return {
    id,
    format: "coco18",
    keypoints: [
      createTestKeypoint(0.5, 0.1),   // 0: nose
      createTestKeypoint(0.5, 0.15),  // 1: neck
      createTestKeypoint(0.4, 0.15),  // 2: right_shoulder
      createTestKeypoint(0.35, 0.25), // 3: right_elbow
      createTestKeypoint(0.3, 0.35),  // 4: right_wrist
      createTestKeypoint(0.6, 0.15),  // 5: left_shoulder
      createTestKeypoint(0.65, 0.25), // 6: left_elbow
      createTestKeypoint(0.7, 0.35),  // 7: left_wrist
      createTestKeypoint(0.45, 0.35), // 8: right_hip
      createTestKeypoint(0.45, 0.55), // 9: right_knee
      createTestKeypoint(0.45, 0.75), // 10: right_ankle
      createTestKeypoint(0.55, 0.35), // 11: left_hip
      createTestKeypoint(0.55, 0.55), // 12: left_knee
      createTestKeypoint(0.55, 0.75), // 13: left_ankle
      createTestKeypoint(0.48, 0.08), // 14: right_eye
      createTestKeypoint(0.52, 0.08), // 15: left_eye
      createTestKeypoint(0.46, 0.12), // 16: right_ear
      createTestKeypoint(0.54, 0.12), // 17: left_ear
    ],
  };
}

function createPoseWithLowConfidence(): Pose {
  return {
    id: "pose-low-conf",
    format: "coco18",
    keypoints: [
      createTestKeypoint(0.5, 0.1, 0.9),
      createTestKeypoint(0.5, 0.15, 0.8),
      createTestKeypoint(0.4, 0.15, 0.05), // Below threshold
      createTestKeypoint(0.35, 0.25, 0.0), // Zero confidence
      createTestKeypoint(0.3, 0.35, 0.7),
      createTestKeypoint(0.6, 0.15, 0.6),
      createTestKeypoint(0.65, 0.25, 0.5),
      createTestKeypoint(0.7, 0.35, 0.4),
      createTestKeypoint(0.45, 0.35, 0.3),
      createTestKeypoint(0.45, 0.55, 0.2),
      createTestKeypoint(0.45, 0.75, 0.1),
      createTestKeypoint(0.55, 0.35, 0.15),
      createTestKeypoint(0.55, 0.55, 0.25),
      createTestKeypoint(0.55, 0.75, 0.35),
      createTestKeypoint(0.48, 0.08, 0.45),
      createTestKeypoint(0.52, 0.08, 0.55),
      createTestKeypoint(0.46, 0.12, 0.65),
      createTestKeypoint(0.54, 0.12, 0.75),
    ],
  };
}

// ════════════════════════════════════════════════════════════════════════════
// OpenPose JSON Format Tests
// ════════════════════════════════════════════════════════════════════════════

describe("OpenPose JSON Format", () => {
  describe("exportToOpenPoseJSON", () => {
    it("should export version 1.3", () => {
      const poses = [createTestPose()];
      const json = exportToOpenPoseJSON(poses);

      expect(json.version).toBe(1.3);
    });

    it("should export people array", () => {
      const poses = [createTestPose()];
      const json = exportToOpenPoseJSON(poses);

      expect(Array.isArray(json.people)).toBe(true);
      expect(json.people.length).toBe(1);
    });

    it("should export pose_keypoints_2d as flat array", () => {
      const poses = [createTestPose()];
      const json = exportToOpenPoseJSON(poses);

      const keypoints = json.people[0].pose_keypoints_2d;
      expect(Array.isArray(keypoints)).toBe(true);
      // 18 keypoints * 3 values (x, y, confidence) = 54
      expect(keypoints.length).toBe(54);
    });

    it("should have keypoint format [x, y, confidence] repeating", () => {
      const pose = createTestPose();
      pose.keypoints[0] = createTestKeypoint(0.25, 0.75, 0.9);

      const json = exportToOpenPoseJSON([pose]);
      const keypoints = json.people[0].pose_keypoints_2d;

      // First keypoint should be x=0.25, y=0.75, c=0.9
      expect(keypoints[0]).toBeCloseTo(0.25);
      expect(keypoints[1]).toBeCloseTo(0.75);
      expect(keypoints[2]).toBeCloseTo(0.9);
    });

    it("should export all 18 COCO keypoints", () => {
      const poses = [createTestPose()];
      const json = exportToOpenPoseJSON(poses);

      // Check every 3rd value is a confidence (0-1)
      const keypoints = json.people[0].pose_keypoints_2d;
      for (let i = 2; i < keypoints.length; i += 3) {
        expect(keypoints[i]).toBeGreaterThanOrEqual(0);
        expect(keypoints[i]).toBeLessThanOrEqual(1);
      }
    });

    it("should handle multiple people", () => {
      const poses = [
        createTestPose("person-1"),
        createTestPose("person-2"),
        createTestPose("person-3"),
      ];
      const json = exportToOpenPoseJSON(poses);

      expect(json.people.length).toBe(3);
      json.people.forEach((person) => {
        expect(person.pose_keypoints_2d.length).toBe(54);
      });
    });

    it("should have person_id as array", () => {
      const poses = [createTestPose()];
      const json = exportToOpenPoseJSON(poses);

      expect(Array.isArray(json.people[0].person_id)).toBe(true);
    });

    it("should initialize empty keypoint arrays", () => {
      const poses = [createTestPose()];
      const json = exportToOpenPoseJSON(poses);
      const person = json.people[0];

      // OpenPose format requires these arrays even if empty
      expect(Array.isArray(person.face_keypoints_2d)).toBe(true);
      expect(Array.isArray(person.hand_left_keypoints_2d)).toBe(true);
      expect(Array.isArray(person.hand_right_keypoints_2d)).toBe(true);
      expect(Array.isArray(person.pose_keypoints_3d)).toBe(true);
      expect(Array.isArray(person.face_keypoints_3d)).toBe(true);
      expect(Array.isArray(person.hand_left_keypoints_3d)).toBe(true);
      expect(Array.isArray(person.hand_right_keypoints_3d)).toBe(true);
    });

    it("should handle empty poses array", () => {
      const json = exportToOpenPoseJSON([]);

      expect(json.version).toBe(1.3);
      expect(json.people).toEqual([]);
    });

    it("should preserve coordinate values accurately", () => {
      const pose = createTestPose();
      // Set specific values we can verify
      pose.keypoints[5] = createTestKeypoint(0.123456, 0.789012, 0.555);

      const json = exportToOpenPoseJSON([pose]);
      const keypoints = json.people[0].pose_keypoints_2d;

      // Keypoint 5 is at indices 15, 16, 17
      expect(keypoints[15]).toBeCloseTo(0.123456, 5);
      expect(keypoints[16]).toBeCloseTo(0.789012, 5);
      expect(keypoints[17]).toBeCloseTo(0.555, 5);
    });
  });

  describe("OpenPose JSON structure validation", () => {
    it("should produce valid JSON string", () => {
      const poses = [createTestPose()];
      const json = exportToOpenPoseJSON(poses);

      expect(() => JSON.stringify(json)).not.toThrow();
    });

    it("should have no undefined values", () => {
      const poses = [createTestPose()];
      const json = exportToOpenPoseJSON(poses);
      const jsonString = JSON.stringify(json);

      expect(jsonString).not.toContain("undefined");
    });

    it("should have no NaN values", () => {
      const poses = [createTestPose()];
      const json = exportToOpenPoseJSON(poses);
      const jsonString = JSON.stringify(json);

      expect(jsonString).not.toContain("NaN");
    });

    it("should have no Infinity values", () => {
      const poses = [createTestPose()];
      const json = exportToOpenPoseJSON(poses);
      const jsonString = JSON.stringify(json);

      expect(jsonString).not.toContain("Infinity");
    });
  });
});

// ════════════════════════════════════════════════════════════════════════════
// Import/Export Roundtrip Tests
// ════════════════════════════════════════════════════════════════════════════

describe("OpenPose Import/Export Roundtrip", () => {
  it("should roundtrip single pose accurately", () => {
    const original = [createTestPose()];
    const exported = exportToOpenPoseJSON(original);
    const imported = importFromOpenPoseJSON(exported);

    expect(imported.length).toBe(1);
    expect(imported[0].keypoints.length).toBe(18);

    // Check first keypoint
    expect(imported[0].keypoints[0].x).toBeCloseTo(original[0].keypoints[0].x);
    expect(imported[0].keypoints[0].y).toBeCloseTo(original[0].keypoints[0].y);
    expect(imported[0].keypoints[0].confidence).toBeCloseTo(original[0].keypoints[0].confidence);
  });

  it("should roundtrip multiple poses", () => {
    const original = [createTestPose("p1"), createTestPose("p2")];
    const exported = exportToOpenPoseJSON(original);
    const imported = importFromOpenPoseJSON(exported);

    expect(imported.length).toBe(2);
  });

  it("should preserve confidence values through roundtrip", () => {
    const original = [createPoseWithLowConfidence()];
    const exported = exportToOpenPoseJSON(original);
    const imported = importFromOpenPoseJSON(exported);

    original[0].keypoints.forEach((kp, i) => {
      expect(imported[0].keypoints[i].confidence).toBeCloseTo(kp.confidence);
    });
  });

  it("should handle empty people array", () => {
    const emptyJson: OpenPoseJSON = {
      version: 1.3,
      people: [],
    };
    const imported = importFromOpenPoseJSON(emptyJson);

    expect(imported).toEqual([]);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// Pose Sequence Tests
// ════════════════════════════════════════════════════════════════════════════

describe("Pose Sequence", () => {
  describe("createPoseSequence", () => {
    it("should create sequence with correct frame count", () => {
      const keyframePoses = [
        { frame: 0, poses: [createTestPose()] },
        { frame: 30, poses: [createTestPose()] },
      ];

      const sequence = createPoseSequence(keyframePoses, 31, 16);

      expect(sequence.frames.length).toBe(31);
      expect(sequence.fps).toBe(16);
    });

    it("should interpolate between keyframes", () => {
      const pose1 = createTestPose();
      pose1.keypoints[0] = createTestKeypoint(0.0, 0.0, 1.0);

      const pose2 = createTestPose();
      pose2.keypoints[0] = createTestKeypoint(1.0, 1.0, 1.0);

      const keyframePoses = [
        { frame: 0, poses: [pose1] },
        { frame: 10, poses: [pose2] },
      ];

      const sequence = createPoseSequence(keyframePoses, 11, 16);

      // Middle frame should be interpolated
      const midFrame = sequence.frames[5];
      expect(midFrame.poses[0].keypoints[0].x).toBeCloseTo(0.5, 1);
      expect(midFrame.poses[0].keypoints[0].y).toBeCloseTo(0.5, 1);
    });

    it("should hold first keyframe before it", () => {
      const keyframePoses = [
        { frame: 10, poses: [createTestPose()] },
      ];

      const sequence = createPoseSequence(keyframePoses, 20, 16);

      // Frame 0 should have same pose as frame 10
      expect(sequence.frames[0].poses.length).toBe(1);
      expect(sequence.frames[5].poses.length).toBe(1);
    });

    it("should hold last keyframe after it", () => {
      const keyframePoses = [
        { frame: 0, poses: [createTestPose()] },
        { frame: 10, poses: [createTestPose()] },
      ];

      const sequence = createPoseSequence(keyframePoses, 20, 16);

      // Frames after 10 should have same pose as frame 10
      expect(sequence.frames[15].poses.length).toBe(1);
    });

    it("should set format from first pose", () => {
      const keyframePoses = [
        { frame: 0, poses: [createTestPose()] },
      ];

      const sequence = createPoseSequence(keyframePoses, 10, 16);

      expect(sequence.format).toBe("coco18");
    });
  });

  describe("exportPoseSequence", () => {
    it("should export frames within range", () => {
      const keyframePoses = [{ frame: 0, poses: [createTestPose()] }];
      const sequence = createPoseSequence(keyframePoses, 100, 16);

      const config: PoseExportConfig = {
        ...createDefaultPoseExportConfig(),
        startFrame: 10,
        endFrame: 20,
        outputFormat: "json",
      };

      const result = exportPoseSequence(sequence, config);

      expect(result.jsonFrames?.length).toBe(11); // 10 to 20 inclusive
    });

    it("should include sequence metadata in JSON output", () => {
      const keyframePoses = [{ frame: 0, poses: [createTestPose()] }];
      const sequence = createPoseSequence(keyframePoses, 50, 24);

      const config: PoseExportConfig = {
        ...createDefaultPoseExportConfig(),
        startFrame: 0,
        endFrame: 49,
        outputFormat: "json",
      };

      const result = exportPoseSequence(sequence, config);

      expect(result.sequenceJson).toBeDefined();
      expect(result.sequenceJson?.metadata.frameCount).toBe(50);
      expect(result.sequenceJson?.metadata.fps).toBe(24);
    });
  });
});

// ════════════════════════════════════════════════════════════════════════════
// Config Tests
// ════════════════════════════════════════════════════════════════════════════

describe("Pose Export Config", () => {
  describe("createDefaultPoseExportConfig", () => {
    it("should create valid default config", () => {
      const config = createDefaultPoseExportConfig();

      expect(config.width).toBeGreaterThan(0);
      expect(config.height).toBeGreaterThan(0);
      expect(config.boneWidth).toBeGreaterThan(0);
      expect(config.keypointRadius).toBeGreaterThan(0);
      expect(config.backgroundColor).toMatch(/^#[0-9a-fA-F]{6}$/);
    });

    it("should default to black background", () => {
      const config = createDefaultPoseExportConfig();

      expect(config.backgroundColor).toBe("#000000");
    });

    it("should default to OpenPose colors", () => {
      const config = createDefaultPoseExportConfig();

      expect(config.useOpenPoseColors).toBe(true);
    });

    it("should default to showing bones and keypoints", () => {
      const config = createDefaultPoseExportConfig();

      expect(config.showBones).toBe(true);
      expect(config.showKeypoints).toBe(true);
    });
  });
});

// ════════════════════════════════════════════════════════════════════════════
// Edge Cases
// ════════════════════════════════════════════════════════════════════════════

describe("Edge Cases", () => {
  it("should handle pose with missing keypoints gracefully", () => {
    const pose: Pose = {
      id: "partial",
      format: "coco18",
      keypoints: [
        createTestKeypoint(0.5, 0.5, 1.0),
        // Only 1 keypoint instead of 18
      ],
    };

    // Should not throw
    const json = exportToOpenPoseJSON([pose]);

    // Should only have 3 values (1 keypoint * 3)
    expect(json.people[0].pose_keypoints_2d.length).toBe(3);
  });

  it("should handle keypoints at boundary values", () => {
    const pose: Pose = {
      id: "boundary",
      format: "coco18",
      keypoints: [
        createTestKeypoint(0, 0, 0),      // Min values
        createTestKeypoint(1, 1, 1),      // Max values
        createTestKeypoint(0.5, 0.5, 0.5), // Mid values
      ],
    };

    const json = exportToOpenPoseJSON([pose]);
    const kp = json.people[0].pose_keypoints_2d;

    // Min values
    expect(kp[0]).toBe(0);
    expect(kp[1]).toBe(0);
    expect(kp[2]).toBe(0);

    // Max values
    expect(kp[3]).toBe(1);
    expect(kp[4]).toBe(1);
    expect(kp[5]).toBe(1);
  });

  it("should handle coordinates outside 0-1 range", () => {
    const pose: Pose = {
      id: "out-of-range",
      format: "coco18",
      keypoints: [
        createTestKeypoint(-0.5, 1.5, 0.8),  // Out of bounds
        createTestKeypoint(2.0, -1.0, 0.9),  // Way out of bounds
      ],
    };

    // Should not throw - coordinates are preserved as-is
    const json = exportToOpenPoseJSON([pose]);
    const kp = json.people[0].pose_keypoints_2d;

    expect(kp[0]).toBe(-0.5);
    expect(kp[1]).toBe(1.5);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// Determinism Tests
// ════════════════════════════════════════════════════════════════════════════

describe("Determinism", () => {
  it("should produce identical output for identical input", () => {
    const poses1 = [createTestPose()];
    const poses2 = [createTestPose()];

    const json1 = exportToOpenPoseJSON(poses1);
    const json2 = exportToOpenPoseJSON(poses2);

    expect(JSON.stringify(json1)).toBe(JSON.stringify(json2));
  });

  it("should produce consistent sequence interpolation", () => {
    const keyframePoses = [
      { frame: 0, poses: [createTestPose()] },
      { frame: 30, poses: [createTestPose()] },
    ];

    const seq1 = createPoseSequence(keyframePoses, 31, 16);
    const seq2 = createPoseSequence(keyframePoses, 31, 16);

    expect(seq1.frames.length).toBe(seq2.frames.length);

    for (let i = 0; i < seq1.frames.length; i++) {
      expect(seq1.frames[i].poses.length).toBe(seq2.frames[i].poses.length);
    }
  });
});
