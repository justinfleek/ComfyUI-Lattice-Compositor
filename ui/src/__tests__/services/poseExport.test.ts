/**
 * Tests for ControlNet Pose Export
 */
import { describe, it, expect } from 'vitest';
import {
  renderPoseFrame,
  createPoseSequence,
  exportToOpenPoseJSON,
  exportPoseSequence,
  exportPoseForControlNet,
  importFromOpenPoseJSON,
  importPoseSequence,
  createDefaultPoseExportConfig
} from '../../services/export/poseExport';
import {
  createDefaultPose,
  scalePose,
  rotatePose,
  translatePose,
  interpolatePoses,
  COCO_KEYPOINTS,
  COCO_BONES
} from '../../engine/layers/PoseLayer';
import type { Pose, PoseKeypoint } from '../../engine/layers/PoseLayer';

// Helper to create test pose
function createTestPose(): Pose {
  return createDefaultPose('coco18');
}

describe('Pose Export - Constants', () => {
  it('should have 18 keypoints in COCO format', () => {
    expect(COCO_KEYPOINTS.length).toBe(18);
  });

  it('should have correct bone connections', () => {
    // Verify some key bone connections
    expect(COCO_BONES).toContainEqual([0, 1]); // nose -> neck
    expect(COCO_BONES).toContainEqual([1, 2]); // neck -> right_shoulder
    expect(COCO_BONES).toContainEqual([1, 5]); // neck -> left_shoulder
    expect(COCO_BONES).toContainEqual([8, 9]); // right_hip -> right_knee
  });
});

describe('Pose Export - Pose Creation', () => {
  describe('createDefaultPose', () => {
    it('should create pose with 18 keypoints for COCO format', () => {
      const pose = createDefaultPose('coco18');
      expect(pose.keypoints.length).toBe(18);
      expect(pose.format).toBe('coco18');
    });

    it('should create T-pose by default', () => {
      const pose = createDefaultPose('coco18');

      // Shoulders should be at roughly same Y, spread on X
      const rightShoulder = pose.keypoints[2];
      const leftShoulder = pose.keypoints[5];

      expect(rightShoulder.x).toBeLessThan(leftShoulder.x); // Right is on left side of image
      expect(Math.abs(rightShoulder.y - leftShoulder.y)).toBeLessThan(0.1);
    });

    it('should have all keypoints with confidence 1', () => {
      const pose = createDefaultPose('coco18');
      for (const kp of pose.keypoints) {
        expect(kp.confidence).toBe(1.0);
      }
    });
  });
});

describe('Pose Export - Pose Manipulation', () => {
  describe('scalePose', () => {
    it('should scale pose around center', () => {
      const pose = createTestPose();
      const originalNose = { ...pose.keypoints[0] };
      const originalCenter = calculateCenter(pose);

      scalePose(pose, 2.0);

      // Distance from center should double
      const newNose = pose.keypoints[0];
      const distBefore = Math.hypot(originalNose.x - originalCenter.x, originalNose.y - originalCenter.y);
      const newCenter = calculateCenter(pose);
      const distAfter = Math.hypot(newNose.x - newCenter.x, newNose.y - newCenter.y);

      expect(distAfter).toBeCloseTo(distBefore * 2, 2);
    });
  });

  describe('rotatePose', () => {
    it('should rotate pose around center', () => {
      const pose = createTestPose();
      const centerBefore = calculateCenter(pose);

      rotatePose(pose, 90);

      // Center should remain the same
      const centerAfter = calculateCenter(pose);
      expect(centerAfter.x).toBeCloseTo(centerBefore.x, 2);
      expect(centerAfter.y).toBeCloseTo(centerBefore.y, 2);
    });
  });

  describe('translatePose', () => {
    it('should move all keypoints by offset', () => {
      const pose = createTestPose();
      const originalNose = { ...pose.keypoints[0] };

      translatePose(pose, 0.1, 0.2);

      expect(pose.keypoints[0].x).toBeCloseTo(originalNose.x + 0.1, 5);
      expect(pose.keypoints[0].y).toBeCloseTo(originalNose.y + 0.2, 5);
    });
  });

  describe('interpolatePoses', () => {
    it('should interpolate between two poses', () => {
      const pose1 = createTestPose();
      const pose2 = createTestPose();

      // Move pose2 to different position
      translatePose(pose2, 0.2, 0);

      const interpolated = interpolatePoses(pose1, pose2, 0.5);

      // Midpoint should be halfway
      expect(interpolated.keypoints[0].x).toBeCloseTo(
        (pose1.keypoints[0].x + pose2.keypoints[0].x) / 2,
        5
      );
    });

    it('should return pose1 at t=0', () => {
      const pose1 = createTestPose();
      const pose2 = createTestPose();
      translatePose(pose2, 0.5, 0);

      const interpolated = interpolatePoses(pose1, pose2, 0);

      expect(interpolated.keypoints[0].x).toBeCloseTo(pose1.keypoints[0].x, 5);
    });

    it('should return pose2 at t=1', () => {
      const pose1 = createTestPose();
      const pose2 = createTestPose();
      translatePose(pose2, 0.5, 0);

      const interpolated = interpolatePoses(pose1, pose2, 1);

      expect(interpolated.keypoints[0].x).toBeCloseTo(pose2.keypoints[0].x, 5);
    });
  });
});

describe('Pose Export - OpenPose JSON', () => {
  describe('exportToOpenPoseJSON', () => {
    it('should export pose in OpenPose format', () => {
      const pose = createTestPose();
      const json = exportToOpenPoseJSON([pose]);

      expect(json.version).toBe(1.3);
      expect(json.people.length).toBe(1);
      expect(json.people[0].pose_keypoints_2d.length).toBe(18 * 3); // x, y, confidence
    });

    it('should handle multiple poses', () => {
      const poses = [createTestPose(), createTestPose()];
      const json = exportToOpenPoseJSON(poses);

      expect(json.people.length).toBe(2);
    });

    it('should export keypoints in correct order', () => {
      const pose = createTestPose();
      const json = exportToOpenPoseJSON([pose]);
      const kp = json.people[0].pose_keypoints_2d;

      // First keypoint (nose)
      expect(kp[0]).toBe(pose.keypoints[0].x);
      expect(kp[1]).toBe(pose.keypoints[0].y);
      expect(kp[2]).toBe(pose.keypoints[0].confidence);
    });
  });

  describe('importFromOpenPoseJSON', () => {
    it('should import OpenPose JSON', () => {
      const original = createTestPose();
      const json = exportToOpenPoseJSON([original]);
      const imported = importFromOpenPoseJSON(json);

      expect(imported.length).toBe(1);
      expect(imported[0].keypoints.length).toBe(18);
    });

    it('should preserve keypoint values', () => {
      const original = createTestPose();
      const json = exportToOpenPoseJSON([original]);
      const imported = importFromOpenPoseJSON(json);

      for (let i = 0; i < 18; i++) {
        expect(imported[0].keypoints[i].x).toBeCloseTo(original.keypoints[i].x, 5);
        expect(imported[0].keypoints[i].y).toBeCloseTo(original.keypoints[i].y, 5);
        expect(imported[0].keypoints[i].confidence).toBeCloseTo(original.keypoints[i].confidence, 5);
      }
    });

    it('should handle empty people array', () => {
      const json = { version: 1.3, people: [] };
      const imported = importFromOpenPoseJSON(json);
      expect(imported.length).toBe(0);
    });
  });
});

describe('Pose Export - Rendering', () => {
  describe('renderPoseFrame', () => {
    it('should render to canvas with correct dimensions', () => {
      const pose = createTestPose();
      const config = createDefaultPoseExportConfig();
      config.width = 256;
      config.height = 256;

      const canvas = renderPoseFrame([pose], config);

      expect(canvas.width).toBe(256);
      expect(canvas.height).toBe(256);
    });

    it('should render black background by default', () => {
      const pose = createTestPose();
      const config = createDefaultPoseExportConfig();
      config.width = 100;
      config.height = 100;

      const canvas = renderPoseFrame([pose], config);
      const ctx = canvas.getContext('2d')!;
      const imageData = ctx.getImageData(0, 0, 1, 1);

      // Corner should be black
      expect(imageData.data[0]).toBeLessThan(10);
      expect(imageData.data[1]).toBeLessThan(10);
      expect(imageData.data[2]).toBeLessThan(10);
    });
  });

  describe('exportPoseForControlNet', () => {
    it('should return both canvas and JSON', () => {
      const pose = createTestPose();
      const result = exportPoseForControlNet([pose], 512, 512);

      expect(result.canvas).toBeDefined();
      expect(result.json).toBeDefined();
      expect(result.canvas.width).toBe(512);
      expect(result.canvas.height).toBe(512);
    });
  });
});

describe('Pose Export - Sequences', () => {
  describe('createPoseSequence', () => {
    it('should create sequence with correct frame count', () => {
      const pose1 = createTestPose();
      const pose2 = createTestPose();
      translatePose(pose2, 0.2, 0);

      const sequence = createPoseSequence([
        { frame: 0, poses: [pose1] },
        { frame: 30, poses: [pose2] }
      ], 31);

      expect(sequence.frames.length).toBe(31);
    });

    it('should interpolate between keyframes', () => {
      const pose1 = createTestPose();
      const pose2 = createTestPose();
      translatePose(pose2, 0.2, 0);

      const sequence = createPoseSequence([
        { frame: 0, poses: [pose1] },
        { frame: 30, poses: [pose2] }
      ], 31);

      // Frame 15 should be halfway
      const frame15 = sequence.frames[15];
      expect(frame15.poses[0].keypoints[0].x).toBeCloseTo(
        (pose1.keypoints[0].x + pose2.keypoints[0].x) / 2,
        2
      );
    });
  });

  describe('exportPoseSequence', () => {
    it('should export images when requested', () => {
      const pose = createTestPose();
      const sequence = createPoseSequence([{ frame: 0, poses: [pose] }], 5);
      const config = createDefaultPoseExportConfig();
      config.startFrame = 0;
      config.endFrame = 4;
      config.outputFormat = 'images';

      const result = exportPoseSequence(sequence, config);

      expect(result.images).toBeDefined();
      expect(result.images!.length).toBe(5);
    });

    it('should export JSON when requested', () => {
      const pose = createTestPose();
      const sequence = createPoseSequence([{ frame: 0, poses: [pose] }], 5);
      const config = createDefaultPoseExportConfig();
      config.startFrame = 0;
      config.endFrame = 4;
      config.outputFormat = 'json';

      const result = exportPoseSequence(sequence, config);

      expect(result.jsonFrames).toBeDefined();
      expect(result.jsonFrames!.length).toBe(5);
      expect(result.sequenceJson).toBeDefined();
      expect(result.sequenceJson!.metadata.frameCount).toBe(5);
    });

    it('should export both when requested', () => {
      const pose = createTestPose();
      const sequence = createPoseSequence([{ frame: 0, poses: [pose] }], 3);
      const config = createDefaultPoseExportConfig();
      config.startFrame = 0;
      config.endFrame = 2;
      config.outputFormat = 'both';

      const result = exportPoseSequence(sequence, config);

      expect(result.images).toBeDefined();
      expect(result.jsonFrames).toBeDefined();
    });
  });

  describe('importPoseSequence', () => {
    it('should import sequence from JSON array', () => {
      const pose = createTestPose();
      const jsonFrames = [
        exportToOpenPoseJSON([pose]),
        exportToOpenPoseJSON([pose]),
        exportToOpenPoseJSON([pose])
      ];

      const sequence = importPoseSequence(jsonFrames, 16);

      expect(sequence.frames.length).toBe(3);
      expect(sequence.fps).toBe(16);
      expect(sequence.format).toBe('coco18');
    });
  });
});

describe('Pose Export - Config', () => {
  describe('createDefaultPoseExportConfig', () => {
    it('should create config with reasonable defaults', () => {
      const config = createDefaultPoseExportConfig();

      expect(config.width).toBe(512);
      expect(config.height).toBe(512);
      expect(config.boneWidth).toBe(4);
      expect(config.keypointRadius).toBe(4);
      expect(config.showKeypoints).toBe(true);
      expect(config.showBones).toBe(true);
      expect(config.useOpenPoseColors).toBe(true);
      expect(config.backgroundColor).toBe('#000000');
    });
  });
});

// Helper function
function calculateCenter(pose: Pose): { x: number; y: number } {
  let sumX = 0, sumY = 0, count = 0;
  for (const kp of pose.keypoints) {
    if (kp.confidence > 0.1) {
      sumX += kp.x;
      sumY += kp.y;
      count++;
    }
  }
  return { x: sumX / count, y: sumY / count };
}
