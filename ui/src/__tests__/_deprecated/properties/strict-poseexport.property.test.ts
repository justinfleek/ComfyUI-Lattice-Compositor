/**
 * STRICT Property Tests: Pose Export
 * 
 * Tests OpenPose JSON format compatibility for ControlNet conditioning.
 * Working backwards from model requirements:
 * 
 * OpenPose JSON Format:
 * {
 *   "version": 1.3,
 *   "people": [{
 *     "person_id": [-1],
 *     "pose_keypoints_2d": [x1, y1, c1, x2, y2, c2, ...], // 18*3 = 54 values
 *     "face_keypoints_2d": [],
 *     "hand_left_keypoints_2d": [],
 *     "hand_right_keypoints_2d": [],
 *     "pose_keypoints_3d": [],
 *     "face_keypoints_3d": [],
 *     "hand_left_keypoints_3d": [],
 *     "hand_right_keypoints_3d": []
 *   }]
 * }
 * 
 * COCO-18 Keypoints:
 * 0: nose, 1: neck, 2-4: right arm, 5-7: left arm, 
 * 8-10: right leg, 11-13: left leg, 14-17: face
 */

import { describe, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  renderPoseFrame,
  createPoseSequence,
  exportToOpenPoseJSON,
  exportPoseSequence,
  exportPoseForControlNet,
  importFromOpenPoseJSON,
  importPoseSequence,
  createDefaultPoseExportConfig,
  type PoseExportConfig,
  type OpenPoseJSON,
  type PoseSequence,
  type PoseFrame,
} from '@/services/export/poseExport';
import type { Pose, PoseKeypoint } from '@/engine/layers/PoseLayer';

// ============================================================================
// ARBITRARIES
// ============================================================================

// Generate a valid keypoint with normalized coordinates
const arbitraryKeypoint = (): fc.Arbitrary<PoseKeypoint> =>
  fc.record({
    x: fc.double({ min: 0, max: 1, noNaN: true }),
    y: fc.double({ min: 0, max: 1, noNaN: true }),
    confidence: fc.double({ min: 0, max: 1, noNaN: true }),
  });

// Generate COCO-18 pose (18 keypoints)
const arbitraryPose = (): fc.Arbitrary<Pose> =>
  fc.record({
    id: fc.uuid(),
    keypoints: fc.array(arbitraryKeypoint(), { minLength: 18, maxLength: 18 }),
    format: fc.constant('coco18' as const),
  });

// Generate multiple poses (for multi-person scenes)
const arbitraryPoses = (maxPeople: number = 5): fc.Arbitrary<Pose[]> =>
  fc.array(arbitraryPose(), { minLength: 1, maxLength: maxPeople });

// Generate pose export config
const arbitraryPoseExportConfig = (): fc.Arbitrary<PoseExportConfig> =>
  fc.record({
    width: fc.integer({ min: 64, max: 2048 }),
    height: fc.integer({ min: 64, max: 2048 }),
    startFrame: fc.integer({ min: 0, max: 100 }),
    endFrame: fc.integer({ min: 10, max: 200 }),
    boneWidth: fc.integer({ min: 1, max: 20 }),
    keypointRadius: fc.integer({ min: 1, max: 20 }),
    showKeypoints: fc.boolean(),
    showBones: fc.boolean(),
    useOpenPoseColors: fc.boolean(),
    customColor: fc.hexaString({ minLength: 6, maxLength: 6 }).map(s => `#${s}`),
    backgroundColor: fc.hexaString({ minLength: 6, maxLength: 6 }).map(s => `#${s}`),
    outputFormat: fc.constantFrom('images', 'json', 'both'),
  }).filter(c => c.endFrame > c.startFrame);

// Generate OpenPose JSON directly (for import tests)
const arbitraryOpenPoseJSON = (numPeople: number = 1): fc.Arbitrary<OpenPoseJSON> =>
  fc.record({
    version: fc.constant(1.3),
    people: fc.array(
      fc.record({
        person_id: fc.constant([-1]),
        pose_keypoints_2d: fc.array(
          fc.double({ min: 0, max: 1, noNaN: true }),
          { minLength: 54, maxLength: 54 } // 18 keypoints * 3 values
        ),
        face_keypoints_2d: fc.constant([]),
        hand_left_keypoints_2d: fc.constant([]),
        hand_right_keypoints_2d: fc.constant([]),
        pose_keypoints_3d: fc.constant([]),
        face_keypoints_3d: fc.constant([]),
        hand_left_keypoints_3d: fc.constant([]),
        hand_right_keypoints_3d: fc.constant([]),
      }),
      { minLength: numPeople, maxLength: numPeople }
    ),
  });

// ============================================================================
// OPENPOSE JSON FORMAT TESTS
// ============================================================================

describe('STRICT: OpenPose JSON Format', () => {
  test.prop([arbitraryPoses()])('exported JSON has correct version', (poses) => {
    const json = exportToOpenPoseJSON(poses);
    
    expect(json.version).toBe(1.3);
  });

  test.prop([arbitraryPoses()])('exported JSON has people array', (poses) => {
    const json = exportToOpenPoseJSON(poses);
    
    expect(Array.isArray(json.people)).toBe(true);
    expect(json.people.length).toBe(poses.length);
  });

  test.prop([arbitraryPose()])('each person has all required fields', (pose) => {
    const json = exportToOpenPoseJSON([pose]);
    const person = json.people[0];
    
    // Required fields per OpenPose spec
    expect(person).toHaveProperty('person_id');
    expect(person).toHaveProperty('pose_keypoints_2d');
    expect(person).toHaveProperty('face_keypoints_2d');
    expect(person).toHaveProperty('hand_left_keypoints_2d');
    expect(person).toHaveProperty('hand_right_keypoints_2d');
    expect(person).toHaveProperty('pose_keypoints_3d');
    expect(person).toHaveProperty('face_keypoints_3d');
    expect(person).toHaveProperty('hand_left_keypoints_3d');
    expect(person).toHaveProperty('hand_right_keypoints_3d');
  });

  test.prop([arbitraryPose()])('pose_keypoints_2d has exactly 54 values (18*3)', (pose) => {
    const json = exportToOpenPoseJSON([pose]);
    const keypoints = json.people[0].pose_keypoints_2d;
    
    // COCO-18 format: 18 keypoints * 3 values (x, y, confidence) = 54
    expect(keypoints.length).toBe(54);
  });

  test.prop([arbitraryPose()])('keypoint values are in correct order: x, y, confidence', (pose) => {
    const json = exportToOpenPoseJSON([pose]);
    const keypoints = json.people[0].pose_keypoints_2d;
    
    for (let i = 0; i < 18; i++) {
      const x = keypoints[i * 3];
      const y = keypoints[i * 3 + 1];
      const confidence = keypoints[i * 3 + 2];
      
      // Values should match input pose
      expect(x).toBe(pose.keypoints[i].x);
      expect(y).toBe(pose.keypoints[i].y);
      expect(confidence).toBe(pose.keypoints[i].confidence);
    }
  });

  test.prop([arbitraryPose()])('all keypoint coordinates are finite numbers', (pose) => {
    const json = exportToOpenPoseJSON([pose]);
    const keypoints = json.people[0].pose_keypoints_2d;
    
    for (const value of keypoints) {
      expect(Number.isFinite(value)).toBe(true);
      expect(Number.isNaN(value)).toBe(false);
    }
  });

  test.prop([arbitraryPose()])('confidence values are in [0, 1] range', (pose) => {
    const json = exportToOpenPoseJSON([pose]);
    const keypoints = json.people[0].pose_keypoints_2d;
    
    for (let i = 2; i < keypoints.length; i += 3) {
      const confidence = keypoints[i];
      expect(confidence).toBeGreaterThanOrEqual(0);
      expect(confidence).toBeLessThanOrEqual(1);
    }
  });

  test.prop([fc.integer({ min: 1, max: 10 })])('multi-person export preserves all people', (numPeople) => {
    const poses: Pose[] = [];
    for (let i = 0; i < numPeople; i++) {
      poses.push({
        id: `person_${i}`,
        keypoints: Array(18).fill(null).map(() => ({ x: 0.5, y: 0.5, confidence: 1.0 })),
        format: 'coco18',
      });
    }
    
    const json = exportToOpenPoseJSON(poses);
    expect(json.people.length).toBe(numPeople);
  });
});

// ============================================================================
// JSON IMPORT/EXPORT ROUNDTRIP TESTS
// ============================================================================

describe('STRICT: Pose Import/Export Roundtrip', () => {
  test.prop([arbitraryPoses()])('import(export(poses)) preserves keypoint count', (poses) => {
    const json = exportToOpenPoseJSON(poses);
    const imported = importFromOpenPoseJSON(json);
    
    expect(imported.length).toBe(poses.length);
    
    for (let i = 0; i < poses.length; i++) {
      expect(imported[i].keypoints.length).toBe(poses[i].keypoints.length);
    }
  });

  test.prop([arbitraryPose()])('import(export(pose)) preserves coordinates', (pose) => {
    const json = exportToOpenPoseJSON([pose]);
    const imported = importFromOpenPoseJSON(json);
    
    expect(imported.length).toBe(1);
    
    for (let i = 0; i < pose.keypoints.length; i++) {
      expect(imported[0].keypoints[i].x).toBeCloseTo(pose.keypoints[i].x, 10);
      expect(imported[0].keypoints[i].y).toBeCloseTo(pose.keypoints[i].y, 10);
      expect(imported[0].keypoints[i].confidence).toBeCloseTo(pose.keypoints[i].confidence, 10);
    }
  });

  test.prop([arbitraryOpenPoseJSON()])('import from valid OpenPose JSON succeeds', (json) => {
    const poses = importFromOpenPoseJSON(json);
    
    expect(poses.length).toBe(json.people.length);
    
    for (const pose of poses) {
      expect(pose.format).toBe('coco18');
      expect(pose.keypoints.length).toBe(18);
    }
  });

  test('import handles empty people array', () => {
    const json: OpenPoseJSON = {
      version: 1.3,
      people: [],
    };
    
    const poses = importFromOpenPoseJSON(json);
    expect(poses.length).toBe(0);
  });

  test('import handles empty keypoints', () => {
    const json: OpenPoseJSON = {
      version: 1.3,
      people: [{
        person_id: [-1],
        pose_keypoints_2d: [],
        face_keypoints_2d: [],
        hand_left_keypoints_2d: [],
        hand_right_keypoints_2d: [],
        pose_keypoints_3d: [],
        face_keypoints_3d: [],
        hand_left_keypoints_3d: [],
        hand_right_keypoints_3d: [],
      }],
    };
    
    const poses = importFromOpenPoseJSON(json);
    // Should handle gracefully - either empty poses or skip person
    expect(poses.length).toBeLessThanOrEqual(1);
  });
});

// ============================================================================
// POSE SEQUENCE TESTS
// ============================================================================

describe('STRICT: Pose Sequence Animation', () => {
  test.prop([
    arbitraryPoses(),
    arbitraryPoses(),
    fc.integer({ min: 2, max: 100 }),
  ])('sequence has correct frame count', (poses1, poses2, totalFrames) => {
    const keyframes = [
      { frame: 0, poses: poses1 },
      { frame: totalFrames - 1, poses: poses2 },
    ];
    
    const sequence = createPoseSequence(keyframes, totalFrames);
    
    expect(sequence.frames.length).toBe(totalFrames);
  });

  test.prop([
    arbitraryPoses(),
    fc.integer({ min: 10, max: 100 }),
    fc.integer({ min: 1, max: 60 }),
  ])('sequence frames are numbered correctly', (poses, totalFrames, fps) => {
    const keyframes = [{ frame: 0, poses }];
    
    const sequence = createPoseSequence(keyframes, totalFrames, fps);
    
    for (let i = 0; i < sequence.frames.length; i++) {
      expect(sequence.frames[i].frameNumber).toBe(i);
    }
  });

  test.prop([
    arbitraryPoses(),
    fc.integer({ min: 1, max: 60 }),
  ])('sequence stores fps correctly', (poses, fps) => {
    const keyframes = [{ frame: 0, poses }];
    
    const sequence = createPoseSequence(keyframes, 10, fps);
    
    expect(sequence.fps).toBe(fps);
  });

  test('interpolation produces valid intermediate poses', () => {
    const startPose: Pose = {
      id: 'test',
      keypoints: Array(18).fill(null).map(() => ({ x: 0, y: 0, confidence: 1.0 })),
      format: 'coco18',
    };
    
    const endPose: Pose = {
      id: 'test',
      keypoints: Array(18).fill(null).map(() => ({ x: 1, y: 1, confidence: 1.0 })),
      format: 'coco18',
    };
    
    const sequence = createPoseSequence([
      { frame: 0, poses: [startPose] },
      { frame: 10, poses: [endPose] },
    ], 11);
    
    // Middle frame should be interpolated
    const midFrame = sequence.frames[5];
    expect(midFrame.poses[0].keypoints[0].x).toBeCloseTo(0.5, 2);
    expect(midFrame.poses[0].keypoints[0].y).toBeCloseTo(0.5, 2);
  });
});

// ============================================================================
// POSE RENDERING TESTS
// ============================================================================

describe('STRICT: Pose Frame Rendering', () => {
  // NOTE: Canvas rendering tests are in browser/poseExport.browser.test.ts
  
  test('default config has correct values', () => {
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

// ============================================================================
// CONTROLNET EXPORT TESTS
// ============================================================================

describe('STRICT: ControlNet Export', () => {
  test.prop([
    arbitraryPoses(),
    fc.integer({ min: 64, max: 2048 }),
    fc.integer({ min: 64, max: 2048 }),
  ])('exportPoseForControlNet returns both canvas and json', (poses, width, height) => {
    // Skip if no document (Node environment)
    if (typeof document === 'undefined') return;
    
    const result = exportPoseForControlNet(poses, width, height);
    
    expect(result).toHaveProperty('canvas');
    expect(result).toHaveProperty('json');
    expect(result.json.version).toBe(1.3);
    expect(result.json.people.length).toBe(poses.length);
  });
});

// ============================================================================
// POSE SEQUENCE EXPORT TESTS
// ============================================================================

describe('STRICT: Full Pose Sequence Export', () => {
  test('exportPoseSequence with json format returns correct structure', () => {
    const pose: Pose = {
      id: 'test',
      keypoints: Array(18).fill(null).map(() => ({ x: 0.5, y: 0.5, confidence: 1.0 })),
      format: 'coco18',
    };
    
    const sequence: PoseSequence = {
      frames: [
        { frameNumber: 0, poses: [pose] },
        { frameNumber: 1, poses: [pose] },
        { frameNumber: 2, poses: [pose] },
      ],
      format: 'coco18',
      fps: 16,
    };
    
    const config = createDefaultPoseExportConfig();
    config.startFrame = 0;
    config.endFrame = 2;
    config.outputFormat = 'json';
    
    const result = exportPoseSequence(sequence, config);
    
    expect(result.jsonFrames).toBeDefined();
    expect(result.jsonFrames!.length).toBe(3);
    expect(result.sequenceJson).toBeDefined();
    expect(result.sequenceJson!.metadata.frameCount).toBe(3);
    expect(result.sequenceJson!.metadata.fps).toBe(16);
  });

  test('exportPoseSequence filters by frame range', () => {
    const pose: Pose = {
      id: 'test',
      keypoints: Array(18).fill(null).map(() => ({ x: 0.5, y: 0.5, confidence: 1.0 })),
      format: 'coco18',
    };
    
    const sequence: PoseSequence = {
      frames: Array(100).fill(null).map((_, i) => ({ frameNumber: i, poses: [pose] })),
      format: 'coco18',
      fps: 16,
    };
    
    const config = createDefaultPoseExportConfig();
    config.startFrame = 10;
    config.endFrame = 20;
    config.outputFormat = 'json';
    
    const result = exportPoseSequence(sequence, config);
    
    expect(result.jsonFrames!.length).toBe(11); // Frames 10-20 inclusive
    expect(result.sequenceJson!.metadata.frameCount).toBe(11);
  });
});

// ============================================================================
// POSE SEQUENCE IMPORT TESTS
// ============================================================================

describe('STRICT: Pose Sequence Import', () => {
  test.prop([
    fc.array(arbitraryOpenPoseJSON(), { minLength: 1, maxLength: 100 }),
    fc.integer({ min: 1, max: 60 }),
  ])('importPoseSequence creates correct frame count', (jsonFrames, fps) => {
    const sequence = importPoseSequence(jsonFrames, fps);
    
    expect(sequence.frames.length).toBe(jsonFrames.length);
    expect(sequence.fps).toBe(fps);
    expect(sequence.format).toBe('coco18');
  });

  test.prop([
    fc.array(arbitraryOpenPoseJSON(), { minLength: 1, maxLength: 50 }),
  ])('imported frames are numbered sequentially', (jsonFrames) => {
    const sequence = importPoseSequence(jsonFrames);
    
    for (let i = 0; i < sequence.frames.length; i++) {
      expect(sequence.frames[i].frameNumber).toBe(i);
    }
  });
});

// ============================================================================
// EDGE CASE TESTS
// ============================================================================

describe('STRICT: Pose Export Edge Cases', () => {
  test('handles zero confidence keypoints', () => {
    const pose: Pose = {
      id: 'test',
      keypoints: Array(18).fill(null).map(() => ({ x: 0.5, y: 0.5, confidence: 0 })),
      format: 'coco18',
    };
    
    const json = exportToOpenPoseJSON([pose]);
    
    // Should still export all keypoints
    expect(json.people[0].pose_keypoints_2d.length).toBe(54);
    
    // All confidence values should be 0
    for (let i = 2; i < 54; i += 3) {
      expect(json.people[0].pose_keypoints_2d[i]).toBe(0);
    }
  });

  test('handles boundary coordinate values', () => {
    const pose: Pose = {
      id: 'test',
      keypoints: [
        { x: 0, y: 0, confidence: 1 },        // Top-left
        { x: 1, y: 0, confidence: 1 },        // Top-right
        { x: 0, y: 1, confidence: 1 },        // Bottom-left
        { x: 1, y: 1, confidence: 1 },        // Bottom-right
        ...Array(14).fill(null).map(() => ({ x: 0.5, y: 0.5, confidence: 1 })),
      ],
      format: 'coco18',
    };
    
    const json = exportToOpenPoseJSON([pose]);
    const kp = json.people[0].pose_keypoints_2d;
    
    expect(kp[0]).toBe(0);  // x1
    expect(kp[1]).toBe(0);  // y1
    expect(kp[3]).toBe(1);  // x2
    expect(kp[4]).toBe(0);  // y2
    expect(kp[6]).toBe(0);  // x3
    expect(kp[7]).toBe(1);  // y3
    expect(kp[9]).toBe(1);  // x4
    expect(kp[10]).toBe(1); // y4
  });

  test('JSON stringification produces valid JSON', () => {
    const pose: Pose = {
      id: 'test',
      keypoints: Array(18).fill(null).map(() => ({ x: 0.5, y: 0.5, confidence: 1.0 })),
      format: 'coco18',
    };
    
    const json = exportToOpenPoseJSON([pose]);
    
    // Should not throw
    const stringified = JSON.stringify(json);
    const parsed = JSON.parse(stringified);
    
    expect(parsed.version).toBe(1.3);
    expect(parsed.people.length).toBe(1);
    expect(parsed.people[0].pose_keypoints_2d.length).toBe(54);
  });
});

// ============================================================================
// COCO KEYPOINT MAPPING TESTS
// ============================================================================

describe('STRICT: COCO-18 Keypoint Mapping', () => {
  const EXPECTED_KEYPOINT_ORDER = [
    'nose',           // 0
    'neck',           // 1
    'right_shoulder', // 2
    'right_elbow',    // 3
    'right_wrist',    // 4
    'left_shoulder',  // 5
    'left_elbow',     // 6
    'left_wrist',     // 7
    'right_hip',      // 8
    'right_knee',     // 9
    'right_ankle',    // 10
    'left_hip',       // 11
    'left_knee',      // 12
    'left_ankle',     // 13
    'right_eye',      // 14
    'left_eye',       // 15
    'right_ear',      // 16
    'left_ear',       // 17
  ];

  test('exactly 18 keypoints are exported', () => {
    const pose: Pose = {
      id: 'test',
      keypoints: Array(18).fill(null).map((_, i) => ({ 
        x: i / 17, 
        y: i / 17, 
        confidence: 1.0 
      })),
      format: 'coco18',
    };
    
    const json = exportToOpenPoseJSON([pose]);
    
    // 18 keypoints * 3 values = 54
    expect(json.people[0].pose_keypoints_2d.length).toBe(54);
    expect(EXPECTED_KEYPOINT_ORDER.length).toBe(18);
  });

  test('keypoints maintain index mapping', () => {
    // Create pose with unique positions for each keypoint
    const pose: Pose = {
      id: 'test',
      keypoints: EXPECTED_KEYPOINT_ORDER.map((_, i) => ({
        x: (i + 1) / 100,  // Unique x: 0.01, 0.02, ..., 0.18
        y: (i + 1) / 100,  // Unique y: 0.01, 0.02, ..., 0.18
        confidence: 1.0,
      })),
      format: 'coco18',
    };
    
    const json = exportToOpenPoseJSON([pose]);
    const kp = json.people[0].pose_keypoints_2d;
    
    // Verify each keypoint is at expected index
    for (let i = 0; i < 18; i++) {
      const expectedX = (i + 1) / 100;
      const actualX = kp[i * 3];
      expect(actualX).toBeCloseTo(expectedX, 10);
    }
  });
});
