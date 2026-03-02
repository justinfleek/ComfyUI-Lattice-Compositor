// FFI implementation for Lattice.Services.Export.Pose
// Renders pose skeletons to canvas for ControlNet conditioning

"use strict";

// COCO bone connections
const COCO_BONES = [
  [0, 1], [0, 2], [1, 3], [2, 4],           // Head
  [5, 6], [5, 7], [7, 9], [6, 8], [8, 10],  // Arms
  [5, 11], [6, 12], [11, 12],               // Torso
  [11, 13], [13, 15], [12, 14], [14, 16]    // Legs
];

// OpenPose colors
const OPENPOSE_COLORS = {
  head: "#FF0000",
  right_arm: "#FF7F00",
  left_arm: "#00FF00",
  right_leg: "#0000FF",
  left_leg: "#FF00FF",
  torso: "#00FFFF"
};

// Get bone color by index
function getBoneColor(idx) {
  if (idx < 4) return OPENPOSE_COLORS.head;
  if (idx < 9) return idx % 2 === 0 ? OPENPOSE_COLORS.right_arm : OPENPOSE_COLORS.left_arm;
  if (idx < 12) return OPENPOSE_COLORS.torso;
  if (idx < 14) return OPENPOSE_COLORS.right_leg;
  return OPENPOSE_COLORS.left_leg;
}

// Get keypoint color
function getKeypointColor(index, useOpenPoseColors, customColor) {
  if (!useOpenPoseColors) {
    return customColor || "#FFFFFF";
  }

  if (index <= 1 || (index >= 14 && index <= 17)) {
    return OPENPOSE_COLORS.head;
  } else if (index >= 2 && index <= 4) {
    return OPENPOSE_COLORS.right_arm;
  } else if (index >= 5 && index <= 7) {
    return OPENPOSE_COLORS.left_arm;
  } else if ([8, 9, 10].includes(index)) {
    return OPENPOSE_COLORS.right_leg;
  } else if ([11, 12, 13].includes(index)) {
    return OPENPOSE_COLORS.left_leg;
  }
  return "#FFFFFF";
}

// Render single pose skeleton
function renderSinglePose(ctx, pose, config) {
  const { keypoints } = pose;
  const { width, height, boneWidth, keypointRadius, showKeypoints, showBones, useOpenPoseColors, customColor } = config;

  // Convert normalized coords to pixels
  const toPixel = (kp) => ({
    x: kp.x * width,
    y: kp.y * height,
    visible: kp.confidence > 0.1
  });

  // Render bones
  if (showBones) {
    ctx.lineCap = "round";
    ctx.lineWidth = boneWidth;

    COCO_BONES.forEach((bone, boneIndex) => {
      const [startIdx, endIdx] = bone;
      if (startIdx >= keypoints.length || endIdx >= keypoints.length) return;

      const start = toPixel(keypoints[startIdx]);
      const end = toPixel(keypoints[endIdx]);

      if (!start.visible || !end.visible) return;

      ctx.strokeStyle = useOpenPoseColors
        ? getBoneColor(boneIndex)
        : (customColor || "#FFFFFF");

      ctx.beginPath();
      ctx.moveTo(start.x, start.y);
      ctx.lineTo(end.x, end.y);
      ctx.stroke();
    });
  }

  // Render keypoints
  if (showKeypoints) {
    keypoints.forEach((kp, index) => {
      const point = toPixel(kp);
      if (!point.visible) return;

      ctx.fillStyle = getKeypointColor(index, useOpenPoseColors, customColor);
      ctx.beginPath();
      ctx.arc(point.x, point.y, keypointRadius, 0, Math.PI * 2);
      ctx.fill();
    });
  }
}

// Render pose frame to canvas
export const renderPoseFrameImpl = function(poses) {
  return function(config) {
    return function() {
      const canvas = document.createElement("canvas");
      canvas.width = config.width;
      canvas.height = config.height;
      const ctx = canvas.getContext("2d");

      if (!ctx) {
        throw new Error("Could not get 2D context");
      }

      // Fill background
      ctx.fillStyle = config.backgroundColor;
      ctx.fillRect(0, 0, config.width, config.height);

      // Render each pose
      for (const pose of poses) {
        renderSinglePose(ctx, pose, config);
      }

      return canvas;
    };
  };
};
