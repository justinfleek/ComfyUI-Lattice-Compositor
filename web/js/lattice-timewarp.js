function createSpeedRampPreset(preset, layerStartFrame, layerDuration, fps = 16) {
  const midFrame = layerStartFrame + layerDuration / 2;
  const endFrame = layerStartFrame + layerDuration;
  const impactFrame = layerStartFrame + layerDuration * 0.3;
  const baseProperty = {
    id: `prop_timewarp_speed_${Date.now()}`,
    name: "Timewarp Speed",
    value: 100,
    type: "number",
    animated: true,
    keyframes: []
  };
  switch (preset) {
    case "slow-fast":
      baseProperty.keyframes = [
        {
          id: `kf_${Date.now()}_1`,
          frame: layerStartFrame,
          value: 25,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: 0, enabled: true },
          outHandle: { frame: 10, value: 20, enabled: true }
        },
        {
          id: `kf_${Date.now()}_2`,
          frame: endFrame,
          value: 200,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: -20, enabled: true },
          outHandle: { frame: 10, value: 0, enabled: true }
        }
      ];
      break;
    case "fast-slow":
      baseProperty.keyframes = [
        {
          id: `kf_${Date.now()}_1`,
          frame: layerStartFrame,
          value: 200,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: 0, enabled: true },
          outHandle: { frame: 10, value: -20, enabled: true }
        },
        {
          id: `kf_${Date.now()}_2`,
          frame: endFrame,
          value: 25,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: 20, enabled: true },
          outHandle: { frame: 10, value: 0, enabled: true }
        }
      ];
      break;
    case "slow-fast-slow":
      baseProperty.keyframes = [
        {
          id: `kf_${Date.now()}_1`,
          frame: layerStartFrame,
          value: 25,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: 0, enabled: true },
          outHandle: { frame: 10, value: 0, enabled: true }
        },
        {
          id: `kf_${Date.now()}_2`,
          frame: midFrame,
          value: 200,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: 0, enabled: true },
          outHandle: { frame: 10, value: 0, enabled: true }
        },
        {
          id: `kf_${Date.now()}_3`,
          frame: endFrame,
          value: 25,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: 0, enabled: true },
          outHandle: { frame: 10, value: 0, enabled: true }
        }
      ];
      break;
    case "impact":
      baseProperty.keyframes = [
        {
          id: `kf_${Date.now()}_1`,
          frame: layerStartFrame,
          value: 100,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true }
        },
        {
          id: `kf_${Date.now()}_2`,
          frame: impactFrame - fps * 0.1,
          value: 100,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -3, value: 0, enabled: true },
          outHandle: { frame: 3, value: -30, enabled: true }
        },
        {
          id: `kf_${Date.now()}_3`,
          frame: impactFrame,
          value: 10,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -3, value: 30, enabled: true },
          outHandle: { frame: 3, value: 30, enabled: true }
        },
        {
          id: `kf_${Date.now()}_4`,
          frame: impactFrame + fps * 0.3,
          value: 100,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -3, value: -30, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true }
        }
      ];
      break;
    case "rewind":
      baseProperty.keyframes = [
        {
          id: `kf_${Date.now()}_1`,
          frame: layerStartFrame,
          value: 100,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true }
        },
        {
          id: `kf_${Date.now()}_2`,
          frame: layerStartFrame + layerDuration * 0.3,
          value: 100,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 3, value: -50, enabled: true }
        },
        {
          id: `kf_${Date.now()}_3`,
          frame: midFrame,
          value: -150,
          // Reverse at 1.5x speed
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -3, value: 50, enabled: true },
          outHandle: { frame: 3, value: 50, enabled: true }
        },
        {
          id: `kf_${Date.now()}_4`,
          frame: layerStartFrame + layerDuration * 0.7,
          value: 100,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -3, value: -50, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true }
        }
      ];
      break;
  }
  return baseProperty;
}

export { createSpeedRampPreset };
