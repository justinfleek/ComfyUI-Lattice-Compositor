//                                                                       // ffi
// Canvas-based video transition rendering

// Power function for easing
export const js_pow = (base) => (exponent) => Math.pow(base, exponent);

// Blend mode functions
function blendMultiply(a, b) {
  return (a * b) / 255;
}

function blendScreen(a, b) {
  return 255 - ((255 - a) * (255 - b)) / 255;
}

function blendOverlay(a, b) {
  if (a < 128) {
    return (2 * a * b) / 255;
  } else {
    return 255 - (2 * (255 - a) * (255 - b)) / 255;
  }
}

function blendSoftLight(a, b) {
  const t = (b / 255) * a + ((255 - b) / 255) * blendScreen(a, a);
  return Math.round(t);
}

function blendAdd(a, b) {
  return Math.min(255, a + b);
}

function blendSubtract(a, b) {
  return Math.max(0, a - b);
}

// Render normal (linear) crossfade
function renderNormalTransition(ctx, fromData, toData, progress) {
  const data = ctx.createImageData(fromData.width, fromData.height);
  const from = fromData.data;
  const to = toData.data;
  const out = data.data;

  for (let i = 0; i < from.length; i += 4) {
    out[i] = from[i] * (1 - progress) + to[i] * progress;
    out[i + 1] = from[i + 1] * (1 - progress) + to[i + 1] * progress;
    out[i + 2] = from[i + 2] * (1 - progress) + to[i + 2] * progress;
    out[i + 3] = from[i + 3] * (1 - progress) + to[i + 3] * progress;
  }

  ctx.putImageData(data, 0, 0);
}

// Render blend mode transition
function renderBlendTransition(ctx, fromData, toData, progress, blendFn) {
  const data = ctx.createImageData(fromData.width, fromData.height);
  const from = fromData.data;
  const to = toData.data;
  const out = data.data;

  for (let i = 0; i < from.length; i += 4) {
    const blendR = blendFn(from[i], to[i]);
    const blendG = blendFn(from[i + 1], to[i + 1]);
    const blendB = blendFn(from[i + 2], to[i + 2]);

    out[i] = from[i] * (1 - progress) + blendR * progress;
    out[i + 1] = from[i + 1] * (1 - progress) + blendG * progress;
    out[i + 2] = from[i + 2] * (1 - progress) + blendB * progress;
    out[i + 3] = from[i + 3] * (1 - progress) + to[i + 3] * progress;
  }

  ctx.putImageData(data, 0, 0);
}

// Render dissolve transition
function renderDissolveTransition(ctx, fromData, toData, progress, seed) {
  const data = ctx.createImageData(fromData.width, fromData.height);
  const from = fromData.data;
  const to = toData.data;
  const out = data.data;

  let state = seed;
  const random = () => {
    state = (state * 1103515245 + 12345) & 0x7fffffff;
    return state / 0x7fffffff;
  };

  for (let i = 0; i < from.length; i += 4) {
    const useTarget = random() < progress;
    if (useTarget) {
      out[i] = to[i];
      out[i + 1] = to[i + 1];
      out[i + 2] = to[i + 2];
      out[i + 3] = to[i + 3];
    } else {
      out[i] = from[i];
      out[i + 1] = from[i + 1];
      out[i + 2] = from[i + 2];
      out[i + 3] = from[i + 3];
    }
  }

  ctx.putImageData(data, 0, 0);
}

// Render directional wipe transition
function renderWipeTransition(ctx, fromData, toData, progress, direction, softness) {
  const { width, height } = fromData;
  const data = ctx.createImageData(width, height);
  const from = fromData.data;
  const to = toData.data;
  const out = data.data;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;

      let localProgress;
      switch (direction) {
        case "left":
          localProgress = (width - x) / width;
          break;
        case "right":
          localProgress = x / width;
          break;
        case "up":
          localProgress = (height - y) / height;
          break;
        case "down":
          localProgress = y / height;
          break;
        default:
          localProgress = x / width;
      }

      const edgeStart = progress - softness / 2;
      const edgeEnd = progress + softness / 2;
      let blend;

      if (localProgress < edgeStart) {
        blend = 1;
      } else if (localProgress > edgeEnd) {
        blend = 0;
      } else {
        blend = 1 - (localProgress - edgeStart) / softness;
      }

      out[i] = from[i] * (1 - blend) + to[i] * blend;
      out[i + 1] = from[i + 1] * (1 - blend) + to[i + 1] * blend;
      out[i + 2] = from[i + 2] * (1 - blend) + to[i + 2] * blend;
      out[i + 3] = from[i + 3] * (1 - blend) + to[i + 3] * blend;
    }
  }

  ctx.putImageData(data, 0, 0);
}

// Render radial wipe transition
function renderRadialWipeTransition(ctx, fromData, toData, progress, centerX, centerY, softness) {
  const { width, height } = fromData;
  const data = ctx.createImageData(width, height);
  const from = fromData.data;
  const to = toData.data;
  const out = data.data;

  const cx = width * centerX;
  const cy = height * centerY;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;

      const angle = Math.atan2(y - cy, x - cx);
      const normalizedAngle = (angle + Math.PI) / (2 * Math.PI);

      const edgeStart = progress - softness;
      const edgeEnd = progress;
      let blend;

      if (normalizedAngle < edgeStart) {
        blend = 1;
      } else if (normalizedAngle > edgeEnd) {
        blend = 0;
      } else {
        blend = 1 - (normalizedAngle - edgeStart) / softness;
      }

      out[i] = from[i] * (1 - blend) + to[i] * blend;
      out[i + 1] = from[i + 1] * (1 - blend) + to[i + 1] * blend;
      out[i + 2] = from[i + 2] * (1 - blend) + to[i + 2] * blend;
      out[i + 3] = from[i + 3] * (1 - blend) + to[i + 3] * blend;
    }
  }

  ctx.putImageData(data, 0, 0);
}

// Render iris transition
function renderIrisTransition(ctx, fromData, toData, progress, direction, centerX, centerY, softness) {
  const { width, height } = fromData;
  const data = ctx.createImageData(width, height);
  const from = fromData.data;
  const to = toData.data;
  const out = data.data;

  const cx = width * centerX;
  const cy = height * centerY;
  const maxRadius = Math.sqrt(width * width + height * height) / 2;

  const effectiveProgress = direction === "in" ? progress : 1 - progress;
  const targetRadius = maxRadius * effectiveProgress;
  const softnessRadius = maxRadius * softness;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;
      const dist = Math.sqrt((x - cx) ** 2 + (y - cy) ** 2);

      let blend;
      if (dist < targetRadius - softnessRadius / 2) {
        blend = direction === "in" ? 1 : 0;
      } else if (dist > targetRadius + softnessRadius / 2) {
        blend = direction === "in" ? 0 : 1;
      } else {
        const t = (dist - (targetRadius - softnessRadius / 2)) / softnessRadius;
        blend = direction === "in" ? 1 - t : t;
      }

      out[i] = from[i] * (1 - blend) + to[i] * blend;
      out[i + 1] = from[i + 1] * (1 - blend) + to[i + 1] * blend;
      out[i + 2] = from[i + 2] * (1 - blend) + to[i + 2] * blend;
      out[i + 3] = from[i + 3] * (1 - blend) + to[i + 3] * blend;
    }
  }

  ctx.putImageData(data, 0, 0);
}

// Main render transition implementation
export const renderTransitionImpl =
  (fromCanvasId) => (toCanvasId) => (progress) => (blendMode) =>
  (softness) => (centerX) => (centerY) => (seed) => () => {
    const fromCanvas = document.getElementById(fromCanvasId);
    const toCanvas = document.getElementById(toCanvasId);

    if (!fromCanvas || !toCanvas) {
      throw new Error(`Canvas elements not found: ${fromCanvasId}, ${toCanvasId}`);
    }

    const { width, height } = fromCanvas;

    // Create output canvas
    const output = document.createElement("canvas");
    output.width = width;
    output.height = height;
    const ctx = output.getContext("2d");
    if (!ctx) {
      throw new Error("Failed to get 2d context");
    }

    // Get image data from both canvases
    const fromCtx = fromCanvas.getContext("2d");
    const toCtx = toCanvas.getContext("2d");
    if (!fromCtx || !toCtx) {
      throw new Error("Failed to get source contexts");
    }

    const fromData = fromCtx.getImageData(0, 0, width, height);
    const toData = toCtx.getImageData(0, 0, width, height);

    // Render based on blend mode
    switch (blendMode) {
      case "normal":
        renderNormalTransition(ctx, fromData, toData, progress);
        break;

      case "multiply":
        renderBlendTransition(ctx, fromData, toData, progress, blendMultiply);
        break;

      case "screen":
        renderBlendTransition(ctx, fromData, toData, progress, blendScreen);
        break;

      case "overlay":
        renderBlendTransition(ctx, fromData, toData, progress, blendOverlay);
        break;

      case "soft-light":
        renderBlendTransition(ctx, fromData, toData, progress, blendSoftLight);
        break;

      case "add":
        renderBlendTransition(ctx, fromData, toData, progress, blendAdd);
        break;

      case "subtract":
        renderBlendTransition(ctx, fromData, toData, progress, blendSubtract);
        break;

      case "dissolve":
        renderDissolveTransition(ctx, fromData, toData, progress, seed);
        break;

      case "wipe-left":
        renderWipeTransition(ctx, fromData, toData, progress, "left", softness);
        break;

      case "wipe-right":
        renderWipeTransition(ctx, fromData, toData, progress, "right", softness);
        break;

      case "wipe-up":
        renderWipeTransition(ctx, fromData, toData, progress, "up", softness);
        break;

      case "wipe-down":
        renderWipeTransition(ctx, fromData, toData, progress, "down", softness);
        break;

      case "radial-wipe":
        renderRadialWipeTransition(ctx, fromData, toData, progress, centerX, centerY, softness);
        break;

      case "iris-in":
        renderIrisTransition(ctx, fromData, toData, progress, "in", centerX, centerY, softness);
        break;

      case "iris-out":
        renderIrisTransition(ctx, fromData, toData, progress, "out", centerX, centerY, softness);
        break;

      case "cross-zoom":
        // Simplified version - full implementation would need GPU
        renderNormalTransition(ctx, fromData, toData, progress);
        break;

      default:
        renderNormalTransition(ctx, fromData, toData, progress);
    }

    return output;
  };
