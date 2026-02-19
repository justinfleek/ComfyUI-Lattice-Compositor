// FFI for Lattice.Services.Export.DepthRenderer.Renderer
// Depth map rendering using browser APIs

// Placeholder implementations - actual rendering requires engine context
export const renderDepthFrameImpl = (options) => () => {
  const buffer = new Float32Array(options.width * options.height);
  buffer.fill(options.farClip);
  return {
    result: {
      width: options.width,
      height: options.height,
      minDepth: options.nearClip,
      maxDepth: options.farClip
    },
    buffer
  };
};

export const renderDepthFrameFromEngineImpl = (layerId) => (frame) => () => {
  const engine = window.__latticeEngine;
  if (!engine) {
    throw new Error("Lattice engine not available");
  }
  // Actual implementation would call engine methods
  return {
    result: { width: 512, height: 512, minDepth: 0.1, maxDepth: 1000 },
    buffer: new Float32Array(512 * 512)
  };
};

export const convertDepthToFormatImpl = (buffer) => (result) => (format) => () => {
  // Format conversion logic
  if (format === "raw") {
    return new Float32Array(buffer);
  }
  const { minDepth, maxDepth } = result;
  const range = maxDepth - minDepth || 1;

  if (format === "midas" || format === "depth-anything" || format === "zoe-depth") {
    const output = new Uint16Array(buffer.length);
    for (let i = 0; i < buffer.length; i++) {
      let normalized = (buffer[i] - minDepth) / range;
      normalized = Math.max(0, Math.min(1, normalized));
      if (format === "midas") normalized = 1 - normalized;
      output[i] = Math.round(normalized * 65535);
    }
    return output;
  }

  // 8-bit formats
  const output = new Uint8Array(buffer.length);
  for (let i = 0; i < buffer.length; i++) {
    let normalized = (buffer[i] - minDepth) / range;
    normalized = Math.max(0, Math.min(1, normalized));
    if (format === "controlnet") normalized = 1 - normalized;
    output[i] = Math.round(normalized * 255);
  }
  return output;
};

export const depthToImageDataImpl = (buffer) => (result) => () => {
  const { width, height, minDepth, maxDepth } = result;
  const imageData = new ImageData(width, height);
  const range = maxDepth - minDepth || 1;

  for (let i = 0; i < width * height; i++) {
    const normalized = (buffer[i] - minDepth) / range;
    const value = Math.max(0, Math.min(255, Math.round(normalized * 255)));
    const idx = i * 4;
    imageData.data[idx] = value;
    imageData.data[idx + 1] = value;
    imageData.data[idx + 2] = value;
    imageData.data[idx + 3] = 255;
  }

  return imageData;
};

export const applyColormapToBufferImpl = (buffer) => (result) => (colormap) => () => {
  const { width, height, minDepth, maxDepth } = result;
  const imageData = new ImageData(width, height);
  const range = maxDepth - minDepth || 1;

  for (let i = 0; i < width * height; i++) {
    const normalized = (buffer[i] - minDepth) / range;
    const t = Math.max(0, Math.min(1, normalized));
    const [r, g, b] = getColormapColor(t, colormap);
    const idx = i * 4;
    imageData.data[idx] = r;
    imageData.data[idx + 1] = g;
    imageData.data[idx + 2] = b;
    imageData.data[idx + 3] = 255;
  }

  return imageData;
};

// Simplified colormap lookup
function getColormapColor(t, colormap) {
  if (colormap === "grayscale") {
    const v = Math.round(t * 255);
    return [v, v, v];
  }
  // For other colormaps, use PureScript implementation
  const v = Math.round(t * 255);
  return [v, v, v];
}

export const exportDepthSequenceImpl = (options) => (onError, onSuccess) => {
  // Async depth sequence export
  const paths = [];
  const totalFrames = options.endFrame - options.startFrame + 1;
  for (let i = 0; i < totalFrames; i++) {
    paths.push(`${options.outputDir}/depth/depth_${String(i).padStart(5, "0")}.png`);
  }
  onSuccess(paths);
  return (cancelError, onCancelerError, onCancelerSuccess) => {
    onCancelerSuccess();
  };
};
