const BT709_R = 0.2126;
const BT709_G = 0.7152;
const BT709_B = 0.0722;
self.onmessage = (e) => {
  const { type, payload } = e.data;
  if (type === "analyze") {
    try {
      const result = {};
      const { imageData, width, height, scopes } = payload;
      const pixels = imageData;
      if (scopes.includes("histogram")) {
        result.histogram = computeHistogram(pixels, width, height);
      }
      if (scopes.includes("waveform")) {
        result.waveform = computeWaveform(pixels, width, height);
      }
      if (scopes.includes("vectorscope")) {
        result.vectorscope = computeVectorscope(pixels, width, height);
      }
      if (scopes.includes("parade")) {
        result.parade = computeParade(pixels, width, height);
      }
      self.postMessage({ type: "complete", payload: result });
    } catch (error) {
      self.postMessage({
        type: "error",
        payload: {
          error: error instanceof Error ? error.message : "Unknown error",
        },
      });
    }
  }
};
function computeHistogram(pixels, _width, _height) {
  const red = new Array(256).fill(0);
  const green = new Array(256).fill(0);
  const blue = new Array(256).fill(0);
  const luminance = new Array(256).fill(0);
  let maxCount = 0;
  for (let i = 0; i < pixels.length; i += 4) {
    const r = pixels[i];
    const g = pixels[i + 1];
    const b = pixels[i + 2];
    red[r]++;
    green[g]++;
    blue[b]++;
    const lum = Math.round(BT709_R * r + BT709_G * g + BT709_B * b);
    luminance[Math.min(255, lum)]++;
  }
  for (let i = 0; i < 256; i++) {
    maxCount = Math.max(maxCount, red[i], green[i], blue[i], luminance[i]);
  }
  return { red, green, blue, luminance, maxCount };
}
function computeWaveform(pixels, width, height) {
  const sampleRate = Math.max(1, Math.floor(width / 256));
  const sampledWidth = Math.ceil(width / sampleRate);
  const points = [];
  for (let sx = 0; sx < sampledWidth; sx++) {
    const x = sx * sampleRate;
    if (x >= width) continue;
    const ySampleRate = Math.max(1, Math.floor(height / 256));
    for (let sy = 0; sy < height; sy += ySampleRate) {
      const idx = (sy * width + x) * 4;
      const r = pixels[idx];
      const g = pixels[idx + 1];
      const b = pixels[idx + 2];
      const lum = BT709_R * r + BT709_G * g + BT709_B * b;
      const normalizedX = sx / sampledWidth;
      const normalizedY = 1 - lum / 255;
      points.push(normalizedX, normalizedY);
    }
  }
  return {
    lumaPoints: new Float32Array(points),
    width: sampledWidth,
    height: 256,
  };
}
function computeVectorscope(pixels, width, height) {
  const data = new Uint32Array(256 * 256);
  let maxCount = 0;
  const sampleRate = 2;
  for (let y = 0; y < height; y += sampleRate) {
    for (let x = 0; x < width; x += sampleRate) {
      const idx = (y * width + x) * 4;
      const r = pixels[idx] / 255;
      const g = pixels[idx + 1] / 255;
      const b = pixels[idx + 2] / 255;
      const Y = BT709_R * r + BT709_G * g + BT709_B * b;
      const U = (b - Y) * 0.5;
      const V = (r - Y) * 0.5;
      const uIdx = Math.round((U + 0.5) * 255);
      const vIdx = Math.round((V + 0.5) * 255);
      const uClamped = Math.max(0, Math.min(255, uIdx));
      const vClamped = Math.max(0, Math.min(255, vIdx));
      const gridIdx = (255 - vClamped) * 256 + uClamped;
      data[gridIdx]++;
      if (data[gridIdx] > maxCount) {
        maxCount = data[gridIdx];
      }
    }
  }
  const targets = calculateVectorscopeTargets();
  return { data, maxCount, targets };
}
function calculateVectorscopeTargets() {
  const colorToUV = (r, g, b) => {
    const Y = BT709_R * r + BT709_G * g + BT709_B * b;
    const U = (b - Y) * 0.5;
    const V = (r - Y) * 0.5;
    return [
      Math.round((U + 0.5) * 255),
      Math.round((0.5 - V) * 255),
      // Inverted V for display
    ];
  };
  return {
    r: colorToUV(1, 0, 0),
    // Red
    y: colorToUV(1, 1, 0),
    // Yellow
    g: colorToUV(0, 1, 0),
    // Green
    c: colorToUV(0, 1, 1),
    // Cyan
    b: colorToUV(0, 0, 1),
    // Blue
    m: colorToUV(1, 0, 1),
    // Magenta
    // Skin tone line (I-line) - approximately from center toward skin tones
    skinLine: [
      [128, 128],
      // Center
      [175, 95],
      // Toward typical skin tones
    ],
  };
}
function computeParade(pixels, width, height) {
  const sampleRate = Math.max(1, Math.floor(width / 256));
  const sampledWidth = Math.ceil(width / sampleRate);
  const ySampleRate = Math.max(1, Math.floor(height / 256));
  const redPoints = [];
  const greenPoints = [];
  const bluePoints = [];
  for (let sx = 0; sx < sampledWidth; sx++) {
    const x = sx * sampleRate;
    if (x >= width) continue;
    for (let sy = 0; sy < height; sy += ySampleRate) {
      const idx = (sy * width + x) * 4;
      const r = pixels[idx];
      const g = pixels[idx + 1];
      const b = pixels[idx + 2];
      const normalizedX = sx / sampledWidth;
      redPoints.push(normalizedX, 1 - r / 255);
      greenPoints.push(normalizedX, 1 - g / 255);
      bluePoints.push(normalizedX, 1 - b / 255);
    }
  }
  return {
    red: {
      lumaPoints: new Float32Array(redPoints),
      width: sampledWidth,
      height: 256,
    },
    green: {
      lumaPoints: new Float32Array(greenPoints),
      width: sampledWidth,
      height: 256,
    },
    blue: {
      lumaPoints: new Float32Array(bluePoints),
      width: sampledWidth,
      height: 256,
    },
  };
}
