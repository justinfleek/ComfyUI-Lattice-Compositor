// FFI bindings for Lattice.Services.Video.FrameInterpolation
// Canvas operations and API calls for frame interpolation

// Fetch available interpolation models
export const getModelsImpl = (url) => () =>
  fetch(url)
    .then(res => {
      if (!res.ok) throw new Error(`HTTP ${res.status}`);
      return res.json();
    })
    .then(data => data.models || []);

// Interpolate a pair of frames via API
export const interpolatePairImpl =
  (url) => (frame1) => (frame2) => (model) => (factor) => (ensemble) => (fastMode) => () =>
    fetch(url, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        frame1,
        frame2,
        model,
        factor,
        ensemble,
        fastMode
      })
    })
      .then(res => {
        if (!res.ok) throw new Error(`HTTP ${res.status}`);
        return res.json();
      })
      .then(data => ({
        success: true,
        frames: data.frames || [],
        processingTime: data.processingTime || 0,
        modelUsed: data.model || model,
        error: null
      }))
      .catch(err => ({
        success: false,
        frames: [],
        processingTime: 0,
        modelUsed: model,
        error: err.message
      }));

// Interpolate a sequence of frames via API
export const interpolateSequenceImpl =
  (url) => (frames) => (model) => (factor) => (ensemble) => (fastMode) => (preserveOriginal) => () =>
    fetch(url, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        frames,
        model,
        factor,
        ensemble,
        fastMode,
        preserveOriginal
      })
    })
      .then(res => {
        if (!res.ok) throw new Error(`HTTP ${res.status}`);
        return res.json();
      })
      .then(data => ({
        success: true,
        originalFrameCount: frames.length,
        outputFrameCount: data.frames?.length || 0,
        frames: data.frames || [],
        totalProcessingTime: data.totalProcessingTime || 0,
        averageTimePerPair: data.averageTimePerPair || 0,
        error: null
      }))
      .catch(err => ({
        success: false,
        originalFrameCount: frames.length,
        outputFrameCount: 0,
        frames: [],
        totalProcessingTime: 0,
        averageTimePerPair: 0,
        error: err.message
      }));

// Create slow motion via API
export const createSlowMotionImpl =
  (url) => (frames) => (model) => (slowdownFactor) => (targetFps) => (sourceFps) => (ensemble) => (fastMode) => () =>
    fetch(url, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        frames,
        model,
        slowdownFactor,
        targetFps,
        sourceFps,
        ensemble,
        fastMode
      })
    })
      .then(res => {
        if (!res.ok) throw new Error(`HTTP ${res.status}`);
        return res.json();
      })
      .then(data => ({
        success: true,
        slowdownFactor,
        originalFps: sourceFps,
        outputFps: targetFps,
        frames: data.frames || [],
        totalProcessingTime: data.totalProcessingTime || 0,
        error: null
      }))
      .catch(err => ({
        success: false,
        slowdownFactor,
        originalFps: sourceFps,
        outputFps: targetFps,
        frames: [],
        totalProcessingTime: 0,
        error: err.message
      }));

// Convert frame element to base64
export const frameToBase64Impl = (elementId) => (format) => (quality) => () => {
  const element = document.getElementById(elementId);
  if (!element) return "";

  const canvas = document.createElement("canvas");
  const ctx = canvas.getContext("2d");

  if (element instanceof HTMLCanvasElement) {
    canvas.width = element.width;
    canvas.height = element.height;
    ctx.drawImage(element, 0, 0);
  } else if (element instanceof HTMLImageElement) {
    canvas.width = element.naturalWidth;
    canvas.height = element.naturalHeight;
    ctx.drawImage(element, 0, 0);
  } else if (element instanceof HTMLVideoElement) {
    canvas.width = element.videoWidth;
    canvas.height = element.videoHeight;
    ctx.drawImage(element, 0, 0);
  } else {
    return "";
  }

  return canvas.toDataURL(format, quality);
};

// Convert base64 to ImageData
export const base64ToImageDataImpl = (base64) => () =>
  new Promise((resolve, reject) => {
    const img = new Image();
    img.onload = () => {
      const canvas = document.createElement("canvas");
      canvas.width = img.width;
      canvas.height = img.height;
      const ctx = canvas.getContext("2d");
      ctx.drawImage(img, 0, 0);
      resolve(ctx.getImageData(0, 0, img.width, img.height));
    };
    img.onerror = () => reject(new Error("Failed to load image"));
    img.src = base64;
  });

// Convert base64 to Blob
export const base64ToBlobImpl = (base64) => (mimeType) => () => {
  // Remove data URL prefix if present
  const base64Data = base64.includes(",") ? base64.split(",")[1] : base64;

  const byteCharacters = atob(base64Data);
  const byteNumbers = new Array(byteCharacters.length);

  for (let i = 0; i < byteCharacters.length; i++) {
    byteNumbers[i] = byteCharacters.charCodeAt(i);
  }

  const byteArray = new Uint8Array(byteNumbers);
  return new Blob([byteArray], { type: mimeType });
};

// Blend two frames at a given ratio (client-side fallback)
export const blendFramesImpl = (frame1) => (frame2) => (ratio) => () =>
  new Promise((resolve, reject) => {
    const img1 = new Image();
    const img2 = new Image();
    let loaded = 0;

    const checkLoaded = () => {
      loaded++;
      if (loaded === 2) {
        try {
          const canvas = document.createElement("canvas");
          canvas.width = Math.max(img1.width, img2.width);
          canvas.height = Math.max(img1.height, img2.height);
          const ctx = canvas.getContext("2d");

          // Draw first frame
          ctx.globalAlpha = 1 - ratio;
          ctx.drawImage(img1, 0, 0, canvas.width, canvas.height);

          // Blend second frame
          ctx.globalAlpha = ratio;
          ctx.drawImage(img2, 0, 0, canvas.width, canvas.height);

          resolve(canvas.toDataURL("image/png"));
        } catch (err) {
          reject(err);
        }
      }
    };

    img1.onload = checkLoaded;
    img2.onload = checkLoaded;
    img1.onerror = () => reject(new Error("Failed to load frame 1"));
    img2.onerror = () => reject(new Error("Failed to load frame 2"));

    img1.src = frame1;
    img2.src = frame2;
  });

// Client-side interpolation between frames (simple blending)
export const interpolateClientImpl = (frame1) => (frame2) => (count) => () =>
  new Promise((resolve, reject) => {
    const img1 = new Image();
    const img2 = new Image();
    let loaded = 0;

    const checkLoaded = () => {
      loaded++;
      if (loaded === 2) {
        try {
          const results = [];
          const canvas = document.createElement("canvas");
          canvas.width = Math.max(img1.width, img2.width);
          canvas.height = Math.max(img1.height, img2.height);
          const ctx = canvas.getContext("2d");

          for (let i = 1; i <= count; i++) {
            const ratio = i / (count + 1);

            // Clear canvas
            ctx.clearRect(0, 0, canvas.width, canvas.height);

            // Draw first frame
            ctx.globalAlpha = 1 - ratio;
            ctx.drawImage(img1, 0, 0, canvas.width, canvas.height);

            // Blend second frame
            ctx.globalAlpha = ratio;
            ctx.drawImage(img2, 0, 0, canvas.width, canvas.height);

            results.push(canvas.toDataURL("image/png"));
          }

          resolve(results);
        } catch (err) {
          reject(err);
        }
      }
    };

    img1.onload = checkLoaded;
    img2.onload = checkLoaded;
    img1.onerror = () => reject(new Error("Failed to load frame 1"));
    img2.onerror = () => reject(new Error("Failed to load frame 2"));

    img1.src = frame1;
    img2.src = frame2;
  });
