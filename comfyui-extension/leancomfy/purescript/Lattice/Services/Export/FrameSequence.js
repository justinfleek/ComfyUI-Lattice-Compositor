// FFI implementation for Lattice.Services.Export.FrameSequence
// Frame sequence export with ZIP packaging

"use strict";

// Dynamic import for JSZip
let JSZip = null;

async function loadJSZip() {
  if (JSZip === null) {
    const module = await import("jszip");
    JSZip = module.default;
  }
  return JSZip;
}

// MIME types for browser formats
const FORMAT_MIME = {
  png: "image/png",
  jpg: "image/jpeg",
  jpeg: "image/jpeg",
  webp: "image/webp"
};

// Export canvas to blob
export const exportCanvasToBlobImpl = function(canvas) {
  return function(format) {
    return function(quality) {
      return function(onError, onSuccess) {
        return function() {
          (async () => {
            try {
              const mime = FORMAT_MIME[format];
              if (!mime) {
                throw new Error("Format " + format + " not supported in browser");
              }

              const qualityValue = format === "png" ? undefined : quality / 100;

              let blob;
              if (canvas instanceof OffscreenCanvas) {
                blob = await canvas.convertToBlob({ type: mime, quality: qualityValue });
              } else {
                blob = await new Promise((resolve, reject) => {
                  canvas.toBlob(
                    (b) => {
                      if (b) resolve(b);
                      else reject(new Error("Failed to create blob"));
                    },
                    mime,
                    qualityValue
                  );
                });
              }

              onSuccess(blob)();
            } catch (err) {
              onError(err)();
            }
          })();
        };
      };
    };
  };
};

// Export canvas to data URL
export const exportCanvasToDataURL = function(canvas) {
  return function(format) {
    return function(quality) {
      return function() {
        const mime = FORMAT_MIME[format];
        if (!mime) {
          throw new Error("Format " + format + " not supported in browser");
        }
        const qualityValue = format === "png" ? undefined : quality / 100;
        return canvas.toDataURL(mime, qualityValue);
      };
    };
  };
};

// Download blob
export const downloadBlob = function(blob) {
  return function(filename) {
    return function() {
      const url = URL.createObjectURL(blob);
      const a = document.createElement("a");
      a.href = url;
      a.download = filename;
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      URL.revokeObjectURL(url);
    };
  };
};

// Create ZIP from frames
export const createZipFromFramesImpl = function(frames) {
  return function(folderName) {
    return function(compressionLevel) {
      return function(onError, onSuccess) {
        return function() {
          (async () => {
            try {
              const JSZipLib = await loadJSZip();
              const zip = new JSZipLib();
              const folder = zip.folder(folderName);

              if (!folder) {
                throw new Error("Failed to create ZIP folder");
              }

              for (const frame of frames) {
                if (frame.blob) {
                  folder.file(frame.filename, frame.blob, {
                    compression: "DEFLATE",
                    compressionOptions: { level: compressionLevel }
                  });
                }
              }

              const blob = await zip.generateAsync({
                type: "blob",
                compression: "DEFLATE",
                compressionOptions: { level: compressionLevel }
              });

              onSuccess(blob)();
            } catch (err) {
              onError(err)();
            }
          })();
        };
      };
    };
  };
};

// Export frame sequence
export const exportFrameSequenceImpl = function(renderFrame) {
  return function(options) {
    return function(onProgress) {
      return function(onError, onSuccess) {
        return function() {
          (async () => {
            try {
              const result = {
                success: true,
                frames: [],
                totalSize: 0,
                errors: [],
                warnings: []
              };

              const { format, quality, filenamePattern, startFrame, endFrame } = options;
              const totalFrames = endFrame - startFrame + 1;
              const isBrowser = ["png", "jpg", "jpeg", "webp"].includes(formatToString(format));

              if (isBrowser) {
                for (let frame = startFrame; frame <= endFrame; frame++) {
                  try {
                    // Call PureScript Aff render function
                    const canvas = await new Promise((resolve, reject) => {
                      renderFrame(frame)(reject, resolve)();
                    });

                    const mime = FORMAT_MIME[formatToString(format)] || "image/png";
                    const qualityValue = formatToString(format) === "png" ? undefined : quality / 100;

                    const blob = await new Promise((resolve, reject) => {
                      if (canvas instanceof OffscreenCanvas) {
                        canvas.convertToBlob({ type: mime, quality: qualityValue })
                          .then(resolve)
                          .catch(reject);
                      } else {
                        canvas.toBlob(
                          (b) => {
                            if (b) resolve(b);
                            else reject(new Error("Failed to create blob"));
                          },
                          mime,
                          qualityValue
                        );
                      }
                    });

                    const filename = generateFilenameJS(filenamePattern, frame, formatToString(format));

                    result.frames.push({
                      frameNumber: frame,
                      filename,
                      blob,
                      dataUrl: null,
                      size: blob.size
                    });

                    result.totalSize += blob.size;
                    onProgress(frame - startFrame + 1)(totalFrames)();
                  } catch (error) {
                    const errorMessage = error instanceof Error ? error.message : String(error);
                    result.errors.push("Frame " + frame + ": " + errorMessage);
                  }
                }

                if (result.frames.length === 0) {
                  throw new Error("No frames exported. All frames failed.");
                }

                result.success = result.errors.length === 0;
              } else {
                result.warnings.push(formatToString(format).toUpperCase() + " export requires backend processing");
                // Backend export would need to be implemented separately
                throw new Error("Backend formats not yet implemented in PureScript FFI");
              }

              onSuccess(result)();
            } catch (err) {
              onError(err)();
            }
          })();
        };
      };
    };
  };
};

// Export via backend
export const exportViaBackendImpl = function(frames) {
  return function(options) {
    return function(backendUrl) {
      return function(onError, onSuccess) {
        return function() {
          (async () => {
            try {
              const frameData = [];

              for (const { canvas, frameNumber } of frames) {
                const dataUrl = canvas.toDataURL("image/png");
                frameData.push({ frame: frameNumber, data: dataUrl });
              }

              const response = await fetch(backendUrl, {
                method: "POST",
                headers: { "Content-Type": "application/json" },
                body: JSON.stringify({
                  frames: frameData,
                  format: formatToString(options.format),
                  bitDepth: options.bitDepth || 16,
                  colorSpace: colorSpaceToString(options.colorSpace),
                  filenamePattern: options.filenamePattern,
                  outputDir: options.outputDir
                })
              });

              if (!response.ok) {
                throw new Error("Backend export failed: " + response.statusText);
              }

              const data = await response.json();

              if (data.success) {
                onSuccess({
                  success: true,
                  frames: data.frames || [],
                  totalSize: data.totalSize || 0,
                  errors: [],
                  warnings: []
                })();
              } else {
                throw new Error("Backend export failed: " + (data.errors || ["Unknown error"]).join("; "));
              }
            } catch (err) {
              onError(err)();
            }
          })();
        };
      };
    };
  };
};

// Helper: format ADT to string
function formatToString(format) {
  if (format.tag === "FormatPNG") return "png";
  if (format.tag === "FormatJPEG") return "jpg";
  if (format.tag === "FormatWebP") return "webp";
  if (format.tag === "FormatTIFF") return "tiff";
  if (format.tag === "FormatEXR") return "exr";
  if (format.tag === "FormatDPX") return "dpx";
  // Constructor-based
  if (format.constructor && format.constructor.name === "FormatPNG") return "png";
  if (format.constructor && format.constructor.name === "FormatJPEG") return "jpg";
  if (format.constructor && format.constructor.name === "FormatWebP") return "webp";
  if (format.constructor && format.constructor.name === "FormatTIFF") return "tiff";
  if (format.constructor && format.constructor.name === "FormatEXR") return "exr";
  if (format.constructor && format.constructor.name === "FormatDPX") return "dpx";
  return "png";
}

// Helper: colorspace ADT to string
function colorSpaceToString(colorSpace) {
  if (!colorSpace) return "sRGB";
  if (colorSpace.tag === "ColorSRGB") return "sRGB";
  if (colorSpace.tag === "ColorLinear") return "Linear";
  if (colorSpace.tag === "ColorACEScg") return "ACEScg";
  if (colorSpace.tag === "ColorRec709") return "Rec709";
  return "sRGB";
}

// Helper: generate filename
function generateFilenameJS(pattern, frame, format) {
  const base = pattern.replace(/\{frame:(\d+)d\}/g, (_, digits) => {
    return frame.toString().padStart(parseInt(digits, 10), "0");
  });
  return base + "." + format;
}
