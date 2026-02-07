// FFI implementation for Lattice.Services.Export.VideoEncoder
// Uses WebCodecs API with mp4-muxer/webm-muxer

"use strict";

// Dynamic imports for muxers (will be bundled)
let MP4Muxer = null;
let MP4Target = null;
let WebMMuxer = null;
let WebMTarget = null;

// Lazy load muxers
async function loadMuxers() {
  if (MP4Muxer === null) {
    const mp4 = await import("mp4-muxer");
    MP4Muxer = mp4.Muxer;
    MP4Target = mp4.ArrayBufferTarget;
  }
  if (WebMMuxer === null) {
    const webm = await import("webm-muxer");
    WebMMuxer = webm.Muxer;
    WebMTarget = webm.ArrayBufferTarget;
  }
}

// Encoder state storage
const encoderState = new WeakMap();

// Check if WebCodecs is supported
export const isWebCodecsSupported = function() {
  return typeof VideoEncoder !== "undefined" && typeof VideoFrame !== "undefined";
};

// Get supported codecs (async)
export const getSupportedCodecsImpl = function(onError, onSuccess) {
  return function() {
    (async () => {
      try {
        if (!isWebCodecsSupported()) {
          onSuccess([])();
          return;
        }

        const codecs = [];
        const testConfigs = [
          { codec: "avc1.42E01F", name: "avc" },
          { codec: "avc1.640028", name: "avc" },
          { codec: "vp9", name: "vp9" },
          { codec: "vp8", name: "vp8" }
        ];

        for (const { codec, name } of testConfigs) {
          try {
            const support = await VideoEncoder.isConfigSupported({
              codec,
              width: 1920,
              height: 1080,
              bitrate: 5000000
            });
            if (support.supported && !codecs.includes(name)) {
              codecs.push(name);
            }
          } catch (e) {
            // Not supported
          }
        }

        onSuccess(codecs)();
      } catch (err) {
        onError(err)();
      }
    })();
  };
};

// Get codec string for WebCodecs
function getCodecString(codec) {
  switch (codec) {
    case "avc": return "avc1.640028";
    case "vp9": return "vp09.00.10.08";
    case "vp8": return "vp8";
    default: return "avc1.640028";
  }
}

// Calculate bitrate based on resolution and quality
function calculateBitrate(width, height, frameRate, quality) {
  const pixels = width * height;
  const baseRate = pixels * frameRate;

  switch (quality) {
    case "low": return Math.round(baseRate * 0.05);
    case "medium": return Math.round(baseRate * 0.1);
    case "high": return Math.round(baseRate * 0.2);
    case "lossless": return Math.round(baseRate * 0.5);
    default: return Math.round(baseRate * 0.1);
  }
}

// Create encoder instance
export const createEncoderImpl = function(config) {
  return function() {
    const handle = {};
    encoderState.set(handle, {
      config: config,
      encoder: null,
      muxer: null,
      frameCount: 0,
      totalBytesWritten: 0,
      onProgress: null
    });
    return handle;
  };
};

// Initialize encoder (async)
export const initializeEncoderImpl = function(handle) {
  return function(onProgress) {
    return function(onError, onSuccess) {
      return function() {
        (async () => {
          try {
            const state = encoderState.get(handle);
            if (!state) {
              throw new Error("Invalid encoder handle");
            }

            if (!isWebCodecsSupported()) {
              throw new Error("WebCodecs API is not supported in this browser");
            }

            await loadMuxers();

            const { config } = state;
            state.onProgress = onProgress;
            state.frameCount = 0;
            state.totalBytesWritten = 0;

            const codecString = getCodecString(config.codec);
            const bitrate = config.bitrate !== null
              ? config.bitrate
              : calculateBitrate(config.width, config.height, config.frameRate, config.quality);

            // Check if configuration is supported
            const support = await VideoEncoder.isConfigSupported({
              codec: codecString,
              width: config.width,
              height: config.height,
              bitrate
            });

            if (!support.supported) {
              throw new Error("Unsupported encoder configuration: " + codecString);
            }

            // Initialize appropriate muxer
            if (config.codec === "avc") {
              state.muxer = new MP4Muxer({
                target: new MP4Target(),
                video: {
                  codec: "avc",
                  width: config.width,
                  height: config.height
                },
                fastStart: "in-memory"
              });
              state.muxerType = "mp4";
            } else {
              const webmCodec = config.codec === "vp9" ? "V_VP9" : "V_VP8";
              state.muxer = new WebMMuxer({
                target: new WebMTarget(),
                video: {
                  codec: webmCodec,
                  width: config.width,
                  height: config.height
                }
              });
              state.muxerType = "webm";
            }

            // Create encoder
            state.encoder = new VideoEncoder({
              output: (chunk, metadata) => {
                if (state.muxer) {
                  state.muxer.addVideoChunk(chunk, metadata);
                }
                state.totalBytesWritten += chunk.byteLength;
              },
              error: (error) => {
                console.error("VideoEncoder error:", error);
              }
            });

            state.encoder.configure({
              codec: codecString,
              width: config.width,
              height: config.height,
              bitrate,
              framerate: config.frameRate
            });

            onSuccess()();
          } catch (err) {
            onError(err)();
          }
        })();
      };
    };
  };
};

// Encode a single frame
export const encodeFrameImpl = function(handle) {
  return function(frameData) {
    return function(frameIndex) {
      return function(totalFrames) {
        return function(keyFrame) {
          return function(onError, onSuccess) {
            return function() {
              (async () => {
                try {
                  const state = encoderState.get(handle);
                  if (!state || !state.encoder) {
                    throw new Error("Encoder not initialized");
                  }

                  const { config } = state;
                  let frame;

                  // Create VideoFrame from various input types
                  if (frameData instanceof ImageData) {
                    frame = new VideoFrame(frameData.data, {
                      timestamp: (frameIndex * 1000000) / config.frameRate,
                      duration: 1000000 / config.frameRate,
                      codedWidth: frameData.width,
                      codedHeight: frameData.height,
                      format: "RGBA"
                    });
                  } else {
                    // Canvas or OffscreenCanvas
                    frame = new VideoFrame(frameData, {
                      timestamp: (frameIndex * 1000000) / config.frameRate,
                      duration: 1000000 / config.frameRate
                    });
                  }

                  // Encode frame
                  const isKeyFrame = keyFrame || frameIndex === 0 || frameIndex % 30 === 0;
                  state.encoder.encode(frame, { keyFrame: isKeyFrame });
                  frame.close();

                  state.frameCount++;

                  // Report progress
                  if (state.onProgress) {
                    state.onProgress({
                      framesEncoded: state.frameCount,
                      totalFrames: totalFrames,
                      percentage: (state.frameCount / totalFrames) * 100,
                      bytesWritten: state.totalBytesWritten
                    })();
                  }

                  onSuccess()();
                } catch (err) {
                  onError(err)();
                }
              })();
            };
          };
        };
      };
    };
  };
};

// Finalize encoding
export const finalizeEncoderImpl = function(handle) {
  return function(onError, onSuccess) {
    return function() {
      (async () => {
        try {
          const state = encoderState.get(handle);
          if (!state || !state.encoder) {
            throw new Error("Encoder not initialized");
          }

          // Flush remaining frames
          await state.encoder.flush();
          state.encoder.close();
          state.encoder = null;

          // Finalize muxer
          let blob;
          let mimeType;

          if (state.muxerType === "mp4") {
            state.muxer.finalize();
            const buffer = state.muxer.target.buffer;
            blob = new Blob([buffer], { type: "video/mp4" });
            mimeType = "video/mp4";
          } else {
            state.muxer.finalize();
            const buffer = state.muxer.target.buffer;
            blob = new Blob([buffer], { type: "video/webm" });
            mimeType = "video/webm";
          }

          state.muxer = null;

          const blobUrl = URL.createObjectURL(blob);

          onSuccess({
            blobUrl,
            mimeType,
            duration: state.frameCount / state.config.frameRate,
            frameCount: state.frameCount,
            size: blob.size
          })();
        } catch (err) {
          onError(err)();
        }
      })();
    };
  };
};

// Cancel encoding
export const cancelEncoderImpl = function(handle) {
  return function() {
    const state = encoderState.get(handle);
    if (state) {
      if (state.encoder) {
        state.encoder.close();
        state.encoder = null;
      }
      state.muxer = null;
    }
  };
};

// Encode frame sequence (convenience function)
export const encodeFrameSequenceImpl = function(frames) {
  return function(config) {
    return function(onProgress) {
      return function(onError, onSuccess) {
        return function() {
          (async () => {
            try {
              await loadMuxers();

              if (!isWebCodecsSupported()) {
                throw new Error("WebCodecs API is not supported in this browser");
              }

              const codecString = getCodecString(config.codec);
              const bitrate = config.bitrate !== null
                ? config.bitrate
                : calculateBitrate(config.width, config.height, config.frameRate, config.quality);

              // Check support
              const support = await VideoEncoder.isConfigSupported({
                codec: codecString,
                width: config.width,
                height: config.height,
                bitrate
              });

              if (!support.supported) {
                throw new Error("Unsupported encoder configuration: " + codecString);
              }

              // Initialize muxer
              let muxer;
              let muxerType;
              if (config.codec === "avc") {
                muxer = new MP4Muxer({
                  target: new MP4Target(),
                  video: {
                    codec: "avc",
                    width: config.width,
                    height: config.height
                  },
                  fastStart: "in-memory"
                });
                muxerType = "mp4";
              } else {
                const webmCodec = config.codec === "vp9" ? "V_VP9" : "V_VP8";
                muxer = new WebMMuxer({
                  target: new WebMTarget(),
                  video: {
                    codec: webmCodec,
                    width: config.width,
                    height: config.height
                  }
                });
                muxerType = "webm";
              }

              let frameCount = 0;
              let totalBytesWritten = 0;

              // Create encoder
              const encoder = new VideoEncoder({
                output: (chunk, metadata) => {
                  muxer.addVideoChunk(chunk, metadata);
                  totalBytesWritten += chunk.byteLength;
                },
                error: (error) => {
                  console.error("VideoEncoder error:", error);
                }
              });

              encoder.configure({
                codec: codecString,
                width: config.width,
                height: config.height,
                bitrate,
                framerate: config.frameRate
              });

              // Encode all frames
              const totalFrames = frames.length;
              for (let i = 0; i < totalFrames; i++) {
                const frameData = frames[i];
                let frame;

                if (frameData instanceof ImageData) {
                  frame = new VideoFrame(frameData.data, {
                    timestamp: (i * 1000000) / config.frameRate,
                    duration: 1000000 / config.frameRate,
                    codedWidth: frameData.width,
                    codedHeight: frameData.height,
                    format: "RGBA"
                  });
                } else {
                  frame = new VideoFrame(frameData, {
                    timestamp: (i * 1000000) / config.frameRate,
                    duration: 1000000 / config.frameRate
                  });
                }

                const isKeyFrame = i === 0 || i % 30 === 0;
                encoder.encode(frame, { keyFrame: isKeyFrame });
                frame.close();

                frameCount++;

                onProgress({
                  framesEncoded: frameCount,
                  totalFrames,
                  percentage: (frameCount / totalFrames) * 100,
                  bytesWritten: totalBytesWritten
                })();
              }

              // Finalize
              await encoder.flush();
              encoder.close();

              muxer.finalize();
              const buffer = muxer.target.buffer;
              const mimeType = muxerType === "mp4" ? "video/mp4" : "video/webm";
              const blob = new Blob([buffer], { type: mimeType });
              const blobUrl = URL.createObjectURL(blob);

              onSuccess({
                blobUrl,
                mimeType,
                duration: frameCount / config.frameRate,
                frameCount,
                size: blob.size
              })();
            } catch (err) {
              onError(err)();
            }
          })();
        };
      };
    };
  };
};

// Download video
export const downloadVideo = function(video) {
  return function(filename) {
    return function() {
      const extension = video.mimeType.includes("webm") ? "webm" : "mp4";
      const fullFilename = filename.includes(".")
        ? filename
        : filename + "." + extension;

      const a = document.createElement("a");
      a.href = video.blobUrl;
      a.download = fullFilename;
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
    };
  };
};

// Convert config to foreign
export const configToForeign = function(config) {
  return {
    width: config.width,
    height: config.height,
    frameRate: config.frameRate,
    codec: codecFromADT(config.codec),
    bitrate: config.bitrate,
    quality: qualityFromADT(config.quality)
  };
};

function codecFromADT(codec) {
  // PureScript ADT: CodecAVC | CodecVP9 | CodecVP8
  if (codec.constructor && codec.constructor.name === "CodecAVC") return "avc";
  if (codec.constructor && codec.constructor.name === "CodecVP9") return "vp9";
  if (codec.constructor && codec.constructor.name === "CodecVP8") return "vp8";
  // Tag-based representation
  if (codec.tag === "CodecAVC") return "avc";
  if (codec.tag === "CodecVP9") return "vp9";
  if (codec.tag === "CodecVP8") return "vp8";
  return "avc";
}

function qualityFromADT(quality) {
  if (quality.constructor && quality.constructor.name === "QualityLow") return "low";
  if (quality.constructor && quality.constructor.name === "QualityMedium") return "medium";
  if (quality.constructor && quality.constructor.name === "QualityHigh") return "high";
  if (quality.constructor && quality.constructor.name === "QualityLossless") return "lossless";
  if (quality.tag === "QualityLow") return "low";
  if (quality.tag === "QualityMedium") return "medium";
  if (quality.tag === "QualityHigh") return "high";
  if (quality.tag === "QualityLossless") return "lossless";
  return "medium";
}
