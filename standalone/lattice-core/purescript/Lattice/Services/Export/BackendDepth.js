//                                                                       // ffi
// Backend depth and normal map generation service

"use strict";

// Singleton service instance
let defaultService = null;

// Service state storage
const serviceState = new WeakMap();

// Helper: depth model to string
function depthModelToString(model) {
  if (model.tag === "DA3Large") return "DA3-LARGE-1.1";
  if (model.tag === "DA3Giant") return "DA3-GIANT-1.1";
  if (model.tag === "DA3NestedGiant") return "DA3NESTED-GIANT-LARGE-1.1";
  // Constructor-based
  if (model.constructor && model.constructor.name === "DA3Large") return "DA3-LARGE-1.1";
  if (model.constructor && model.constructor.name === "DA3Giant") return "DA3-GIANT-1.1";
  if (model.constructor && model.constructor.name === "DA3NestedGiant") return "DA3NESTED-GIANT-LARGE-1.1";
  return "DA3-LARGE-1.1";
}

// Helper: normal method to string
function normalMethodToString(method) {
  if (method.tag === "MethodAlgebraic") return "algebraic";
  if (method.tag === "MethodNormalCrafter") return "normalcrafter";
  if (method.constructor && method.constructor.name === "MethodAlgebraic") return "algebraic";
  if (method.constructor && method.constructor.name === "MethodNormalCrafter") return "normalcrafter";
  return "algebraic";
}

// Helper: unwrap Maybe
function unwrapMaybe(maybe) {
  if (maybe === null || maybe === undefined) return null;
  if (maybe.tag === "Nothing") return null;
  if (maybe.tag === "Just") return maybe.value0;
  // Constructor-based
  if (maybe.constructor && maybe.constructor.name === "Nothing") return null;
  if (maybe.constructor && maybe.constructor.name === "Just") return maybe.value0;
  return null;
}

// Create service
export const createServiceImpl = function(serverAddressMaybe) {
  return function() {
    const serverAddress = unwrapMaybe(serverAddressMaybe);
    const service = {};

    // Determine base URL
    let baseUrl;
    if (serverAddress) {
      baseUrl = "http://" + serverAddress;
    } else {
      // Try to get from ComfyUI client or use default
      baseUrl = "http://127.0.0.1:8188";
    }

    serviceState.set(service, { baseUrl });
    return service;
  };
};

// Get default service
export const getDefaultService = function() {
  if (!defaultService) {
    defaultService = {};
    serviceState.set(defaultService, { baseUrl: "http://127.0.0.1:8188" });
  }
  return defaultService;
};

// Generate depth
export const generateDepthImpl = function(service) {
  return function(imageBase64) {
    return function(options) {
      return function(onError, onSuccess) {
        return function() {
          (async () => {
            try {
              const state = serviceState.get(service);
              if (!state) {
                throw new Error("Invalid service handle");
              }

              const model = depthModelToString(options.model);
              const returnConfidence = options.returnConfidence;
              const returnIntrinsics = options.returnIntrinsics;

              const response = await fetch(state.baseUrl + "/lattice/depth", {
                method: "POST",
                headers: { "Content-Type": "application/json" },
                body: JSON.stringify({
                  image: imageBase64,
                  model,
                  return_confidence: returnConfidence,
                  return_intrinsics: returnIntrinsics
                })
              });

              if (!response.ok) {
                throw new Error("Depth API error: " + response.status + " " + response.statusText);
              }

              const result = await response.json();

              if (result.status === "error") {
                throw new Error(result.message || "Depth generation failed");
              }

              onSuccess({
                status: result.status || "success",
                depth: result.depth || "",
                confidence: result.confidence || null,
                intrinsics: result.intrinsics || null,
                fallback: result.fallback || false,
                message: result.message || null,
                metadata: result.metadata ? {
                  model: result.metadata.model || model,
                  width: result.metadata.width || 0,
                  height: result.metadata.height || 0,
                  depthMin: result.metadata.depth_min || null,
                  depthMax: result.metadata.depth_max || null
                } : null
              })();
            } catch (err) {
              const errorMsg = err instanceof Error ? err.message : String(err);
              onSuccess({
                status: "error",
                depth: "",
                confidence: null,
                intrinsics: null,
                fallback: false,
                message: errorMsg,
                metadata: null
              })();
            }
          })();
        };
      };
    };
  };
};

// Generate normal
export const generateNormalImpl = function(service) {
  return function(imageBase64Maybe) {
    return function(depthBase64Maybe) {
      return function(options) {
        return function(onError, onSuccess) {
          return function() {
            (async () => {
              try {
                const state = serviceState.get(service);
                if (!state) {
                  throw new Error("Invalid service handle");
                }

                const imageBase64 = unwrapMaybe(imageBase64Maybe);
                const depthBase64 = unwrapMaybe(depthBase64Maybe);

                if (!imageBase64 && !depthBase64) {
                  onSuccess({
                    status: "error",
                    normal: "",
                    depth: null,
                    fallback: false,
                    message: "Either image or depth must be provided",
                    metadata: null
                  })();
                  return;
                }

                const method = normalMethodToString(options.method);
                const depthModel = depthModelToString(options.depthModel);

                const requestBody = {
                  method,
                  depth_model: depthModel
                };

                if (imageBase64) {
                  requestBody.image = imageBase64;
                }
                if (depthBase64) {
                  requestBody.depth = depthBase64;
                }

                const response = await fetch(state.baseUrl + "/lattice/normal", {
                  method: "POST",
                  headers: { "Content-Type": "application/json" },
                  body: JSON.stringify(requestBody)
                });

                if (!response.ok) {
                  throw new Error("Normal API error: " + response.status + " " + response.statusText);
                }

                const result = await response.json();

                if (result.status === "error") {
                  throw new Error(result.message || "Normal generation failed");
                }

                onSuccess({
                  status: result.status || "success",
                  normal: result.normal || "",
                  depth: result.depth || null,
                  fallback: result.fallback || false,
                  message: result.message || null,
                  metadata: result.metadata ? {
                    method: result.metadata.method || method,
                    width: result.metadata.width || 0,
                    height: result.metadata.height || 0
                  } : null
                })();
              } catch (err) {
                const errorMsg = err instanceof Error ? err.message : String(err);
                onSuccess({
                  status: "error",
                  normal: "",
                  depth: null,
                  fallback: false,
                  message: errorMsg,
                  metadata: null
                })();
              }
            })();
          };
        };
      };
    };
  };
};

// Generate depth and normal
export const generateDepthAndNormalImpl = function(service) {
  return function(imageBase64) {
    return function(depthOptions) {
      return function(normalOptions) {
        return function(onError, onSuccess) {
          return function() {
            (async () => {
              try {
                const state = serviceState.get(service);
                if (!state) {
                  throw new Error("Invalid service handle");
                }

                // First generate depth
                const depthModel = depthModelToString(depthOptions.model);

                const depthResponse = await fetch(state.baseUrl + "/lattice/depth", {
                  method: "POST",
                  headers: { "Content-Type": "application/json" },
                  body: JSON.stringify({
                    image: imageBase64,
                    model: depthModel,
                    return_confidence: depthOptions.returnConfidence,
                    return_intrinsics: depthOptions.returnIntrinsics
                  })
                });

                let depthResult;
                if (!depthResponse.ok) {
                  depthResult = {
                    status: "error",
                    depth: "",
                    confidence: null,
                    intrinsics: null,
                    fallback: false,
                    message: "Depth API error: " + depthResponse.status,
                    metadata: null
                  };
                } else {
                  const dr = await depthResponse.json();
                  depthResult = {
                    status: dr.status || "success",
                    depth: dr.depth || "",
                    confidence: dr.confidence || null,
                    intrinsics: dr.intrinsics || null,
                    fallback: dr.fallback || false,
                    message: dr.message || null,
                    metadata: dr.metadata ? {
                      model: dr.metadata.model || depthModel,
                      width: dr.metadata.width || 0,
                      height: dr.metadata.height || 0,
                      depthMin: dr.metadata.depth_min || null,
                      depthMax: dr.metadata.depth_max || null
                    } : null
                  };
                }

                // If depth failed, return error for normal too
                if (depthResult.status === "error" || !depthResult.depth) {
                  onSuccess({
                    depth: depthResult,
                    normal: {
                      status: "error",
                      normal: "",
                      depth: null,
                      fallback: false,
                      message: "Cannot generate normal without depth",
                      metadata: null
                    }
                  })();
                  return;
                }

                // Generate normal using the depth
                const normalMethod = normalMethodToString(normalOptions.method);

                const normalResponse = await fetch(state.baseUrl + "/lattice/normal", {
                  method: "POST",
                  headers: { "Content-Type": "application/json" },
                  body: JSON.stringify({
                    method: normalMethod,
                    depth_model: depthModel,
                    depth: depthResult.depth
                  })
                });

                let normalResult;
                if (!normalResponse.ok) {
                  normalResult = {
                    status: "error",
                    normal: "",
                    depth: null,
                    fallback: false,
                    message: "Normal API error: " + normalResponse.status,
                    metadata: null
                  };
                } else {
                  const nr = await normalResponse.json();
                  normalResult = {
                    status: nr.status || "success",
                    normal: nr.normal || "",
                    depth: nr.depth || null,
                    fallback: nr.fallback || false,
                    message: nr.message || null,
                    metadata: nr.metadata ? {
                      method: nr.metadata.method || normalMethod,
                      width: nr.metadata.width || 0,
                      height: nr.metadata.height || 0
                    } : null
                  };
                }

                onSuccess({
                  depth: depthResult,
                  normal: normalResult
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
};

// Check availability
export const checkAvailabilityImpl = function(service) {
  return function(onError, onSuccess) {
    return function() {
      (async () => {
        try {
          const state = serviceState.get(service);
          if (!state) {
            throw new Error("Invalid service handle");
          }

          // Create a tiny test image (1x1 white pixel)
          const testImage = "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mP8/5/hPwAIAgL/4d1j8wAAAABJRU5ErkJggg==";

          const response = await fetch(state.baseUrl + "/lattice/depth", {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify({
              image: testImage,
              model: "DA3-LARGE-1.1"
            })
          });

          if (!response.ok) {
            onSuccess({
              depthAvailable: false,
              normalAvailable: false,
              fallbackOnly: true
            })();
            return;
          }

          const result = await response.json();
          const depthAvailable = result.status === "success";
          const fallbackOnly = result.fallback === true;

          onSuccess({
            depthAvailable,
            normalAvailable: depthAvailable,
            fallbackOnly
          })();
        } catch (err) {
          onSuccess({
            depthAvailable: false,
            normalAvailable: false,
            fallbackOnly: true
          })();
        }
      })();
    };
  };
};

// Canvas to base64
export const canvasToBase64 = function(canvas) {
  return function() {
    if (canvas instanceof HTMLCanvasElement) {
      const dataUrl = canvas.toDataURL("image/png");
      return dataUrl.replace(/^data:image\/png;base64,/, "");
    }

    // OffscreenCanvas fallback
    const tempCanvas = document.createElement("canvas");
    tempCanvas.width = canvas.width;
    tempCanvas.height = canvas.height;
    const ctx = tempCanvas.getContext("2d");
    if (ctx) {
      ctx.drawImage(canvas, 0, 0);
    }
    const dataUrl = tempCanvas.toDataURL("image/png");
    return dataUrl.replace(/^data:image\/png;base64,/, "");
  };
};

// Base64 to blob
export const base64ToBlobImpl = function(base64) {
  return function(mimeType) {
    return function() {
      const byteCharacters = atob(base64);
      const byteNumbers = new Array(byteCharacters.length);
      for (let i = 0; i < byteCharacters.length; i++) {
        byteNumbers[i] = byteCharacters.charCodeAt(i);
      }
      const byteArray = new Uint8Array(byteNumbers);
      return new Blob([byteArray], { type: mimeType });
    };
  };
};

// Base64 to data URL
export const base64ToDataUrl = function(base64) {
  return function(mimeType) {
    return "data:" + mimeType + ";base64," + base64;
  };
};
