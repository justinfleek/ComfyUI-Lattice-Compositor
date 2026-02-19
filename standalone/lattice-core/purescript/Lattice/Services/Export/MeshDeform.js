//                                                                       // ffi

"use strict";

export const exportPinsAsTrajectoryImpl = (pins) => (frameRange) => (composition) => () => {
  throw new Error("FFI stub: exportPinsAsTrajectoryImpl");
};

export const exportPinPositionsPerFrameImpl = (pins) => (frameRange) => (frameRate) => () => {
  throw new Error("FFI stub: exportPinPositionsPerFrameImpl");
};

export const exportOverlapAsDepthImpl = (mesh) => (vertices) => (pins) => (frame) => (width) => (height) => (format) => () => {
  throw new Error("FFI stub: exportOverlapAsDepthImpl");
};

export const depthBufferToImageData = (buffer) => (width) => (height) => () => {
  throw new Error("FFI stub: depthBufferToImageData");
};

export const exportOverlapDepthSequenceImpl = (mesh) => (verticesPerFrame) => (pins) => (frameRange) => (width) => (height) => (format) => () => {
  throw new Error("FFI stub: exportOverlapDepthSequenceImpl");
};

export const exportDeformedMeshMask = (mesh) => (vertices) => (width) => (height) => () => {
  throw new Error("FFI stub: exportDeformedMeshMask");
};

export const exportDeformedMeshMaskBinary = (mesh) => (vertices) => (width) => (height) => () => {
  throw new Error("FFI stub: exportDeformedMeshMaskBinary");
};

export const exportMeshMaskSequenceImpl = (mesh) => (verticesPerFrame) => (frameRange) => (width) => (height) => () => {
  throw new Error("FFI stub: exportMeshMaskSequenceImpl");
};
