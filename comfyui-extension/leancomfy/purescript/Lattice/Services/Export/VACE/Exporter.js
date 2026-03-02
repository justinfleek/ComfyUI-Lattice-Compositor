// FFI stubs for Lattice.Services.Export.VACE.Exporter

"use strict";

export const createPathFollowerImpl = (config) => () => {
  throw new Error("FFI stub: createPathFollowerImpl");
};

export const getStateAtFrameImpl = (handle) => (frame) => () => {
  throw new Error("FFI stub: getStateAtFrameImpl");
};

export const getPathLength = (handle) => () => {
  throw new Error("FFI stub: getPathLength");
};

export const getPathSpeed = (handle) => () => {
  throw new Error("FFI stub: getPathSpeed");
};

export const createExporterImpl = (config) => () => {
  throw new Error("FFI stub: createExporterImpl");
};

export const renderFrameImpl = (handle) => (frame) => () => {
  throw new Error("FFI stub: renderFrameImpl");
};

export const renderAllFramesImpl = (handle) => () =>
  Promise.reject(new Error("FFI stub: renderAllFramesImpl"));

export const getFrameCount = (handle) => () => {
  throw new Error("FFI stub: getFrameCount");
};

export const getPathStats = (handle) => () => {
  throw new Error("FFI stub: getPathStats");
};

export const exportToImageDataArrayImpl = (handle) => () =>
  Promise.reject(new Error("FFI stub: exportToImageDataArrayImpl"));
