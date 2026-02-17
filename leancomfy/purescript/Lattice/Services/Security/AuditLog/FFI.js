// FFI stubs for Lattice.Services.Security.AuditLog.FFI
"use strict";

export const getSessionId = function () {
  throw new Error("FFI stub: getSessionId not implemented");
};

export const getCurrentISOTimestamp = function () {
  return new Date().toISOString();
};

export const openDatabaseImpl = function (dbName) {
  return function (version) {
    return function (storeName) {
      return function (onError, onSuccess) {
        throw new Error("FFI stub: openDatabaseImpl not implemented");
      };
    };
  };
};

export const addEntryImpl = function (storeName) {
  return function (entry) {
    return function (onError, onSuccess) {
      throw new Error("FFI stub: addEntryImpl not implemented");
    };
  };
};

export const queryEntriesImpl = function (storeName) {
  return function (query) {
    return function (onError, onSuccess) {
      throw new Error("FFI stub: queryEntriesImpl not implemented");
    };
  };
};

export const countEntriesImpl = function (storeName) {
  return function (onError, onSuccess) {
    throw new Error("FFI stub: countEntriesImpl not implemented");
  };
};

export const clearStoreImpl = function (storeName) {
  return function (onError, onSuccess) {
    throw new Error("FFI stub: clearStoreImpl not implemented");
  };
};

export const deleteOldEntriesImpl = function (storeName) {
  return function (cutoffTimestamp) {
    return function (maxToDelete) {
      return function (onError, onSuccess) {
        throw new Error("FFI stub: deleteOldEntriesImpl not implemented");
      };
    };
  };
};

export const downloadBlobImpl = function (content) {
  return function (filename) {
    return function () {
      throw new Error("FFI stub: downloadBlobImpl not implemented");
    };
  };
};
