//                                                                       // ffi
"use strict";

export const now = function () {
  return Date.now();
};

export const generateId = function () {
  return crypto.randomUUID();
};

export const setIntervalImpl = function (callback) {
  return function (ms) {
    return function () {
      return setInterval(callback, ms);
    };
  };
};

export const clearIntervalImpl = function (timerId) {
  return function () {
    clearInterval(timerId);
  };
};
