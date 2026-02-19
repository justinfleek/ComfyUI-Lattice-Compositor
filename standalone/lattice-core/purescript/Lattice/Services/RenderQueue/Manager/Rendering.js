//                                                                       // ffi

"use strict";

export const clearIntervalInternal = (timerId) => () => {
  clearInterval(timerId);
};
