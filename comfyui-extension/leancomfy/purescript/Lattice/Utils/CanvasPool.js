// FFI bindings for CanvasPool.purs

export const createCanvas = (width) => (height) => () => {
  const canvas = document.createElement("canvas");
  canvas.width = width;
  canvas.height = height;
  return canvas;
};

export const getContext2D = (canvas) => () => {
  const ctx = canvas.getContext("2d");
  if (!ctx) {
    throw new Error("Failed to get 2D context");
  }
  return ctx;
};

export const clearRect = (ctx) => (x) => (y) => (width) => (height) => () => {
  ctx.clearRect(x, y, width, height);
};

export const canvasEquals = (canvas1) => (canvas2) => {
  return canvas1 === canvas2;
};

export const unsafeIndex = (arr) => (i) => {
  return arr[i];
};
