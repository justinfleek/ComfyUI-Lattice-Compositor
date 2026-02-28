// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // slider
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Slider pointer event handling and value calculation

/**
 * Clamp a value between min and max
 */
const clamp = (value, min, max) => Math.min(Math.max(value, min), max);

/**
 * Round to nearest step
 */
const roundToStep = (value, step, min) => {
  const steps = Math.round((value - min) / step);
  return min + steps * step;
};

/**
 * Calculate value from pointer position
 */
const calculateValue = (element, clientX, clientY, opts) => {
  const rect = element.getBoundingClientRect();
  let percent;

  if (opts.vertical) {
    // For vertical sliders, bottom is min, top is max
    percent = 1 - (clientY - rect.top) / rect.height;
  } else {
    percent = (clientX - rect.left) / rect.width;
  }

  percent = clamp(percent, 0, 1);
  const rawValue = opts.min + percent * (opts.max - opts.min);
  return roundToStep(rawValue, opts.step, opts.min);
};

/**
 * Initialize single value slider
 */
export const initSliderImpl = (element, onChange, opts) => {
  let isDragging = false;
  let currentThumb = null;

  const track = element.querySelector("[data-track]") || element.firstElementChild;

  const handlePointerDown = (e) => {
    if (element.hasAttribute("disabled")) return;

    isDragging = true;
    currentThumb = e.target.closest('[role="slider"]');
    element.setPointerCapture(e.pointerId);

    const value = calculateValue(track, e.clientX, e.clientY, opts);
    onChange(value)();
  };

  const handlePointerMove = (e) => {
    if (!isDragging) return;

    const value = calculateValue(track, e.clientX, e.clientY, opts);
    onChange(value)();
  };

  const handlePointerUp = (e) => {
    if (isDragging) {
      isDragging = false;
      element.releasePointerCapture(e.pointerId);
      currentThumb = null;
    }
  };

  const handleKeyDown = (e) => {
    const thumb = e.target.closest('[role="slider"]');
    if (!thumb) return;

    const currentValue = parseFloat(thumb.getAttribute("aria-valuenow") || "0");
    let newValue = currentValue;
    const bigStep = opts.step * 10;

    switch (e.key) {
      case "ArrowRight":
      case "ArrowUp":
        newValue = Math.min(currentValue + opts.step, opts.max);
        e.preventDefault();
        break;
      case "ArrowLeft":
      case "ArrowDown":
        newValue = Math.max(currentValue - opts.step, opts.min);
        e.preventDefault();
        break;
      case "PageUp":
        newValue = Math.min(currentValue + bigStep, opts.max);
        e.preventDefault();
        break;
      case "PageDown":
        newValue = Math.max(currentValue - bigStep, opts.min);
        e.preventDefault();
        break;
      case "Home":
        newValue = opts.min;
        e.preventDefault();
        break;
      case "End":
        newValue = opts.max;
        e.preventDefault();
        break;
      default:
        return;
    }

    onChange(newValue)();
  };

  element.addEventListener("pointerdown", handlePointerDown);
  element.addEventListener("pointermove", handlePointerMove);
  element.addEventListener("pointerup", handlePointerUp);
  element.addEventListener("pointercancel", handlePointerUp);
  element.addEventListener("keydown", handleKeyDown);

  // Return cleanup object
  return {
    element,
    cleanup: () => {
      element.removeEventListener("pointerdown", handlePointerDown);
      element.removeEventListener("pointermove", handlePointerMove);
      element.removeEventListener("pointerup", handlePointerUp);
      element.removeEventListener("pointercancel", handlePointerUp);
      element.removeEventListener("keydown", handleKeyDown);
    },
  };
};

/**
 * Initialize range slider (dual thumbs)
 */
export const initRangeSliderImpl = (element, onRangeChange, opts) => {
  let isDragging = false;
  let activeThumb = null; // 'min' or 'max'

  const track = element.querySelector("[data-track]") || element.firstElementChild;

  const getCurrentRange = () => {
    const minThumb = element.querySelector('[data-thumb="min"]');
    const maxThumb = element.querySelector('[data-thumb="max"]');
    return {
      min: parseFloat(minThumb?.getAttribute("aria-valuenow") || String(opts.min)),
      max: parseFloat(maxThumb?.getAttribute("aria-valuenow") || String(opts.max)),
    };
  };

  const handlePointerDown = (e) => {
    if (element.hasAttribute("disabled")) return;

    const thumb = e.target.closest('[role="slider"]');
    if (thumb) {
      activeThumb = thumb.getAttribute("data-thumb");
    } else {
      // Clicked on track - determine which thumb to move
      const value = calculateValue(track, e.clientX, e.clientY, opts);
      const range = getCurrentRange();
      const distToMin = Math.abs(value - range.min);
      const distToMax = Math.abs(value - range.max);
      activeThumb = distToMin < distToMax ? "min" : "max";
    }

    isDragging = true;
    element.setPointerCapture(e.pointerId);

    const value = calculateValue(track, e.clientX, e.clientY, opts);
    const range = getCurrentRange();

    if (activeThumb === "min") {
      onRangeChange({ min: clamp(value, opts.min, range.max), max: range.max })();
    } else {
      onRangeChange({ min: range.min, max: clamp(value, range.min, opts.max) })();
    }
  };

  const handlePointerMove = (e) => {
    if (!isDragging || !activeThumb) return;

    const value = calculateValue(track, e.clientX, e.clientY, opts);
    const range = getCurrentRange();

    if (activeThumb === "min") {
      onRangeChange({ min: clamp(value, opts.min, range.max), max: range.max })();
    } else {
      onRangeChange({ min: range.min, max: clamp(value, range.min, opts.max) })();
    }
  };

  const handlePointerUp = (e) => {
    if (isDragging) {
      isDragging = false;
      element.releasePointerCapture(e.pointerId);
      activeThumb = null;
    }
  };

  const handleKeyDown = (e) => {
    const thumb = e.target.closest('[role="slider"]');
    if (!thumb) return;

    const thumbType = thumb.getAttribute("data-thumb");
    const range = getCurrentRange();
    const currentValue = thumbType === "min" ? range.min : range.max;
    let newValue = currentValue;
    const bigStep = opts.step * 10;

    switch (e.key) {
      case "ArrowRight":
      case "ArrowUp":
        newValue = currentValue + opts.step;
        e.preventDefault();
        break;
      case "ArrowLeft":
      case "ArrowDown":
        newValue = currentValue - opts.step;
        e.preventDefault();
        break;
      case "PageUp":
        newValue = currentValue + bigStep;
        e.preventDefault();
        break;
      case "PageDown":
        newValue = currentValue - bigStep;
        e.preventDefault();
        break;
      case "Home":
        newValue = thumbType === "min" ? opts.min : range.min;
        e.preventDefault();
        break;
      case "End":
        newValue = thumbType === "max" ? opts.max : range.max;
        e.preventDefault();
        break;
      default:
        return;
    }

    if (thumbType === "min") {
      onRangeChange({ min: clamp(newValue, opts.min, range.max), max: range.max })();
    } else {
      onRangeChange({ min: range.min, max: clamp(newValue, range.min, opts.max) })();
    }
  };

  element.addEventListener("pointerdown", handlePointerDown);
  element.addEventListener("pointermove", handlePointerMove);
  element.addEventListener("pointerup", handlePointerUp);
  element.addEventListener("pointercancel", handlePointerUp);
  element.addEventListener("keydown", handleKeyDown);

  return {
    element,
    cleanup: () => {
      element.removeEventListener("pointerdown", handlePointerDown);
      element.removeEventListener("pointermove", handlePointerMove);
      element.removeEventListener("pointerup", handlePointerUp);
      element.removeEventListener("pointercancel", handlePointerUp);
      element.removeEventListener("keydown", handleKeyDown);
    },
  };
};

/**
 * Destroy slider and cleanup listeners
 */
export const destroySliderImpl = (sliderObj) => {
  if (sliderObj && sliderObj.cleanup) {
    sliderObj.cleanup();
  }
};

/**
 * Get slider position from event
 */
export const getSliderPositionImpl = (event, opts) => {
  const element = event.currentTarget;
  if (!element) return opts.min;

  const rect = element.getBoundingClientRect();
  let percent;

  if (opts.vertical) {
    percent = 1 - (event.clientY - rect.top) / rect.height;
  } else {
    percent = (event.clientX - rect.left) / rect.width;
  }

  percent = clamp(percent, 0, 1);
  const rawValue = opts.min + percent * (opts.max - opts.min);
  return roundToStep(rawValue, opts.step, opts.min);
};
