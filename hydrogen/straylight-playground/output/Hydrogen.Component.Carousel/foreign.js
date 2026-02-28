// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // carousel
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Carousel FFI for touch/swipe support and auto-play functionality

/**
 * Initialize carousel touch/swipe support
 * @param {Element} container - Carousel container element
 * @param {Object} callbacks - Event callbacks
 * @param {Object} options - Configuration options
 * @returns {Object} Carousel controller
 */
export const initCarouselImpl = (container) => (callbacks) => (options) => () => {
  const { threshold = 50, preventScroll = true } = options;

  let touchStartX = 0;
  let touchStartY = 0;
  let touchEndX = 0;
  let touchEndY = 0;
  let isSwiping = false;

  /**
   * Handle touch start
   */
  const handleTouchStart = (e) => {
    touchStartX = e.touches[0].clientX;
    touchStartY = e.touches[0].clientY;
    isSwiping = true;

    callbacks.onTouchStart();
  };

  /**
   * Handle touch move
   */
  const handleTouchMove = (e) => {
    if (!isSwiping) return;

    touchEndX = e.touches[0].clientX;
    touchEndY = e.touches[0].clientY;

    // Calculate movement
    const deltaX = touchEndX - touchStartX;
    const deltaY = touchEndY - touchStartY;

    // Prevent vertical scroll if horizontal swipe is dominant
    if (preventScroll && Math.abs(deltaX) > Math.abs(deltaY)) {
      e.preventDefault();
    }
  };

  /**
   * Handle touch end
   */
  const handleTouchEnd = (e) => {
    if (!isSwiping) return;
    isSwiping = false;

    const deltaX = touchEndX - touchStartX;
    const deltaY = touchEndY - touchStartY;

    // Only trigger swipe if horizontal movement exceeds threshold
    // and is greater than vertical movement
    if (Math.abs(deltaX) > threshold && Math.abs(deltaX) > Math.abs(deltaY)) {
      if (deltaX > 0) {
        // Swiped right (go to previous)
        callbacks.onSwipeRight();
      } else {
        // Swiped left (go to next)
        callbacks.onSwipeLeft();
      }
    }

    callbacks.onTouchEnd();

    // Reset
    touchStartX = 0;
    touchStartY = 0;
    touchEndX = 0;
    touchEndY = 0;
  };

  /**
   * Handle mouse drag for desktop swipe
   */
  let mouseStartX = 0;
  let isDragging = false;

  const handleMouseDown = (e) => {
    mouseStartX = e.clientX;
    isDragging = true;
    container.style.cursor = "grabbing";
  };

  const handleMouseMove = (e) => {
    if (!isDragging) return;
    // Optional: Add visual feedback during drag
  };

  const handleMouseUp = (e) => {
    if (!isDragging) return;
    isDragging = false;
    container.style.cursor = "";

    const deltaX = e.clientX - mouseStartX;

    if (Math.abs(deltaX) > threshold) {
      if (deltaX > 0) {
        callbacks.onSwipeRight();
      } else {
        callbacks.onSwipeLeft();
      }
    }

    mouseStartX = 0;
  };

  const handleMouseLeave = () => {
    isDragging = false;
    container.style.cursor = "";
  };

  // Attach event listeners
  container.addEventListener("touchstart", handleTouchStart, { passive: true });
  container.addEventListener("touchmove", handleTouchMove, { passive: !preventScroll });
  container.addEventListener("touchend", handleTouchEnd, { passive: true });

  // Mouse events for desktop
  container.addEventListener("mousedown", handleMouseDown);
  container.addEventListener("mousemove", handleMouseMove);
  container.addEventListener("mouseup", handleMouseUp);
  container.addEventListener("mouseleave", handleMouseLeave);

  return {
    container,
    autoPlayTimer: null,
    destroy: () => {
      container.removeEventListener("touchstart", handleTouchStart);
      container.removeEventListener("touchmove", handleTouchMove);
      container.removeEventListener("touchend", handleTouchEnd);
      container.removeEventListener("mousedown", handleMouseDown);
      container.removeEventListener("mousemove", handleMouseMove);
      container.removeEventListener("mouseup", handleMouseUp);
      container.removeEventListener("mouseleave", handleMouseLeave);
    },
  };
};

/**
 * Destroy carousel and cleanup
 * @param {Object} carousel - Carousel controller
 */
export const destroyCarouselImpl = (carousel) => () => {
  if (carousel) {
    if (carousel.autoPlayTimer) {
      clearInterval(carousel.autoPlayTimer);
    }
    if (carousel.destroy) {
      carousel.destroy();
    }
  }
};

/**
 * Start auto-play timer
 * @param {Object} carousel - Carousel controller
 * @param {number} interval - Interval in milliseconds
 * @param {Function} onTick - Callback on each tick
 */
export const startAutoPlayImpl = (carousel) => (interval) => (onTick) => () => {
  if (carousel.autoPlayTimer) {
    clearInterval(carousel.autoPlayTimer);
  }

  carousel.autoPlayTimer = setInterval(() => {
    onTick();
  }, interval);
};

/**
 * Stop auto-play timer
 * @param {Object} carousel - Carousel controller
 */
export const stopAutoPlayImpl = (carousel) => () => {
  if (carousel && carousel.autoPlayTimer) {
    clearInterval(carousel.autoPlayTimer);
    carousel.autoPlayTimer = null;
  }
};

/**
 * Unsafe placeholder for CarouselElement
 */
export const unsafeCarouselElement = {
  container: null,
  autoPlayTimer: null,
  destroy: () => {},
};

/**
 * Convert Int to Number
 * @param {number} n - Integer value
 * @returns {number} Number value
 */
export const unsafeToNumber = (n) => n;

/**
 * Generate array range [start, end]
 * @param {number} start - Start index
 * @param {number} end - End index (inclusive)
 * @returns {number[]} Array of integers
 */
export const rangeImpl = (start) => (end) => {
  if (end < start) return [];
  const result = [];
  for (let i = start; i <= end; i++) {
    result.push(i);
  }
  return result;
};
