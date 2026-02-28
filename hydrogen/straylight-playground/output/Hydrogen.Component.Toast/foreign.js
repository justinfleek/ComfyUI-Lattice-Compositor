// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                          // hydrogen // toast
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Toast timer management and accessibility announcements

/**
 * Start auto-dismiss timer
 * @param {number} duration - Duration in milliseconds
 * @param {function} onDismiss - Callback when timer fires
 * @returns {number} Timer ID
 */
export const startTimerImpl = (duration, onDismiss) => {
  return setTimeout(() => {
    onDismiss();
  }, duration);
};

/**
 * Clear auto-dismiss timer
 * @param {number} timerId - Timer ID to clear
 */
export const clearTimerImpl = (timerId) => {
  clearTimeout(timerId);
};

/**
 * Announce message to screen readers
 * Uses ARIA live regions for accessibility
 * @param {string} message - Message to announce
 * @param {string} priority - "polite" or "assertive"
 */
export const announceImpl = (message, priority) => {
  // Find or create announcer element
  let announcer = document.getElementById("hydrogen-toast-announcer");

  if (!announcer) {
    announcer = document.createElement("div");
    announcer.id = "hydrogen-toast-announcer";
    announcer.setAttribute("role", "status");
    announcer.setAttribute("aria-live", priority);
    announcer.setAttribute("aria-atomic", "true");
    announcer.style.cssText = `
      position: absolute;
      width: 1px;
      height: 1px;
      padding: 0;
      margin: -1px;
      overflow: hidden;
      clip: rect(0, 0, 0, 0);
      white-space: nowrap;
      border: 0;
    `;
    document.body.appendChild(announcer);
  } else {
    announcer.setAttribute("aria-live", priority);
  }

  // Clear and set message (forces re-announcement)
  announcer.textContent = "";

  // Use requestAnimationFrame to ensure DOM updates
  requestAnimationFrame(() => {
    requestAnimationFrame(() => {
      announcer.textContent = message;
    });
  });
};

/**
 * Toast animation utilities
 */
export const animateIn = (element) => {
  if (!element) return;

  element.style.opacity = "0";
  element.style.transform = "translateX(100%)";

  requestAnimationFrame(() => {
    element.style.transition = "opacity 150ms ease-out, transform 150ms ease-out";
    element.style.opacity = "1";
    element.style.transform = "translateX(0)";
  });
};

export const animateOut = (element, onComplete) => {
  if (!element) {
    onComplete();
    return;
  }

  element.style.transition = "opacity 150ms ease-in, transform 150ms ease-in";
  element.style.opacity = "0";
  element.style.transform = "translateX(100%)";

  setTimeout(onComplete, 150);
};

/**
 * Pause timer when hovering
 */
export const createHoverPauseHandlers = (timerId, duration, onDismiss) => {
  let remainingTime = duration;
  let startTime = Date.now();
  let currentTimerId = timerId;

  const pause = () => {
    if (currentTimerId) {
      clearTimeout(currentTimerId);
      remainingTime -= Date.now() - startTime;
      currentTimerId = null;
    }
  };

  const resume = () => {
    if (!currentTimerId && remainingTime > 0) {
      startTime = Date.now();
      currentTimerId = setTimeout(onDismiss, remainingTime);
    }
  };

  return { pause, resume, getTimerId: () => currentTimerId };
};

/**
 * Swipe to dismiss support
 */
export const initSwipeDismiss = (element, onDismiss, threshold = 100) => {
  let startX = 0;
  let currentX = 0;
  let isDragging = false;

  const handleTouchStart = (e) => {
    startX = e.touches[0].clientX;
    isDragging = true;
  };

  const handleTouchMove = (e) => {
    if (!isDragging) return;

    currentX = e.touches[0].clientX;
    const deltaX = currentX - startX;

    // Only allow swiping right (to dismiss)
    if (deltaX > 0) {
      element.style.transform = `translateX(${deltaX}px)`;
      element.style.opacity = String(1 - deltaX / threshold / 2);
    }
  };

  const handleTouchEnd = () => {
    if (!isDragging) return;
    isDragging = false;

    const deltaX = currentX - startX;

    if (deltaX > threshold) {
      // Dismiss
      animateOut(element, onDismiss);
    } else {
      // Snap back
      element.style.transition = "transform 150ms ease-out, opacity 150ms ease-out";
      element.style.transform = "translateX(0)";
      element.style.opacity = "1";

      setTimeout(() => {
        element.style.transition = "";
      }, 150);
    }
  };

  element.addEventListener("touchstart", handleTouchStart, { passive: true });
  element.addEventListener("touchmove", handleTouchMove, { passive: true });
  element.addEventListener("touchend", handleTouchEnd);

  return () => {
    element.removeEventListener("touchstart", handleTouchStart);
    element.removeEventListener("touchmove", handleTouchMove);
    element.removeEventListener("touchend", handleTouchEnd);
  };
};
