// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // hydrogen // hovercard
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // hover card manager
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * HoverCard state management
 */
const hoverCardState = new WeakMap();

/**
 * Initialize a hover card with event listeners
 * @param {Element} root - The hover card root element
 * @returns {Function} Cleanup function
 */
export const initHoverCardImpl = (root) => () => {
  const trigger = root.querySelector('[data-hover-card="trigger"]');
  const content = root.querySelector('[data-hover-card="content"]');

  if (!trigger || !content) return () => {};

  const state = {
    isOpen: false,
    openTimeout: null,
    closeTimeout: null,
    openDelay: parseInt(root.dataset.openDelay, 10) || 700,
    closeDelay: parseInt(root.dataset.closeDelay, 10) || 300,
    closeOnEscape: root.dataset.closeOnEscape === "true",
    cleanupFns: [],
  };

  hoverCardState.set(root, state);

  // Open hover card
  const open = () => {
    clearTimeout(state.closeTimeout);
    state.isOpen = true;

    root.dataset.state = "open";
    content.dataset.state = "open";

    content.classList.remove(
      "opacity-0",
      "invisible",
      "scale-95",
      "group-hover:opacity-100",
      "group-hover:visible",
      "group-hover:scale-100"
    );
    content.classList.add("opacity-100", "visible", "scale-100");
  };

  // Close hover card
  const close = () => {
    clearTimeout(state.openTimeout);
    state.isOpen = false;

    root.dataset.state = "closed";
    content.dataset.state = "closed";

    content.classList.remove("opacity-100", "visible", "scale-100");
    content.classList.add("opacity-0", "invisible", "scale-95");
  };

  // Schedule open with delay
  const scheduleOpen = () => {
    clearTimeout(state.closeTimeout);
    state.openTimeout = setTimeout(open, state.openDelay);
  };

  // Schedule close with delay
  const scheduleClose = () => {
    clearTimeout(state.openTimeout);
    state.closeTimeout = setTimeout(close, state.closeDelay);
  };

  // Trigger hover events
  const handleTriggerEnter = () => scheduleOpen();
  const handleTriggerLeave = () => scheduleClose();

  trigger.addEventListener("mouseenter", handleTriggerEnter);
  trigger.addEventListener("mouseleave", handleTriggerLeave);
  state.cleanupFns.push(() => {
    trigger.removeEventListener("mouseenter", handleTriggerEnter);
    trigger.removeEventListener("mouseleave", handleTriggerLeave);
  });

  // Content hover events (keep open when hovering content)
  const handleContentEnter = () => {
    clearTimeout(state.closeTimeout);
  };
  const handleContentLeave = () => scheduleClose();

  content.addEventListener("mouseenter", handleContentEnter);
  content.addEventListener("mouseleave", handleContentLeave);
  state.cleanupFns.push(() => {
    content.removeEventListener("mouseenter", handleContentEnter);
    content.removeEventListener("mouseleave", handleContentLeave);
  });

  // Focus events (for accessibility)
  const handleTriggerFocus = () => scheduleOpen();
  const handleTriggerBlur = (e) => {
    if (!root.contains(e.relatedTarget)) {
      scheduleClose();
    }
  };

  trigger.addEventListener("focusin", handleTriggerFocus);
  trigger.addEventListener("focusout", handleTriggerBlur);
  state.cleanupFns.push(() => {
    trigger.removeEventListener("focusin", handleTriggerFocus);
    trigger.removeEventListener("focusout", handleTriggerBlur);
  });

  // Close on escape
  if (state.closeOnEscape) {
    const handleEscape = (e) => {
      if (state.isOpen && e.key === "Escape") {
        close();
      }
    };
    document.addEventListener("keydown", handleEscape);
    state.cleanupFns.push(() =>
      document.removeEventListener("keydown", handleEscape)
    );
  }

  // Cleanup
  return () => {
    clearTimeout(state.openTimeout);
    clearTimeout(state.closeTimeout);
    for (const fn of state.cleanupFns) {
      fn();
    }
    hoverCardState.delete(root);
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // programmatic api
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Open hover card programmatically
 * @param {Element} root - The hover card root element
 */
export const openHoverCardImpl = (root) => () => {
  const content = root.querySelector('[data-hover-card="content"]');
  if (content) {
    root.dataset.state = "open";
    content.dataset.state = "open";
    content.classList.remove("opacity-0", "invisible", "scale-95");
    content.classList.add("opacity-100", "visible", "scale-100");
  }
};

/**
 * Close hover card programmatically
 * @param {Element} root - The hover card root element
 */
export const closeHoverCardImpl = (root) => () => {
  const content = root.querySelector('[data-hover-card="content"]');
  if (content) {
    root.dataset.state = "closed";
    content.dataset.state = "closed";
    content.classList.remove("opacity-100", "visible", "scale-100");
    content.classList.add("opacity-0", "invisible", "scale-95");
  }
};

/**
 * Check if hover card is open
 * @param {Element} root - The hover card root element
 * @returns {boolean}
 */
export const isHoverCardOpenImpl = (root) => () => {
  return root.dataset.state === "open";
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // delay utilities
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Set open delay for hover card
 * @param {Element} root - The hover card root element
 * @param {number} delay - Delay in milliseconds
 */
export const setOpenDelayImpl = (root) => (delay) => () => {
  root.dataset.openDelay = String(delay);
  const state = hoverCardState.get(root);
  if (state) {
    state.openDelay = delay;
  }
};

/**
 * Set close delay for hover card
 * @param {Element} root - The hover card root element
 * @param {number} delay - Delay in milliseconds
 */
export const setCloseDelayImpl = (root) => (delay) => () => {
  root.dataset.closeDelay = String(delay);
  const state = hoverCardState.get(root);
  if (state) {
    state.closeDelay = delay;
  }
};
