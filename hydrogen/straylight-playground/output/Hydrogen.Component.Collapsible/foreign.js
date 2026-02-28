// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                     // hydrogen // collapsible
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Collapsible component FFI for animated expand/collapse behavior

/**
 * Initialize collapsible behavior
 * @param {Object} config - Configuration with container selector and duration
 * @param {Object} callbacks - Event callbacks
 * @returns {Object} Collapsible controller
 */
export const initCollapsibleImpl = (config, callbacks) => {
  const { container: containerSelector, duration } = config;
  const { onOpen, onClose } = callbacks;

  const container = document.querySelector(containerSelector);
  if (!container) return null;

  const trigger = container.querySelector(".collapsible-trigger");
  const content = container.querySelector(".collapsible-content");
  const contentInner = container.querySelector(".collapsible-content-inner");
  const chevron = container.querySelector(".collapsible-chevron");

  if (!trigger || !content) return null;

  let isOpen = container.dataset.state === "open";

  /**
   * Update state and animate
   */
  const updateState = (open) => {
    isOpen = open;

    // Update container state
    container.dataset.state = open ? "open" : "closed";

    // Update trigger ARIA
    trigger.setAttribute("aria-expanded", String(open));

    // Update content state
    content.dataset.state = open ? "open" : "closed";
    content.setAttribute("aria-hidden", String(!open));

    // Update chevron state
    if (chevron) {
      chevron.dataset.state = open ? "open" : "closed";
    }

    // Animate height
    if (open) {
      // Expand
      const height = contentInner ? contentInner.offsetHeight : "auto";
      content.style.height = "0px";
      content.style.opacity = "0";

      requestAnimationFrame(() => {
        content.style.transition = `height ${duration}ms ease-out, opacity ${duration}ms ease-out`;
        content.style.height = typeof height === "number" ? `${height}px` : height;
        content.style.opacity = "1";
      });

      // Cleanup after animation
      setTimeout(() => {
        content.style.height = "auto";
        onOpen();
      }, duration);
    } else {
      // Collapse
      const height = content.offsetHeight;
      content.style.height = `${height}px`;
      content.style.opacity = "1";

      requestAnimationFrame(() => {
        content.style.transition = `height ${duration}ms ease-out, opacity ${duration}ms ease-out`;
        content.style.height = "0px";
        content.style.opacity = "0";
      });

      setTimeout(() => {
        onClose();
      }, duration);
    }
  };

  /**
   * Handle trigger click
   */
  const handleClick = (e) => {
    if (container.dataset.disabled === "true") return;

    e.preventDefault();
    updateState(!isOpen);
  };

  // Attach click handler
  trigger.addEventListener("click", handleClick);

  // Keyboard support
  trigger.addEventListener("keydown", (e) => {
    if (e.key === "Enter" || e.key === " ") {
      e.preventDefault();
      handleClick(e);
    }
  });

  // Initialize state
  if (isOpen) {
    content.style.height = "auto";
    content.style.opacity = "1";
    content.dataset.state = "open";
    content.setAttribute("aria-hidden", "false");
    trigger.setAttribute("aria-expanded", "true");
  } else {
    content.style.height = "0px";
    content.style.opacity = "0";
    content.dataset.state = "closed";
    content.setAttribute("aria-hidden", "true");
    trigger.setAttribute("aria-expanded", "false");
  }

  return {
    container,
    trigger,
    content,
    isOpen: () => isOpen,
    toggle: () => {
      updateState(!isOpen);
      return isOpen;
    },
    open: () => {
      if (!isOpen) updateState(true);
    },
    close: () => {
      if (isOpen) updateState(false);
    },
    destroy: () => {
      trigger.removeEventListener("click", handleClick);
    },
  };
};

/**
 * Destroy collapsible
 */
export const destroyCollapsibleImpl = (collapsible) => {
  if (collapsible && collapsible.destroy) {
    collapsible.destroy();
  }
};

/**
 * Toggle collapsible state
 */
export const toggleImpl = (collapsible) => {
  if (collapsible && collapsible.toggle) {
    return collapsible.toggle();
  }
  return false;
};

/**
 * Open collapsible
 */
export const openImpl = (collapsible) => {
  if (collapsible && collapsible.open) {
    collapsible.open();
  }
};

/**
 * Close collapsible
 */
export const closeImpl = (collapsible) => {
  if (collapsible && collapsible.close) {
    collapsible.close();
  }
};

/**
 * Placeholder collapsible element
 */
export const unsafeCollapsibleElement = {
  container: null,
  trigger: null,
  content: null,
  isOpen: () => false,
  toggle: () => false,
  open: () => {},
  close: () => {},
  destroy: () => {},
};
