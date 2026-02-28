// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // hydrogen // popover
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // popover manager
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Popover state management
 */
const popoverState = new WeakMap();

/**
 * Initialize a popover with event listeners
 * @param {Element} root - The popover root element
 * @returns {Function} Cleanup function
 */
export const initPopoverImpl = (root) => () => {
  const trigger = root.querySelector('[data-popover="trigger"]');
  const content = root.querySelector('[data-popover="content"]');

  if (!trigger || !content) return () => {};

  const state = {
    isOpen: false,
    triggerMode: trigger.dataset.triggerMode || "click",
    closeOnEscape: root.dataset.closeOnEscape === "true",
    closeOnClickOutside: root.dataset.closeOnClickOutside === "true",
    autoFlip: root.dataset.autoFlip === "true",
    cleanupFns: [],
  };

  popoverState.set(root, state);

  // Open/close functions
  const open = () => {
    state.isOpen = true;
    root.dataset.state = "open";
    content.dataset.state = "open";
    trigger.setAttribute("aria-expanded", "true");
    content.classList.remove("opacity-0", "scale-95", "pointer-events-none");
    content.classList.add("opacity-100", "scale-100");

    if (state.autoFlip) {
      autoFlipPosition(root, content);
    }

    // Focus first focusable element if trap focus is enabled
    if (content.dataset.trapFocus === "true") {
      const focusable = content.querySelectorAll(
        'button, [href], input, select, textarea, [tabindex]:not([tabindex="-1"])'
      );
      if (focusable.length > 0) {
        focusable[0].focus();
      }
    }
  };

  const close = () => {
    state.isOpen = false;
    root.dataset.state = "closed";
    content.dataset.state = "closed";
    trigger.setAttribute("aria-expanded", "false");
    content.classList.remove("opacity-100", "scale-100");
    content.classList.add("opacity-0", "scale-95", "pointer-events-none");
  };

  const toggle = () => {
    if (state.isOpen) {
      close();
    } else {
      open();
    }
  };

  // Click trigger
  if (state.triggerMode === "click") {
    const handleClick = (e) => {
      e.stopPropagation();
      toggle();
    };
    trigger.addEventListener("click", handleClick);
    state.cleanupFns.push(() =>
      trigger.removeEventListener("click", handleClick)
    );
  }

  // Hover trigger
  if (state.triggerMode === "hover") {
    let hoverTimeout;

    const handleMouseEnter = () => {
      clearTimeout(hoverTimeout);
      hoverTimeout = setTimeout(open, 100);
    };

    const handleMouseLeave = () => {
      clearTimeout(hoverTimeout);
      hoverTimeout = setTimeout(close, 150);
    };

    root.addEventListener("mouseenter", handleMouseEnter);
    root.addEventListener("mouseleave", handleMouseLeave);
    state.cleanupFns.push(() => {
      root.removeEventListener("mouseenter", handleMouseEnter);
      root.removeEventListener("mouseleave", handleMouseLeave);
      clearTimeout(hoverTimeout);
    });
  }

  // Focus trigger
  if (state.triggerMode === "focus") {
    const handleFocusIn = () => open();
    const handleFocusOut = (e) => {
      if (!root.contains(e.relatedTarget)) {
        close();
      }
    };

    root.addEventListener("focusin", handleFocusIn);
    root.addEventListener("focusout", handleFocusOut);
    state.cleanupFns.push(() => {
      root.removeEventListener("focusin", handleFocusIn);
      root.removeEventListener("focusout", handleFocusOut);
    });
  }

  // Close on click outside
  if (state.closeOnClickOutside) {
    const handleClickOutside = (e) => {
      if (state.isOpen && !root.contains(e.target)) {
        close();
      }
    };
    document.addEventListener("click", handleClickOutside);
    state.cleanupFns.push(() =>
      document.removeEventListener("click", handleClickOutside)
    );
  }

  // Close on escape
  if (state.closeOnEscape) {
    const handleEscape = (e) => {
      if (state.isOpen && e.key === "Escape") {
        close();
        trigger.focus();
      }
    };
    document.addEventListener("keydown", handleEscape);
    state.cleanupFns.push(() =>
      document.removeEventListener("keydown", handleEscape)
    );
  }

  // Close button
  const closeBtn = content.querySelector('[data-popover="close"]');
  if (closeBtn) {
    const handleCloseClick = () => close();
    closeBtn.addEventListener("click", handleCloseClick);
    state.cleanupFns.push(() =>
      closeBtn.removeEventListener("click", handleCloseClick)
    );
  }

  // Focus trap
  if (content.dataset.trapFocus === "true") {
    const handleTab = (e) => {
      if (!state.isOpen || e.key !== "Tab") return;

      const focusable = content.querySelectorAll(
        'button, [href], input, select, textarea, [tabindex]:not([tabindex="-1"])'
      );
      if (focusable.length === 0) return;

      const first = focusable[0];
      const last = focusable[focusable.length - 1];

      if (e.shiftKey && document.activeElement === first) {
        e.preventDefault();
        last.focus();
      } else if (!e.shiftKey && document.activeElement === last) {
        e.preventDefault();
        first.focus();
      }
    };

    content.addEventListener("keydown", handleTab);
    state.cleanupFns.push(() =>
      content.removeEventListener("keydown", handleTab)
    );
  }

  // Cleanup function
  return () => {
    for (const fn of state.cleanupFns) {
      fn();
    }
    popoverState.delete(root);
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // auto-flip logic
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Auto-flip popover position if it would overflow viewport
 * @param {Element} root - Popover root element
 * @param {Element} content - Popover content element
 */
function autoFlipPosition(root, content) {
  const contentRect = content.getBoundingClientRect();
  const viewportWidth = window.innerWidth;
  const viewportHeight = window.innerHeight;

  const side = content.dataset.side;
  let needsFlip = false;

  // Check if content overflows viewport
  switch (side) {
    case "top":
      needsFlip = contentRect.top < 0;
      break;
    case "bottom":
      needsFlip = contentRect.bottom > viewportHeight;
      break;
    case "left":
      needsFlip = contentRect.left < 0;
      break;
    case "right":
      needsFlip = contentRect.right > viewportWidth;
      break;
  }

  if (needsFlip) {
    // Apply flipped classes
    const flipMap = {
      top: "bottom",
      bottom: "top",
      left: "right",
      right: "left",
    };

    const flippedSide = flipMap[side];
    content.dataset.side = flippedSide;

    // Update positioning classes
    const positionClasses = {
      top: "bottom-full mb-2",
      bottom: "top-full mt-2",
      left: "right-full mr-2",
      right: "left-full ml-2",
    };

    // Remove old position classes and add new ones
    for (const cls of Object.values(positionClasses)) {
      for (const c of cls.split(" ")) {
        content.classList.remove(c);
      }
    }

    for (const c of positionClasses[flippedSide].split(" ")) {
      content.classList.add(c);
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // portal management
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Move popover content to portal (document body)
 * @param {Element} content - The popover content element
 * @param {Element} trigger - The trigger element (for positioning)
 * @returns {Function} Cleanup function to restore original position
 */
export const portalizeImpl = (content) => (trigger) => () => {
  const originalParent = content.parentNode;
  const placeholder = document.createComment("popover-portal-placeholder");

  // Insert placeholder and move to body
  originalParent.insertBefore(placeholder, content);

  // Create portal container
  const portal = document.createElement("div");
  portal.setAttribute("data-popover-portal", "true");
  portal.style.cssText =
    "position: fixed; top: 0; left: 0; z-index: 50; pointer-events: none;";
  document.body.appendChild(portal);

  // Move content to portal
  portal.appendChild(content);
  content.style.pointerEvents = "auto";

  // Position content relative to trigger
  const updatePosition = () => {
    const triggerRect = trigger.getBoundingClientRect();
    const side = content.dataset.side || "bottom";
    const align = content.dataset.align || "center";

    let top, left;

    switch (side) {
      case "top":
        top = triggerRect.top - content.offsetHeight - 8;
        break;
      case "bottom":
        top = triggerRect.bottom + 8;
        break;
      case "left":
        top =
          align === "center"
            ? triggerRect.top +
              (triggerRect.height - content.offsetHeight) / 2
            : align === "start"
              ? triggerRect.top
              : triggerRect.bottom - content.offsetHeight;
        break;
      case "right":
        top =
          align === "center"
            ? triggerRect.top +
              (triggerRect.height - content.offsetHeight) / 2
            : align === "start"
              ? triggerRect.top
              : triggerRect.bottom - content.offsetHeight;
        break;
    }

    switch (side) {
      case "top":
      case "bottom":
        left =
          align === "center"
            ? triggerRect.left +
              (triggerRect.width - content.offsetWidth) / 2
            : align === "start"
              ? triggerRect.left
              : triggerRect.right - content.offsetWidth;
        break;
      case "left":
        left = triggerRect.left - content.offsetWidth - 8;
        break;
      case "right":
        left = triggerRect.right + 8;
        break;
    }

    // Remove transform classes since we're using absolute positioning
    content.classList.remove("-translate-x-1/2", "-translate-y-1/2");
    content.classList.remove(
      "top-full",
      "bottom-full",
      "left-full",
      "right-full"
    );
    content.classList.remove("mt-2", "mb-2", "ml-2", "mr-2");
    content.classList.remove("left-0", "right-0", "top-0", "bottom-0");
    content.classList.remove("left-1/2", "top-1/2");

    content.style.position = "fixed";
    content.style.top = `${top}px`;
    content.style.left = `${left}px`;
  };

  updatePosition();
  window.addEventListener("scroll", updatePosition, true);
  window.addEventListener("resize", updatePosition);

  // Return cleanup function
  return () => {
    window.removeEventListener("scroll", updatePosition, true);
    window.removeEventListener("resize", updatePosition);

    // Restore content to original position
    content.style.position = "";
    content.style.top = "";
    content.style.left = "";
    content.style.pointerEvents = "";

    placeholder.parentNode.insertBefore(content, placeholder);
    placeholder.remove();
    portal.remove();
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // programmatic api
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Open a popover programmatically
 * @param {Element} root - The popover root element
 */
export const openPopoverImpl = (root) => () => {
  const content = root.querySelector('[data-popover="content"]');
  const trigger = root.querySelector('[data-popover="trigger"]');

  if (content && trigger) {
    root.dataset.state = "open";
    content.dataset.state = "open";
    trigger.setAttribute("aria-expanded", "true");
    content.classList.remove("opacity-0", "scale-95", "pointer-events-none");
    content.classList.add("opacity-100", "scale-100");
  }
};

/**
 * Close a popover programmatically
 * @param {Element} root - The popover root element
 */
export const closePopoverImpl = (root) => () => {
  const content = root.querySelector('[data-popover="content"]');
  const trigger = root.querySelector('[data-popover="trigger"]');

  if (content && trigger) {
    root.dataset.state = "closed";
    content.dataset.state = "closed";
    trigger.setAttribute("aria-expanded", "false");
    content.classList.remove("opacity-100", "scale-100");
    content.classList.add("opacity-0", "scale-95", "pointer-events-none");
  }
};

/**
 * Toggle a popover programmatically
 * @param {Element} root - The popover root element
 */
export const togglePopoverImpl = (root) => () => {
  const isOpen = root.dataset.state === "open";
  if (isOpen) {
    closePopoverImpl(root)();
  } else {
    openPopoverImpl(root)();
  }
};
