// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                 // hydrogen // scroll-animation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Scroll-triggered animations using Intersection Observer

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // viewport trigger
// ═══════════════════════════════════════════════════════════════════════════════

const addClass = (el, cls) => { el.classList.add(cls); };
const removeClass = (el, cls) => { el.classList.remove(cls); };

export const onEnterViewportImpl = (element) => (config) => () => {
  let hasAnimated = false;
  
  // Set initial state
  const initialClasses = config.animation.initial.split(" ").filter(Boolean);
  for (const cls of initialClasses) {
    addClass(element, cls);
  }
  
  const observer = new IntersectionObserver(
    (entries) => {
      for (const entry of entries) {
        if (entry.isIntersecting) {
          if (config.once && hasAnimated) continue;
          hasAnimated = true;
          
          const animate = () => {
            // Remove initial classes
            for (const cls of initialClasses) {
              removeClass(element, cls);
            }
            // Add animation classes
            const animateClasses = config.animation.animate.split(" ").filter(Boolean);
            for (const cls of animateClasses) {
              addClass(element, cls);
            }
            config.onEnter();
          };
          
          if (config.delay > 0) {
            setTimeout(animate, config.delay);
          } else {
            animate();
          }
          
          if (config.once) {
            observer.disconnect();
          }
        } else {
          if (!config.once && hasAnimated) {
            // Reset for re-animation
            const animateClasses = config.animation.animate.split(" ").filter(Boolean);
            for (const cls of animateClasses) {
              removeClass(element, cls);
            }
            for (const cls of initialClasses) {
              addClass(element, cls);
            }
            config.onExit();
          }
        }
      }
    },
    {
      threshold: config.threshold,
      rootMargin: config.rootMargin,
    }
  );
  
  observer.observe(element);
  
  return {
    observer,
    element,
    disconnect: () => observer.disconnect(),
    reconnect: () => observer.observe(element),
  };
};

export const onExitViewportImpl = (element) => (config) => () => {
  const observer = new IntersectionObserver(
    (entries) => {
      for (const entry of entries) {
        if (!entry.isIntersecting) {
          config.onExit();
        }
      }
    },
    {
      threshold: config.threshold,
      rootMargin: config.rootMargin,
    }
  );
  
  observer.observe(element);
  
  return {
    observer,
    element,
    disconnect: () => observer.disconnect(),
    reconnect: () => observer.observe(element),
  };
};

export const onViewportChangeImpl = (element) => (config) => () => {
  const observer = new IntersectionObserver(
    (entries) => {
      for (const entry of entries) {
        config.onChange(entry.isIntersecting)(entry.intersectionRatio)();
      }
    },
    {
      threshold: config.threshold,
      rootMargin: config.rootMargin,
    }
  );
  
  observer.observe(element);
  
  return {
    observer,
    element,
    disconnect: () => observer.disconnect(),
    reconnect: () => observer.observe(element),
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // progress animation
// ═══════════════════════════════════════════════════════════════════════════════

export const onScrollProgressImpl = (element) => (config) => () => {
  let ticking = false;
  
  const calculateProgress = () => {
    const rect = element.getBoundingClientRect();
    const windowHeight = window.innerHeight;
    
    // Element position relative to viewport
    // 0 = element top at viewport bottom
    // 1 = element bottom at viewport top
    const elementHeight = rect.height;
    const startY = windowHeight; // When element enters from bottom
    const endY = -elementHeight; // When element exits from top
    const currentY = rect.top;
    
    // Map to 0-1 range based on config
    const totalRange = startY - endY;
    const currentPosition = startY - currentY;
    let progress = currentPosition / totalRange;
    
    // Remap based on start/end config
    progress = (progress - config.start) / (config.end - config.start);
    
    if (config.clamp) {
      progress = Math.max(0, Math.min(1, progress));
    }
    
    return progress;
  };
  
  const onScroll = () => {
    if (!ticking) {
      requestAnimationFrame(() => {
        const progress = calculateProgress();
        config.onProgress(progress)();
        ticking = false;
      });
      ticking = true;
    }
  };
  
  window.addEventListener("scroll", onScroll, { passive: true });
  
  // Initial call
  onScroll();
  
  return {
    observer: null,
    element,
    disconnect: () => window.removeEventListener("scroll", onScroll),
    reconnect: () => window.addEventListener("scroll", onScroll, { passive: true }),
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // scroll direction
// ═══════════════════════════════════════════════════════════════════════════════

let lastScrollY = 0;
let currentDirection = "none";

export const onScrollDirectionImpl = (config) => () => {
  const onScroll = () => {
    const currentScrollY = window.scrollY;
    const delta = currentScrollY - lastScrollY;
    
    if (Math.abs(delta) >= config.threshold) {
      if (delta > 0 && currentDirection !== "down") {
        currentDirection = "down";
        config.onDown();
      } else if (delta < 0 && currentDirection !== "up") {
        currentDirection = "up";
        config.onUp();
      }
    }
    
    lastScrollY = currentScrollY;
  };
  
  window.addEventListener("scroll", onScroll, { passive: true });
  
  // Return unsubscribe function
  return () => {
    window.removeEventListener("scroll", onScroll);
  };
};

export const getScrollDirectionImpl = () => {
  return currentDirection;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // smooth scroll
// ═══════════════════════════════════════════════════════════════════════════════

export const scrollToElementImpl = (element) => (options) => () => {
  element.scrollIntoView({
    behavior: options.behavior,
    block: options.block,
    inline: options.inline,
  });
};

export const scrollToTopImpl = (behavior) => () => {
  window.scrollTo({
    top: 0,
    left: 0,
    behavior,
  });
};

export const scrollToPositionImpl = (position) => (behavior) => () => {
  window.scrollTo({
    top: position.y,
    left: position.x,
    behavior,
  });
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // observer management
// ═══════════════════════════════════════════════════════════════════════════════

export const disconnectObserver = (scrollObserver) => () => {
  if (scrollObserver && scrollObserver.disconnect) {
    scrollObserver.disconnect();
  }
};

export const reconnectObserver = (scrollObserver) => () => {
  if (scrollObserver && scrollObserver.reconnect) {
    scrollObserver.reconnect();
  }
};
