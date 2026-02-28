// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // confetti
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Confetti celebration effects FFI

let particles = [];
let animationFrame = null;
let canvas = null;
let ctx = null;

/**
 * Initialize canvas if needed
 */
const initCanvas = () => {
  if (canvas) return;

  canvas = document.getElementById("confetti-canvas");
  if (!canvas) {
    // Create canvas if it doesn't exist
    const container = document.getElementById("confetti-container");
    if (!container) return null;

    canvas = document.createElement("canvas");
    canvas.id = "confetti-canvas";
    canvas.className = "confetti-canvas w-full h-full";
    container.appendChild(canvas);
  }

  ctx = canvas.getContext("2d");
  resizeCanvas();

  window.addEventListener("resize", resizeCanvas);
};

/**
 * Resize canvas to window size
 */
const resizeCanvas = () => {
  if (!canvas) return;
  canvas.width = window.innerWidth;
  canvas.height = window.innerHeight;
};

/**
 * Create a single particle
 */
const createParticle = (options) => {
  const {
    x,
    y,
    color,
    shape,
    velocity,
    angle,
    gravity,
    drift,
    decay,
    scalar,
  } = options;

  const rad = (angle * Math.PI) / 180;

  return {
    x,
    y,
    color,
    shape,
    velocity: {
      x: Math.cos(rad) * velocity + (Math.random() - 0.5) * drift,
      y: Math.sin(rad) * velocity,
    },
    gravity,
    decay,
    scalar,
    rotation: Math.random() * 360,
    rotationSpeed: (Math.random() - 0.5) * 20,
    size: Math.random() * 10 * scalar + 5,
    opacity: 1,
    ticks: 0,
  };
};

/**
 * Create emoji particle
 */
const createEmojiParticle = (options) => {
  const particle = createParticle(options);
  particle.emoji = options.emoji;
  particle.shape = "emoji";
  return particle;
};

/**
 * Draw a particle
 */
const drawParticle = (particle) => {
  if (!ctx) return;

  ctx.save();
  ctx.translate(particle.x, particle.y);
  ctx.rotate((particle.rotation * Math.PI) / 180);
  ctx.globalAlpha = particle.opacity;

  if (particle.shape === "emoji") {
    ctx.font = `${particle.size * 2}px serif`;
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.fillText(particle.emoji, 0, 0);
  } else if (particle.shape === "circle") {
    ctx.beginPath();
    ctx.arc(0, 0, particle.size / 2, 0, Math.PI * 2);
    ctx.fillStyle = particle.color;
    ctx.fill();
  } else if (particle.shape === "star") {
    drawStar(particle.size / 2, particle.color);
  } else {
    // Square (default)
    ctx.fillStyle = particle.color;
    ctx.fillRect(-particle.size / 2, -particle.size / 2, particle.size, particle.size);
  }

  ctx.restore();
};

/**
 * Draw a star shape
 */
const drawStar = (radius, color) => {
  if (!ctx) return;

  const spikes = 5;
  const outerRadius = radius;
  const innerRadius = radius / 2;

  ctx.beginPath();
  ctx.fillStyle = color;

  for (let i = 0; i < spikes * 2; i++) {
    const r = i % 2 === 0 ? outerRadius : innerRadius;
    const angle = (i * Math.PI) / spikes - Math.PI / 2;
    const x = Math.cos(angle) * r;
    const y = Math.sin(angle) * r;

    if (i === 0) {
      ctx.moveTo(x, y);
    } else {
      ctx.lineTo(x, y);
    }
  }

  ctx.closePath();
  ctx.fill();
};

/**
 * Update particle physics
 */
const updateParticle = (particle) => {
  particle.ticks++;

  // Apply velocity
  particle.x += particle.velocity.x;
  particle.y += particle.velocity.y;

  // Apply gravity
  particle.velocity.y += particle.gravity * 0.1;

  // Apply decay
  particle.velocity.x *= particle.decay;
  particle.velocity.y *= particle.decay;

  // Update rotation
  particle.rotation += particle.rotationSpeed;

  // Fade out
  particle.opacity = Math.max(0, 1 - particle.ticks / 100);

  return particle.opacity > 0 && particle.y < canvas.height + 50;
};

/**
 * Animation loop
 */
const animate = () => {
  if (!ctx || !canvas) return;

  ctx.clearRect(0, 0, canvas.width, canvas.height);

  // Update and draw particles
  particles = particles.filter((particle) => {
    const alive = updateParticle(particle);
    if (alive) {
      drawParticle(particle);
    }
    return alive;
  });

  if (particles.length > 0) {
    animationFrame = requestAnimationFrame(animate);
  } else {
    animationFrame = null;
  }
};

/**
 * Start animation if not running
 */
const startAnimation = () => {
  if (!animationFrame) {
    animationFrame = requestAnimationFrame(animate);
  }
};

/**
 * Fire basic confetti burst
 */
export const fireImpl = (options) => {
  initCanvas();
  if (!canvas) return {};

  const {
    particleCount,
    spread,
    origin,
    colors,
    shapes,
    gravity,
    drift,
    decay,
    scalar,
  } = options;

  const x = origin.x * canvas.width;
  const y = origin.y * canvas.height;

  for (let i = 0; i < particleCount; i++) {
    const angle = 270 + (Math.random() - 0.5) * spread;
    const velocity = Math.random() * 15 + 10;
    const color = colors[Math.floor(Math.random() * colors.length)];
    const shape = shapes[Math.floor(Math.random() * shapes.length)];

    particles.push(
      createParticle({
        x,
        y,
        color,
        shape,
        velocity,
        angle,
        gravity,
        drift,
        decay,
        scalar,
      })
    );
  }

  startAnimation();
  return { particles: particles.length };
};

/**
 * Fire cannon effect (directional)
 */
export const fireCannonImpl = (options) => {
  initCanvas();
  if (!canvas) return {};

  const {
    particleCount,
    angle,
    spread,
    origin,
    colors,
    shapes,
    velocity: baseVelocity,
  } = options;

  const x = origin.x * canvas.width;
  const y = origin.y * canvas.height;

  for (let i = 0; i < particleCount; i++) {
    const particleAngle = angle + (Math.random() - 0.5) * spread;
    const velocity = baseVelocity * (0.5 + Math.random() * 0.5);
    const color = colors[Math.floor(Math.random() * colors.length)];
    const shape = shapes[Math.floor(Math.random() * shapes.length)];

    particles.push(
      createParticle({
        x,
        y,
        color,
        shape,
        velocity,
        angle: particleAngle,
        gravity: 1,
        drift: 0,
        decay: 0.94,
        scalar: 1,
      })
    );
  }

  startAnimation();
  return { particles: particles.length };
};

/**
 * Fire fireworks effect (multiple bursts)
 */
export const fireFireworksImpl = (options) => {
  initCanvas();
  if (!canvas) return {};

  const { duration, colors } = options;

  const interval = 200;
  let elapsed = 0;

  const fireworkInterval = setInterval(() => {
    elapsed += interval;

    if (elapsed >= duration) {
      clearInterval(fireworkInterval);
      return;
    }

    // Random position
    const x = 0.2 + Math.random() * 0.6;
    const y = 0.2 + Math.random() * 0.4;

    // Fire burst at random position
    fireImpl({
      particleCount: 30,
      spread: 360,
      origin: { x, y },
      colors,
      shapes: ["square", "circle"],
      gravity: 0.8,
      drift: 0,
      decay: 0.92,
      scalar: 0.8,
    });
  }, interval);

  return { duration };
};

/**
 * Fire emoji confetti
 */
export const fireEmojisImpl = (options) => {
  initCanvas();
  if (!canvas) return {};

  const { emojis, particleCount, spread, origin, scalar } = options;

  const x = origin.x * canvas.width;
  const y = origin.y * canvas.height;

  for (let i = 0; i < particleCount; i++) {
    const angle = 270 + (Math.random() - 0.5) * spread;
    const velocity = Math.random() * 12 + 8;
    const emoji = emojis[Math.floor(Math.random() * emojis.length)];

    particles.push(
      createEmojiParticle({
        x,
        y,
        emoji,
        velocity,
        angle,
        gravity: 0.8,
        drift: 0,
        decay: 0.94,
        scalar,
      })
    );
  }

  startAnimation();
  return { particles: particles.length };
};

/**
 * Reset/clear all confetti
 */
export const resetImpl = () => {
  particles = [];

  if (animationFrame) {
    cancelAnimationFrame(animationFrame);
    animationFrame = null;
  }

  if (ctx && canvas) {
    ctx.clearRect(0, 0, canvas.width, canvas.height);
  }
};

/**
 * Placeholder confetti instance
 */
export const unsafeConfettiInstance = {
  particles: 0,
};
