// ============================================================================
// Spring/Soft Body Simulation - WebGPU Compute Shader
// Position-Based Dynamics with Verlet integration
// ============================================================================

// Particle data structure
struct Particle {
  position: vec3f,
  velocity: vec3f,
  age: f32,
  lifetime: f32,
  mass: f32,
  size: f32,
  rotation: f32,
  angularVelocity: f32,
  color: vec4f,
}

// Spring definition
struct Spring {
  particleA: u32,
  particleB: u32,
  restLength: f32,
  stiffness: f32,
  damping: f32,
  breakThreshold: f32,
  active: u32, // 0 = inactive, 1 = active
  padding: u32,
}

// Pin constraint
struct Pin {
  particleIndex: u32,
  active: u32,
  position: vec3f,
  padding: f32,
}

// Simulation parameters
struct SpringParams {
  gravity: vec3f,
  deltaTime: f32,
  particleCount: u32,
  springCount: u32,
  pinCount: u32,
  solverIterations: u32,
  globalStiffness: f32,
  globalDamping: f32,
  padding: vec2f,
}

// Bindings
@group(0) @binding(0) var<storage, read_write> particles: array<Particle>;
@group(0) @binding(1) var<storage, read_write> prevPositions: array<vec3f>;
@group(0) @binding(2) var<storage, read_write> springs: array<Spring>;
@group(0) @binding(3) var<storage, read> pins: array<Pin>;
@group(0) @binding(4) var<uniform> params: SpringParams;

// ============================================================================
// PASS 1: VERLET INTEGRATION (Position prediction)
// ============================================================================

@compute @workgroup_size(256)
fn verletIntegrate(@builtin(global_invocation_id) id: vec3u) {
  let i = id.x;
  if (i >= params.particleCount) { return; }

  var p = particles[i];
  
  // Skip dead particles
  if (p.lifetime <= 0.0 || p.age >= p.lifetime) { return; }

  let dt = params.deltaTime;
  let dt2 = dt * dt;

  // Current position
  let pos = p.position;
  
  // Previous position
  let prevPos = prevPositions[i];

  // Verlet: new_pos = 2 * pos - prev_pos + acceleration * dt²
  let acceleration = params.gravity;
  let newPos = 2.0 * pos - prevPos + acceleration * dt2;

  // Store current as previous
  prevPositions[i] = pos;

  // Update position
  p.position = newPos;

  // Derive velocity from position change
  p.velocity = (newPos - pos) / dt;

  particles[i] = p;
}

// ============================================================================
// PASS 2: SPRING CONSTRAINT SOLVING
// ============================================================================

@compute @workgroup_size(256)
fn solveSpringConstraints(@builtin(global_invocation_id) id: vec3u) {
  let springIdx = id.x;
  if (springIdx >= params.springCount) { return; }

  var spring = springs[springIdx];
  
  // Skip inactive springs
  if (spring.active == 0u) { return; }

  let idxA = spring.particleA;
  let idxB = spring.particleB;

  // Bounds check
  if (idxA >= params.particleCount || idxB >= params.particleCount) { return; }

  var pA = particles[idxA];
  var pB = particles[idxB];

  // Skip if either particle is dead
  if (pA.lifetime <= 0.0 || pA.age >= pA.lifetime) { return; }
  if (pB.lifetime <= 0.0 || pB.age >= pB.lifetime) { return; }

  // Calculate current length
  let delta = pB.position - pA.position;
  let dist = length(delta);

  if (dist < 0.0001) { return; }

  // Check for breaking
  if (spring.breakThreshold > 0.0) {
    let stretch = abs(dist - spring.restLength) / spring.restLength;
    if (stretch > spring.breakThreshold) {
      springs[springIdx].active = 0u;
      return;
    }
  }

  // Calculate correction
  let diff = (dist - spring.restLength) / dist;
  let correction = delta * diff * 0.5; // 0.5 for relaxation

  // Mass-weighted correction
  let massA = max(pA.mass, 0.1);
  let massB = max(pB.mass, 0.1);
  let invMassA = 1.0 / massA;
  let invMassB = 1.0 / massB;
  let invMassSum = invMassA + invMassB;

  if (invMassSum < 0.0001) { return; }

  let weightA = invMassA / invMassSum;
  let weightB = invMassB / invMassSum;

  // Apply corrections with stiffness factor
  let stiffnessFactor = spring.stiffness * params.globalStiffness / f32(params.solverIterations);
  
  pA.position += correction * weightA * stiffnessFactor;
  pB.position -= correction * weightB * stiffnessFactor;

  particles[idxA] = pA;
  particles[idxB] = pB;
}

// ============================================================================
// PASS 3: PIN CONSTRAINTS
// ============================================================================

@compute @workgroup_size(256)
fn applyPins(@builtin(global_invocation_id) id: vec3u) {
  let pinIdx = id.x;
  if (pinIdx >= params.pinCount) { return; }

  let pin = pins[pinIdx];
  
  if (pin.active == 0u) { return; }
  if (pin.particleIndex >= params.particleCount) { return; }

  var p = particles[pin.particleIndex];

  // Force position to pin location
  p.position = pin.position;
  p.velocity = vec3f(0.0);

  // Update previous position for Verlet
  prevPositions[pin.particleIndex] = pin.position;

  particles[pin.particleIndex] = p;
}

// ============================================================================
// PASS 4: EULER INTEGRATION (Alternative - force-based)
// Used when Verlet isn't appropriate
// ============================================================================

@compute @workgroup_size(256)
fn eulerSpringForces(@builtin(global_invocation_id) id: vec3u) {
  let springIdx = id.x;
  if (springIdx >= params.springCount) { return; }

  let spring = springs[springIdx];
  
  if (spring.active == 0u) { return; }

  let idxA = spring.particleA;
  let idxB = spring.particleB;

  if (idxA >= params.particleCount || idxB >= params.particleCount) { return; }

  var pA = particles[idxA];
  var pB = particles[idxB];

  if (pA.lifetime <= 0.0 || pA.age >= pA.lifetime) { return; }
  if (pB.lifetime <= 0.0 || pB.age >= pB.lifetime) { return; }

  // Calculate spring vector
  let delta = pB.position - pA.position;
  let dist = length(delta);

  if (dist < 0.0001) { return; }

  // Normalize direction
  let n = delta / dist;

  // Hooke's Law: F = -k * (x - rest)
  let displacement = dist - spring.restLength;
  let springForce = spring.stiffness * params.globalStiffness * displacement;

  // Damping: F_damp = -c * v_relative_along_spring
  let relVel = pB.velocity - pA.velocity;
  let relVelAlongSpring = dot(relVel, n);
  let dampingForce = spring.damping * params.globalDamping * relVelAlongSpring;

  // Total force magnitude
  let forceMag = springForce + dampingForce;
  let force = n * forceMag;

  let dt = params.deltaTime;
  let massA = max(pA.mass, 0.1);
  let massB = max(pB.mass, 0.1);

  // Apply to velocities (F = ma -> a = F/m)
  pA.velocity += (force / massA) * dt;
  pB.velocity -= (force / massB) * dt;

  particles[idxA] = pA;
  particles[idxB] = pB;
}
