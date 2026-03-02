// ============================================================================
// SPH Fluid Simulation - WebGPU Compute Shader
// Based on Müller et al. "Particle-Based Fluid Simulation"
// ============================================================================

// Particle data structure (matches CPU layout)
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

// SPH-specific data per particle
struct SPHData {
  density: f32,
  pressure: f32,
  force: vec3f,
}

// Simulation parameters
struct SPHParams {
  smoothingRadius: f32,
  restDensity: f32,
  gasConstant: f32,
  viscosity: f32,
  surfaceTension: f32,
  gravity: vec3f,
  deltaTime: f32,
  particleCount: u32,
  boundsMin: vec3f,
  boundsMax: vec3f,
  cellSize: f32,
  gridDimX: u32,
  gridDimY: u32,
  gridDimZ: u32,
}

// Bindings
@group(0) @binding(0) var<storage, read_write> particles: array<Particle>;
@group(0) @binding(1) var<storage, read_write> sphData: array<SPHData>;
@group(0) @binding(2) var<uniform> params: SPHParams;

// Spatial hash grid (cell start/end indices)
@group(0) @binding(3) var<storage, read> cellStart: array<u32>;
@group(0) @binding(4) var<storage, read> cellEnd: array<u32>;
@group(0) @binding(5) var<storage, read> particleIndices: array<u32>;

// Constants
const PI: f32 = 3.14159265359;

// ============================================================================
// KERNEL FUNCTIONS
// ============================================================================

// Poly6 kernel - for density calculation
fn poly6Kernel(r: f32, h: f32) -> f32 {
  if (r > h || r < 0.0) { return 0.0; }
  let h2 = h * h;
  let r2 = r * r;
  let diff = h2 - r2;
  // W = 315 / (64 * π * h^9) * (h² - r²)³
  return (315.0 / (64.0 * PI * pow(h, 9.0))) * diff * diff * diff;
}

// Poly6 gradient - for surface tension
fn poly6Gradient(r_vec: vec3f, r: f32, h: f32) -> vec3f {
  if (r > h || r < 0.0001) { return vec3f(0.0); }
  let h2 = h * h;
  let r2 = r * r;
  let diff = h2 - r2;
  // ∇W = -945 / (32 * π * h^9) * (h² - r²)² * r_vec
  let coeff = (-945.0 / (32.0 * PI * pow(h, 9.0))) * diff * diff;
  return coeff * r_vec;
}

// Spiky gradient - for pressure forces (non-zero at r=0)
fn spikyGradient(r_vec: vec3f, r: f32, h: f32) -> vec3f {
  if (r > h || r < 0.0001) { return vec3f(0.0); }
  let diff = h - r;
  // ∇W = -45 / (π * h^6) * (h - r)² * r_normalized
  let coeff = (-45.0 / (PI * pow(h, 6.0))) * diff * diff / r;
  return coeff * r_vec;
}

// Viscosity Laplacian - always positive (dampens relative motion)
fn viscosityLaplacian(r: f32, h: f32) -> f32 {
  if (r > h || r < 0.0) { return 0.0; }
  // ∇²W = 45 / (π * h^6) * (h - r)
  return (45.0 / (PI * pow(h, 6.0))) * (h - r);
}

// ============================================================================
// SPATIAL HASH FUNCTIONS
// ============================================================================

fn positionToCell(pos: vec3f) -> vec3i {
  let cellSize = max(params.cellSize, 0.001);
  return vec3i(
    i32(floor((pos.x - params.boundsMin.x) / cellSize)),
    i32(floor((pos.y - params.boundsMin.y) / cellSize)),
    i32(floor((pos.z - params.boundsMin.z) / cellSize))
  );
}

fn cellToIndex(cell: vec3i) -> u32 {
  // Clamp to grid bounds
  let cx = clamp(cell.x, 0, i32(params.gridDimX) - 1);
  let cy = clamp(cell.y, 0, i32(params.gridDimY) - 1);
  let cz = clamp(cell.z, 0, i32(params.gridDimZ) - 1);
  return u32(cx) + u32(cy) * params.gridDimX + u32(cz) * params.gridDimX * params.gridDimY;
}

fn isValidCell(cell: vec3i) -> bool {
  return cell.x >= 0 && cell.x < i32(params.gridDimX) &&
         cell.y >= 0 && cell.y < i32(params.gridDimY) &&
         cell.z >= 0 && cell.z < i32(params.gridDimZ);
}

// ============================================================================
// PASS 1: COMPUTE DENSITY AND PRESSURE
// ============================================================================

@compute @workgroup_size(256)
fn computeDensity(@builtin(global_invocation_id) id: vec3u) {
  let i = id.x;
  if (i >= params.particleCount) { return; }

  let p = particles[i];
  
  // Skip dead particles
  if (p.lifetime <= 0.0 || p.age >= p.lifetime) {
    sphData[i].density = 0.0;
    sphData[i].pressure = 0.0;
    return;
  }

  let h = params.smoothingRadius;
  var density: f32 = 0.0;

  // Self contribution
  density += p.mass * poly6Kernel(0.0, h);

  // Get cell for this particle
  let cell = positionToCell(p.position);

  // Search neighboring cells (3x3x3)
  for (var dz: i32 = -1; dz <= 1; dz++) {
    for (var dy: i32 = -1; dy <= 1; dy++) {
      for (var dx: i32 = -1; dx <= 1; dx++) {
        let neighborCell = cell + vec3i(dx, dy, dz);
        
        if (!isValidCell(neighborCell)) { continue; }
        
        let cellIdx = cellToIndex(neighborCell);
        let start = cellStart[cellIdx];
        let end = cellEnd[cellIdx];

        // Iterate particles in this cell
        for (var j = start; j < end; j++) {
          let neighborIdx = particleIndices[j];
          if (neighborIdx == i) { continue; }

          let neighbor = particles[neighborIdx];
          if (neighbor.lifetime <= 0.0 || neighbor.age >= neighbor.lifetime) { continue; }

          let r_vec = p.position - neighbor.position;
          let r = length(r_vec);

          density += neighbor.mass * poly6Kernel(r, h);
        }
      }
    }
  }

  // Store density
  sphData[i].density = density;

  // Compute pressure using equation of state
  // P = k * (ρ - ρ₀)
  sphData[i].pressure = max(0.0, params.gasConstant * (density - params.restDensity));
}

// ============================================================================
// PASS 2: COMPUTE FORCES
// ============================================================================

@compute @workgroup_size(256)
fn computeForces(@builtin(global_invocation_id) id: vec3u) {
  let i = id.x;
  if (i >= params.particleCount) { return; }

  let p = particles[i];
  
  // Skip dead particles
  if (p.lifetime <= 0.0 || p.age >= p.lifetime) {
    sphData[i].force = vec3f(0.0);
    return;
  }

  let density_i = sphData[i].density;
  if (density_i < 0.0001) {
    sphData[i].force = vec3f(0.0);
    return;
  }

  let pressure_i = sphData[i].pressure;
  let h = params.smoothingRadius;

  var fPressure = vec3f(0.0);
  var fViscosity = vec3f(0.0);
  var colorGrad = vec3f(0.0);
  var colorLaplacian: f32 = 0.0;

  let cell = positionToCell(p.position);

  // Search neighboring cells
  for (var dz: i32 = -1; dz <= 1; dz++) {
    for (var dy: i32 = -1; dy <= 1; dy++) {
      for (var dx: i32 = -1; dx <= 1; dx++) {
        let neighborCell = cell + vec3i(dx, dy, dz);
        
        if (!isValidCell(neighborCell)) { continue; }
        
        let cellIdx = cellToIndex(neighborCell);
        let start = cellStart[cellIdx];
        let end = cellEnd[cellIdx];

        for (var j = start; j < end; j++) {
          let neighborIdx = particleIndices[j];
          if (neighborIdx == i) { continue; }

          let neighbor = particles[neighborIdx];
          if (neighbor.lifetime <= 0.0 || neighbor.age >= neighbor.lifetime) { continue; }

          let density_j = sphData[neighborIdx].density;
          if (density_j < 0.0001) { continue; }

          let pressure_j = sphData[neighborIdx].pressure;
          let r_vec = p.position - neighbor.position;
          let r = length(r_vec);

          if (r > h || r < 0.0001) { continue; }

          // Pressure force: -∑ m_j * (P_i + P_j) / (2 * ρ_j) * ∇W_spiky
          let pressureGrad = spikyGradient(r_vec, r, h);
          let pressureTerm = neighbor.mass * (pressure_i + pressure_j) / (2.0 * density_j);
          fPressure -= pressureTerm * pressureGrad;

          // Viscosity force: μ * ∑ m_j * (v_j - v_i) / ρ_j * ∇²W_viscosity
          let viscLaplacian = viscosityLaplacian(r, h);
          let viscTerm = neighbor.mass / density_j * viscLaplacian;
          fViscosity += viscTerm * (neighbor.velocity - p.velocity);

          // Surface tension (color field)
          let colorGradContrib = poly6Gradient(r_vec, r, h);
          let colorTerm = neighbor.mass / density_j;
          colorGrad += colorTerm * colorGradContrib;
          colorLaplacian += colorTerm * poly6Kernel(r, h);
        }
      }
    }
  }

  // Apply viscosity coefficient
  fViscosity *= params.viscosity;

  // Surface tension: -σ * κ * n
  var fSurface = vec3f(0.0);
  let gradMag = length(colorGrad);
  if (gradMag > 0.1) {
    let curvature = -colorLaplacian / gradMag;
    fSurface = params.surfaceTension * curvature * colorGrad / gradMag;
  }

  // Total force
  sphData[i].force = fPressure + fViscosity + fSurface;
}

// ============================================================================
// PASS 3: INTEGRATE
// ============================================================================

@compute @workgroup_size(256)
fn integrate(@builtin(global_invocation_id) id: vec3u) {
  let i = id.x;
  if (i >= params.particleCount) { return; }

  var p = particles[i];
  
  // Skip dead particles
  if (p.lifetime <= 0.0 || p.age >= p.lifetime) { return; }

  let density = sphData[i].density;
  if (density < 0.0001) { return; }

  let dt = params.deltaTime;

  // Acceleration = Force / density + gravity
  let acceleration = sphData[i].force / density + params.gravity;

  // Update velocity
  p.velocity += acceleration * dt;

  // Update position
  p.position += p.velocity * dt;

  // Boundary handling (simple bounce)
  for (var axis = 0u; axis < 3u; axis++) {
    if (p.position[axis] < params.boundsMin[axis]) {
      p.position[axis] = params.boundsMin[axis];
      p.velocity[axis] *= -0.5; // Damped bounce
    }
    if (p.position[axis] > params.boundsMax[axis]) {
      p.position[axis] = params.boundsMax[axis];
      p.velocity[axis] *= -0.5;
    }
  }

  particles[i] = p;
}
