// ============================================================================
// GPU Particle Physics Compute Shader
// WebGL2 Transform Feedback implementation
// ============================================================================

// Vertex shader for transform feedback (physics simulation)
#version 300 es
precision highp float;

// ============================================================================
// INPUT ATTRIBUTES (current particle state)
// ============================================================================

in vec3 a_position;
in vec3 a_velocity;
in vec2 a_life;          // x = age, y = lifetime
in vec2 a_physical;      // x = mass, y = size
in vec2 a_rotation;      // x = rotation, y = angular velocity
in vec4 a_color;

// ============================================================================
// OUTPUT (next frame state via transform feedback)
// ============================================================================

out vec3 v_position;
out vec3 v_velocity;
out vec2 v_life;
out vec2 v_physical;
out vec2 v_rotation;
out vec4 v_color;

// ============================================================================
// UNIFORMS
// ============================================================================

uniform float u_deltaTime;
uniform float u_time;
uniform vec3 u_emitterPosition;
uniform int u_maxParticles;

// Global physics
uniform vec3 u_gravity;
uniform float u_globalDrag;
uniform float u_airResistance;

// Noise parameters
uniform float u_noiseScale;
uniform float u_noiseStrength;
uniform float u_noiseSpeed;

// Bounds
uniform vec3 u_boundsMin;
uniform vec3 u_boundsMax;
uniform int u_boundsBehavior;  // 0=kill, 1=bounce, 2=wrap, 3=clamp
uniform float u_bounceDamping;

// Force field uniforms (up to 16 force fields)
#define MAX_FORCE_FIELDS 16

uniform int u_forceFieldCount;
uniform int u_forceFieldTypes[MAX_FORCE_FIELDS];
uniform vec3 u_forceFieldPositions[MAX_FORCE_FIELDS];
uniform float u_forceFieldStrengths[MAX_FORCE_FIELDS];
uniform vec4 u_forceFieldParams[MAX_FORCE_FIELDS];  // Type-specific params
uniform vec4 u_forceFieldParams2[MAX_FORCE_FIELDS]; // Additional params

// Flocking (optional)
uniform int u_flockingEnabled;
uniform float u_separationWeight;
uniform float u_alignmentWeight;
uniform float u_cohesionWeight;
uniform float u_separationRadius;
uniform float u_alignmentRadius;
uniform float u_cohesionRadius;
uniform float u_maxSpeed;
uniform float u_maxForce;

// Neighbor data texture (for flocking/spatial queries)
uniform sampler2D u_neighborTexture;
uniform int u_neighborTextureSize;

// Lifetime modulation curves (packed as textures)
uniform sampler2D u_sizeOverLifetime;
uniform sampler2D u_opacityOverLifetime;
uniform sampler2D u_colorOverLifetime;

// Audio reactivity
uniform float u_audioAmplitude;
uniform float u_audioBass;
uniform float u_audioMid;
uniform float u_audioHigh;
uniform float u_audioBeat;

// ============================================================================
// NOISE FUNCTIONS
// ============================================================================

// Simplex noise for turbulence
vec3 mod289(vec3 x) { return x - floor(x * (1.0 / 289.0)) * 289.0; }
vec4 mod289(vec4 x) { return x - floor(x * (1.0 / 289.0)) * 289.0; }
vec4 permute(vec4 x) { return mod289(((x * 34.0) + 1.0) * x); }
vec4 taylorInvSqrt(vec4 r) { return 1.79284291400159 - 0.85373472095314 * r; }

float snoise(vec3 v) {
  const vec2 C = vec2(1.0 / 6.0, 1.0 / 3.0);
  const vec4 D = vec4(0.0, 0.5, 1.0, 2.0);

  vec3 i = floor(v + dot(v, C.yyy));
  vec3 x0 = v - i + dot(i, C.xxx);

  vec3 g = step(x0.yzx, x0.xyz);
  vec3 l = 1.0 - g;
  vec3 i1 = min(g.xyz, l.zxy);
  vec3 i2 = max(g.xyz, l.zxy);

  vec3 x1 = x0 - i1 + C.xxx;
  vec3 x2 = x0 - i2 + C.yyy;
  vec3 x3 = x0 - D.yyy;

  i = mod289(i);
  vec4 p = permute(permute(permute(
    i.z + vec4(0.0, i1.z, i2.z, 1.0))
    + i.y + vec4(0.0, i1.y, i2.y, 1.0))
    + i.x + vec4(0.0, i1.x, i2.x, 1.0));

  float n_ = 0.142857142857;
  vec3 ns = n_ * D.wyz - D.xzx;

  vec4 j = p - 49.0 * floor(p * ns.z * ns.z);
  vec4 x_ = floor(j * ns.z);
  vec4 y_ = floor(j - 7.0 * x_);

  vec4 x = x_ * ns.x + ns.yyyy;
  vec4 y = y_ * ns.x + ns.yyyy;
  vec4 h = 1.0 - abs(x) - abs(y);

  vec4 b0 = vec4(x.xy, y.xy);
  vec4 b1 = vec4(x.zw, y.zw);

  vec4 s0 = floor(b0) * 2.0 + 1.0;
  vec4 s1 = floor(b1) * 2.0 + 1.0;
  vec4 sh = -step(h, vec4(0.0));

  vec4 a0 = b0.xzyw + s0.xzyw * sh.xxyy;
  vec4 a1 = b1.xzyw + s1.xzyw * sh.zzww;

  vec3 p0 = vec3(a0.xy, h.x);
  vec3 p1 = vec3(a0.zw, h.y);
  vec3 p2 = vec3(a1.xy, h.z);
  vec3 p3 = vec3(a1.zw, h.w);

  vec4 norm = taylorInvSqrt(vec4(dot(p0, p0), dot(p1, p1), dot(p2, p2), dot(p3, p3)));
  p0 *= norm.x;
  p1 *= norm.y;
  p2 *= norm.z;
  p3 *= norm.w;

  vec4 m = max(0.6 - vec4(dot(x0, x0), dot(x1, x1), dot(x2, x2), dot(x3, x3)), 0.0);
  m = m * m;
  return 42.0 * dot(m * m, vec4(dot(p0, x0), dot(p1, x1), dot(p2, x2), dot(p3, x3)));
}

// Curl noise for fluid-like motion
vec3 curlNoise(vec3 p) {
  const float e = 0.1;
  vec3 dx = vec3(e, 0.0, 0.0);
  vec3 dy = vec3(0.0, e, 0.0);
  vec3 dz = vec3(0.0, 0.0, e);

  float n1 = snoise(p + dy) - snoise(p - dy);
  float n2 = snoise(p + dz) - snoise(p - dz);
  float n3 = snoise(p + dx) - snoise(p - dx);
  float n4 = snoise(p + dz) - snoise(p - dz);
  float n5 = snoise(p + dx) - snoise(p - dx);
  float n6 = snoise(p + dy) - snoise(p - dy);

  vec3 curl = vec3(n1 - n2, n3 - n4, n5 - n6);
  float len = length(curl);
  // Guard against normalizing zero vector (produces NaN)
  return len > 0.0001 ? curl / len : vec3(0.0, 1.0, 0.0);
}

// FBM (Fractal Brownian Motion) for multi-octave noise
float fbm(vec3 p, int octaves, float lacunarity, float gain) {
  float value = 0.0;
  float amplitude = 0.5;
  float frequency = 1.0;

  for (int i = 0; i < 8; i++) {
    if (i >= octaves) break;
    value += amplitude * snoise(p * frequency);
    frequency *= lacunarity;
    amplitude *= gain;
  }

  return value;
}

// ============================================================================
// FORCE FIELD CALCULATIONS
// ============================================================================

vec3 calculateGravityForce(int index, vec3 pos, vec3 vel, float mass) {
  vec3 dir = u_forceFieldParams[index].xyz;
  float len = length(dir);
  // Guard against normalizing zero vector
  vec3 direction = len > 0.0001 ? dir / len : vec3(0.0, -1.0, 0.0);
  return direction * u_forceFieldStrengths[index];
}

vec3 calculatePointForce(int index, vec3 pos, vec3 vel, float mass) {
  vec3 toField = u_forceFieldPositions[index] - pos;
  float dist = length(toField);

  if (dist < 0.001) return vec3(0.0);

  float falloffStart = u_forceFieldParams[index].x;
  float falloffEnd = u_forceFieldParams[index].y;
  int falloffType = int(u_forceFieldParams[index].z);

  float falloff = 1.0;
  // Guard against division by zero when falloffEnd == falloffStart
  if (dist > falloffStart && falloffEnd > falloffStart) {
    float t = clamp((dist - falloffStart) / (falloffEnd - falloffStart), 0.0, 1.0);
    if (falloffType == 1) falloff = 1.0 - t;                    // Linear
    else if (falloffType == 2) falloff = 1.0 - t * t;           // Quadratic
    else if (falloffType == 3) falloff = exp(-t * 3.0);         // Exponential
    else if (falloffType == 4) falloff = smoothstep(1.0, 0.0, t); // Smoothstep
  } else if (dist > falloffEnd) {
    falloff = 0.0; // Beyond falloff range
  }

  vec3 direction = toField / dist;
  return direction * u_forceFieldStrengths[index] * falloff / (mass + 0.1);
}

vec3 calculateVortexForce(int index, vec3 pos, vec3 vel, float mass) {
  vec3 toField = pos - u_forceFieldPositions[index];
  vec3 axisRaw = u_forceFieldParams[index].xyz;
  float axisLen = length(axisRaw);
  // Guard against normalizing zero vector - default to Y-up
  vec3 axis = axisLen > 0.0001 ? axisRaw / axisLen : vec3(0.0, 1.0, 0.0);
  float inwardForce = u_forceFieldParams[index].w;

  // Project position onto plane perpendicular to axis
  float distAlongAxis = dot(toField, axis);
  vec3 radialVec = toField - axis * distAlongAxis;
  float radialDist = length(radialVec);

  if (radialDist < 0.001) return vec3(0.0);

  // Tangential force (perpendicular to radial and axis)
  vec3 tangent = cross(axis, radialVec / radialDist);

  // Inward force
  vec3 inward = -radialVec / radialDist;

  float falloffEnd = u_forceFieldParams2[index].x;
  float falloff = 1.0 - clamp(radialDist / falloffEnd, 0.0, 1.0);

  return (tangent * u_forceFieldStrengths[index] + inward * inwardForce) * falloff;
}

vec3 calculateTurbulenceForce(int index, vec3 pos, vec3 vel, float mass) {
  float scale = u_forceFieldParams[index].x;
  float speed = u_forceFieldParams[index].y;
  int octaves = int(u_forceFieldParams[index].z);
  float lacunarity = u_forceFieldParams[index].w;
  float gain = u_forceFieldParams2[index].x;

  vec3 noisePos = pos * scale + vec3(u_time * speed);

  vec3 force;
  force.x = fbm(noisePos, octaves, lacunarity, gain);
  force.y = fbm(noisePos + vec3(31.416, 0.0, 0.0), octaves, lacunarity, gain);
  force.z = fbm(noisePos + vec3(0.0, 27.183, 0.0), octaves, lacunarity, gain);

  return force * u_forceFieldStrengths[index];
}

vec3 calculateCurlForce(int index, vec3 pos, vec3 vel, float mass) {
  float scale = u_forceFieldParams[index].x;
  float speed = u_forceFieldParams[index].y;

  vec3 noisePos = pos * scale + vec3(u_time * speed);
  return curlNoise(noisePos) * u_forceFieldStrengths[index];
}

vec3 calculateDragForce(int index, vec3 pos, vec3 vel, float mass) {
  float linearDrag = u_forceFieldParams[index].x;
  float quadraticDrag = u_forceFieldParams[index].y;

  float speed = length(vel);
  if (speed < 0.001) return vec3(0.0);

  vec3 dragDir = -vel / speed;
  float dragMag = linearDrag * speed + quadraticDrag * speed * speed;

  return dragDir * dragMag * u_forceFieldStrengths[index];
}

vec3 calculateWindForce(int index, vec3 pos, vec3 vel, float mass) {
  vec3 windRaw = u_forceFieldParams[index].xyz;
  float windLen = length(windRaw);
  // Guard against normalizing zero vector - default to X direction
  vec3 windDir = windLen > 0.0001 ? windRaw / windLen : vec3(1.0, 0.0, 0.0);
  float gustStrength = u_forceFieldParams[index].w;
  float gustFreq = u_forceFieldParams2[index].x;

  // Add gusts via noise
  float gust = snoise(pos * gustFreq + vec3(u_time * 0.5)) * gustStrength;

  return windDir * (u_forceFieldStrengths[index] + gust);
}

vec3 calculateLorenzForce(int index, vec3 pos, vec3 vel, float mass) {
  // Lorenz attractor for chaotic motion
  float sigma = u_forceFieldParams[index].x;  // Default: 10
  float rho = u_forceFieldParams[index].y;    // Default: 28
  float beta = u_forceFieldParams[index].z;   // Default: 8/3

  vec3 centered = pos - u_forceFieldPositions[index];

  vec3 force;
  force.x = sigma * (centered.y - centered.x);
  force.y = centered.x * (rho - centered.z) - centered.y;
  force.z = centered.x * centered.y - beta * centered.z;

  return force * u_forceFieldStrengths[index] * 0.01;
}

vec3 calculateForceField(int index, vec3 pos, vec3 vel, float mass) {
  int fieldType = u_forceFieldTypes[index];

  if (fieldType == 0) return calculateGravityForce(index, pos, vel, mass);
  if (fieldType == 1) return calculatePointForce(index, pos, vel, mass);
  if (fieldType == 2) return calculateVortexForce(index, pos, vel, mass);
  if (fieldType == 3) return calculateTurbulenceForce(index, pos, vel, mass);
  if (fieldType == 4) return calculateDragForce(index, pos, vel, mass);
  if (fieldType == 5) return calculateWindForce(index, pos, vel, mass);
  if (fieldType == 6) return calculateCurlForce(index, pos, vel, mass);
  if (fieldType == 11) return calculateLorenzForce(index, pos, vel, mass);

  return vec3(0.0);
}

// ============================================================================
// BOUNDS HANDLING
// ============================================================================

vec3 handleBounds(vec3 pos, vec3 vel, out vec3 newVel, out bool killed) {
  killed = false;
  newVel = vel;

  vec3 newPos = pos;

  if (u_boundsBehavior == 0) {
    // Kill
    if (any(lessThan(pos, u_boundsMin)) || any(greaterThan(pos, u_boundsMax))) {
      killed = true;
    }
  }
  else if (u_boundsBehavior == 1) {
    // Bounce with overshoot clamping
    for (int i = 0; i < 3; i++) {
      if (pos[i] < u_boundsMin[i]) {
        newPos[i] = u_boundsMin[i] + (u_boundsMin[i] - pos[i]);
        newVel[i] = -vel[i] * u_bounceDamping;
        // Clamp to prevent overshoot to opposite side
        if (newPos[i] > u_boundsMax[i]) newPos[i] = u_boundsMax[i];
      }
      else if (pos[i] > u_boundsMax[i]) {
        newPos[i] = u_boundsMax[i] - (pos[i] - u_boundsMax[i]);
        newVel[i] = -vel[i] * u_bounceDamping;
        // Clamp to prevent overshoot to opposite side
        if (newPos[i] < u_boundsMin[i]) newPos[i] = u_boundsMin[i];
      }
    }
  }
  else if (u_boundsBehavior == 2) {
    // Wrap - guard against zero-dimension bounds (mod by zero is undefined)
    vec3 range = u_boundsMax - u_boundsMin;
    vec3 safeRange = vec3(
      max(range.x, 1.0),
      max(range.y, 1.0),
      max(range.z, 1.0)
    );
    newPos = mod(pos - u_boundsMin, safeRange) + u_boundsMin;
  }
  else if (u_boundsBehavior == 3) {
    // Clamp
    newPos = clamp(pos, u_boundsMin, u_boundsMax);
    // Kill velocity on clamped axes
    for (int i = 0; i < 3; i++) {
      if (pos[i] <= u_boundsMin[i] || pos[i] >= u_boundsMax[i]) {
        newVel[i] = 0.0;
      }
    }
  }

  return newPos;
}

// ============================================================================
// LIFETIME MODULATION
// ============================================================================

float sampleCurve(sampler2D curve, float t) {
  return texture(curve, vec2(t, 0.5)).r;
}

vec4 sampleColorGradient(sampler2D gradient, float t) {
  return texture(gradient, vec2(t, 0.5));
}

// ============================================================================
// MAIN SIMULATION
// ============================================================================

void main() {
  // Read current state
  vec3 pos = a_position;
  vec3 vel = a_velocity;
  float age = a_life.x;
  float lifetime = a_life.y;
  float mass = a_physical.x;
  float size = a_physical.y;
  float rotation = a_rotation.x;
  float angularVel = a_rotation.y;
  vec4 color = a_color;

  // Check if particle is dead
  if (age >= lifetime || lifetime <= 0.0) {
    // Output dead particle (will be recycled)
    v_position = vec3(0.0);
    v_velocity = vec3(0.0);
    v_life = vec2(lifetime + 1.0, 0.0);  // Mark as dead
    v_physical = vec2(0.0);
    v_rotation = vec2(0.0);
    v_color = vec4(0.0);
    return;
  }

  // Calculate life ratio for modulation
  float lifeRatio = age / lifetime;

  // Accumulate forces
  vec3 totalForce = vec3(0.0);

  // Global gravity
  totalForce += u_gravity;

  // Process all force fields
  for (int i = 0; i < MAX_FORCE_FIELDS; i++) {
    if (i >= u_forceFieldCount) break;
    totalForce += calculateForceField(i, pos, vel, mass);
  }

  // Apply forces (F = ma -> a = F/m)
  vec3 acceleration = totalForce / max(mass, 0.1);

  // Integrate velocity (semi-implicit Euler)
  vel += acceleration * u_deltaTime;

  // Apply global drag
  float dragFactor = 1.0 - u_globalDrag * u_deltaTime;
  vel *= dragFactor;

  // Apply air resistance (velocity-squared drag)
  float speed = length(vel);
  if (speed > 0.001) {
    // Use safeMass to prevent division by zero (consistent with line 442)
    float safeMass = max(mass, 0.1);
    float airDrag = u_airResistance * speed * speed * u_deltaTime / safeMass;
    vel -= normalize(vel) * min(airDrag, speed);
  }

  // Integrate position
  pos += vel * u_deltaTime;

  // Handle bounds
  vec3 newVel;
  bool killed;
  pos = handleBounds(pos, vel, newVel, killed);
  vel = newVel;

  if (killed) {
    v_life = vec2(lifetime + 1.0, 0.0);
    v_position = pos;
    v_velocity = vel;
    v_physical = a_physical;
    v_rotation = a_rotation;
    v_color = color;
    return;
  }

  // Update rotation
  rotation += angularVel * u_deltaTime;

  // Apply lifetime modulation
  float sizeMod = sampleCurve(u_sizeOverLifetime, lifeRatio);
  float opacityMod = sampleCurve(u_opacityOverLifetime, lifeRatio);
  vec4 colorMod = sampleColorGradient(u_colorOverLifetime, lifeRatio);

  // Increment age
  age += u_deltaTime;

  // Output updated state
  v_position = pos;
  v_velocity = vel;
  v_life = vec2(age, lifetime);
  v_physical = vec2(mass, size * sizeMod);
  v_rotation = vec2(rotation, angularVel);
  v_color = vec4(colorMod.rgb, colorMod.a * opacityMod);
}
