/**
 * Particle System Shaders
 * Extracted from GPUParticleSystem.ts to reduce file size
 */

// GLSL Simplex Noise functions (shared by shaders)
const GLSL_NOISE = `
vec3 mod289(vec3 x) { return x - floor(x * (1.0 / 289.0)) * 289.0; }
vec4 mod289(vec4 x) { return x - floor(x * (1.0 / 289.0)) * 289.0; }
vec4 permute(vec4 x) { return mod289(((x*34.0)+1.0)*x); }
vec4 taylorInvSqrt(vec4 r) { return 1.79284291400159 - 0.85373472095314 * r; }

float snoise(vec3 v) {
  const vec2 C = vec2(1.0/6.0, 1.0/3.0);
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
  vec4 norm = taylorInvSqrt(vec4(dot(p0,p0), dot(p1,p1), dot(p2,p2), dot(p3,p3)));
  p0 *= norm.x; p1 *= norm.y; p2 *= norm.z; p3 *= norm.w;
  vec4 m = max(0.6 - vec4(dot(x0,x0), dot(x1,x1), dot(x2,x2), dot(x3,x3)), 0.0);
  m = m * m;
  return 42.0 * dot(m*m, vec4(dot(p0,x0), dot(p1,x1), dot(p2,x2), dot(p3,x3)));
}
`;

// Force calculation function for GPU physics
const GLSL_FORCE_CALC = `
vec3 calculateForce(int fieldIndex, vec3 pos, vec3 vel, float mass) {
  vec4 row0 = texelFetch(u_forceFields, ivec2(fieldIndex, 0), 0);
  vec4 row1 = texelFetch(u_forceFields, ivec2(fieldIndex, 1), 0);
  vec4 row2 = texelFetch(u_forceFields, ivec2(fieldIndex, 2), 0);
  vec4 row3 = texelFetch(u_forceFields, ivec2(fieldIndex, 3), 0);
  vec3 fieldPos = row0.xyz;
  int fieldType = int(row0.w);
  float strength = row1.x;
  float falloffStart = row1.y;
  float falloffEnd = row1.z;
  int falloffType = int(row1.w);
  vec3 toField = fieldPos - pos;
  float dist = length(toField);
  float falloff = 1.0;
  if (dist > falloffStart && falloffEnd > falloffStart) {
    float t = clamp((dist - falloffStart) / (falloffEnd - falloffStart), 0.0, 1.0);
    if (falloffType == 1) falloff = 1.0 - t;
    else if (falloffType == 2) falloff = 1.0 - t * t;
    else if (falloffType == 3) falloff = exp(-t * 3.0);
    else if (falloffType == 4) falloff = 1.0 - (3.0 * t * t - 2.0 * t * t * t);
  }
  vec3 force = vec3(0.0);
  float effectiveStrength = strength * falloff;
  if (fieldType == 0) { force = row2.xyz * effectiveStrength; }
  else if (fieldType == 1) {
    if (dist > 0.001) { force = normalize(toField) * effectiveStrength / max(mass, 0.1); }
  }
  else if (fieldType == 2) {
    if (dist > 0.001) {
      vec3 axis = normalize(row2.xyz);
      vec3 tangent = normalize(cross(axis, toField));
      force = tangent * effectiveStrength + normalize(toField) * row2.w;
    }
  }
  else if (fieldType == 3) {
    float noiseScale = row3.x;
    float noiseSpeed = row3.y;
    vec3 noisePos = pos * noiseScale + vec3(u_time * noiseSpeed);
    force.x = snoise(noisePos) * effectiveStrength;
    force.y = snoise(noisePos + vec3(100.0)) * effectiveStrength;
    force.z = snoise(noisePos + vec3(200.0)) * effectiveStrength;
  }
  else if (fieldType == 4) {
    float linearDrag = row3.x;
    float quadDrag = row3.y;
    float speed = length(vel);
    if (speed > 0.001) {
      float dragMag = linearDrag * speed + quadDrag * speed * speed;
      force = -normalize(vel) * dragMag * effectiveStrength;
    }
  }
  else if (fieldType == 5) {
    // Guard against normalizing zero vector
    vec3 windDirRaw = row2.xyz;
    float windLen = length(windDirRaw);
    vec3 windDir = windLen > 0.0001 ? windDirRaw / windLen : vec3(1.0, 0.0, 0.0);
    float gustStrength = row3.x;
    float gustFreq = row3.y;
    float gust = sin(u_time * gustFreq) * gustStrength;
    force = windDir * (effectiveStrength + gust);
  }
  // Type 6: Lorenz Attractor (chaotic motion)
  else if (fieldType == 6) {
    float sigma = row2.x;   // Default: 10.0
    float rho = row2.y;     // Default: 28.0
    float beta = row2.z;    // Default: 8.0/3.0
    // Get position relative to attractor center
    vec3 rel = pos - fieldPos;
    // Lorenz equations (scaled for visualization)
    float scale = 0.01; // Scale factor for visual effect
    float dx = sigma * (rel.y - rel.x);
    float dy = rel.x * (rho - rel.z * scale) - rel.y;
    float dz = rel.x * rel.y * scale - beta * rel.z;
    force = vec3(dx, dy, dz) * effectiveStrength * 0.1;
  }
  // Type 7: Curl Noise (divergence-free turbulence)
  else if (fieldType == 7) {
    float noiseScale = row3.x;
    float noiseSpeed = row3.y;
    float eps = 0.01;
    vec3 noisePos = pos * noiseScale + vec3(u_time * noiseSpeed);
    // Compute curl of noise field for divergence-free flow
    float n1 = snoise(noisePos + vec3(eps, 0.0, 0.0));
    float n2 = snoise(noisePos - vec3(eps, 0.0, 0.0));
    float n3 = snoise(noisePos + vec3(0.0, eps, 0.0));
    float n4 = snoise(noisePos - vec3(0.0, eps, 0.0));
    float n5 = snoise(noisePos + vec3(0.0, 0.0, eps));
    float n6 = snoise(noisePos - vec3(0.0, 0.0, eps));
    force.x = (n3 - n4 - n5 + n6) / (2.0 * eps);
    force.y = (n5 - n6 - n1 + n2) / (2.0 * eps);
    force.z = (n1 - n2 - n3 + n4) / (2.0 * eps);
    force *= effectiveStrength;
  }
  // Type 8: Magnetic Field (cross product with velocity)
  else if (fieldType == 8) {
    // Guard against normalizing zero vector
    vec3 fieldDirRaw = row2.xyz;
    float fieldLen = length(fieldDirRaw);
    vec3 fieldDir = fieldLen > 0.0001 ? fieldDirRaw / fieldLen : vec3(0.0, 1.0, 0.0);
    float charge = row3.x; // Particle "charge"
    // Lorentz force: F = q * (v × B)
    force = cross(vel, fieldDir) * charge * effectiveStrength;
  }
  // Type 9: Orbit (centripetal force for circular motion)
  else if (fieldType == 9) {
    float orbitRadius = row2.w;
    // Guard against normalizing zero vector
    vec3 axisRaw = row2.xyz;
    float axisLen = length(axisRaw);
    vec3 axis = axisLen > 0.0001 ? axisRaw / axisLen : vec3(0.0, 1.0, 0.0);
    // Project position onto plane perpendicular to axis
    float distAlongAxis = dot(toField, axis);
    vec3 radialVec = -toField + axis * distAlongAxis;
    float radialDist = length(radialVec);
    if (radialDist > 0.001) {
      // Tangential force for orbit
      vec3 tangent = normalize(cross(axis, radialVec));
      // Radial correction to maintain orbit radius
      vec3 radialDir = radialVec / radialDist;
      float radiusError = radialDist - orbitRadius;
      force = tangent * effectiveStrength - radialDir * radiusError * effectiveStrength * 0.5;
    }
  }
  return force;
}
`;

/**
 * Transform Feedback Vertex Shader for GPU Physics
 */
export const TRANSFORM_FEEDBACK_VERTEX_SHADER = `#version 300 es
precision highp float;
layout(location = 0) in vec3 a_position;
layout(location = 1) in vec3 a_velocity;
layout(location = 2) in vec2 a_life;
layout(location = 3) in vec2 a_physical;
layout(location = 4) in vec2 a_rotation;
layout(location = 5) in vec4 a_color;
out vec3 tf_position;
out vec3 tf_velocity;
out vec2 tf_life;
out vec2 tf_physical;
out vec2 tf_rotation;
out vec4 tf_color;
uniform float u_deltaTime;
uniform float u_time;
uniform int u_forceFieldCount;
uniform sampler2D u_forceFields;
${GLSL_NOISE}
${GLSL_FORCE_CALC}
void main() {
  if (a_life.y <= 0.0 || a_life.x >= a_life.y) {
    tf_position = a_position;
    tf_velocity = a_velocity;
    tf_life = a_life;
    tf_physical = a_physical;
    tf_rotation = a_rotation;
    tf_color = a_color;
    return;
  }
  vec3 pos = a_position;
  vec3 vel = a_velocity;
  float age = a_life.x;
  float lifetime = a_life.y;
  float mass = a_physical.x;
  float size = a_physical.y;
  float rotation = a_rotation.x;
  float angularVel = a_rotation.y;
  vec3 totalForce = vec3(0.0);
  for (int i = 0; i < u_forceFieldCount; i++) {
    totalForce += calculateForce(i, pos, vel, mass);
  }
  vec3 acceleration = totalForce / max(mass, 0.1);
  vel += acceleration * u_deltaTime;
  pos += vel * u_deltaTime;
  rotation += angularVel * u_deltaTime;
  age += u_deltaTime;
  float lifeRatio = age / lifetime;
  float sizeMod = 1.0 - lifeRatio * 0.5;
  size = a_physical.y * sizeMod;
  float opacityMod = 1.0 - lifeRatio;
  tf_position = pos;
  tf_velocity = vel;
  tf_life = vec2(age, lifetime);
  tf_physical = vec2(mass, size);
  tf_rotation = vec2(rotation, angularVel);
  tf_color = vec4(a_color.rgb, a_color.a * opacityMod);
}
`;

/**
 * Transform Feedback Fragment Shader (minimal, required but unused)
 */
export const TRANSFORM_FEEDBACK_FRAGMENT_SHADER = `#version 300 es
precision highp float;
out vec4 fragColor;
void main() { fragColor = vec4(0.0); }
`;

/**
 * Particle Render Vertex Shader
 * Supports:
 * - Standard billboard rendering
 * - Velocity-based motion blur (stretched billboards)
 * - Per-particle rotation
 */
export const PARTICLE_VERTEX_SHADER = `
precision highp float;
attribute vec3 position;  // 3D for mesh mode, 2D+0 for billboard mode
attribute vec2 uv;
attribute vec3 i_position;
attribute vec3 i_velocity;
attribute vec2 i_life;
attribute vec2 i_physical;
attribute vec2 i_rotation;
attribute vec4 i_color;
uniform mat4 modelViewMatrix;
uniform mat4 projectionMatrix;
uniform vec3 cameraPosition;
// Motion blur uniforms
uniform int motionBlurEnabled;
uniform float motionBlurStrength;
uniform float minStretch;
uniform float maxStretch;
// LOD uniforms
uniform int lodEnabled;
uniform vec3 lodDistances;  // [near, mid, far] distances
uniform vec3 lodSizeMultipliers;  // [near, mid, far] size multipliers
// 3D mesh mode
uniform int meshMode3D;  // 0 = billboard, 1 = 3D mesh
// DoF uniforms
uniform int dofEnabled;
uniform float dofFocusDistance;
uniform float dofFocusRange;
uniform float dofMaxBlur;
varying vec2 vUv;
varying vec4 vColor;
varying float vLifeRatio;
varying float vDepth;  // Distance from camera for DoF

// Calculate LOD size multiplier based on camera distance
float getLODMultiplier(float dist) {
  if (lodEnabled == 0) return 1.0;
  
  if (dist < lodDistances.x) {
    return lodSizeMultipliers.x;  // Near: full detail
  } else if (dist < lodDistances.y) {
    // Interpolate between near and mid
    float t = (dist - lodDistances.x) / (lodDistances.y - lodDistances.x);
    return mix(lodSizeMultipliers.x, lodSizeMultipliers.y, t);
  } else if (dist < lodDistances.z) {
    // Interpolate between mid and far
    float t = (dist - lodDistances.y) / (lodDistances.z - lodDistances.y);
    return mix(lodSizeMultipliers.y, lodSizeMultipliers.z, t);
  } else {
    return lodSizeMultipliers.z;  // Far: minimum detail
  }
}

void main() {
  if (i_life.y <= 0.0 || i_life.x >= i_life.y) {
    gl_Position = vec4(0.0, 0.0, -1000.0, 1.0);
    return;
  }

  // Calculate distance to camera for LOD
  float distToCamera = length(i_position - cameraPosition);
  float lodMult = getLODMultiplier(distToCamera);
  
  // Apply LOD multiplier to size
  float size = i_physical.y * lodMult;
  float rotation = i_rotation.x;
  float lifeRatio = i_life.x / i_life.y;

  // Camera basis vectors
  vec3 cameraRight = vec3(modelViewMatrix[0][0], modelViewMatrix[1][0], modelViewMatrix[2][0]);
  vec3 cameraUp = vec3(modelViewMatrix[0][1], modelViewMatrix[1][1], modelViewMatrix[2][1]);
  vec3 cameraForward = vec3(modelViewMatrix[0][2], modelViewMatrix[1][2], modelViewMatrix[2][2]);

  vec3 vertexPos;

  if (meshMode3D == 1) {
    // 3D MESH MODE: position is 3D, apply rotation and scale
    vec3 meshPos = vec3(position.x, position.y, position.z);
    
    // Apply rotation around Y axis (heading)
    float cosR = cos(rotation);
    float sinR = sin(rotation);
    vec3 rotatedPos = vec3(
      meshPos.x * cosR - meshPos.z * sinR,
      meshPos.y,
      meshPos.x * sinR + meshPos.z * cosR
    );
    
    // Apply scale
    vertexPos = i_position + rotatedPos * size;
  } else {
    // BILLBOARD MODE: position is 2D, face camera
    vec2 offsetPos = vec2(position.x, position.y);

    // Motion blur: stretch billboard along velocity direction
    if (motionBlurEnabled == 1) {
      float speed = length(i_velocity);
      if (speed > 0.01) {
        // Project velocity onto camera plane
        vec3 velNorm = normalize(i_velocity);
        float velRight = dot(velNorm, cameraRight);
        float velUp = dot(velNorm, cameraUp);
        // Guard against normalizing zero 2D vector (velocity parallel to camera)
        float velDir2DLen = length(vec2(velRight, velUp));
        vec2 velDir2D = velDir2DLen > 0.0001 ? vec2(velRight, velUp) / velDir2DLen : vec2(1.0, 0.0);

        // Calculate stretch factor based on speed
        float stretch = clamp(speed * motionBlurStrength, minStretch, maxStretch);

        // Rotate and stretch the quad along velocity direction
        float angle = atan(velDir2D.y, velDir2D.x);
        float cosA = cos(angle);
        float sinA = sin(angle);

        // Apply rotation to align with velocity, then stretch in X
        vec2 rotated = vec2(
          offsetPos.x * cosA - offsetPos.y * sinA,
          offsetPos.x * sinA + offsetPos.y * cosA
        );
        offsetPos = vec2(rotated.x * stretch, rotated.y);

        // Rotate back to world space
        offsetPos = vec2(
          offsetPos.x * cosA + offsetPos.y * sinA,
          -offsetPos.x * sinA + offsetPos.y * cosA
        );
      }
    }

    // Apply per-particle rotation (if no motion blur or in addition to)
    if (motionBlurEnabled == 0) {
      float cosR = cos(rotation);
      float sinR = sin(rotation);
      offsetPos = vec2(
        offsetPos.x * cosR - offsetPos.y * sinR,
        offsetPos.x * sinR + offsetPos.y * cosR
      );
    }

    vertexPos = i_position + cameraRight * offsetPos.x * size + cameraUp * offsetPos.y * size;
  }
  gl_Position = projectionMatrix * modelViewMatrix * vec4(vertexPos, 1.0);
  vUv = uv;
  vColor = i_color;
  vLifeRatio = lifeRatio;
  // Compute depth from camera for DoF
  vDepth = distToCamera;
}
`;

/**
 * Particle Render Fragment Shader
 * Supports:
 * - Diffuse texture mapping
 * - Sprite sheet animation
 * - Procedural shapes (circle, ring, square, star)
 */
export const PARTICLE_FRAGMENT_SHADER = `
precision highp float;
varying vec2 vUv;
varying vec4 vColor;
varying float vLifeRatio;
varying float vDepth;  // Distance from camera for DoF
uniform sampler2D diffuseMap;
uniform int hasDiffuseMap;
uniform int proceduralShape;
// DoF uniforms
uniform int dofEnabled;
uniform float dofFocusDistance;
uniform float dofFocusRange;
uniform float dofMaxBlur;
// Sprite sheet uniforms
uniform vec2 spriteSheetSize;  // columns, rows
uniform int spriteFrameCount;
uniform int animateSprite;
uniform float spriteFrameRate;
uniform float time;
uniform int randomStartFrame;  // Per-particle random start frame for texture animation variety
// Color over lifetime gradient texture
uniform sampler2D colorOverLifetime;
uniform int hasColorOverLifetime;

// Procedural shape generation (supports all 9 particle shapes)
// 0 = none, 1 = circle, 2 = ring, 3 = square, 4 = star, 5 = noise, 6 = line, 7 = triangle, 8 = shadedSphere, 9 = fadedSphere
float proceduralAlpha(vec2 uv, int shape) {
  vec2 centered = uv * 2.0 - 1.0;
  float dist = length(centered);

  // Circle - soft edge
  if (shape == 1) {
    return 1.0 - smoothstep(0.8, 1.0, dist);
  }
  // Ring - hollow circle
  else if (shape == 2) {
    return smoothstep(0.5, 0.6, dist) * (1.0 - smoothstep(0.9, 1.0, dist));
  }
  // Square - rounded corners
  else if (shape == 3) {
    float maxCoord = max(abs(centered.x), abs(centered.y));
    return 1.0 - smoothstep(0.8, 0.95, maxCoord);
  }
  // Star - 5-pointed
  else if (shape == 4) {
    float angle = atan(centered.y, centered.x);
    float star = 0.5 + 0.5 * cos(angle * 5.0);
    float r = mix(0.4, 0.9, star);
    return 1.0 - smoothstep(r - 0.1, r, dist);
  }
  // Noise - procedural noise texture
  else if (shape == 5) {
    // Simple value noise using sin for determinism
    float n = sin(centered.x * 10.0) * sin(centered.y * 10.0);
    n += 0.5 * sin(centered.x * 20.0 + 1.0) * sin(centered.y * 20.0 + 1.0);
    n += 0.25 * sin(centered.x * 40.0 + 2.0) * sin(centered.y * 40.0 + 2.0);
    n = n * 0.5 + 0.5;  // Normalize to 0-1
    float edge = 1.0 - smoothstep(0.8, 1.0, dist);
    return n * edge;
  }
  // Line - horizontal line with soft edges
  else if (shape == 6) {
    float lineWidth = 0.15;
    float alpha = 1.0 - smoothstep(lineWidth, lineWidth + 0.1, abs(centered.y));
    alpha *= 1.0 - smoothstep(0.8, 1.0, abs(centered.x));
    return alpha;
  }
  // Triangle - equilateral pointing up
  else if (shape == 7) {
    // Triangle SDF
    vec2 p = centered;
    p.y -= 0.1;  // Center vertically
    float k = sqrt(3.0);
    p.x = abs(p.x) - 0.8;
    p.y = p.y + 0.8 / k;
    if (p.x + k * p.y > 0.0) {
      p = vec2(p.x - k * p.y, -k * p.x - p.y) / 2.0;
    }
    p.x -= clamp(p.x, -1.6, 0.0);
    float d = -length(p) * sign(p.y);
    return 1.0 - smoothstep(-0.05, 0.05, d);
  }
  // Shaded Sphere - 3D appearance with lighting
  else if (shape == 8) {
    if (dist > 1.0) return 0.0;
    // Calculate sphere normal
    float z = sqrt(1.0 - dist * dist);
    vec3 normal = vec3(centered.x, centered.y, z);
    // Light from upper-left
    vec3 lightDir = normalize(vec3(-0.5, -0.5, 1.0));
    float diffuse = max(dot(normal, lightDir), 0.0);
    // Add specular highlight
    vec3 viewDir = vec3(0.0, 0.0, 1.0);
    vec3 halfVec = normalize(lightDir + viewDir);
    float specular = pow(max(dot(normal, halfVec), 0.0), 32.0);
    float shade = 0.3 + 0.5 * diffuse + 0.4 * specular;
    float edge = 1.0 - smoothstep(0.95, 1.0, dist);
    return shade * edge;
  }
  // Faded Sphere - radial gradient falloff
  else if (shape == 9) {
    // Exponential falloff from center
    float fade = exp(-dist * dist * 2.0);
    return fade;
  }
  return 1.0;
}

// Get UV coordinates for sprite sheet frame
vec2 getSpriteUV(vec2 uv, int frame, vec2 sheetSize) {
  float col = mod(float(frame), sheetSize.x);
  float row = floor(float(frame) / sheetSize.x);
  vec2 frameSize = 1.0 / sheetSize;
  vec2 offset = vec2(col, sheetSize.y - 1.0 - row) * frameSize;
  return offset + uv * frameSize;
}

void main() {
  vec4 texColor = vec4(1.0);

  if (hasDiffuseMap == 1) {
    vec2 texUV = vUv;

    // Sprite sheet animation
    if (spriteFrameCount > 1) {
      int frame;

      // Calculate per-particle random offset for sprite sheet variety
      int frameOffset = 0;
      if (randomStartFrame == 1) {
        // Use particle color as seed for deterministic per-particle offset
        // This creates a pseudo-random but deterministic offset based on particle instance
        float seed = vColor.r * 31.0 + vColor.g * 37.0 + vColor.b * 41.0 + vColor.a * 43.0;
        frameOffset = int(mod(seed * 127.0, float(spriteFrameCount)));
      }

      if (animateSprite == 1) {
        // Time-based animation with random start offset
        frame = int(mod(time * spriteFrameRate + float(frameOffset), float(spriteFrameCount)));
      } else {
        // Life-based animation (frame changes with particle age) with random start offset
        frame = int(mod(vLifeRatio * float(spriteFrameCount - 1) + float(frameOffset), float(spriteFrameCount)));
      }
      texUV = getSpriteUV(vUv, frame, spriteSheetSize);
    }

    texColor = texture2D(diffuseMap, texUV);
  }
  else if (proceduralShape > 0) {
    float alpha = proceduralAlpha(vUv, proceduralShape);
    texColor = vec4(1.0, 1.0, 1.0, alpha);
  }

  vec4 finalColor = texColor * vColor;

  // Apply color over lifetime gradient modulation
  if (hasColorOverLifetime == 1) {
    // Sample the 1D gradient texture at the particle's life ratio
    vec4 lifetimeColor = texture2D(colorOverLifetime, vec2(vLifeRatio, 0.5));
    // Multiply the color channels, preserving texture alpha
    finalColor.rgb *= lifetimeColor.rgb;
    finalColor.a *= lifetimeColor.a;
  }

  // Apply Depth of Field effect
  if (dofEnabled == 1) {
    // Calculate distance from focus plane
    float focusDist = abs(vDepth - dofFocusDistance);
    // Calculate blur factor (0 = in focus, 1 = max blur)
    float blurFactor = smoothstep(0.0, dofFocusRange, focusDist);
    // Apply blur by reducing alpha (simulating circle of confusion)
    finalColor.a *= mix(1.0, 1.0 - dofMaxBlur, blurFactor);
    // Optionally desaturate out-of-focus particles slightly
    float gray = dot(finalColor.rgb, vec3(0.299, 0.587, 0.114));
    finalColor.rgb = mix(finalColor.rgb, vec3(gray), blurFactor * 0.2);
  }

  if (finalColor.a < 0.01) discard;
  gl_FragColor = finalColor;
}
`;

/**
 * Particle Glow Fragment Shader
 * Renders an expanded soft glow behind particles
 * Used as a second pass with additive blending
 */
export const PARTICLE_GLOW_FRAGMENT_SHADER = `
precision highp float;
varying vec2 vUv;
varying vec4 vColor;
varying float vLifeRatio;
uniform float glowRadius;
uniform float glowIntensity;

void main() {
  vec2 centered = vUv * 2.0 - 1.0;
  float dist = length(centered);

  // Soft falloff for glow
  float glow = 1.0 - smoothstep(0.0, 1.0, dist);
  glow = pow(glow, 2.0) * glowIntensity;

  // Fade with particle life
  glow *= (1.0 - vLifeRatio * 0.5);

  vec4 glowColor = vec4(vColor.rgb, glow * vColor.a);
  if (glowColor.a < 0.001) discard;
  gl_FragColor = glowColor;
}
`;

/**
 * Particle Glow Vertex Shader
 * Expands billboards by glow radius
 */
export const PARTICLE_GLOW_VERTEX_SHADER = `
precision highp float;
attribute vec2 position;
attribute vec2 uv;
attribute vec3 i_position;
attribute vec3 i_velocity;
attribute vec2 i_life;
attribute vec2 i_physical;
attribute vec2 i_rotation;
attribute vec4 i_color;
uniform mat4 modelViewMatrix;
uniform mat4 projectionMatrix;
uniform float glowRadius;
varying vec2 vUv;
varying vec4 vColor;
varying float vLifeRatio;

void main() {
  if (i_life.y <= 0.0 || i_life.x >= i_life.y) {
    gl_Position = vec4(0.0, 0.0, -1000.0, 1.0);
    return;
  }

  // Expand size by glow radius
  float size = i_physical.y * (1.0 + glowRadius);
  float lifeRatio = i_life.x / i_life.y;

  vec3 cameraRight = vec3(modelViewMatrix[0][0], modelViewMatrix[1][0], modelViewMatrix[2][0]);
  vec3 cameraUp = vec3(modelViewMatrix[0][1], modelViewMatrix[1][1], modelViewMatrix[2][1]);

  vec3 vertexPos = i_position + cameraRight * position.x * size + cameraUp * position.y * size;
  gl_Position = projectionMatrix * modelViewMatrix * vec4(vertexPos, 1.0);
  vUv = uv;
  vColor = i_color;
  vLifeRatio = lifeRatio;
}
`;
