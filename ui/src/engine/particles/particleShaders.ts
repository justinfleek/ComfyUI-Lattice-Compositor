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
    vec3 windDir = normalize(row2.xyz);
    float gustStrength = row3.x;
    float gustFreq = row3.y;
    float gust = sin(u_time * gustFreq) * gustStrength;
    force = windDir * (effectiveStrength + gust);
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
 */
export const PARTICLE_VERTEX_SHADER = `
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
uniform vec3 cameraPosition;
varying vec2 vUv;
varying vec4 vColor;
varying float vLifeRatio;
void main() {
  if (i_life.y <= 0.0 || i_life.x >= i_life.y) {
    gl_Position = vec4(0.0, 0.0, -1000.0, 1.0);
    return;
  }
  float size = i_physical.y;
  float rotation = i_rotation.x;
  float lifeRatio = i_life.x / i_life.y;
  vec3 cameraRight = vec3(modelViewMatrix[0][0], modelViewMatrix[1][0], modelViewMatrix[2][0]);
  vec3 cameraUp = vec3(modelViewMatrix[0][1], modelViewMatrix[1][1], modelViewMatrix[2][1]);
  float cosR = cos(rotation);
  float sinR = sin(rotation);
  vec2 rotatedPos = vec2(
    position.x * cosR - position.y * sinR,
    position.x * sinR + position.y * cosR
  );
  vec3 vertexPos = i_position + cameraRight * rotatedPos.x * size + cameraUp * rotatedPos.y * size;
  gl_Position = projectionMatrix * modelViewMatrix * vec4(vertexPos, 1.0);
  vUv = uv;
  vColor = i_color;
  vLifeRatio = lifeRatio;
}
`;

/**
 * Particle Render Fragment Shader
 */
export const PARTICLE_FRAGMENT_SHADER = `
precision highp float;
varying vec2 vUv;
varying vec4 vColor;
varying float vLifeRatio;
uniform sampler2D diffuseMap;
uniform int hasDiffuseMap;
uniform int proceduralShape;
float proceduralAlpha(vec2 uv, int shape) {
  vec2 centered = uv * 2.0 - 1.0;
  float dist = length(centered);
  if (shape == 1) { return 1.0 - smoothstep(0.8, 1.0, dist); }
  else if (shape == 2) { return smoothstep(0.5, 0.6, dist) * (1.0 - smoothstep(0.9, 1.0, dist)); }
  return 1.0;
}
void main() {
  vec4 texColor = vec4(1.0);
  if (hasDiffuseMap == 1) { texColor = texture2D(diffuseMap, vUv); }
  else if (proceduralShape > 0) {
    float alpha = proceduralAlpha(vUv, proceduralShape);
    texColor = vec4(1.0, 1.0, 1.0, alpha);
  }
  vec4 finalColor = texColor * vColor;
  if (finalColor.a < 0.01) discard;
  gl_FragColor = finalColor;
}
`;
