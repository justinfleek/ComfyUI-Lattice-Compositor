// ============================================================================
// GPU Particle Render Shaders
// Instanced billboard rendering with shadows and lighting
// ============================================================================

// ============================================================================
// VERTEX SHADER
// ============================================================================

#version 300 es
precision highp float;

// Per-vertex attributes (quad geometry)
in vec2 a_quadVertex;    // -1 to 1 quad corners
in vec2 a_quadUV;        // 0 to 1 UV coords

// Per-instance attributes (particle data)
in vec3 i_position;
in vec3 i_velocity;
in vec2 i_life;          // x = age, y = lifetime
in vec2 i_physical;      // x = mass, y = size
in vec2 i_rotation;      // x = rotation, y = angular velocity
in vec4 i_color;

// Outputs to fragment shader
out vec2 v_uv;
out vec4 v_color;
out vec3 v_worldPos;
out vec3 v_normal;
out float v_depth;
out float v_lifeRatio;

// Uniforms
uniform mat4 u_projectionMatrix;
uniform mat4 u_viewMatrix;
uniform mat4 u_modelMatrix;
uniform vec3 u_cameraPosition;
uniform vec3 u_cameraUp;
uniform vec3 u_cameraRight;

// Render mode
uniform int u_renderMode;  // 0=billboard, 1=stretched, 2=mesh
uniform float u_stretchFactor;
uniform float u_minStretch;
uniform float u_maxStretch;

// Sprite sheet
uniform int u_spriteColumns;
uniform int u_spriteRows;
uniform int u_animateSprite;
uniform float u_spriteFrameRate;

void main() {
  // Skip dead particles
  if (i_life.y <= 0.0 || i_life.x >= i_life.y) {
    gl_Position = vec4(0.0, 0.0, -1000.0, 1.0);
    return;
  }

  float size = i_physical.y;
  float rotation = i_rotation.x;
  float lifeRatio = i_life.x / i_life.y;

  // Calculate billboard orientation
  vec3 right, up;

  if (u_renderMode == 0) {
    // Standard billboard - always face camera
    right = u_cameraRight;
    up = u_cameraUp;
  }
  else if (u_renderMode == 1) {
    // Stretched billboard - stretch along velocity
    float speed = length(i_velocity);
    if (speed > 0.001) {
      vec3 velDir = i_velocity / speed;

      // Calculate stretch amount
      float stretch = clamp(speed * u_stretchFactor, u_minStretch, u_maxStretch);

      // Right vector is velocity direction
      right = velDir;

      // Up vector is perpendicular, facing camera
      vec3 toCamera = normalize(u_cameraPosition - i_position);
      up = normalize(cross(right, toCamera));

      // Apply stretch to size
      size *= mix(1.0, stretch, 0.5);
    }
    else {
      right = u_cameraRight;
      up = u_cameraUp;
    }
  }

  // Apply rotation around view direction
  float cosR = cos(rotation);
  float sinR = sin(rotation);
  vec3 rotatedRight = right * cosR - up * sinR;
  vec3 rotatedUp = right * sinR + up * cosR;

  // Calculate vertex position
  vec3 vertexPos = i_position
    + rotatedRight * a_quadVertex.x * size
    + rotatedUp * a_quadVertex.y * size;

  // Transform to clip space
  vec4 worldPos = u_modelMatrix * vec4(vertexPos, 1.0);
  vec4 viewPos = u_viewMatrix * worldPos;
  gl_Position = u_projectionMatrix * viewPos;

  // Calculate UV with sprite sheet support
  vec2 uv = a_quadUV;
  if (u_spriteColumns > 1 || u_spriteRows > 1) {
    int totalFrames = u_spriteColumns * u_spriteRows;
    int frame;

    if (u_animateSprite == 1) {
      // Animate based on age
      frame = int(i_life.x * u_spriteFrameRate) % totalFrames;
    }
    else {
      // Use life ratio to select frame
      frame = int(lifeRatio * float(totalFrames - 1));
    }

    int col = frame % u_spriteColumns;
    int row = frame / u_spriteColumns;

    float frameWidth = 1.0 / float(u_spriteColumns);
    float frameHeight = 1.0 / float(u_spriteRows);

    uv.x = (float(col) + a_quadUV.x) * frameWidth;
    uv.y = (float(row) + a_quadUV.y) * frameHeight;
  }

  // Output
  v_uv = uv;
  v_color = i_color;
  v_worldPos = worldPos.xyz;
  v_normal = normalize(u_cameraPosition - worldPos.xyz);  // Facing camera
  v_depth = -viewPos.z;
  v_lifeRatio = lifeRatio;
}

// ============================================================================
// FRAGMENT SHADER
// ============================================================================

#version 300 es
precision highp float;

in vec2 v_uv;
in vec4 v_color;
in vec3 v_worldPos;
in vec3 v_normal;
in float v_depth;
in float v_lifeRatio;

out vec4 fragColor;

// Textures
uniform sampler2D u_diffuseMap;
uniform sampler2D u_normalMap;
uniform sampler2D u_emissiveMap;
uniform int u_hasDiffuseMap;
uniform int u_hasNormalMap;
uniform int u_hasEmissiveMap;

// Lighting
uniform int u_receiveLighting;
uniform vec3 u_lightDirection;
uniform vec3 u_lightColor;
uniform float u_lightIntensity;
uniform vec3 u_ambientColor;
uniform float u_roughness;
uniform float u_metalness;
uniform float u_emissiveIntensity;

// Shadows
uniform int u_receiveShadows;
uniform sampler2D u_shadowMap;
uniform mat4 u_shadowMatrix;
uniform float u_shadowSoftness;
uniform float u_shadowBias;

// Ambient Occlusion
uniform int u_aoEnabled;
uniform sampler2D u_aoTexture;

// Soft particles
uniform int u_softParticles;
uniform sampler2D u_depthTexture;
uniform float u_softParticleScale;
uniform vec2 u_screenSize;

// Blending
uniform int u_blendMode;  // 0=normal, 1=additive, 2=multiply, 3=screen

// Procedural shape
uniform int u_proceduralShape;  // 0=none, 1=circle, 2=ring, 3=star

float proceduralAlpha(vec2 uv, int shape) {
  vec2 centered = uv * 2.0 - 1.0;
  float dist = length(centered);

  if (shape == 1) {
    // Soft circle
    return 1.0 - smoothstep(0.8, 1.0, dist);
  }
  else if (shape == 2) {
    // Ring
    return smoothstep(0.5, 0.6, dist) * (1.0 - smoothstep(0.9, 1.0, dist));
  }
  else if (shape == 3) {
    // Star (5-pointed)
    float angle = atan(centered.y, centered.x);
    float star = 0.5 + 0.5 * cos(angle * 5.0);
    float threshold = mix(0.3, 0.8, star);
    return 1.0 - smoothstep(threshold - 0.1, threshold, dist);
  }

  return 1.0;
}

float sampleShadow(vec3 worldPos) {
  if (u_receiveShadows == 0) return 1.0;

  vec4 shadowCoord = u_shadowMatrix * vec4(worldPos, 1.0);
  shadowCoord.xyz /= shadowCoord.w;
  shadowCoord.xyz = shadowCoord.xyz * 0.5 + 0.5;

  if (shadowCoord.z > 1.0) return 1.0;

  float shadow = 0.0;
  float texelSize = 1.0 / 1024.0;  // Shadow map size

  // PCF soft shadows
  int samples = int(u_shadowSoftness * 4.0) + 1;
  float sampleCount = 0.0;

  for (int x = -2; x <= 2; x++) {
    for (int y = -2; y <= 2; y++) {
      if (abs(x) + abs(y) > samples) continue;

      vec2 offset = vec2(float(x), float(y)) * texelSize * u_shadowSoftness;
      float shadowDepth = texture(u_shadowMap, shadowCoord.xy + offset).r;
      shadow += shadowCoord.z - u_shadowBias > shadowDepth ? 0.0 : 1.0;
      sampleCount += 1.0;
    }
  }

  return shadow / sampleCount;
}

float softParticleFade() {
  if (u_softParticles == 0) return 1.0;

  vec2 screenUV = gl_FragCoord.xy / u_screenSize;
  float sceneDepth = texture(u_depthTexture, screenUV).r;

  // Linearize depths
  float near = 0.1;
  float far = 1000.0;
  float linearSceneDepth = (2.0 * near * far) / (far + near - sceneDepth * (far - near));
  float linearParticleDepth = v_depth;

  float depthDiff = linearSceneDepth - linearParticleDepth;
  return smoothstep(0.0, u_softParticleScale, depthDiff);
}

void main() {
  // Sample diffuse texture or use procedural
  vec4 texColor = vec4(1.0);
  if (u_hasDiffuseMap == 1) {
    texColor = texture(u_diffuseMap, v_uv);
  }
  else if (u_proceduralShape > 0) {
    float alpha = proceduralAlpha(v_uv, u_proceduralShape);
    texColor = vec4(1.0, 1.0, 1.0, alpha);
  }

  // Combine with vertex color
  vec4 baseColor = texColor * v_color;

  // Early discard for transparent pixels
  if (baseColor.a < 0.01) discard;

  vec3 finalColor = baseColor.rgb;

  // Apply lighting
  if (u_receiveLighting == 1) {
    vec3 normal = v_normal;

    // Sample normal map
    if (u_hasNormalMap == 1) {
      vec3 normalSample = texture(u_normalMap, v_uv).xyz * 2.0 - 1.0;
      // Transform to world space (simplified for billboards)
      normal = normalize(normal + normalSample * 0.5);
    }

    // Diffuse lighting
    float NdotL = max(dot(normal, -u_lightDirection), 0.0);
    vec3 diffuse = u_lightColor * u_lightIntensity * NdotL;

    // Ambient
    vec3 ambient = u_ambientColor;

    // Shadow
    float shadow = sampleShadow(v_worldPos);

    finalColor = baseColor.rgb * (ambient + diffuse * shadow);
  }

  // Emissive
  if (u_hasEmissiveMap == 1) {
    vec3 emissive = texture(u_emissiveMap, v_uv).rgb;
    finalColor += emissive * u_emissiveIntensity;
  }

  // Soft particles
  float softFade = softParticleFade();
  baseColor.a *= softFade;

  // Apply blend mode in shader (for proper depth sorting)
  if (u_blendMode == 1) {
    // Additive
    fragColor = vec4(finalColor * baseColor.a, 0.0);
  }
  else if (u_blendMode == 2) {
    // Multiply
    fragColor = vec4(mix(vec3(1.0), finalColor, baseColor.a), 1.0);
  }
  else if (u_blendMode == 3) {
    // Screen
    fragColor = vec4(1.0 - (1.0 - finalColor) * (1.0 - baseColor.a), baseColor.a);
  }
  else {
    // Normal
    fragColor = vec4(finalColor, baseColor.a);
  }
}
