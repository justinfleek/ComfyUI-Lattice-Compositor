#version 300 es
precision highp float;

// Rectangle fragment shader
// SDF-based rounded rectangles with smooth borders

in vec2 v_texCoord;
in vec4 v_color;
in vec4 v_borderColor;
in vec4 v_rect;
in vec4 v_corner;
in vec2 v_borderWidth;

out vec4 fragColor;

// Signed distance function for rounded rectangle
float sdRoundedRect(vec2 p, vec2 size, vec4 radius) {
  // Select corner radius based on quadrant
  float r = radius.x;  // Default to top-left
  if (p.x > 0.5 * size.x) {
    r = (p.y < 0.5 * size.y) ? radius.y : radius.z;  // Top-right or bottom-right
  } else {
    r = (p.y < 0.5 * size.y) ? radius.x : radius.w;  // Top-left or bottom-left
  }
  
  vec2 q = abs(p) - size * 0.5 + r;
  return min(max(q.x, q.y), 0.0) + length(max(q, 0.0)) - r;
}

void main() {
  // Calculate position relative to rectangle center
  vec2 rectCenter = v_rect.xy + v_rect.zw * 0.5;
  vec2 pixelPos = gl_FragCoord.xy - rectCenter;
  
  // Calculate SDF
  float dist = sdRoundedRect(pixelPos, v_rect.zw, v_corner);
  
  // Anti-aliased fill
  float fillAlpha = 1.0 - smoothstep(-0.5, 0.5, dist);
  
  // Anti-aliased border
  float borderInner = -v_borderWidth.x;
  float borderOuter = 0.0;
  float borderAlpha = smoothstep(borderInner - 0.5, borderInner + 0.5, dist) 
                    * (1.0 - smoothstep(borderOuter - 0.5, borderOuter + 0.5, dist));
  
  // Composite: border over fill
  vec4 fill = v_color * fillAlpha;
  vec4 border = v_borderColor * borderAlpha;
  
  fragColor = mix(fill, border, borderAlpha);
  
  // Discard fully transparent pixels
  if (fragColor.a < 0.01) discard;
}
