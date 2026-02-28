#version 300 es

// Rectangle vertex shader
// Renders filled rectangles with rounded corners, borders, and shadows

in vec2 a_position;    // Vertex position (0,0 to 1,1)
in vec2 a_texCoord;    // Texture coordinates

// Per-instance attributes
in vec4 a_rect;        // x, y, width, height
in vec4 a_color;       // RGBA color
in vec4 a_borderColor; // Border color
in vec4 a_corner;      // Corner radii (TL, TR, BR, BL)
in vec2 a_borderWidth; // Border width

uniform mat4 u_projection;  // Orthographic projection (screen space)
uniform vec2 u_resolution;  // Canvas resolution

out vec2 v_texCoord;
out vec4 v_color;
out vec4 v_borderColor;
out vec4 v_rect;
out vec4 v_corner;
out vec2 v_borderWidth;

void main() {
  // Calculate vertex position in screen space
  vec2 pos = a_rect.xy + a_position * a_rect.zw;
  
  // Transform to clip space
  gl_Position = u_projection * vec4(pos, 0.0, 1.0);
  
  // Pass to fragment shader
  v_texCoord = a_texCoord;
  v_color = a_color;
  v_borderColor = a_borderColor;
  v_rect = a_rect;
  v_corner = a_corner;
  v_borderWidth = a_borderWidth;
}
