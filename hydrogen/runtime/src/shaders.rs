//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                            // hydrogen // runtime // shaders
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! WGSL shaders for Hydrogen rendering.
//!
//! All shaders are compiled at runtime from these strings.

/// Shader for rendering rectangles with rounded corners via SDF.
pub const RECT_SHADER: &str = r#"
// Uniforms
struct Uniforms {
    resolution: vec2<f32>,
    _padding: vec2<f32>,
}

@group(0) @binding(0) var<uniform> uniforms: Uniforms;

// Vertex input
struct VertexInput {
    @location(0) position: vec2<f32>,
    @location(1) rect: vec4<f32>,       // x, y, width, height
    @location(2) color: vec4<f32>,      // r, g, b, a
    @location(3) radii: vec4<f32>,      // tl, tr, br, bl
    @location(4) depth_pick: vec2<f32>, // depth, pick_id
}

// Vertex output / Fragment input
struct VertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) local_pos: vec2<f32>,
    @location(1) color: vec4<f32>,
    @location(2) half_size: vec2<f32>,
    @location(3) radii: vec4<f32>,
    @location(4) pick_id: f32,
}

// Vertex shader: expand rect to quad
@vertex
fn vs_main(input: VertexInput) -> VertexOutput {
    var output: VertexOutput;
    
    // Expand vertex position to rect corners
    let rect_pos = input.rect.xy + input.position * input.rect.zw;
    
    // Convert to clip space
    let x = (rect_pos.x / uniforms.resolution.x) * 2.0 - 1.0;
    let y = 1.0 - (rect_pos.y / uniforms.resolution.y) * 2.0;
    
    output.clip_position = vec4<f32>(x, y, input.depth_pick.x, 1.0);
    output.local_pos = (input.position - 0.5) * input.rect.zw;
    output.color = input.color;
    output.half_size = input.rect.zw * 0.5;
    output.radii = input.radii;
    output.pick_id = input.depth_pick.y;
    
    return output;
}

// SDF for rounded rectangle
fn sd_rounded_rect(p: vec2<f32>, b: vec2<f32>, r: vec4<f32>) -> f32 {
    var radius: f32;
    
    // Select corner radius based on quadrant
    if (p.x > 0.0) {
        if (p.y > 0.0) {
            radius = r.y; // top-right
        } else {
            radius = r.z; // bottom-right
        }
    } else {
        if (p.y > 0.0) {
            radius = r.x; // top-left
        } else {
            radius = r.w; // bottom-left
        }
    }
    
    let q = abs(p) - b + radius;
    return min(max(q.x, q.y), 0.0) + length(max(q, vec2<f32>(0.0))) - radius;
}

// Fragment shader: render with SDF
@fragment
fn fs_main(input: VertexOutput) -> @location(0) vec4<f32> {
    // SDF distance
    let d = sd_rounded_rect(input.local_pos, input.half_size, input.radii);
    
    // Anti-aliased edge
    let aa = fwidth(d);
    let alpha = 1.0 - smoothstep(-aa, aa, d);
    
    return vec4<f32>(input.color.rgb, input.color.a * alpha);
}
"#;

/// Shader for the pick buffer (renders pick IDs as colors).
pub const PICK_SHADER: &str = r#"
// Uniforms
struct Uniforms {
    resolution: vec2<f32>,
    _padding: vec2<f32>,
}

@group(0) @binding(0) var<uniform> uniforms: Uniforms;

// Vertex input
struct VertexInput {
    @location(0) position: vec2<f32>,
    @location(1) rect: vec4<f32>,
    @location(2) pick_id: f32,
}

// Vertex output
struct VertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) pick_id: f32,
}

@vertex
fn vs_main(input: VertexInput) -> VertexOutput {
    var output: VertexOutput;
    
    let rect_pos = input.rect.xy + input.position * input.rect.zw;
    let x = (rect_pos.x / uniforms.resolution.x) * 2.0 - 1.0;
    let y = 1.0 - (rect_pos.y / uniforms.resolution.y) * 2.0;
    
    output.clip_position = vec4<f32>(x, y, 0.0, 1.0);
    output.pick_id = input.pick_id;
    
    return output;
}

@fragment
fn fs_main(input: VertexOutput) -> @location(0) vec4<f32> {
    // Encode pick ID as color (RGBA8)
    let id = u32(input.pick_id);
    let r = f32((id >> 0u) & 0xFFu) / 255.0;
    let g = f32((id >> 8u) & 0xFFu) / 255.0;
    let b = f32((id >> 16u) & 0xFFu) / 255.0;
    let a = f32((id >> 24u) & 0xFFu) / 255.0;
    return vec4<f32>(r, g, b, a);
}
"#;

/// Shader for rendering filled paths (typography as geometry).
pub const PATH_SHADER: &str = r#"
// Uniforms
struct Uniforms {
    resolution: vec2<f32>,
    _padding: vec2<f32>,
}

@group(0) @binding(0) var<uniform> uniforms: Uniforms;

// Vertex input
struct VertexInput {
    @location(0) position: vec2<f32>,    // vertex position
    @location(1) transform: vec4<f32>,   // position.xy, scale.xy
    @location(2) rotation: vec3<f32>,    // rotation.xyz (degrees)
    @location(3) color: vec4<f32>,       // r, g, b, a
    @location(4) depth_pick: vec2<f32>,  // depth, pick_id
}

// Vertex output
struct VertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) color: vec4<f32>,
    @location(1) pick_id: f32,
}

// Rotation matrix for Z rotation (2D)
fn rotate_z(angle_deg: f32) -> mat2x2<f32> {
    let angle = radians(angle_deg);
    let c = cos(angle);
    let s = sin(angle);
    return mat2x2<f32>(c, -s, s, c);
}

@vertex
fn vs_main(input: VertexInput) -> VertexOutput {
    var output: VertexOutput;
    
    // Apply scale
    var pos = input.position * input.transform.zw;
    
    // Apply Z rotation (2D rotation in the XY plane)
    pos = rotate_z(input.rotation.z) * pos;
    
    // Apply translation
    pos = pos + input.transform.xy;
    
    // Convert to clip space
    let x = (pos.x / uniforms.resolution.x) * 2.0 - 1.0;
    let y = 1.0 - (pos.y / uniforms.resolution.y) * 2.0;
    
    output.clip_position = vec4<f32>(x, y, input.depth_pick.x, 1.0);
    output.color = input.color;
    output.pick_id = input.depth_pick.y;
    
    return output;
}

@fragment
fn fs_main(input: VertexOutput) -> @location(0) vec4<f32> {
    return input.color;
}
"#;

/// Shader for particle rendering (point sprites).
pub const PARTICLE_SHADER: &str = r#"
// Uniforms
struct Uniforms {
    resolution: vec2<f32>,
    _padding: vec2<f32>,
}

@group(0) @binding(0) var<uniform> uniforms: Uniforms;

// Vertex input (instanced)
struct VertexInput {
    @builtin(vertex_index) vertex_index: u32,
    @location(0) position: vec3<f32>,  // x, y, z
    @location(1) size: f32,
    @location(2) color: vec4<f32>,
    @location(3) pick_id: f32,
}

struct VertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) uv: vec2<f32>,
    @location(1) color: vec4<f32>,
    @location(2) pick_id: f32,
}

@vertex
fn vs_main(input: VertexInput) -> VertexOutput {
    var output: VertexOutput;
    
    // Expand point to quad (6 vertices per particle for 2 triangles)
    let quad_vertices = array<vec2<f32>, 6>(
        vec2<f32>(-0.5, -0.5),
        vec2<f32>(0.5, -0.5),
        vec2<f32>(0.5, 0.5),
        vec2<f32>(-0.5, -0.5),
        vec2<f32>(0.5, 0.5),
        vec2<f32>(-0.5, 0.5),
    );
    
    let local_pos = quad_vertices[input.vertex_index % 6u];
    let world_pos = input.position.xy + local_pos * input.size;
    
    let x = (world_pos.x / uniforms.resolution.x) * 2.0 - 1.0;
    let y = 1.0 - (world_pos.y / uniforms.resolution.y) * 2.0;
    
    output.clip_position = vec4<f32>(x, y, input.position.z, 1.0);
    output.uv = local_pos + 0.5;
    output.color = input.color;
    output.pick_id = input.pick_id;
    
    return output;
}

@fragment
fn fs_main(input: VertexOutput) -> @location(0) vec4<f32> {
    // Circle SDF
    let center = input.uv - 0.5;
    let dist = length(center);
    let alpha = 1.0 - smoothstep(0.45, 0.5, dist);
    
    return vec4<f32>(input.color.rgb, input.color.a * alpha);
}
"#;
