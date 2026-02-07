#version 450 core

layout(location=0) in vec4 position;
layout(location=1) in uint index;
layout(location=2) in vec3 normal;
layout(location=3) in vec3 front_color;
layout(location=4) in vec3 back_color;

uniform mat4 mvp_matrix;
uniform mat4 model_matrix;
uniform vec4 clipping_plane; // world space: dot(clipping_plane.xyz, world_position) + clipping_plane.w >= 0

out vec3 world_position;
out vec3 world_normal;
flat out uint index_through;
out vec3 front_color_through;
out vec3 back_color_through;

out gl_PerVertex
{
  vec4 gl_Position;
  float gl_ClipDistance[1];
};

void main(void)
{
	gl_Position = mvp_matrix * position;
	world_position = (model_matrix * position).xyz;
	world_normal = mat3(model_matrix) * normal;
	index_through = index;
	front_color_through = front_color;
	back_color_through = back_color;
	gl_ClipDistance[0] = dot(world_position, clipping_plane.xyz) + clipping_plane.w;
}