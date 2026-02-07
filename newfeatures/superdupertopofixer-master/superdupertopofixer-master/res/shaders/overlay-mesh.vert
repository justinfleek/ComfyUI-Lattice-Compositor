#version 450 core

layout(location=0) in vec4 position;

uniform mat4 mvp_matrix;
uniform mat4 model_matrix;
uniform vec4 clipping_plane; // world space: dot(clipping_plane.xyz, world_position) + clipping_plane.w >= 0

out gl_PerVertex
{
  vec4 gl_Position;
  float gl_ClipDistance[1];
};

void main(void)
{
	gl_Position = mvp_matrix * position;
	vec3 world_position = (model_matrix * position).xyz;
	gl_ClipDistance[0] = dot(world_position, clipping_plane.xyz) + clipping_plane.w;
}