#version 450 core

in vec3 world_position;
in vec3 world_normal;
flat in uint index_through;
in vec3 front_color_through;
in vec3 back_color_through;

uniform vec3 world_camera;
uniform float angle_attenuation;

layout(location=0) out vec3 out_color;
layout(location=1) out uint out_index;

void main(void)
{
	vec3 color = gl_FrontFacing ? front_color_through : back_color_through;
	if (angle_attenuation != 0.0) {
		vec3 to_camera = normalize(world_camera - world_position);
		float attenuation_factor = dot(normalize(world_normal), to_camera) * (gl_FrontFacing ? 1.0 : -1.0);
		float factor = 1.0 - angle_attenuation * (1.0 - max(0,attenuation_factor));
		out_color = color * factor;
	} else {
		out_color = color;
	}
	out_index = index_through;
}