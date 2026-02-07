#version 450 core

in vec3 world_position;
in vec3 color_through;

layout(location=0) out vec3 out_color;

void main(void)
{
	out_color = color_through;
}