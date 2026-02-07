#version 450 core

layout(pixel_center_integer) in vec4 gl_FragCoord;

uniform vec3 color;
uniform int pattern_front;
uniform int pattern_back;

layout(location=0) out vec3 out_color;

void main(void)
{
	out_color = color;
	ivec4 frag_coord = ivec4(gl_FragCoord);
	int pattern = gl_FrontFacing ? pattern_front : pattern_back;
	if (pattern == 0)
	{
		if (frag_coord.x % 2 == frag_coord.y % 2)
			discard;
	}
	else if (pattern == 1)
	{
		if (frag_coord.x % 2 == 0 || frag_coord.y % 2 == 0)
			discard;
	}
	else if (pattern == 2)
	{
		if (frag_coord.x % 4 <= 1)
			discard;
	}
	else if (pattern == 3)
	{
		if (frag_coord.y % 4 <= 1)
			discard;
	}
}