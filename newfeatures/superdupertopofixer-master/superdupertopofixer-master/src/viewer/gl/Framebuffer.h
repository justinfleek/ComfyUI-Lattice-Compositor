#pragma once

#include <memory>

#include "Texture.h"

// Wrapper of an OpenGL framebuffer

namespace sdtf::viewer::gl {;

class Framebuffer
{
public:
	Framebuffer();
	~Framebuffer();

	// Attaches a texture at the specified attachment point.
	// The GL rules for compatible textures attached to the same framebuffer apply.
	void attach(Texture* texture, GLenum attachment);

	// GL-internal Name of the buffer object
	auto name() const { return name_; }

private:
	GLuint name_;
};

}