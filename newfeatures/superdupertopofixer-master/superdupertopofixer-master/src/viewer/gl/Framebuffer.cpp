#include "gl/Framebuffer.h"

namespace sdtf::viewer::gl {;

Framebuffer::Framebuffer()
{
	glCreateFramebuffers(1, &name_);
}

Framebuffer::~Framebuffer()
{
	glDeleteFramebuffers(1, &name_);
}

void Framebuffer::attach(Texture* texture, GLenum attachment)
{
	glNamedFramebufferTexture(name_, attachment, texture->name(), 0);
}


}