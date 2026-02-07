#include "gl/Texture.h"

namespace sdtf::viewer::gl {;

Texture::Texture(GLsizei width, GLsizei height, GLint internal_format, GLenum format,GLsizei num_samples)
	: width_(width), height_(height), internal_format_(internal_format), format_(format), num_samples_(num_samples)
{
	target_ = (num_samples == 0) ? GL_TEXTURE_2D : GL_TEXTURE_2D_MULTISAMPLE;

	glGenTextures(1, &name_);
	glBindTexture(target_, name_);

	if (num_samples == 0)
	{
		glTexImage2D(target_, 0, internal_format, width, height, 0, format, GL_UNSIGNED_BYTE, nullptr);
		glTexParameteri(target_, GL_TEXTURE_MIN_FILTER, min_filter_);
		glTexParameteri(target_, GL_TEXTURE_MAG_FILTER, mag_filter_);
	}
	else
		glTexImage2DMultisample(target_, num_samples, internal_format, width, height, GL_FALSE);

	glBindTexture(target_, 0);
}

void Texture::resize(GLsizei width, GLsizei height)
{
	width_ = width;
	height_ = height;
	glBindTexture(target_, name_);
	if (target_ == GL_TEXTURE_2D)
		glTexImage2D(target_, 0, internal_format_, width, height, 0, format_, GL_UNSIGNED_BYTE, nullptr);
	else if (target_ == GL_TEXTURE_2D_MULTISAMPLE)
		glTexImage2DMultisample(target_, num_samples_, internal_format_, width, height, GL_FALSE);
	glBindTexture(target_, 0);
}

Texture::~Texture()
{
	glDeleteTextures(1, &name_);
}

std::unique_ptr<Texture> Texture::makeBasic2D(GLsizei width, GLsizei height, GLint internal_format, GLenum format)
{
	return std::unique_ptr<Texture>(new Texture(width, height, internal_format, format, 0));
}

std::unique_ptr<Texture> Texture::makeBasic2DMultisample(GLsizei width, GLsizei height, GLint internal_format, GLsizei num_samples)
{
	return std::unique_ptr<Texture>(new Texture(width, height, internal_format, 0, num_samples));
}

}