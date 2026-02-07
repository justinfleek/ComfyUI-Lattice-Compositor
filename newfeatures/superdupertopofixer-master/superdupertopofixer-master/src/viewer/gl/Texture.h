#pragma once

#include <glad/glad.h>
#include <memory>

namespace sdtf::viewer::gl {;

// Wrapper for OpenGL Texture

class Texture
{
public:
	~Texture();

	static std::unique_ptr<Texture> makeBasic2D(GLsizei width, GLsizei height, GLint internal_format, GLenum format);
	static std::unique_ptr<Texture> makeBasic2DMultisample(GLsizei width, GLsizei height, GLint internal_format, GLsizei num_samples);

	void resize(GLsizei width, GLsizei height);

	auto target() const { return target_; }
	auto name() const { return name_; }

private:
	Texture(GLsizei width, GLsizei height, GLint internal_format, GLenum format, GLsizei num_samples);

	GLuint name_;

	bool immutable_ = false;
	GLsizei width_, height_;
	GLint internal_format_;
	GLenum format_;

	GLint min_filter_ = GL_NEAREST, mag_filter_ = GL_NEAREST;
	bool has_mipmaps_ = false;
	GLsizei num_samples_ = 0;
	GLenum target_;
};

}
