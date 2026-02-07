#pragma once

#include <string>

#include "gl/Buffer.h"

// Wrapper for OpenGL Vertex Array ("VAO")

namespace sdtf::viewer::gl {;

class VertexArray
{
public:
	VertexArray();

	void clear();
	~VertexArray();

	void attachBuffer(const Buffer* buffer, GLuint index, GLint size, GLenum type, GLuint divisor = 0);
	void attachElementBuffer(const Buffer* buffer);

	inline GLuint name() const { return name_; }

	void bind() const;

private:
	GLuint name_ = -1;
	bool created_ = false;
};

}