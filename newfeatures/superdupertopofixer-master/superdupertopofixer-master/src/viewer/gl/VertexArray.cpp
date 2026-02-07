#include "gl/VertexArray.h"

#include <cassert>

namespace sdtf::viewer::gl {;

VertexArray::VertexArray()
{
	glCreateVertexArrays(1, &name_);
	created_ = true;
}

void VertexArray::clear()
{
	if (created_)
	{
		glDeleteVertexArrays(1, &name_);
		created_ = false;
		name_ = false;
	}
}

VertexArray::~VertexArray()
{
	if (created_)
		clear();
}

void VertexArray::attachBuffer(const Buffer* buffer, GLuint index, GLint size, GLenum type, GLuint divisor/* = 0*/)
{
	glBindVertexArray(name_);
	glBindBuffer(GL_ARRAY_BUFFER, buffer->name());
	glEnableVertexAttribArray(index);

	//assert(type == GL_FLOAT);
	if (type == GL_FLOAT)
		glVertexAttribPointer(index, size, type, GL_FALSE, 0, nullptr);
	else if (type == GL_UNSIGNED_INT)
		glVertexAttribIPointer(index, size, type, 0, nullptr);

	if (divisor > 0)
		glVertexAttribDivisor(index, divisor);

	glBindVertexArray(0);
}

void VertexArray::attachElementBuffer(const Buffer* buffer)
{
	glBindVertexArray(name_);
	glBindBuffer(GL_ELEMENT_ARRAY_BUFFER, buffer->name());
	glBindVertexArray(0);
}

void VertexArray::bind() const
{
	glBindVertexArray(name_);
}

}