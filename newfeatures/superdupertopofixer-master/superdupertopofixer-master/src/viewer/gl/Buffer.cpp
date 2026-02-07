#include "gl/Buffer.h"

#include <cassert>

namespace sdtf::viewer::gl {;

void Buffer::clear()
{
	if (created_)
	{
		glDeleteBuffers(1, &name_);
		created_ = false;
		name_ = -1;
	}
}

Buffer::~Buffer()
{
	if (created_)
		clear();
}

std::unique_ptr<Buffer> Buffer::newMutable(GLenum target, GLsizeiptr size, const GLvoid* data, GLenum usage)
{
	auto ret = std::unique_ptr<Buffer>(new Buffer());

	glCreateBuffers(1, &ret->name_);
	ret->target_ = target;
	ret->size_ = size;
	ret->immutable_ = false;
	ret->usage_ = usage;
	glNamedBufferData(ret->name_, size, data, usage);
	ret->created_ = true;

	return ret;
}

std::unique_ptr<Buffer> Buffer::newImmutable(GLenum target, GLsizeiptr size, const GLvoid* data, GLbitfield flags)
{
	auto ret = std::unique_ptr<Buffer>(new Buffer());

	glCreateBuffers(1, &ret->name_);
	ret->target_ = target;
	ret->size_ = size;
	ret->capacity_ = size;
	ret->immutable_ = false;
	ret->flags_ = flags;
	glNamedBufferStorage(ret->name_, size, data, flags);
	ret->created_ = true;

	return ret;
}

void Buffer::resize(GLsizeiptr size)
{
	assert(!immutable_);
	glNamedBufferData(name_, size_, 0, usage_);
}

void Buffer::setData(GLsizeiptr size, const GLvoid* data)
{
	if (immutable_)
	{
		assert((flags_ & GL_DYNAMIC_STORAGE_BIT) != 0);
		assert(size <= capacity_);
		glNamedBufferSubData(name_, 0, size, data);
		size_ = size;
	}
	else
	{
		if (size <= size_)
			glNamedBufferSubData(name_, 0, size, data);
		else
			glNamedBufferData(name_, size, data, usage_);

		size_ = size;
	}
}

}