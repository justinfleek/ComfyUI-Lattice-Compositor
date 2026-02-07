#pragma once

#include <glad/glad.h>

#include <memory>
#include <string>

// Wrapper of the OpenGL "Buffer" concept, e.g., used to store vertex attributes ("VBO") and collect them in
// a VertexArray ("VAO").

namespace sdtf::viewer::gl {
;

class Buffer {
 public:
	~Buffer();

	// Creates a Buffer with mutable storage, i.e., the GPU memory is allocated with "glBufferData"
	static std::unique_ptr<Buffer> newMutable(GLenum target, GLsizeiptr size, const GLvoid* data,
	                                          GLenum usage);
	// Creates a Buffer with immutable storage, i.e., the GPU memory is allocated with "glBufferStorage"
	static std::unique_ptr<Buffer> newImmutable(GLenum target, GLsizeiptr size, const GLvoid* data,
	                                            GLbitfield flags = 0);

	// Resizes the capacity of the buffer memory, invalidating the contents in the process
	void resize(GLsizeiptr size);
	// Uploads data to the GPU buffer memory, overwriting old data. If the buffer is immutable,
	// then the size of the new data must not be greater than the initial capacity of the buffer.
	// If the buffer is mutable, the capacity of the buffer is increased if necessary. The
	// capacity is not decreased if the size of the new data is smaller than the capacity.
	void setData(GLsizeiptr size, const GLvoid* data);
	// Size of the data currently stored. May be smaller than the allocated capacity.
	GLsizeiptr size() const { return size_; }
	// GL-internal Name of the buffer object
	auto name() const { return name_; }

	// Deallocated the memory on the GPU and deletes the GL buffer object
	void clear();

 private:
	Buffer() {}

	bool created_ = false;
	GLuint name_ = -1;
	GLenum target_ = -1;
	GLsizeiptr size_ = 0;
	bool immutable_ = false;
	// mutable only
	GLenum usage_ = -1;
	// immutable only
	GLbitfield flags_ = 0;
	GLsizeiptr capacity_ = 0;
};

}  // namespace sdtf::viewer::gl