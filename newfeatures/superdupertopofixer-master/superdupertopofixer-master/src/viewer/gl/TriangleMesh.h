#pragma once

#include <Eigen/Core>

#include "gl/Buffer.h"
#include "gl/Geometry.h"
#include "gl/VertexArray.h"

// Wrapper for several buffers and a VertexArray to represent a triangle mesh. Supports indexed and
// non-indexed drawing.

namespace sdtf::viewer::gl {
;

class TriangleMesh : public Geometry {
 public:
	TriangleMesh(const Eigen::Matrix<GLfloat, 3, -1>& vertices = Eigen::Matrix<GLfloat, 3, -1>(3, 0),
	             const Eigen::Matrix<GLuint, 3, -1>& elements = Eigen::Matrix<GLuint, 3, -1>(3, 0));

	virtual GLuint vaoName() const override { return vao_->name(); }

	virtual int numVertices() const override { return num_vertices_; }
	virtual int numElements() const override { return num_elements_; }
	virtual bool hasElements() const override { return has_elements_; }

	bool hasIndices() const { return has_indices_; }
	bool hasFrontColor() const { return has_front_color_; }
	bool hasBackColor() const { return has_back_color_; }
	bool hasNormals() const { return has_normals_; }

	void setVertices(const Eigen::Matrix<GLfloat, 3, -1>& vertices);

	// All attributes below are per-vertex. float attributes can be used for interpolating over
	// triangles. The index buffer cannot be interpolated, so every element will use the index of the
	// "provoking vertex".
	void setFrontColor(const Eigen::Matrix<GLfloat, 3, -1>& front_color);
	void setBackColor(const Eigen::Matrix<GLfloat, 3, -1>& back_color);
	void setNormals(const Eigen::Matrix<GLfloat, 3, -1>& normals);
	void setIndices(const Eigen::Vector<GLuint, -1>& indices);

 private:
	std::unique_ptr<Buffer> buffer_v_, buffer_el_, buffer_index_, buffer_front_color_,
	    buffer_back_color_, buffer_normals_;
	std::unique_ptr<VertexArray> vao_;

	int num_vertices_, num_elements_;
	bool has_elements_ = false;
	bool has_indices_ = false;
	bool has_front_color_ = false;
	bool has_back_color_ = false;
	bool has_normals_ = false;
};

}  // namespace sdtf::viewer::gl