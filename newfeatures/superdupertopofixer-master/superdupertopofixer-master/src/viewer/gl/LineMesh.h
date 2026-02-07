#pragma once

#include <Eigen/Core>

#include "gl/Buffer.h"
#include "gl/Geometry.h"
#include "gl/VertexArray.h"

// Collection of buffers used to draw a line mesh, and a VertexArray to bundle them. Supports
// indexed drawing (if "elements" are provided) and non-indexed drawing (otherwise).

namespace sdtf::viewer::gl {
;

class LineMesh : public Geometry {
 public:
	LineMesh(const Eigen::Matrix<GLfloat, 3, -1>& vertices = Eigen::Matrix<GLfloat, 3, -1>(3, 0),
	         const Eigen::Matrix<GLuint, 2, -1>& elements = Eigen::Matrix<GLuint, 2, -1>(2, 0));

	void setVertices(const Eigen::Matrix<GLfloat, 3, -1>& vertices);
	// void resetData();

	virtual GLuint vaoName() const override { return vao_->name(); }

	virtual int numVertices() const override { return num_vertices_; }
	virtual int numElements() const override { return num_elements_; }
	virtual bool hasElements() const override { return has_elements_; }

 private:
	std::unique_ptr<Buffer> buffer_v_, buffer_el_;
	std::unique_ptr<VertexArray> vao_;

	int num_vertices_ = 0, num_elements_ = 0;
	bool has_elements_ = false;
};

}  // namespace sdtf::viewer::gl