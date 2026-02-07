#pragma once

#include <Eigen/Core>
#include "gl/Buffer.h"
#include "gl/VertexArray.h"
#include "gl/Geometry.h"

// A Buffer object for vertex positions attached to a VertexArray

namespace sdtf::viewer::gl {;

class PointSet : public Geometry
{
public:
	PointSet(const Eigen::Matrix<GLfloat, 3, -1>& vertices = Eigen::Matrix<GLfloat, 3, -1>(3, 0));

	void setData(const Eigen::Matrix<GLfloat, 3, -1>& vertices);

	virtual GLuint vaoName() const override { return vao_->name(); }

	virtual int numVertices() const override { return num_vertices_; }
	virtual int numElements() const override { return num_vertices_; }

private:
	std::unique_ptr<Buffer> buffer_v_;
	std::unique_ptr<VertexArray> vao_;

	int num_vertices_;
};

}
