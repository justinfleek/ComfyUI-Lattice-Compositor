#include "gl/PointSet.h"

namespace sdtf::viewer::gl {;

PointSet::PointSet(const Eigen::Matrix<GLfloat, 3, -1>& vertices)
{
	vao_ = std::make_unique<VertexArray>();

	num_vertices_ = static_cast<int>(vertices.cols());
	buffer_v_ = Buffer::newMutable(GL_ARRAY_BUFFER, sizeof(GLfloat) * vertices.size(), vertices.data(), GL_STATIC_DRAW);
	vao_->attachBuffer(buffer_v_.get(), 0, 3, GL_FLOAT);
}

void PointSet::setData(const Eigen::Matrix<GLfloat, 3, -1>& vertices)
{
	num_vertices_ = static_cast<int>(vertices.cols());
	buffer_v_->setData(sizeof(GLfloat) * vertices.size(), vertices.data());
}

}