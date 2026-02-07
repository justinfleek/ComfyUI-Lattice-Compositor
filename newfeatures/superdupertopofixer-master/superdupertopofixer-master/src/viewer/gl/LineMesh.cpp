#include "gl/LineMesh.h"

namespace sdtf::viewer::gl {;

LineMesh::LineMesh(const Eigen::Matrix<GLfloat, 3, -1>& vertices, const Eigen::Matrix<GLuint, 2, -1>& elements)
{
	vao_ = std::make_unique<VertexArray>();

	num_vertices_ = static_cast<int>(vertices.cols());
	buffer_v_ = Buffer::newMutable(GL_ARRAY_BUFFER, sizeof(GLfloat) * vertices.size(), vertices.data(), GL_STATIC_DRAW);
	vao_->attachBuffer(buffer_v_.get(), 0, 3, GL_FLOAT);

	num_elements_ = static_cast<int>(elements.cols());
	has_elements_ = num_elements_ > 0;
	if (has_elements_) {
	buffer_el_ = Buffer::newMutable(GL_ELEMENT_ARRAY_BUFFER, sizeof(GLuint) * elements.size(), elements.data(), GL_STATIC_DRAW);
		vao_->attachElementBuffer(buffer_el_.get());
	}

}

void LineMesh::setVertices(const Eigen::Matrix<GLfloat, 3, -1>& vertices)
{
	num_vertices_ = static_cast<int>(vertices.cols());
	buffer_v_->setData(sizeof(GLfloat) * vertices.size(), vertices.data());
}

//void LineMesh::resetData()
//{
//	buffer_v_->setData(0, nullptr);
//	buffer_el_->setData(0, nullptr);
//	num_vertices_ = 0;
//	num_elements_ = 0;
//}

}