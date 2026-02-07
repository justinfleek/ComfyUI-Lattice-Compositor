#include "gl/TriangleMesh.h"

namespace sdtf::viewer::gl {
;

TriangleMesh::TriangleMesh(const Eigen::Matrix<GLfloat, 3, -1>& vertices,
                           const Eigen::Matrix<GLuint, 3, -1>& elements)
    : buffer_v_(nullptr), buffer_index_(nullptr), buffer_el_(nullptr) {
	vao_ = std::make_unique<VertexArray>();

	num_vertices_ = static_cast<int>(vertices.cols());
	buffer_v_ = Buffer::newMutable(GL_ARRAY_BUFFER, sizeof(GLfloat) * vertices.size(),
	                               vertices.data(), GL_STATIC_DRAW);
	vao_->attachBuffer(buffer_v_.get(), 0, 3, GL_FLOAT);

	num_elements_ = static_cast<int>(elements.cols());
	has_elements_ = num_elements_ > 0;
	if (has_elements_) {
		buffer_el_ = Buffer::newMutable(GL_ELEMENT_ARRAY_BUFFER, sizeof(GLuint) * elements.size(),
		                                elements.data(), GL_STATIC_DRAW);
		vao_->attachElementBuffer(buffer_el_.get());
	}
}

void TriangleMesh::setVertices(const Eigen::Matrix<GLfloat, 3, -1>& vertices) {
	num_vertices_ = static_cast<int>(vertices.cols());
	buffer_v_->setData(sizeof(GLfloat) * vertices.size(), vertices.data());
}

void TriangleMesh::setFrontColor(const Eigen::Matrix<GLfloat, 3, -1>& front_color)
{
	if (!has_front_color_) {
		has_front_color_ = true;
		buffer_front_color_ = Buffer::newMutable(GL_ARRAY_BUFFER, sizeof(GLfloat) * front_color.size(),
		                                         front_color.data(), GL_STATIC_DRAW);
		vao_->attachBuffer(buffer_front_color_.get(), 3, 3, GL_FLOAT);
	} else {
		buffer_front_color_->setData(sizeof(GLfloat) * front_color.size(), front_color.data());
	}
}
void TriangleMesh::setBackColor(const Eigen::Matrix<GLfloat, 3, -1>& back_color)
{
	if (!has_back_color_) {
		has_back_color_ = true;
		buffer_back_color_ = Buffer::newMutable(GL_ARRAY_BUFFER, sizeof(GLfloat) * back_color.size(),
		                                        back_color.data(), GL_STATIC_DRAW);
		vao_->attachBuffer(buffer_back_color_.get(), 4, 3, GL_FLOAT);
	} else {
		buffer_back_color_->setData(sizeof(GLfloat) * back_color.size(), back_color.data());
	}
}

void TriangleMesh::setNormals(const Eigen::Matrix<GLfloat, 3, -1>& normals) {
	if (!has_normals_) {
		has_normals_ = true;
		buffer_normals_ = Buffer::newMutable(GL_ARRAY_BUFFER, sizeof(GLfloat) * normals.size(),
		                                     normals.data(), GL_STATIC_DRAW);
		vao_->attachBuffer(buffer_normals_.get(), 2, 3, GL_FLOAT);
	} else {
		buffer_normals_->setData(sizeof(GLfloat) * normals.size(), normals.data());
	}
}

void TriangleMesh::setIndices(const Eigen::Vector<GLuint, -1>& indices) {
	if (!has_indices_) {
		has_indices_ = true;
		buffer_index_ = Buffer::newMutable(GL_ARRAY_BUFFER, sizeof(GLuint) * indices.size(),
		                                   indices.data(), GL_STATIC_DRAW);
		vao_->attachBuffer(buffer_index_.get(), 1, 1, GL_UNSIGNED_INT);
	} else {
		buffer_index_->setData(sizeof(GLuint) * indices.size(), indices.data());
	}
}

}  // namespace sdtf::viewer::gl