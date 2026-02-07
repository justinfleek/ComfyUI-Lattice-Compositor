#include "NonmanifoldEdgeVisualizer.h"

#include "datastructures/Mesh3DHalfCorner.h"

NonmanifoldEdgeVisualizer::~NonmanifoldEdgeVisualizer() {
	if (initialized_) {
		glDeleteBuffers(1, nonmanifold_edge_buffers_);
	}
}

void NonmanifoldEdgeVisualizer::init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) {
	glGenBuffers(1, nonmanifold_edge_buffers_);
	absl::flat_hash_set<SortedMeshEdge> nonmanifold_edges =
	    nonmanifoldEdges(*topofixer->getMesh3DInterface());
	num_vertices_ = 2 * nonmanifold_edges.size();
	std::vector<float> vertex_data(3 * num_vertices_);

	size_t vertex_idx = 0;
	for (const SortedMeshEdge& edge : nonmanifold_edges) {
		Vec3d coords = edge.getSmaller()->getCoords();
		vertex_data[vertex_idx + 0] = coords[0];
		vertex_data[vertex_idx + 1] = coords[1];
		vertex_data[vertex_idx + 2] = coords[2];
		vertex_idx += 3;

		coords = edge.getLarger()->getCoords();
		vertex_data[vertex_idx + 0] = coords[0];
		vertex_data[vertex_idx + 1] = coords[1];
		vertex_data[vertex_idx + 2] = coords[2];
		vertex_idx += 3;
	}
	glBindBuffer(GL_ARRAY_BUFFER, nonmanifold_edge_buffers_[0]);
	glBufferData(GL_ARRAY_BUFFER, vertex_data.size() * sizeof(float), vertex_data.data(),
	             GL_STATIC_DRAW);
	glBindBuffer(GL_ARRAY_BUFFER, 0);
	initialized_ = true;
}

void NonmanifoldEdgeVisualizer::display() {
	if (enabled_) {
		renderEdges();
	}
}

absl::flat_hash_set<SortedMeshEdge> NonmanifoldEdgeVisualizer::nonmanifoldEdges(
    Mesh3DInterface& mesh) const {
	absl::flat_hash_set<SortedMeshEdge> nonmanifold_edges;
	for (Mesh3DTriangle* tri : mesh.ListTriangles()) {
		Mesh3DHalfCorner* hfc = tri->getHalfCorner();
		for (int i = 0; i < 3; ++i, hfc = hfc->getNext()) {
			if (mesh.isEdgeNonmanifold(hfc)) {
				nonmanifold_edges.emplace(hfc->getNext()->getVertex(), hfc->getPrev()->getVertex());
			}
		}
	}
	return nonmanifold_edges;
}

void NonmanifoldEdgeVisualizer::renderEdges() const {
	// save current glLineWidth, and set it to the input value
	GLfloat width;
	glGetFloatv(GL_LINE_WIDTH, &width);
	glLineWidth(15.0);

	glEnableClientState(GL_VERTEX_ARRAY);

	glBindBuffer(GL_ARRAY_BUFFER, nonmanifold_edge_buffers_[0]);
	glVertexPointer(3, GL_FLOAT, 0, 0);
	glBindBuffer(GL_ARRAY_BUFFER, 0);
	glColor3f(0.0, 0.0, 0.0);

	glDrawArrays(GL_LINES, 0, num_vertices_);

	glDisableClientState(GL_VERTEX_ARRAY);
	glLineWidth(width);
}
