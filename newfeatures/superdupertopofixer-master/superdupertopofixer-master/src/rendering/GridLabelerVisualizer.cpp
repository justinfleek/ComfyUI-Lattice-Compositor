#include "GridLabelerVisualizer.h"

// clang-format off
#include <GL/glew.h>
#include <GL/glu.h>
#include <GL/glut.h>
#include <GL/gl.h>
// clang-format on

#include "OpenGLRenderer.h"

void GridLabelerVisualizer::init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) {
	current_state_ = 0;
	grid_ = topofixer->getGrid3DCubical();
	grid_labeler_ = topofixer->getGridLabeler();
	material_colors_ = colors;
	grid_labels_ = grid_labeler_->getLabelsPerOrientation();

	const double cell_dx = grid_->get_cell_dx();
	const double displacement = 0.055 * cell_dx;
	displacements_ = {{-displacement, 0, 0}, {displacement, 0, 0},  {0, -displacement, 0},
	                  {0, displacement, 0},  {0, 0, -displacement}, {0, 0, displacement}};
	cube_half_side_ = 0.025 * cell_dx;
}

void GridLabelerVisualizer::display() {
	switch (current_state_) {
		// Render nothing.
		case 0:
			break;

		// Render all material labels at grid points.
		case 1:
			renderGridLabels();
			break;

		// Render labels from one of the orientations.
		case 2:
		case 3:
		case 4:
			renderGridLabelsFromOrientation(current_state_ - 2);
			break;
		case 5:
			renderUniqueGridLabels();
	}
}

void GridLabelerVisualizer::renderGridLabels() {
	drawSetup();

	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
	glBegin(GL_TRIANGLES);

	for (const long long cell_id : grid_->getCellsWithTriangles()) {
		for (const long long vertex_id : grid_->get_verts_neighboring_cell(cell_id)) {
			renderMaterialAtVertex(vertex_id, grid_->getVertexMaterial(vertex_id), cube_half_side_,
			                       displacements_);
		}
	}
	glEnd();
}

void GridLabelerVisualizer::renderGridLabelsFromOrientation(int orientation) {
	drawSetup();

	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
	glBegin(GL_TRIANGLES);

	for (const auto& [vertex_id, material] : grid_labels_[orientation]) {
		renderMaterialAtVertex(vertex_id, material, cube_half_side_, displacements_);
	}

	glEnd();
}

void GridLabelerVisualizer::renderUniqueGridLabels() {
	drawSetup();

	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
	glBegin(GL_TRIANGLES);

	for (const auto& [vertex_id, material_idx] : grid_->getUniqueLabelingMap()) {
		SparseVector<int> material;
		material.assign(material_idx, 1.0);
		renderMaterialAtVertex(vertex_id, material, cube_half_side_, displacements_);
	}

	glEnd();
}

void GridLabelerVisualizer::drawSetup() {
	OpenGLRenderer::setLights();
	glEnable(GL_COLOR_MATERIAL);
}

void GridLabelerVisualizer::renderMaterialAtVertex(const long long vertex_id,
                                                   const SparseVector<int>& material,
                                                   const double cube_epsilon,
                                                   const std::vector<Vec3d> dis) {
	long long i, j, k;
	Vec3d vertex_pos;
	Vec3d render_pos;
	grid_->get_vertex_coords(vertex_id, i, j, k);
	grid_->getVertexPosition(i, j, k, vertex_pos.v[0], vertex_pos.v[1], vertex_pos.v[2]);
	int material_index;
	int material_value;
	for (int j = 0; j < material.getNNZ(); j++) {
		material_index = material.getKey(j);
		material_value = material.getValue(j);
		// TODO: change this so that when material_value > 1, two boxes are drawn
		if (material_value > 1 || material_value == 0) {
			continue;
		}
		material_index = grid_->convertGridLabelToMeshLabel(material_index);
		if (material_value == 1) {
			// inside material
			glColor3f(material_colors_[material_index][0], material_colors_[material_index][1],
			          material_colors_[material_index][2]);
		} else if (material_value < 0) {
			// it is outside a mateiral once or more than once
			glColor3f(0.0, 0.0, 0.0);  // by default
		}
		render_pos = vertex_pos + dis[material_index];
		OpenGLRenderer::constructCube(render_pos[0], render_pos[1], render_pos[2], cube_epsilon);
	}
}

void GridLabelerVisualizer::nextState() {
	current_state_ = (current_state_ + 1) % kMaxStates;
	printDescription();
}

void GridLabelerVisualizer::printDescription() {
	switch (current_state_) {
		case 0:
			std::cout << "(render no vertex labels on the grid)" << std::endl;
			break;

		case 1:
			std::cout << "(render vertex labels stored on the grid)" << std::endl;
			break;

		case 2:
		case 3:
		case 4:
			std::cout << "(render vertex labels for orientation " << current_state_ - 2 << ")"
			          << std::endl;
			break;
	}
}
