/* OldComplexCellVisualizer.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the implementation file for an alternative version of the complex cell viualizer.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "OldComplexCellVisualizer.h"

#include <unordered_map>

#include "../datastructures/Grid3DInterface.h"
#include "../datastructures/Mesh3DTriangle.h"
#include "../utilities/vec.h"
#include "RenderingPrimitives.h"

//------------------------------------------------------------
// functions
//------------------------------------------------------------

// initialize variables and populate `complex_cell_vertices_` and `complex_front_triangles_`
void OldComplexCellVisualizer::init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) {
	current_state_ = 0;
	Grid3DInterface* grid = topofixer->getGrid3DCubical();

	// Store complex cell edges as two consecutive vertex positions.
	for (const auto cell_id : grid->getComplexCellsSet(Grid3DInterface::ComplexCellType::kBoth)) {
		const std::vector<long long> edges = grid->get_edges_neighboring_cell(cell_id);
		for (const long long edge_id : edges) {
			Vec3d pos;
			std::vector<long long> vertices = grid->get_verts_neighboring_edge(edge_id);
			grid->getVertexPosition(vertices[0], pos[0], pos[1], pos[2]);
			complex_cell_vertices_.push_back(pos);
			grid->getVertexPosition(vertices[1], pos[0], pos[1], pos[2]);
			complex_cell_vertices_.push_back(pos);
		}
		num_complex_cells_ += 1;
	}

	// Store grid front face triangles.
	for (long long face_id : grid->getFrontFacesVector()) {
		for (Vec3ll tri : grid->get_face_triangles(face_id)) {
			std::vector<Vec3d> tri_poses;
			tri_poses.reserve(3);
			for (int i = 0; i < 3; ++i) {
				Vec3d pos;
				grid->getVertexPosition(tri[i], pos[0], pos[1], pos[2]);
				tri_poses.push_back(pos);
			}
			complex_front_triangles_.push_back(tri_poses);
		}
		num_complex_front_faces_ = +1;
	}
}

// main display function, based on `current_state_` renders specific complex cell-related elements
void OldComplexCellVisualizer::display() {
	switch (current_state_) {
		case 0:
			break;
		case 1:
			renderComplexCells();
			break;
		case 2:
			renderFrontFaces();
			break;
	}
}

// switches to the next rendering state
void OldComplexCellVisualizer::nextState() {
	current_state_ = (current_state_ + 1) % kMaxStates;
	printDescription();
}

// prints the description of the current state, called whenever the state is changed
void OldComplexCellVisualizer::printDescription() {
	switch (current_state_) {
		case 0:
			std::cout << "(render no complex cell elements)" << std::endl;
			break;

		case 1:
			std::cout << "(render complex cell outlines)" << std::endl;
			std::cout << "Number of complex cells: " << num_complex_cells_ << std::endl;
			break;

		case 2:
			std::cout << "(render complex cell front faces)" << std::endl;
			std::cout << "Number of complex cell front faces: " << num_complex_front_faces_ << std::endl;
			break;
	}
}

// render the edges of complex cells
void OldComplexCellVisualizer::renderComplexCells() {
	GLfloat width;
	glGetFloatv(GL_LINE_WIDTH, &width);
	glLineWidth(7.0);
	glBegin(GL_LINES);
	glColor3f(0, 1, 0);
	for (Vec3d pos : complex_cell_vertices_) {
		glVertex3f(pos[0], pos[1], pos[2]);
	}
	glEnd();
	glLineWidth(width);
}

// render front face triangles
void OldComplexCellVisualizer::renderFrontFaces() {
	glEnable(GL_DEPTH_TEST);
	glDepthFunc(GL_LEQUAL);
	glDepthRange(0.0f, 1.0f);
	glClearDepth(1.0f);

	RenderingPrimitives::renderTrianglesEdgesAndFaces(complex_front_triangles_, {{0, 0.5, 0, 1.0}},
	                                                  {{0, 0.5, 0, 1.0}}, {{0, 1.0, 0, 1.0}});
}