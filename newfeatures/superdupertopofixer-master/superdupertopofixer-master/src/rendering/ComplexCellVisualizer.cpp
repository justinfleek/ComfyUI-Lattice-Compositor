/* ComplexCellVisualizer.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the implementation file for complex cell visualizer.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "ComplexCellVisualizer.h"

// clang-format off
#include <GL/glew.h>
#include <GL/glu.h>
#include <GL/glut.h>
#include <GL/gl.h>
// clang-format on

#include <unordered_map>

//------------------------------------------------------------
// controlling functions
//------------------------------------------------------------

// initialization of variables
void ComplexCellVisualizer::init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) {
	complex_cell_detector_ = topofixer->getComplexCellDetector();
	grid_ = topofixer->getGrid3DCubical();

	current_state = 0;
	current_element_iterator = complex_cell_detector_->getAllFaceGraphs()->begin();
	if (complex_cell_detector_->getAllFaceGraphs()->empty()) {
		current_element = -1;
	} else {
		current_element = current_element_iterator->first;
	}

	// colors
	// 0: graph edges
	// 1: graph vertices
	// 2: grid faces
	// 3: grid cells
	// TODO: collect this from the input vector
	object_colors = {{1.0, 0.0, 0.0}, {0.0, 0.0, 1.0}, {0.65, 0.9, 0.9}, {1.0, 0.0, 0.0}};
}

// main display function, based on `current_state` renders specific elements related to complexity
// detection
void ComplexCellVisualizer::display() {
	switch (current_state) {
		// Render nothing.
		case 0:
			break;

		// Render all complex cells.
		case 1:
			renderAllComplexCells();
			break;

		// Render all shallow cells (topologically complex, but excluded from remeshing).
		case 2:
			renderAllShallowCells();
			renderAllDeepCells();
			break;

		// Render all grid face graphs (edges and vertices), highlight all grid faces with non-empty
		// graphs, and draw all grid cells adjacent to such faces.
		case 3:
			renderAllComplexFaces();
			break;

		// Render all grid face graphs (edges and vertices) on complex faces, highlight these faces, and
		// draw all grid cells adjacent to them.
		case 4:
			renderAllComplexFaceElements();
			break;

		// Render all grid face graphs (edges and vertices), highlight all grid faces with non-empty
		// graphs, and draw all grid cells adjacent to such faces.
		case 5:
			renderAllGraphFaces();
			break;

		// Render all grid face graphs (edges and vertices), highlight all grid faces with non-empty
		// graphs, and draw all grid cells adjacent to such faces.
		case 6:
			renderAllGraphFaceElements();
			break;

		// Highlight all front faces, that is faces adjacent to one complex and one non-complex grid
		// cell.
		case 7:
			renderAllFrontFaces();
			renderAllComplexCells();

		// Render one grid face graph (edges and vertices), highlight its grid face, and draw its
		// adjacent grid cells. Calling function `nextElement` iterates over all faces with non-empty
		// face graphs.
		case 8:
			if (!complex_cell_detector_->getAllFaceGraphs()->empty()) {
				renderOneConfiguration();
			}
			break;

		// Ask the user to input a face id, then render its grid face graph (edges and vertices) if
		// non-empty, highlight its grid face, and draw its adjacent grid cells.
		case 9:
			if (!complex_cell_detector_->getAllFaceGraphs()->empty()) {
				std::cout << "-input id of grid face to be rendered: " << std::endl;
				std::cin >> current_element;
				std::cout << std::endl;

				renderOneConfiguration();
			}
			break;
	}
}

// prints the description of the current state, called whenever the state is changed
void ComplexCellVisualizer::printDescription() {
	switch (current_state) {
		case 0:
			std::cout << "-no complex elements rendered" << std::endl;
			break;

		case 1:
			std::cout << "-rendered objects: all complex cells" << std::endl;
			break;

		case 2:
			std::cout << "-rendered objects: all shallow cells " << std::endl;
			break;

		case 3:
			std::cout << "-rendered objects: all complex faces " << std::endl;
			break;

		case 4:
			std::cout << "-rendered objects: all complex cells, all complex faces, all face graphs on "
			             "complex faces"
			          << std::endl;
			break;

		case 5:
			std::cout << "-rendered objects: all faces with non-empty graphs " << std::endl;
			break;

		case 6:
			std::cout << "-rendered objects: all faces with non-empty graphs, their face graphs, and the "
			             "cells they are adjacent to"
			          << std::endl;
			break;

		case 7:
			std::cout << "-rendered objects: all front faces" << std::endl;
			break;

		case 8:
			if (!complex_cell_detector_->getAllFaceGraphs()->empty()) {
				std::cout << "-rendered objects: for face: " << current_element
				          << " face graph, grid face, and adjacent grid cells" << std::endl;
			} else {
				std::cout << "-no grid faces with graphs to render" << std::endl;
			}
			break;

		case 9:
			if (complex_cell_detector_->getAllFaceGraphs()->count(current_element)) {
				std::cout << "-rendered objects: for face: " << current_element
				          << " face graph, grid face, and adjacent grid cells" << std::endl;
			} else {
				long long face_i_coord, face_j_coord, face_k_coord, face_orient;
				grid_->get_face_coords(current_element, face_i_coord, face_j_coord, face_k_coord,
				                       face_orient);
				if (!grid_->face_out_of_bounds(face_i_coord, face_j_coord, face_k_coord, face_orient)) {
					std::cout << "-rendered objects: for face: " << current_element
					          << " grid face, and adjacent grid cells (no grid face graph is stored)"
					          << std::endl;
				} else {
					std::cout << "-input face out of bounds, nothing is rendered" << std::endl;
				}
			}
			break;
	}
}

// switches to the next rendering state
void ComplexCellVisualizer::nextState() {
	current_state = (current_state + 1) % kMaxStates;
	printDescription();
}

// switch to the next element (for element-wise drawing)
void ComplexCellVisualizer::nextElement() {
	if (complex_cell_detector_->getAllFaceGraphs()->empty()) {
		return;
	}

	current_element_iterator++;
	if (current_element_iterator == complex_cell_detector_->getAllFaceGraphs()->end()) {
		current_element_iterator = complex_cell_detector_->getAllFaceGraphs()->begin();
	}
	current_element = current_element_iterator->first;

	std::cout << "-current element for drawing: " << current_element << std::endl;
}

//------------------------------------------------------------
// display functions
//------------------------------------------------------------

// renders all complex cells, complex faces, and graphs on complex faces
void ComplexCellVisualizer::renderAllComplexFaceElements() {
	renderAllComplexCells();
	renderAllComplexFaces();
	renderAllComplexFaceGraphEdges();
	renderAllComplexFaceGraphVertices();
}

// renders all face graphs, their grid faces, and adjacent grid cells
void ComplexCellVisualizer::renderAllGraphFaceElements() {
	renderCellsAdjacentToGraphFaces();
	renderAllGraphFaces();
	renderAllGraphEdges();
	renderAllGraphVertices();
}

// renders one face graph (edges and vertices), its grid faces, and adjacent grid cells; calling
// `nextElement` iterates to the next face
void ComplexCellVisualizer::renderOneConfiguration() {
	setUpCellHighlighting(Vec3d(0.0, 0.0, 0.0));
	std::vector<long long> cells_to_draw = grid_->get_cells_neighboring_face(current_element);
	for (long long cell : cells_to_draw) {
		renderCell(cell);
	}
	wrapUpCellHighlighting();

	setUpFaceHighlighting();
	renderFace(current_element);
	wrapUpFaceHighlighting();

	setUpGraphEdgeDrawing();
	renderGraphEdges(current_element);
	wrapUpGraphEdgeDrawing();

	setUpGraphVertexDrawing();
	renderGraphEdges(current_element);
	wrapUpGraphVertexDrawing();
}

//------------------------------------------------------------
// render grid cells
//------------------------------------------------------------

// renders all complex cells
void ComplexCellVisualizer::renderAllComplexCells() {
	setUpCellHighlighting(Vec3d(0.0, 0.0, 0.0));

	absl::flat_hash_set<long long> cells_to_draw =
	    grid_->getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed);
	for (long long cell : cells_to_draw) {
		renderCell(cell);
	}

	wrapUpCellHighlighting();
}

// renders all shallow cells
void ComplexCellVisualizer::renderAllShallowCells() {
	setUpCellHighlighting(Vec3d(1.0, 0.0, 0.0));

	absl::flat_hash_set<long long> cells_to_draw = grid_->getEdgeShallowCells();
	for (long long cell : cells_to_draw) {
		renderCell(cell);
	}

	wrapUpCellHighlighting();
}

// renders all deep cells
void ComplexCellVisualizer::renderAllDeepCells() {
	setUpCellHighlighting(Vec3d(0.0, 0.0, 1.0));

	absl::flat_hash_set<long long> cells_to_draw = grid_->getEdgeDeepCells();
	for (long long cell : cells_to_draw) {
		renderCell(cell);
	}

	wrapUpCellHighlighting();
}

// renders all complex cells
void ComplexCellVisualizer::renderCellsAdjacentToGraphFaces() {
	setUpCellHighlighting(Vec3d(1.0, 0.0, 0.0));

	absl::flat_hash_map<long long, std::vector<std::pair<Vec3d, Vec3d>>>* all_face_graphs =
	    complex_cell_detector_->getAllFaceGraphs();

	for (auto& [key, val] : (*all_face_graphs)) {
		std::vector<long long> cells_to_draw = grid_->get_cells_neighboring_face(key);
		for (long long cell : cells_to_draw) {
			renderCell(cell);
		}
	}

	wrapUpCellHighlighting();
}

// renders a cell with the given id
void ComplexCellVisualizer::renderCell(long long cell_id) {
	double x, y, z;
	for (const long long edge : grid_->get_edges_neighboring_cell(cell_id)) {
		std::vector<long long> edge_vertices = grid_->get_verts_neighboring_edge(edge);
		grid_->getVertexPosition(edge_vertices[0], x, y, z);
		glVertex3f(x, y, z);
		grid_->getVertexPosition(edge_vertices[1], x, y, z);
		glVertex3f(x, y, z);
	}
}

void ComplexCellVisualizer::setUpCellHighlighting(Vec3d rendering_color) {
	glGetFloatv(GL_LINE_WIDTH, &stored_line_width);
	glLineWidth(2);

	glBegin(GL_LINES);
	glColor3f(rendering_color[0], rendering_color[1], rendering_color[2]);
}
void ComplexCellVisualizer::wrapUpCellHighlighting() {
	glEnd();
	glLineWidth(stored_line_width);
}

//------------------------------------------------------------
// render grid faces
//------------------------------------------------------------

// highlights all complex faces by repeatedly calling function `renderFace`
void ComplexCellVisualizer::renderAllComplexFaces() {
	setUpFaceHighlighting();

	absl::flat_hash_set<long long> faces_to_draw = grid_->getTopoComplexFaces();
	for (long long face : faces_to_draw) {
		renderFace(face);
	}

	wrapUpFaceHighlighting();
}

// highlights all grid faces with graphs by repeatedly calling function `renderFace`
void ComplexCellVisualizer::renderAllGraphFaces() {
	setUpFaceHighlighting();

	absl::flat_hash_map<long long, std::vector<std::pair<Vec3d, Vec3d>>>* all_face_graphs =
	    complex_cell_detector_->getAllFaceGraphs();

	for (auto& [key, val] : (*all_face_graphs)) {
		renderFace(key);
	}

	wrapUpFaceHighlighting();
}

void ComplexCellVisualizer::renderAllFrontFaces() {
	setUpFaceHighlighting();

	absl::flat_hash_set<long long> faces_to_draw = grid_->getFrontFacesSet();
	for (long long face : faces_to_draw) {
		renderFace(face);
	}

	wrapUpFaceHighlighting();
}

// renders highlighting of grid face with `face_id`
void ComplexCellVisualizer::renderFace(long long face_id) {
	std::vector<long long> grid_face_vertices = grid_->get_verts_neighboring_face(face_id);
	// ASSERT: check that there are exactly 4 vertices on the face with `face_id`
	assert(grid_face_vertices.size() == 4 &&
	       "-ERROR: less than 4 vertices on an in-bounds grid face\n");

	long long i, j, k;
	double x, y, z;
	for (int it = 0; it <= 2; ++it) {
		grid_->get_vertex_coords(grid_face_vertices[it], i, j, k);
		grid_->getVertexPosition(i, j, k, x, y, z);
		glVertex3f(x, y, z);
	}
	for (int it = 1; it <= 3; ++it) {
		grid_->get_vertex_coords(grid_face_vertices[it], i, j, k);
		grid_->getVertexPosition(i, j, k, x, y, z);
		glVertex3f(x, y, z);
	}
}

// calls openGL routines that set up grid face highlighting
void ComplexCellVisualizer::setUpFaceHighlighting() {
	glEnable(GL_DEPTH_TEST);
	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);

	glBegin(GL_TRIANGLES);
	glColor3d(object_colors[2][0], object_colors[2][1], object_colors[2][2]);
}

// calls openGL routines that wrap up grid face highlighting
void ComplexCellVisualizer::wrapUpFaceHighlighting() { glEnd(); }

//------------------------------------------------------------
// render graph edges
//------------------------------------------------------------

// renders all grid face graph edges on complex faces by repeatedly calling function
// `renderFaceGraphEdges`
void ComplexCellVisualizer::renderAllComplexFaceGraphEdges() {
	setUpGraphEdgeDrawing();

	absl::flat_hash_map<long long, std::vector<std::pair<Vec3d, Vec3d>>>* all_face_graphs =
	    complex_cell_detector_->getAllFaceGraphs();

	for (auto& [key, val] : (*all_face_graphs)) {
		if (grid_->isFaceMarkedTopoComplex(key)) {
			renderGraphEdges(key);
		}
	}
	wrapUpGraphEdgeDrawing();
}

// renders all grid face graph edges by repeatedly calling function `renderFaceGraphEdges`
void ComplexCellVisualizer::renderAllGraphEdges() {
	setUpGraphEdgeDrawing();

	absl::flat_hash_map<long long, std::vector<std::pair<Vec3d, Vec3d>>>* all_face_graphs =
	    complex_cell_detector_->getAllFaceGraphs();

	for (auto& [key, val] : (*all_face_graphs)) {
		renderGraphEdges(key);
	}

	for (long long front_face : grid_->getFrontFacesSet()) {
		for (auto& [edge, triangle] : grid_->getGraphOnFace(front_face)) {
			glVertex3f(edge.first->getXCoord(), edge.first->getYCoord(), edge.first->getZCoord());
			glVertex3f(edge.second->getXCoord(), edge.second->getYCoord(), edge.second->getZCoord());
		}
	}

	wrapUpGraphEdgeDrawing();
}

// renders the face graph edges of the grid face with the input `face_id`
void ComplexCellVisualizer::renderGraphEdges(long long face_id) {
	std::vector<std::pair<Vec3d, Vec3d>> edge_coords =
	    complex_cell_detector_->getAllFaceGraphs()->at(face_id);

	for (auto& [v0, v1] : edge_coords) {
		glVertex3f(v0[0], v0[1], v0[2]);
		glVertex3f(v1[0], v1[1], v1[2]);
	}
}

// calls openGL routines that set up graph edge drawing
void ComplexCellVisualizer::setUpGraphEdgeDrawing() {
	glGetFloatv(GL_LINE_WIDTH, &stored_line_width);
	glLineWidth(3);

	glEnable(GL_DEPTH_TEST);
	glBegin(GL_LINES);
	glColor3d(object_colors[0][0], object_colors[0][1], object_colors[0][2]);
}

// calls openGL routines that wrap up graph edge drawing
void ComplexCellVisualizer::wrapUpGraphEdgeDrawing() {
	glEnd();
	glLineWidth(stored_line_width);
}

//------------------------------------------------------------
// render graph vertices
//------------------------------------------------------------

// renders all grid face graph vertices on complex faces, apart from setup and wrapup functionally
// equivalent to calling `renderAllComplexFaceGraphEdges`
void ComplexCellVisualizer::renderAllComplexFaceGraphVertices() {
	setUpGraphVertexDrawing();

	absl::flat_hash_map<long long, std::vector<std::pair<Vec3d, Vec3d>>>* all_face_graphs =
	    complex_cell_detector_->getAllFaceGraphs();

	for (auto& [key, val] : (*all_face_graphs)) {
		if (grid_->isFaceMarkedTopoComplex(key)) {
			renderGraphEdges(key);
		}
	}

	wrapUpGraphVertexDrawing();
}

// renders the face graph vertices, apart from setup and wrapup functionally equivalent to calling
// `renderAllGraphEdges`
void ComplexCellVisualizer::renderAllGraphVertices() {
	setUpGraphVertexDrawing();

	absl::flat_hash_map<long long, std::vector<std::pair<Vec3d, Vec3d>>>* all_face_graphs =
	    complex_cell_detector_->getAllFaceGraphs();

	for (auto& [key, val] : (*all_face_graphs)) {
		renderGraphEdges(key);
	}

	wrapUpGraphVertexDrawing();
}

// calls openGL routines that set up graph vertex drawing
void ComplexCellVisualizer::setUpGraphVertexDrawing() {
	glGetFloatv(GL_POINT_SIZE, &stored_point_size);
	glPointSize(10.0);

	glEnable(GL_DEPTH_TEST);
	glEnable(GL_PROGRAM_POINT_SIZE);
	glEnable(GL_POINT_SMOOTH);
	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

	glBegin(GL_POINTS);
	glColor3d(object_colors[1][0], object_colors[1][1], object_colors[1][2]);
}

// calls openGL routines that wrap up graph vertex drawing
void ComplexCellVisualizer::wrapUpGraphVertexDrawing() {
	glEnd();
	glPointSize(stored_point_size);
}
