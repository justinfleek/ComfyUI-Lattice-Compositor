/* ComplexCellVisualizer.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the header file for complex cell visualizer.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "../datastructures/Grid3DInterface.h"
#include "../modules/ComplexCellDetector.h"
#include "../utilities/vec.h"
#include "Visualizer.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this class manages the visualization of complex elements
class ComplexCellVisualizer : public Visualizer {
	friend ImGUIWindows;

 public:
	ComplexCellVisualizer() = default;
	~ComplexCellVisualizer() = default;

	// We have to initialize separately, because the visualizer is used in a static object.
	// TODO: refactor the visualization system to be able to use constructors directly.
	virtual void init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) override;

	// Draw grid labels based on `current_state`:
	// -0: draws nothing,
	// -1: draws all complex cells,
	// -2: draws all features at all complex faces,
	// -3: draws all features at all faces with non-empty face graphs,
	// -4: draws all features at one face with non-empty face graph, iterate by calling `nextElement`,
	// -5: ask user to input a face id, then draws all features at the given face.
	virtual void display() override;

	// Switch to the next rendering state.
	virtual void nextState() override;

	// Switch to the next element (for element-wise drawing).
	void nextElement();

 private:
	// Parameters to track current draw state.
	unsigned int current_state;
	const unsigned int kMaxStates = 9;
	absl::flat_hash_map<long long, std::vector<std::pair<Vec3d, Vec3d>>>::iterator
	    current_element_iterator;
	unsigned long long current_element;

	// Data structures and modules that the visualizer pulls data from.
	ComplexCellDetector* complex_cell_detector_;
	Grid3DInterface* grid_;

	// Colors used in the rendering:
	// 0: graph edges
	// 1: graph vertices
	// 2: grid faces with graphs
	// 3: grid cells
	std::vector<Vec3d> object_colors;

	// Prints the description of the current state, called whenever the state changes.
	void printDescription();

	// Stores global drawing parameters; these are stored before being changed within class functions,
	// and are subsequently restored as part of wrap up, once the class functions finish rendering.
	GLfloat stored_line_width;
	GLfloat stored_point_size;

	// Calls openGL routines that set up and wrap up drawing of elements.
	void setUpGraphEdgeDrawing();
	void wrapUpGraphEdgeDrawing();
	void setUpGraphVertexDrawing();
	void wrapUpGraphVertexDrawing();
	void setUpFaceHighlighting();
	void wrapUpFaceHighlighting();
	void setUpCellHighlighting(Vec3d rendering_color);
	void wrapUpCellHighlighting();

	// Renders grid face graphs, highlights grid faces, and draws adjacent grid cells to all complex
	// faces/all faces with non-empty graphs/one specific face (determined by current_element,
	// iterated by calling function nextElement).
	void renderAllComplexFaceElements();
	void renderAllGraphFaceElements();
	void renderOneConfiguration();

	// Highlights grid cell adjacent to face with given `face_id`/all grid cells adjacent to faces
	// that tested positive for complexity/all cells that are topologically complex, but excluded from
	// remeshing/all grid cells adjacent to faces that were tested for complexity and have non-empty
	// face graphs.
	void renderCell(long long face_id);
	void renderAllComplexCells();
	void renderAllShallowCells();
	void renderAllDeepCells();
	void renderCellsAdjacentToGraphFaces();

	// Highlights grid face with given `face_id`/ all grid faces that tested positive for complexity/
	// all grid faces that were tested for complexity, and have non-empty face graphs/ all front
	// faces.
	void renderFace(long long face_id);
	void renderAllComplexFaces();
	void renderAllGraphFaces();
	void renderAllFrontFaces();

	// Renders face graph edges for the face with the given `face_id`/all faces that tested positive
	// for complexity/all faces that were tested for complexity, and have non-empty face graphs.
	void renderGraphEdges(long long face_id);
	void renderAllComplexFaceGraphEdges();
	void renderAllGraphEdges();

	// Renders face graph vertices for all faces that tested positive for complexity/all faces that
	// were tested for complexity, and have non-empty face graphs. Rendering graph vertices on one
	// given face is functionally equivalent to rendering graph edges on a given face, and so doesn't
	// have its own function.
	void renderAllComplexFaceGraphVertices();
	void renderAllGraphVertices();
};
