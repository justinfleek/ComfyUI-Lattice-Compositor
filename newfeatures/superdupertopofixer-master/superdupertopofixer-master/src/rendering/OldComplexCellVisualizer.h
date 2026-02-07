/* ComplexCellVisualizer.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the header file for an alternative version of complex cell viualizer.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "Visualizer.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

class OldComplexCellVisualizer : public Visualizer {
	friend ImGUIWindows;

 public:
	OldComplexCellVisualizer(){};
	~OldComplexCellVisualizer(){};

	// Sets up variables, then, in order to achieve faster visualization, retrieves from the grid and
	// stores edges of complex cells as two consecutive vertex positions (`complex_cell_vertices_`)
	// sand triangles that make up the grid front faces (`complex_front_triangles_`).
	virtual void init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) override;

	// Main display function, draws complex cell-related elements based on state.
	// State 0 draws nothing.
	// State 1 draws complex cells.
	// State 2 draws complex face front.
	virtual void display() override;

	// Switch to the next state as described above.
	virtual void nextState() override;

 private:
	// Prints the description of the current state, called whenever the state changes.
	void printDescription();

	// Draw the edges of all complex cells.
	void renderComplexCells();

	// Draw front faces, each as two triangles, by calling `RenderingPrimitives` class functions.
	void renderFrontFaces();

	// Locally stored data used to facilitate faster rendering.
	std::vector<Vec3d> complex_cell_vertices_;
	std::vector<std::vector<Vec3d>> complex_front_triangles_;

	// Statistics of complex elements, printed when `printDescription` is called.
	size_t num_complex_cells_ = 0;
	size_t num_complex_front_faces_ = 0;

	// Parameters to track current draw state.
	int current_state_;
	const size_t kMaxStates = 3;
};