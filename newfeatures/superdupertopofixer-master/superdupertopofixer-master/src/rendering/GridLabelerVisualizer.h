#pragma once

#include "../datastructures/Grid3DInterface.h"
#include "../modules/GridLabeler.h"
#include "../utilities/vec.h"
#include "Visualizer.h"

// TODO: Does not support more than 6 materials.
class GridLabelerVisualizer : public Visualizer {
 public:
	GridLabelerVisualizer() = default;
	virtual ~GridLabelerVisualizer() = default;

	// We have to initialize separately, because it is used in a static object.
	// TODO: refactor the visualization system to be able to use constructors directly.
	virtual void init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) override;

	// Draw grid labels based on the state.
	// State 0 draws nothing.
	// State 1 draws vertex labels stored on the grid.
	// State 2-4 draws labels for different directions saved as a part of grid labeling algorithm.
	virtual void display() override;

	// Switch to the next rendering state.
	virtual void nextState() override;

 private:
	// Draws labels stored on the grid.
	void renderGridLabels();

	// Draws labels computed by grid labeling algorithm for a certain grid orientation.
	void renderGridLabelsFromOrientation(int orientation);

	// Draws labels obtained after LabelResolver.
	void renderUniqueGridLabels();

	// Sets up OpenGL to draw the grid label cubes.
	void drawSetup();

	// Renders a material cube for a given vertex.
	void renderMaterialAtVertex(const long long vertex_id, const SparseVector<int>& material,
	                            const double cube_epsilon, const std::vector<Vec3d> dis);

	// Prints the description of the current state.
	void printDescription();

	// Parameters to track current draw state.
	unsigned int current_state_;
	const unsigned int kMaxStates = 6;

	// Label cube marker parameters. Computed based on the grid cell size.
	std::vector<Vec3d> displacements_;
	double cube_half_side_;

	Grid3DInterface* grid_;
	GridLabeler* grid_labeler_;
	std::vector<Vec4d> material_colors_;

	// Labels for each orientation computed by grid labeling module.
	std::vector<absl::flat_hash_map<long long, SparseVector<int>>> grid_labels_;
};
