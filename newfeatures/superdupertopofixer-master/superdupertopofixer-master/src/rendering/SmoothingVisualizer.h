#pragma once

#include "../datastructures/Mesh3DInterface.h"
#include "../submodules/Smoother.h"
#include "Visualizer.h"
#include "../schemes/TopoFixerSettings.h"

// Computes smoothed positions for mesh vertices, which allows interpolating between the original
// and smoothed mesh states.
class SmoothingVisualizer : public Visualizer {
	friend ImGUIWindows;

 public:
	SmoothingVisualizer() = default;
	~SmoothingVisualizer(){};

	// Retrieves mesh vertex positions, and computes smoothed positions.
	virtual void init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) override;

	// If `alpha_` value was changed, calculates the interpolated mesh vertex positions, and saves
	// them in the mesh corner table.
	virtual void display() override;

	// There is only one state, therefore no change in state can happen. Instead, the visualizer
	// calculates continuous interpolation between original and smoothed vertex positions based on
	// `alpha_` parameter directly.
	virtual void nextState() override{};

	virtual bool isMeshChanged() const override;

 private:
	// Computes vertex neighbors of each mesh vertex, then computes smoothed mesh vertex positions,
	// and returns them. Actual vertex positions in Mesh3DCornerTable remain at the original values.
	std::vector<Vec3d> computeSmoothedPositions(Mesh3DInterface* mesh,
	                                            const std::vector<Vec3d>& original_coords);

	// Use the input vector `coords` of vertex coordinates to set vertex positions in mesh corner
	// table.
	void setMeshCoords(Mesh3DInterface* mesh, const std::vector<Vec3d>& coords);

	// Mesh data structure.
	Mesh3DInterface* mesh_;

	// Vectors of coordinates that store the actual (original) mesh vertices, and their smoothed
	// counterparts.
	std::vector<Vec3d> original_vpos_;
	std::vector<Vec3d> smoothed_vpos_;

	// Blending coefficient that determines the interpolation between original and smoothed vertex
	// positions (original is 0 and smoothed is 1). `alpha_` value is set by the friend class
	// `ImGUIWindows`.
	float prev_alpha_;
	float alpha_;

	// Smoother class for calculating smoothed mesh vertex positions.
	JacobiSmoother smoother_;
	// Number of smoothing steps performed for visualization (not for actually moving mesh vertices!)
	size_t kSmoothingSteps;
};