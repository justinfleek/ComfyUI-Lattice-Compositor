#pragma once

#include <exception>

#include "../datastructures/Mesh3DHalfCorner.h"
#include "../datastructures/Mesh3DInterface.h"
#include "Visualizer.h"
#include "absl/container/flat_hash_set.h"

// Computes smoothed positions for mesh vertices, which allows interpolating between the original
// and smoothed mesh states.
class NonmanifoldEdgeVisualizer : public Visualizer {
	friend ImGUIWindows;

 public:
	NonmanifoldEdgeVisualizer(){};
	virtual ~NonmanifoldEdgeVisualizer();

	// Finds nonmanifold edges and initializes vertex buffers.
	virtual void init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) override;
	virtual void display() override;
	virtual void nextState() override { enabled_ = !enabled_; };

 private:
	absl::flat_hash_set<SortedMeshEdge> nonmanifoldEdges(Mesh3DInterface& mesh) const;
	void renderEdges() const;

	int num_vertices_;
	bool enabled_;
	// 0: line vertices.
	GLuint nonmanifold_edge_buffers_[1];
	bool initialized_ = false;
};