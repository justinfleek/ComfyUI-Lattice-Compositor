#include "SmoothingVisualizer.h"

#include <unordered_map>

#include "../datastructures/Mesh3DTriangle.h"

// retrieves current mesh vertex positions, and computes smoothed positions
void SmoothingVisualizer::init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) {
	prev_alpha_ = 0;
	alpha_ = 0;
	kSmoothingSteps = topofixer->getSettings().vis_vertex_smoothing_steps;
	mesh_ = topofixer->getMesh3DInterface();
	mesh_->getVertexPositions(original_vpos_);
	smoothed_vpos_ = computeSmoothedPositions(mesh_, original_vpos_);
}

// based on `alpha_`, calculate interpolated mesh positions and save them in the corner table
void SmoothingVisualizer::display() {
	if (alpha_ == prev_alpha_) {
		return;
	}
	prev_alpha_ = alpha_;
	std::vector<Vec3d> blended_vpos;
	blended_vpos.reserve(original_vpos_.size());
	for (int i = 0; i < original_vpos_.size(); ++i) {
		blended_vpos.push_back(original_vpos_[i] * (1 - alpha_) + smoothed_vpos_[i] * alpha_);
	}
	setMeshCoords(mesh_, blended_vpos);
}

bool SmoothingVisualizer::isMeshChanged() const { return alpha_ != prev_alpha_; }

// computes and returns smoothed vertex positions, doesn't change actual vertex coordinates
std::vector<Vec3d> SmoothingVisualizer::computeSmoothedPositions(
    Mesh3DInterface* mesh, const std::vector<Vec3d>& original_coords) {
	// Compute vertex neighbours.
	absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DVertex*>> vertneibs;
	for (Mesh3DTriangle* tri : mesh->ListTriangles()) {
		Mesh3DVertex* hfc_v = tri->getHalfCorner()->getVertex();
		Mesh3DVertex* nhfc_v = tri->getHalfCorner()->getNext()->getVertex();
		Mesh3DVertex* phfc_v = tri->getHalfCorner()->getPrev()->getVertex();

		vertneibs[hfc_v].insert(nhfc_v);
		vertneibs[hfc_v].insert(phfc_v);

		vertneibs[nhfc_v].insert(hfc_v);
		vertneibs[nhfc_v].insert(phfc_v);

		vertneibs[phfc_v].insert(hfc_v);
		vertneibs[phfc_v].insert(nhfc_v);
	}

	smoother_.smooth(vertneibs, kSmoothingSteps);
	std::vector<Vec3d> smoothed_coords;
	mesh->getVertexPositions(smoothed_coords);
	setMeshCoords(mesh, original_coords);
	return smoothed_coords;
}

// set the input vector `coords` of coordinates as the mesh positions in the corner table
void SmoothingVisualizer::setMeshCoords(Mesh3DInterface* mesh, const std::vector<Vec3d>& coords) {
	size_t cur_count = 0;
	for (Mesh3DVertex* vert : mesh->ListVertices()) {
		Vec3d coord = coords[cur_count];
		vert->setCoords(coord);
		++cur_count;
	}
}
