#pragma once

#include "gl/TriangleMesh.h"
#include "scene/Node.h"

// A triangle mesh rendered with dithering.
// Used to highlight parts of the scene, e.g., mesh/grid elements selected by the user
// Can set separate dithering patterns for front and back faces
// Default polygon offset is such it is drawn in front of TriangleMeshInstances with default polygon offset.

namespace sdtf::viewer::scene {
;

class OverlayMeshInstance {
 public:
	OverlayMeshInstance(gl::TriangleMesh* mesh, Node* node);

	// 0 = 50% dithering
	// 1 = 25% dithering
	// 2 = vertical lines
	// 3 = horizontal lines
	// 4 = fully filled
	enum class DitheringPattern : int { Pattern0, Pattern1, Pattern2, Pattern3, Pattern4 };

	const auto node() const { return node_; }
	auto node() { return node_; }

	const auto mesh() const { return mesh_; }
	auto mesh() { return mesh_; }

	void setColor(const Eigen::Vector3f& color) { color_ = color; }
	const auto& color() const { return color_; }

	void setPattern(DitheringPattern pattern) {
		pattern_front_ = pattern;
		pattern_back_ = pattern;
	}
	auto pattern() const { return pattern_front_; }

	void setPatternFront(DitheringPattern pattern) { pattern_front_ = pattern; }
	auto patternFront() const { return pattern_front_; }

	void setPatternBack(DitheringPattern pattern) { pattern_back_ = pattern; }
	auto patternBack() const { return pattern_back_; }

	void setVisible(bool visible) { visible_ = visible; }
	const bool visible() const { return visible_; }

	void setPolygonOffset(float factor, float units) { polygon_offset_ << factor, units; }
	void setPolygonOffset(Eigen::Vector2f offset) { polygon_offset_ = offset; }
	auto polygonOffset() const { return polygon_offset_; }

 private:
	gl::TriangleMesh* mesh_;
	Node* node_;
	bool visible_ = true;
	Eigen::Vector2f polygon_offset_ = Eigen::Vector2f(-1.f, -1.f);

	Eigen::Vector3f color_ = Eigen::Vector3f(0.f, 0.f, 0.f);
	DitheringPattern pattern_front_ = DitheringPattern::Pattern0;
	DitheringPattern pattern_back_ = DitheringPattern::Pattern0;
};

}  // namespace sdtf::viewer::scene