#pragma once

#include "gl/LineMesh.h"
#include "scene/Node.h"

// A scene element that points to a gl::LineMesh (the mesh data on the GPU) and a scene node (the
// position and orientation of the instance). Contains rendering options such as color, line width
// etc. Add this to the scene in order for the line mesh instance to be drawn by the renderer.

namespace sdtf::viewer::scene {
;

class LineMeshInstance {
 public:
	LineMeshInstance(gl::LineMesh* mesh, Node* node);

	const auto node() const { return node_; }
	auto node() { return node_; }

	const auto mesh() const { return mesh_; }
	auto mesh() { return mesh_; }

	void setColor(const Eigen::Vector3f& color) { color_ = color; }
	const auto& color() const { return color_; }

	void setLineWidth(float lw) { line_width_ = lw; }
	float lineWidth() const { return line_width_; }

	void setVisible(bool visible) { visible_ = visible; }
	bool visible() const { return visible_; }

	void setClippable(bool clippable) { clippable_ = clippable; }
	bool clippable() const { return clippable_; }

	// void setID(int id) { id_ = id; }
	// int id() const { return id_; }

 private:
	gl::LineMesh* mesh_;
	Node* node_;
	// Eigen::Vector3d color_ = Eigen::Vector3d::Zero();
	bool visible_ = true;
	bool clippable_ = true;
	// int id_ = 0;

	Eigen::Vector3f color_ = Eigen::Vector3f(0.f, 0.f, 0.f);
	float line_width_ = 1.0;
};

}  // namespace sdtf::viewer::scene