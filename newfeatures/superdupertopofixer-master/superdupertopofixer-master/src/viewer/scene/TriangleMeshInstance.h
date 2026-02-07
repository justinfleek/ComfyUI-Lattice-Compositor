#pragma once

#include "gl/TriangleMesh.h"
#include "scene/Node.h"

// A scene element that points to a gl::TriangleMesh (the mesh data on the GPU) and a scene node
// (the position and orientation of the instance). Contains rendering options such as color, and
// camera lighting etc. Add this to the scene in order for the triangle mesh instance to be drawn by
// the renderer.

namespace sdtf::viewer::scene {
;

class TriangleMeshInstance {
 public:
	TriangleMeshInstance(gl::TriangleMesh* mesh, Node* node);

	const auto node() const { return node_; }
	auto node() { return node_; }

	const auto mesh() const { return mesh_; }
	auto mesh() { return mesh_; }

	// Set color of front and back faces
	void setFrontColor(const Eigen::Vector3f& color) { front_color_ = color; }
	const auto& frontColor() const { return front_color_; }
	void setBackColor(const Eigen::Vector3f& color) { back_color_ = color; }
	const auto& backColor() const { return back_color_; }

	// The angle attenuation controls how much the color is darkened for faces that are viewed at an
	// angle. Mimics a light sources places at the camera's location.
	void setAngleAttenuation(float angle_attenuation) { angle_attenuation_ = angle_attenuation; }
	auto angleAttenuation() const { return angle_attenuation_; }

	void setVisible(bool visible) { visible_ = visible; }
	bool visible() const { return visible_; }

	void setClippable(bool clippable) { clippable_ = clippable; }
	bool clippable() const { return clippable_; }

	void setPolygonOffset(float factor, float units) { polygon_offset_ << factor, units; }
	void setPolygonOffset(Eigen::Vector2f offset) { polygon_offset_ = offset; }
	auto polygonOffset() const { return polygon_offset_; }

	// void setDoubleSided(bool double_sided) { double_sided_ = double_sided; }
	// const bool doubleSided() const { return double_sided_; }

	// void setID(int id) { id_ = id; }
	// int id() const { return id_; }

 private:
	gl::TriangleMesh* mesh_;
	Node* node_;
	// Eigen::Vector3d color_ = Eigen::Vector3d::Zero();
	// double shininess_ = 10.;
	bool visible_ = true;
	bool clippable_ = true;
	Eigen::Vector2f polygon_offset_ = Eigen::Vector2f(0.f, 0.f);
	// bool double_sided_ = false;
	// int id_ = 0;

	Eigen::Vector3f front_color_ = Eigen::Vector3f(0.f, 0.f, 0.f);
	Eigen::Vector3f back_color_ = Eigen::Vector3f(0.f, 0.f, 0.f);
	float angle_attenuation_ = 0.f;
};

}  // namespace sdtf::viewer::scene