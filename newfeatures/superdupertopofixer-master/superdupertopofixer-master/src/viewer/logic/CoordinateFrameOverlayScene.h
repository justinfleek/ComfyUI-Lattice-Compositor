#pragma once

#include "scene/Scene.h"
#include "scene/TriangleMeshInstance.h"

// A scene used to display a small coordinate frame in the corner of the application. Contains three
// colored arrows for the coordinate axes, and a camera.

namespace sdtf::viewer::logic {
;

class CoordinateFrameOverlayScene {
 public:
	CoordinateFrameOverlayScene();

	// Call this function to set the camera orientation in this scene, so it mirrors the active camera node other_node.
	void mimicCamera(const scene::Node* other_node);
	void updateWorldTransform() { scene_->updateWorldTransform(); }

	scene::Camera* camera() { return camera_; }
	const scene::Camera* camera() const { return camera_; }

	scene::Node* cameraNode() { return camera_node_; }
	const scene::Node* cameraNode() const { return camera_node_; }

	scene::Scene* scene() { return scene_.get(); }
	const scene::Scene* scene() const { return scene_.get(); }

 private:
	void initColors();

	// Geometric primitives to draw the coordinate system
	std::unique_ptr<gl::TriangleMesh> cylinder_, cone_;
	std::array<scene::TriangleMeshInstance*, 3> cylinder_inst_;
	std::array<scene::TriangleMeshInstance*, 3> cone_inst_;
	std::unique_ptr<gl::TriangleMesh> box_;
	scene::TriangleMeshInstance* box_inst_;

	// Simple scene to build the coordinate system arroves
	std::unique_ptr<scene::Scene> scene_;
	std::array<scene::Node*, 3> arrow_nodes_;
	scene::Node* box_node_;
	scene::Node* camera_node_;
	scene::Camera* camera_;

	std::array<Eigen::Vector3f, 3> colors_;
};

}  // namespace sdtf::viewer::logic