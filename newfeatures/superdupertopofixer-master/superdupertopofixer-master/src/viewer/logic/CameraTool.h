#pragma once

#include <Eigen/Core>

#include "Tool.h"
#include "scene/Node.h"
#include "scene/cameras.h"
#include "tool_settings.h"

// Tool to allow the user to control a camera by:
// Drag MMB: Orbit camera
// Shift + Drag MMB : Pan camera
// Shift + Ctrl + Drag MMB : Dolly camera
// Mouse wheel : zoom
// Key R: Reset to default camera location

namespace sdtf::viewer::logic {
;

class CameraTool : public Tool {
 public:
	CameraTool(ViewerInterface* interface, scene::Node* node, scene::Camera* camera);

	virtual ToolResponse cursorCallback(logic::CursorEvent event) override;
	virtual ToolResponse mouseButtonCallback(logic::MouseButtonEvent event) override;
	virtual ToolResponse scrollCallback(logic::ScrollEvent event) override;
	virtual ToolResponse keyCallback(logic::KeyEvent event) override;

	virtual bool isActive() const override;

	// Sets the scene node to which the camera is attached. All operations of reading/writing
	// the position or orientiation of this node are done within the local coordinate system of
	// this node. To ensure intuitive control over the camera, this node should be a direct child
	// of the root node of the scene.
	void setNode(scene::Node* node) { node_ = node; }

 private:
	CameraToolSettings settings_;

	scene::Node* node_;
	scene::Camera* camera_;

	enum class Action { None, Orbit, Pan, Dolly };
	Action action_ = Action::None;

	Eigen::Vector2d cursor_initial_ = Eigen::Vector2d(0.0, 0.0);
	Eigen::Vector3d world_target_ = Eigen::Vector3d(0.5,0.5,0.5);
	Eigen::Vector3d node_position_initial_;
	Eigen::Matrix3d node_frame_initial_;
	Eigen::Matrix2d pan_frame_;
	Eigen::Vector3d dolly_velocity_;
};

}  // namespace sdtf::viewer::logic