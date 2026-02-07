#include "CameraTool.h"

#include <Eigen/Dense>
#include <iostream>

#include "include_glfw.h"
#include "scene/Scene.h"

namespace sdtf::viewer::logic {
;

CameraTool::CameraTool(ViewerInterface* interface, scene::Node* node, scene::Camera* camera)
    : Tool(interface), node_(node), camera_(camera) {}

ToolResponse CameraTool::cursorCallback(logic::CursorEvent event) {
	if (action_ == Action::Orbit) {
		// Orbiting moves the camera around a target point in world space while adjusting the rotation
		// so this target point stays constant in screen space.
		Eigen::Vector2d rel_pos =
		    (Eigen::Vector2d(event.xpos, event.ypos) - cursor_initial_) / interface_->contentScale();

		// Pitch = looking up and down
		double pitch = -rel_pos(1) * settings_.orbit_pitch_speed;
		// Yaw = looking left and right
		double yaw = -rel_pos(0) * settings_.orbit_yaw_speed;
		double cp = cos(pitch);
		double sp = sin(pitch);
		double cy = cos(yaw);
		double sy = sin(yaw);

		Eigen::Matrix3d pitch_rotation;
		pitch_rotation << 1.0, 0.0, 0.0, 0.0, cp, -sp, 0.0, sp, cp;
		Eigen::Matrix3d yaw_rotation;
		yaw_rotation << cy, -sy, 0., sy, cy, 0., 0., 0., 1.;

		Eigen::Matrix3d new_frame = yaw_rotation * node_frame_initial_ * pitch_rotation;
		Eigen::Vector3d new_position =
		    world_target_ +
		    new_frame * (node_frame_initial_.transpose() * (node_position_initial_ - world_target_));

		node_->setFrame(new_frame);
		node_->setPosition(new_position);
	} else if (action_ == Action::Pan) {
		// Panning translates the camera in the plane normal to the view vector, without rotating it
		Eigen::Vector2d rel_pos = Eigen::Vector2d(event.xpos, event.ypos) - cursor_initial_;
		Eigen::Vector2d delta_z = 2 * Eigen::Vector2d(rel_pos(0) / interface_->canvasWidth(),
		                                              -rel_pos(1) / interface_->canvasHeight());
		Eigen::Vector2d delta_lambda = pan_frame_ * delta_z;
		Eigen::Vector3d new_position =
		    node_position_initial_ - node_frame_initial_.template block<3, 2>(0, 0) * delta_lambda;

		node_->setPosition(new_position);
	} else if (action_ == Action::Dolly) {
		// Dollying physically translates the camera along the view vector without rotating it
		double displ = (event.ypos - cursor_initial_(1)) / interface_->contentScale();
		Eigen::Vector3d new_position =
		    node_position_initial_ + settings_.dolly_speed_ * displ * dolly_velocity_;
		node_->setPosition(new_position);
	}
	return ToolResponse::None;
}
ToolResponse CameraTool::mouseButtonCallback(logic::MouseButtonEvent event) {
	if (action_ == Action::None && event.action == GLFW_PRESS) {
		if (event.button == GLFW_MOUSE_BUTTON_MIDDLE) {
			if (event.mods & GLFW_MOD_SHIFT) {
				if (event.mods & GLFW_MOD_CONTROL)
					action_ = Action::Dolly;
				else
					action_ = Action::Pan;
			} else {
				action_ = Action::Orbit;
			}

			cursor_initial_ << event.xpos, event.ypos;
			node_position_initial_ = node_->position();
			node_frame_initial_ = node_->frame();

			Eigen::Vector3d cursor_world_pos;
			if (interface_->cursorWorldPosition(&cursor_world_pos))
				world_target_ = cursor_world_pos;

			if (action_ == Action::Pan) {
				Eigen::Matrix4d vp_matrix;
				interface_->scene()->computeViewProjectionMatrix(&vp_matrix);
				Eigen::Matrix<double, 3, 2> F = node_frame_initial_.template block<3, 2>(0, 0);
				Eigen::Matrix<double, 2, 2> M = vp_matrix.template block<2, 3>(0, 0) * F;
				Eigen::Matrix<double, 1, 2> m = vp_matrix.template block<1, 3>(3, 0) * F;

				Eigen::Vector4d world_target_hom;
				world_target_hom << world_target_, 1.0;
				Eigen::Vector4d proj_target = vp_matrix * world_target_hom;
				Eigen::Vector2d y = proj_target.template block<2, 1>(0, 0);
				double w = proj_target(3);
				Eigen::Matrix2d A = (M * w - y * m) / (w * w);
				pan_frame_ = A.inverse();  // This matrix converts an xy-movement in normalized device
				                           // coordinates to a movement of the point below the cursor in the
				                           // frame spanned by the x- and y-axes of the cameraa
			} else if (action_ == Action::Dolly) {
				Eigen::Vector3d forward = node_->frame().col(2);
				Eigen::Vector3d to = world_target_ - node_->position();
				dolly_velocity_ = to.dot(forward) * forward;
			}

			return ToolResponse::Activate;
		}
	}

	if (action_ != Action::None && event.action == GLFW_RELEASE) {
		if ((action_ == Action::Orbit || action_ == Action::Pan || action_ == Action::Dolly) &&
		    event.button == GLFW_MOUSE_BUTTON_MIDDLE) {
			action_ = Action::None;
			return ToolResponse::Deactivate;
		}
	}

	return ToolResponse::None;
}
ToolResponse CameraTool::scrollCallback(logic::ScrollEvent event) {
	if (action_ == Action::None) {
		// Zooming changes the opening angle of the camera. This causes a uniform
		// scale in screen space without distorting the image.
		double old_zoom = camera_->zoom();
		double factor = std::pow(1. - settings_.zoom_scroll_interval, event.yoffset);
		double new_zoom = std::min(1.0, old_zoom * factor);
		camera_->setZoom(new_zoom);
		return ToolResponse::InstantAction;
	}
	return ToolResponse::None;
}
ToolResponse CameraTool::keyCallback(logic::KeyEvent event) {
	if (event.key == GLFW_KEY_R) {
		// Reset camera to default position
		Eigen::Vector3d pos;
		Eigen::Matrix3d frame;
		interface_->getDefaultCameraLocation(&pos, &frame);
		node_->setPosition(pos);
		node_->setFrame(frame);
		return ToolResponse::InstantAction;
	} else
		return ToolResponse::None;
}

bool CameraTool::isActive() const { return action_ != Action::None; }

}  // namespace sdtf::viewer::logic