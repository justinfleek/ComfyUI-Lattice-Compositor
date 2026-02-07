#include "VisualizationTool.h"

#include <Eigen/Dense>
#include <iostream>

#include "include_glfw.h"
#include "scene/Scene.h"

namespace sdtf::viewer::logic {
;

VisualizationTool::VisualizationTool(ViewerInterface* interface, Renderer* renderer)
    : Tool(interface), renderer_(renderer) {}

ToolResponse VisualizationTool::cursorCallback(logic::CursorEvent event) {
	if (action_ == Action::EditClippingPlane) {
		updateClippingPlanePosition(event.ypos);
		updateRendererClippingPlane();
	}
	return ToolResponse::None;
}

void VisualizationTool::updateClippingPlanePosition(double cursor_y_pos) {
	double mouse_rel = (cursor_initial_[1] - cursor_y_pos) / interface_->contentScale();
	double displ = mouse_rel * settings_.clipping_plane_speed * interface_->sceneDiameter();
	clip_current_.point = world_target_ + displ * clip_current_.direction;
}

double VisualizationTool::initialCursorY(double current_cursor_y) {
	double displ = (clip_initial_.point - world_target_).dot(clip_initial_.direction);
	double mouse_rel = displ / (settings_.clipping_plane_speed * interface_->sceneDiameter());
	return current_cursor_y + mouse_rel * interface_->contentScale();
}

ToolResponse VisualizationTool::mouseButtonCallback(logic::MouseButtonEvent event) {
	if (event.action == GLFW_PRESS && action_ == Action::EditClippingPlane) {
		if (event.button == GLFW_MOUSE_BUTTON_LEFT) {
			action_ = Action::None;
			return ToolResponse::Deactivate;
		} else if (event.button == GLFW_MOUSE_BUTTON_RIGHT) {
			clip_current_.active = false;
			updateRendererClippingPlane();
			action_ = Action::None;
			return ToolResponse::Deactivate;
		}
	}
	return ToolResponse::None;
}
ToolResponse VisualizationTool::scrollCallback(logic::ScrollEvent event) {
	return ToolResponse::None;
}
ToolResponse VisualizationTool::keyCallback(logic::KeyEvent event) {
	if (event.action != GLFW_PRESS)
		return ToolResponse::None;

	if (event.key == GLFW_KEY_M) {
		mesh_state_ = static_cast<MeshState>((static_cast<int>(mesh_state_) + 1) % 4);
		updateMeshVisualization();
		return ToolResponse::InstantAction;
	} else if (event.key == GLFW_KEY_G) {
		grid_state_ = static_cast<GridState>((static_cast<int>(grid_state_) + 1) % 4);
		updateComplexGridVisualization();
		return ToolResponse::InstantAction;
	} else if (event.key == GLFW_KEY_C && action_ == Action::None) {
		if (!interface_->cursorPixelPosition(&cursor_initial_))
			return ToolResponse::None;

		bool cursor_valid = interface_->cursorWorldPosition(&world_target_);
		if (!cursor_valid) {
			world_target_ = interface_->sceneCenter();
		}

		if (clip_current_.active) {
			// Start moving existing plane
			clip_initial_ = clip_current_;
			cursor_initial_[1] = initialCursorY(cursor_initial_[1]);
			last_direction_key_ = -1;
		} else {
			clip_initial_.active = false;

			// Put plane in cam direction and start moving
			clip_current_.point = world_target_;
			clip_current_.direction = -interface_->scene()->activeCameraNode()->worldFrame().col(2);
			clip_current_.active = true;
			clip_current_.flipped = false;
			last_direction_key_ = GLFW_KEY_C;
		}
		updateRendererClippingPlane();
		action_ = Action::EditClippingPlane;
		return ToolResponse::Activate;
	} else if (action_ == Action::EditClippingPlane) {
		if (event.key == GLFW_KEY_X || event.key == GLFW_KEY_Y || event.key == GLFW_KEY_Z ||
		    event.key == GLFW_KEY_C) {
			if (event.key == last_direction_key_) {
				clip_current_.flipped = !clip_current_.flipped;
			} else {
				interface_->cursorPixelPosition(&cursor_initial_);
				last_direction_key_ = event.key;
				if (event.key == GLFW_KEY_X) {
					clip_current_.direction = Eigen::Vector3d(1., 0., 0.);
				} else if (event.key == GLFW_KEY_Y) {
					clip_current_.direction = Eigen::Vector3d(0., 1., 0.);
				} else if (event.key == GLFW_KEY_Z) {
					clip_current_.direction = Eigen::Vector3d(0., 0., 1.);
				} else if (event.key == GLFW_KEY_C) {
					clip_current_.direction = -interface_->scene()->activeCameraNode()->worldFrame().col(2);
				}
			}
			updateClippingPlanePosition(cursor_initial_[1]);
			updateRendererClippingPlane();
			return ToolResponse::None;
		} else if (event.key == GLFW_KEY_F) {
			clip_current_.flipped = !clip_current_.flipped;
			updateRendererClippingPlane();
			return ToolResponse::None;
		} else if (event.key == GLFW_KEY_ENTER) {
			action_ = Action::None;
			return ToolResponse::Deactivate;
		} else if (event.key == GLFW_KEY_ESCAPE) {
			clip_current_ = clip_initial_;
			updateRendererClippingPlane();
			action_ = Action::None;
			return ToolResponse::Deactivate;
		} else if (event.key == GLFW_KEY_DELETE) {
			clip_current_.active = false;
			updateRendererClippingPlane();
			action_ = Action::None;
			return ToolResponse::Deactivate;
		}
	}
	return ToolResponse::None;
}

void VisualizationTool::setMeshes(scene::TriangleMeshInstance* tri_mesh,
                                  scene::LineMeshInstance* line_mesh) {
	resetMeshes();
	tri_mesh_ = tri_mesh;
	line_mesh_ = line_mesh;
	updateMeshVisualization();
}
void VisualizationTool::resetMeshes() {
	tri_mesh_ = nullptr;
	line_mesh_ = nullptr;
	mesh_state_ = MeshState::All;
	clip_current_ = ClippingPlane();
	clip_initial_ = ClippingPlane();
	updateRendererClippingPlane();
}

void VisualizationTool::updateMeshVisualization() {
	if (!tri_mesh_)
		return;

	tri_mesh_->setVisible(mesh_state_ == MeshState::All || mesh_state_ == MeshState::TrianglesOnly);
	line_mesh_->setVisible(mesh_state_ == MeshState::All || mesh_state_ == MeshState::LinesOnly);

	bool use_offset = (mesh_state_ == MeshState::All);
	tri_mesh_->setPolygonOffset(use_offset ? Eigen::Vector2f(1.f, 1.f) : Eigen::Vector2f(0.f, 0.f));
}

void VisualizationTool::setComplexGridMeshes(scene::TriangleMeshInstance* tri_mesh,
                                             scene::LineMeshInstance* line_mesh) {
	complex_grid_mesh_ = tri_mesh;
	complex_grid_line_mesh_ = line_mesh;
	updateComplexGridVisualization();
}
void VisualizationTool::resetComplexGridMeshes() {
	complex_grid_mesh_ = nullptr;
	complex_grid_line_mesh_ = nullptr;
	grid_state_ = GridState::None;
}


const VisualizationTool::ClippingPlane&
VisualizationTool::getClippingPlane() const {
        return clip_current_;
}

void VisualizationTool::setClippingPlane(const ClippingPlane &plane) {
        clip_current_ = plane;
        updateRendererClippingPlane();
}


void VisualizationTool::updateComplexGridVisualization() {
	if (!complex_grid_mesh_)
		return;

	complex_grid_mesh_->setVisible(grid_state_ == GridState::All ||
	                               grid_state_ == GridState::TrianglesOnly);
	complex_grid_line_mesh_->setVisible(grid_state_ == GridState::All ||
	                                    grid_state_ == GridState::LinesOnly);
}

void VisualizationTool::updateRendererClippingPlane() {
	if (clip_current_.active) {
		renderer_->setClippingPlane(clip_current_.point, clip_current_.flipped
		                                                     ? -clip_current_.direction
		                                                     : clip_current_.direction);
	} else {
		renderer_->resetClippingPlane();
	}
}

bool VisualizationTool::isActive() const { return false; }

}  // namespace sdtf::viewer::logic
