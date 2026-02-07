#pragma once

#include <Eigen/Core>

#include "Renderer.h"
#include "Tool.h"
#include "scene/LineMeshInstance.h"
#include "scene/TriangleMeshInstance.h"
#include "tool_settings.h"

// Tool for cycling through mesh and grid visualization modes.
// Keys M and G for cycling through mesh/grid visualization modes: Show all, triangles-only, lines-only, none
// Note that selecting elements with the LMB will only work if the triangles are shown.

namespace sdtf::viewer::logic {
;

class VisualizationTool : public Tool {
 public:
	VisualizationTool(ViewerInterface* interface, Renderer* renderer);

	virtual ToolResponse cursorCallback(logic::CursorEvent event) override;
	virtual ToolResponse mouseButtonCallback(logic::MouseButtonEvent event) override;
	virtual ToolResponse scrollCallback(logic::ScrollEvent event) override;
	virtual ToolResponse keyCallback(logic::KeyEvent event) override;

	virtual bool isActive() const override;

	void setMeshes(scene::TriangleMeshInstance* tri_mesh, scene::LineMeshInstance* line_mesh);
	void resetMeshes();

	void setComplexGridMeshes(scene::TriangleMeshInstance* tri_mesh,
	                          scene::LineMeshInstance* line_mesh);
	void resetComplexGridMeshes();

	struct ClippingPlane {
        private:
		Eigen::Vector3d point = Eigen::Vector3d(0., 0., 0.);
		Eigen::Vector3d direction = Eigen::Vector3d(1., 0., 0.);
		bool active = false;
		bool flipped = false;
                friend class VisualizationTool;
	};
    
        const ClippingPlane& getClippingPlane() const;
        void setClippingPlane(const ClippingPlane &plane);
    
 private:
	void updateClippingPlanePosition(double cursor_y_pos);
	double initialCursorY(double current_cursor_y);

	void updateMeshVisualization();
	void updateComplexGridVisualization();
	void updateRendererClippingPlane();

	VisualizationToolSettings settings_;

	enum class Action { None, EditClippingPlane };
	Action action_ = Action::None;

	Eigen::Vector2d cursor_initial_ = Eigen::Vector2d(0.0, 0.0);
	Eigen::Vector3d world_target_ = Eigen::Vector3d(0.5, 0.5, 0.5);
	unsigned int last_direction_key_ = -1;

	ClippingPlane clip_current_;
	ClippingPlane clip_initial_;

	enum class MeshState : int { All = 0, TrianglesOnly = 1, LinesOnly = 2, None = 3 };
	MeshState mesh_state_ = MeshState::All;
	Renderer* renderer_ = nullptr;

	scene::TriangleMeshInstance* tri_mesh_ = nullptr;
	scene::LineMeshInstance* line_mesh_ = nullptr;

	enum class GridState : int { All = 0, TrianglesOnly = 1, LinesOnly = 2, None = 3 };
	GridState grid_state_ = GridState::None;

	scene::TriangleMeshInstance* complex_grid_mesh_ = nullptr;
	scene::LineMeshInstance* complex_grid_line_mesh_ = nullptr;
};

}  // namespace sdtf::viewer::logic
