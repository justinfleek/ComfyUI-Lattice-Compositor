#pragma once

#include <Eigen/Core>

#include "Tool.h"
#include "logic/LinearMesh3DView.h"
#include "scene/Scene.h"
#include "scene/Node.h"
#include "scene/OverlayMeshInstance.h"

// Tool to select TopoFixer mesh elements (faces and halfcorners), and traverse the halfcorner datastructure.
// Use the keys . and , to select the next/previous halfcorner. Key T for twin, and key O for opposite halfcorner.
// The LMB can be used to select a mesh face in the scene. If the selected half-corner appeares with a striped dithering
// pattern in the scene, then it is currently being viewed from the back.
// Responds to the command line command "sm {v|h|f} id" to change the current selection.

namespace sdtf::viewer::logic {
;

class MeshTraversalTool : public Tool {
 public:
	MeshTraversalTool(ViewerInterface* interface, scene::Scene* scene, scene::Node* node);
	void setMesh(const logic::LinearMesh3DView& mesh);
	void resetMesh();
	void clearSelection();

	virtual ToolResponse cursorCallback(logic::CursorEvent event) override;
	virtual ToolResponse mouseButtonCallback(logic::MouseButtonEvent event) override;
	virtual ToolResponse scrollCallback(logic::ScrollEvent event) override;
	virtual ToolResponse keyCallback(logic::KeyEvent event) override;
	virtual ToolResponse commandCallback(logic::CommandEvent event) override;
	virtual void getCommandStatus(std::string* response) const override {
		*response = command_response_;
	}

	virtual const std::string& getToolStatus() const override { return tool_status_string_; }

	virtual bool isActive() const override;

 private:
	void selectFace(unsigned int fi);
	void updateFaceMesh();
	void updateHalfCornerMesh();
	void updateStatusString();
	
	void traverseNextHalfCorner();
	void traversePrevHalfCorner();
	void traverseTwinHalfCorner();
	void traverseOppositeHalfCorner();

	const logic::LinearMesh3DView* mesh_ = nullptr;
	scene::Node* node_;
	scene::Scene* scene_;

	std::unique_ptr<gl::TriangleMesh> selected_face_mesh_ = nullptr;
	scene::OverlayMeshInstance* selected_face_inst_ = nullptr;

	std::unique_ptr<gl::TriangleMesh> selected_hc_mesh_ = nullptr;
	scene::OverlayMeshInstance* selected_hc_inst_ = nullptr;

	bool is_face_selected_ = false;
	unsigned int selected_face_ = -1;
	unsigned int selected_hc_ = -1;
	std::string tool_status_string_ = "";
	std::string command_response_ = "";
};

}  // namespace sdtf::viewer::logic