#pragma once

#include <Eigen/Core>

#include "Tool.h"
#include "datastructures/Grid3DInterface.h"
#include "scene/OverlayMeshInstance.h"
#include "scene/Scene.h"

// Tool for selecting and traversing grid elements
// Allows the user to select a face in the boundary of the complex cell region with the LMB.
// The keys 1-4 can be used to convert the currently selected grid element to a
// vertex/edge/face/cell selection. Repeatedly pressing the key 2 or 3 cycles through edges/faces
// aligned with the different coordinate axes. The keys X,Y,Z will translate the current selection
// along the specific axis; Holding down Shift will translate it in the negative direction.
// Reacts to command line commands "sg {v|e|f|c} id" to change the current selection

namespace sdtf::viewer::logic {
;

class GridTraversalTool : public Tool {
 public:
	GridTraversalTool(ViewerInterface* interface, scene::Scene* scene, scene::Node* node);
	void setGrid(const Grid3DInterface& grid, std::vector<long long>&& face_ids,
	             unsigned int index_offset);
	void resetGrid();
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
	void initColors();

	enum class SelectionMode { None, Face, Edge, Vertex, Cell };
	void setSelection(long long id, SelectionMode mode);
	void updateStatusString();

	void addFaceToVisualization(const Eigen::Vector<long long, 4>& coords,
	                            scene::OverlayMeshInstance::DitheringPattern pattern,
	                            const Eigen::Vector3f& color);
	bool getFaceOrientation(const Eigen::Vector<long long, 4>& coords, Eigen::Vector3d* position,
	                        Eigen::Matrix3d* frame) const;

	void addEdgeGridToVisualization(const Eigen::Vector<long long, 3>& p,
	                                const Eigen::Vector<long long, 3>& sz,
	                                scene::OverlayMeshInstance::DitheringPattern pattern,
	                                const Eigen::Vector3f& color);
	void addEdgeToVisualization(const Eigen::Vector<long long, 4>& coords,
	                            scene::OverlayMeshInstance::DitheringPattern pattern,
	                            const Eigen::Vector3f& color);
	bool getEdgeOrientation(const Eigen::Vector<long long, 4>& coords, Eigen::Vector3d* position,
	                        Eigen::Matrix3d* frame) const;

	void addVertexToVisualization(const Eigen::Vector<long long, 3>& coords,
	                              scene::OverlayMeshInstance::DitheringPattern pattern,
	                              const Eigen::Vector3f& color);

	const Grid3DInterface* grid_ = nullptr;
	std::vector<long long> complex_face_ids_;
	unsigned int index_offset_ = 0;

	scene::Node* root_node_;
	scene::Scene* scene_;

	std::unique_ptr<gl::TriangleMesh> selected_face_mesh_ = nullptr;
	std::unique_ptr<gl::TriangleMesh> selected_edge_mesh_ = nullptr;
	std::unique_ptr<gl::TriangleMesh> selected_vertex_mesh_ = nullptr;
	std::vector<scene::OverlayMeshInstance*> selection_inst_;
	std::vector<scene::Node*> nodes_;

	SelectionMode selection_mode_ = SelectionMode::None;
	long long selected_id_ = -1;

	std::array<Eigen::Vector3f, 2> selection_colors_;

	std::string command_response_ = "";
	std::string tool_status_string_ = "";
};

}  // namespace sdtf::viewer::logic