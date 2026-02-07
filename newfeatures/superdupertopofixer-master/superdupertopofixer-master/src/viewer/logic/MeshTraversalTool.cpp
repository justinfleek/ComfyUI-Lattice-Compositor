#include "MeshTraversalTool.h"

#include <Eigen/Dense>
#include <iostream>

#include "include_glfw.h"
#include "scene/Scene.h"
#include "../utilities/string_util.h"

namespace sdtf::viewer::logic {
;

MeshTraversalTool::MeshTraversalTool(ViewerInterface* interface, scene::Scene* scene,
                                     scene::Node* node)
    : Tool(interface), scene_(scene), node_(node) {
	Eigen::Matrix3f v = Eigen::Matrix3f::Identity();
	selected_face_mesh_ = std::make_unique<gl::TriangleMesh>(v);

	selected_face_inst_ = scene_->addInstance(
	    std::make_unique<scene::OverlayMeshInstance>(selected_face_mesh_.get(), node_));
	selected_face_inst_->setColor(Eigen::Vector3f(1.f, 1.f, 1.f));
	selected_face_inst_->setPattern(scene::OverlayMeshInstance::DitheringPattern::Pattern1);
	selected_face_inst_->setVisible(false);

	selected_hc_mesh_ = std::make_unique<gl::TriangleMesh>(v);
	selected_hc_inst_ = scene_->addInstance(
	    std::make_unique<scene::OverlayMeshInstance>(selected_hc_mesh_.get(), node_));
	selected_hc_inst_->setColor(Eigen::Vector3f(1.f, 1.f, 1.f));
	selected_hc_inst_->setPatternFront(scene::OverlayMeshInstance::DitheringPattern::Pattern4);
	selected_hc_inst_->setPatternBack(scene::OverlayMeshInstance::DitheringPattern::Pattern3);
	selected_hc_inst_->setVisible(false);
}

void MeshTraversalTool::setMesh(const logic::LinearMesh3DView& mesh) {
	resetMesh();
	mesh_ = &mesh;
}
void MeshTraversalTool::resetMesh() {
	selectFace(-1);
	mesh_ = nullptr;
}

void MeshTraversalTool::clearSelection() { selectFace(-1); }

void MeshTraversalTool::selectFace(unsigned int fi) {
	if (fi == -1) {
		is_face_selected_ = false;
		selected_face_ = -1;
		selected_hc_ = -1;
		selected_hc_inst_->setVisible(false);
	} else {
		is_face_selected_ = true;
		selected_face_ = fi;
		auto t = mesh_->triangle(fi);
		auto verts = t->getVerts();
		Eigen::Matrix3Xd pos(3, 3);
		for (int i = 0; i < 3; i++) {
			pos.col(i) << verts[i]->getXCoord(), verts[i]->getYCoord(), verts[i]->getZCoord();
		}

		Eigen::Vector3d world_pos = interface_->scene()->activeCameraNode()->worldPosition();
		Eigen::Vector3d face_out_normal = (pos.col(1) - pos.col(0)).cross(pos.col(2) - pos.col(0));
		Eigen::Vector3d face_to_cam = world_pos - pos.col(0);
		bool seeing_front_face = face_out_normal.dot(face_to_cam) >= 0;

		auto hc = t->getHalfCorner();
		if (!seeing_front_face) {
			hc = hc->getDual();
		}
		selected_hc_ = mesh_->halfCornerIndex(hc);
	}

	updateStatusString();
	updateFaceMesh();
	updateHalfCornerMesh();
}

void MeshTraversalTool::updateFaceMesh() {
	if (is_face_selected_) {
		auto verts = mesh_->triangle(selected_face_)->getVerts();
		Eigen::Matrix3Xd pos(3, 3);
		for (int i = 0; i < 3; i++) {
			pos.col(i) << verts[i]->getXCoord(), verts[i]->getYCoord(), verts[i]->getZCoord();
		}
		selected_face_mesh_->setVertices(pos.cast<float>());
		selected_face_inst_->setVisible(true);
	} else {
		selected_face_inst_->setVisible(false);
	}
}

void MeshTraversalTool::updateHalfCornerMesh() {
	if (is_face_selected_) {
		auto hc = mesh_->halfCorner(selected_hc_);
		auto p0_3d = hc->getVertex()->getCoords();
		Eigen::Matrix3Xd pos(3, 3);
		pos.col(0) << p0_3d[0], p0_3d[1], p0_3d[2];
		std::array<Eigen::Vector3d, 2> to;
		std::array<double, 2> to_norms;
		for (int i = 0; i < 2; i++) {
			hc = hc->getNext();
			auto pi_3d = hc->getVertex()->getCoords();
			Eigen::Vector3d pi(pi_3d[0], pi_3d[1], pi_3d[2]);
			to[i] = (1. / 3.) * (pi - pos.col(0));
			to_norms[i] = to[i].norm();
		}
		if (to_norms[0] < to_norms[1]) {
			to[1] = to[1] * to_norms[0] / to_norms[1];
		} else {
			to[0] = to[0] * to_norms[1] / to_norms[0];
		}
		pos.col(1) = pos.col(0) + to[0];
		pos.col(2) = pos.col(0) + to[1];

		selected_hc_mesh_->setVertices(pos.cast<float>());
		selected_hc_inst_->setVisible(true);
	} else {
		selected_hc_inst_->setVisible(false);
	}
}

ToolResponse MeshTraversalTool::cursorCallback(logic::CursorEvent event) {
	return ToolResponse::None;
}
ToolResponse MeshTraversalTool::mouseButtonCallback(logic::MouseButtonEvent event) {
	if (!mesh_)
		return ToolResponse::None;

	if (event.button == GLFW_MOUSE_BUTTON_LEFT && event.action == GLFW_PRESS) {
		unsigned int face_index = interface_->cursorIndex();
		if (face_index >= mesh_->numTriangles())
			face_index = -1;
		selectFace(face_index);
		return ToolResponse::InstantAction;
	} else {
		return ToolResponse::None;
	}
}
ToolResponse MeshTraversalTool::scrollCallback(logic::ScrollEvent event) {
	return ToolResponse::None;
}
ToolResponse MeshTraversalTool::keyCallback(logic::KeyEvent event) {
	if (is_face_selected_) {
		if (event.action == GLFW_PRESS) {
			if (event.key == GLFW_KEY_PERIOD) {
				traverseNextHalfCorner();
				return ToolResponse::InstantAction;
			} else if (event.key == GLFW_KEY_COMMA) {
				traversePrevHalfCorner();
				return ToolResponse::InstantAction;
			} else if (event.key == GLFW_KEY_T) {
				traverseTwinHalfCorner();
				return ToolResponse::InstantAction;
			} else if (event.key == GLFW_KEY_O) {
				traverseOppositeHalfCorner();
				return ToolResponse::InstantAction;
			} else {
				return ToolResponse::None;
			}
		} else {
			return ToolResponse::None;
		}
	} else {
		return ToolResponse::None;
	}
}

void MeshTraversalTool::traverseNextHalfCorner() {
	auto hc = mesh_->halfCorner(selected_hc_);
	hc = hc->getNext();
	selected_hc_ = mesh_->halfCornerIndex(hc);
	updateStatusString();
	updateHalfCornerMesh();
}
void MeshTraversalTool::traversePrevHalfCorner() {
	auto hc = mesh_->halfCorner(selected_hc_);
	hc = hc->getPrev();
	selected_hc_ = mesh_->halfCornerIndex(hc);
	updateStatusString();
	updateHalfCornerMesh();
}
void MeshTraversalTool::traverseTwinHalfCorner() {
	auto hc = mesh_->halfCorner(selected_hc_);
	hc = hc->getDual();
	selected_hc_ = mesh_->halfCornerIndex(hc);
	updateStatusString();
	updateHalfCornerMesh();
}
void MeshTraversalTool::traverseOppositeHalfCorner() {
	auto hc = mesh_->halfCorner(selected_hc_);
	hc = hc->getOppos();
	selected_hc_ = mesh_->halfCornerIndex(hc);
	auto face = hc->getTri();
	selected_face_ = mesh_->triangleIndex(face);
	updateStatusString();
	updateFaceMesh();
	updateHalfCornerMesh();
}

void MeshTraversalTool::updateStatusString() {
	tool_status_string_ = "";
	if (is_face_selected_) {
		std::ostringstream oss;
		oss << "Mesh face: " << selected_face_ << std::endl;
		oss << "Mesh halfcorner: " << selected_hc_ << std::endl;
		auto v = mesh_->halfCorner(selected_hc_)->getVertex();
		auto vi = mesh_->vertexIndex(v);
		oss << "Mesh vertex: " << vi;
		tool_status_string_ = oss.str();
	}
}

ToolResponse MeshTraversalTool::commandCallback(logic::CommandEvent event)
{
	auto tokens = tokenize(event.command);

	if (tokens.empty() || (tokens.size() > 0 && tokens[0] != "sm"))
		return ToolResponse::None;

	std::string usage_string = "Usage of selection command: sm {v|h|f} id";
	if (tokens.size() != 3 || (tokens.size() > 1 && tokens[1] != "v" && tokens[1] != "h" &&
	                           tokens[1] != "f")) {
		command_response_ = usage_string;
		return ToolResponse::InstantAction;
	}

	long long sel_id = -1;
	try {
		sel_id = std::stol(tokens[2]);
	} catch (std::exception& e) {
		command_response_ = usage_string;
		return ToolResponse::InstantAction;
	}

	// Try to perform selection
	if (!mesh_) {
		command_response_ = "Mesh is not loaded. Cannot execute selection command.";
		return ToolResponse::InstantAction;
	}

	if (tokens[1] == "f")
	{
		if (sel_id < 0 || sel_id >= mesh_->numTriangles()) {
			command_response_ = "Face id is out of bounds.";
			return ToolResponse::InstantAction;
		}
		interface_->clearSelection();
		selectFace(sel_id);
		return ToolResponse::InstantAction;
	}
	else if (tokens[1] == "h")
	{
		if (sel_id < 0 || sel_id >= mesh_->numHalfCorners()) {
			command_response_ = "Half corner id is out of bounds.";
			return ToolResponse::InstantAction;
		}
		auto hc = mesh_->halfCorner(sel_id);
		auto fi = mesh_->triangleIndex(hc->getTri());
		interface_->clearSelection();
		selectFace(fi);
		selected_hc_ = sel_id;
		updateStatusString();
		updateHalfCornerMesh();
		return ToolResponse::InstantAction;
	}
	else if (tokens[1] == "v")
	{
		if (sel_id < 0 || sel_id >= mesh_->numVertices()) {
			command_response_ = "Vertex id is out of bounds.";
			return ToolResponse::InstantAction;
		}
		auto hc = mesh_->halfEdgeAtVertex(sel_id);
		auto fi = mesh_->triangleIndex(hc->getTri());
		interface_->clearSelection();
		selectFace(fi);
		selected_hc_ = mesh_->halfCornerIndex(hc);
		updateStatusString();
		updateHalfCornerMesh();
		return ToolResponse::InstantAction;
	}

	return ToolResponse::None;
}

bool MeshTraversalTool::isActive() const { return false; }

}  // namespace sdtf::viewer::logic