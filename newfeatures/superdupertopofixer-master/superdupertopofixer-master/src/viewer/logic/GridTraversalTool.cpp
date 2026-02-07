#include "GridTraversalTool.h"

#include <Eigen/Dense>
#include <iostream>

#include "../utilities/string_util.h"
#include "geom/Primitives.h"
#include "include_glfw.h"
#include "scene/Scene.h"

namespace sdtf::viewer::logic {
;

using DitheringPattern = scene::OverlayMeshInstance::DitheringPattern;

GridTraversalTool::GridTraversalTool(ViewerInterface* interface, scene::Scene* scene,
                                     scene::Node* node)
    : Tool(interface), scene_(scene), root_node_(node) {
	initColors();

	Eigen::Matrix3Xf v = Eigen::Matrix3Xf::Zero(3, 4);
	Eigen::Matrix<GLuint, 3, -1> i(3, 2);
	i << 0, 2, 1, 1, 2, 3;
	selected_face_mesh_ = std::make_unique<gl::TriangleMesh>(v, i);

	auto cube_mesh = geom::MeshPrimitives<float>::getUnitCubeIndexed(true, true);
	selected_edge_mesh_ = std::make_unique<gl::TriangleMesh>(cube_mesh.vertices, cube_mesh.triangles);
	selected_vertex_mesh_ =
	    std::make_unique<gl::TriangleMesh>(cube_mesh.vertices, cube_mesh.triangles);
}

void GridTraversalTool::setGrid(const Grid3DInterface& grid, std::vector<long long>&& face_ids,
                                unsigned int index_offset) {
	grid_ = &grid;
	complex_face_ids_ = std::move(face_ids);
	index_offset_ = index_offset;

	float cell_dx = static_cast<float>(grid_->get_cell_dx());
	Eigen::Matrix3Xf v = Eigen::Matrix3Xf::Zero(3, 4);
	v.col(1) << cell_dx, 0.f, 0.f;
	v.col(2) << 0.f, cell_dx, 0.f;
	v.col(3) << cell_dx, cell_dx, 0.f;
	selected_face_mesh_->setVertices(v);

	float hw = 0.03f * cell_dx;
	auto edge_mesh = geom::MeshPrimitives<float>::getCubeIndexed(
	    Eigen::Vector3f::Constant(-hw), Eigen::Vector3f(hw, hw, cell_dx + hw), true);
	selected_edge_mesh_->setVertices(edge_mesh.vertices);

	auto vertex_mesh = geom::MeshPrimitives<float>::getCubeIndexed(
	    Eigen::Vector3f::Constant(-hw * 2.5f), Eigen::Vector3f::Constant(hw * 2.5f), true);
	selected_vertex_mesh_->setVertices(vertex_mesh.vertices);
}

void GridTraversalTool::resetGrid() {
	setSelection(-1, SelectionMode::None);
	grid_ = nullptr;
	complex_face_ids_.clear();
	index_offset_ = 0;
}

void GridTraversalTool::clearSelection() { setSelection(-1, SelectionMode::None); }

void GridTraversalTool::setSelection(long long id, SelectionMode mode) {
	if (selection_mode_ == mode && selected_id_ == id)
		return;

	for (auto inst : selection_inst_)
		scene_->removeInstance(inst);
	selection_inst_.clear();
	for (auto node : nodes_)
		root_node_->removeNode(node);
	nodes_.clear();

	selected_id_ = id;
	selection_mode_ = mode;
	if (selection_mode_ == SelectionMode::Face) {
		Eigen::Vector<long long, 4> coords;
		grid_->get_face_coords(id, coords(0), coords(1), coords(2), coords(3));
		addFaceToVisualization(coords, DitheringPattern::Pattern1, selection_colors_[0]);

		Eigen::Vector<long long, 3> p_corner = coords.template block<3, 1>(0, 0);
		p_corner(coords(3))--;
		Eigen::Vector<long long, 3> sz(1, 1, 1);
		sz(coords(3))++;
		addEdgeGridToVisualization(p_corner, sz, DitheringPattern::Pattern0, selection_colors_[1]);
	} else if (selection_mode_ == SelectionMode::Edge) {
		Eigen::Vector<long long, 4> coords;
		grid_->get_edge_coords(id, coords(0), coords(1), coords(2), coords(3));
		addEdgeToVisualization(coords, DitheringPattern::Pattern1, selection_colors_[0]);

		Eigen::Vector<long long, 3> p_corner = coords.template block<3, 1>(0, 0);
		p_corner((coords(3) + 1) % 3)--;
		p_corner((coords(3) + 2) % 3)--;
		Eigen::Vector<long long, 3> sz(2, 2, 2);
		sz(coords(3))--;
		addEdgeGridToVisualization(p_corner, sz, DitheringPattern::Pattern0, selection_colors_[1]);
	} else if (selection_mode_ == SelectionMode::Vertex) {
		Eigen::Vector<long long, 3> coords;
		grid_->get_vertex_coords(id, coords(0), coords(1), coords(2));
		addVertexToVisualization(coords, DitheringPattern::Pattern1, selection_colors_[0]);

		Eigen::Vector<long long, 3> p_corner = coords - Eigen::Vector<long long, 3>(1, 1, 1);
		Eigen::Vector<long long, 3> sz(2, 2, 2);
		addEdgeGridToVisualization(p_corner, sz, DitheringPattern::Pattern0, selection_colors_[1]);
	} else if (selection_mode_ == SelectionMode::Cell) {
		Eigen::Vector<long long, 3> coords;
		grid_->get_cell_coords(id, coords(0), coords(1), coords(2));
		Eigen::Vector<long long, 3> sz(1, 1, 1);
		addEdgeGridToVisualization(coords, sz, DitheringPattern::Pattern1, selection_colors_[0]);

		for (int di = 0; di < 3; di++) {
			for (int i = -1; i <= 1; i += 2) {
				Eigen::Vector<long long, 3> c = coords;
				c(di) += i;
				addEdgeGridToVisualization(c, sz, DitheringPattern::Pattern0, selection_colors_[1]);
			}
		}
	}
	updateStatusString();
}

void GridTraversalTool::updateStatusString() {
	if (selection_mode_ == SelectionMode::None) {
		tool_status_string_ = "";
		return;
	}

	std::ostringstream oss;
	if (selection_mode_ == SelectionMode::Vertex) {
		oss << "Grid vertex: ";
	} else if (selection_mode_ == SelectionMode::Edge) {
		oss << "Grid edge: ";
	} else if (selection_mode_ == SelectionMode::Face) {
		oss << "Grid face: ";
	} else if (selection_mode_ == SelectionMode::Cell) {
		oss << "Grid cell: ";
	}
	oss << selected_id_;

	tool_status_string_ = oss.str();
}

void GridTraversalTool::addFaceToVisualization(const Eigen::Vector<long long, 4>& coords,
                                               DitheringPattern pattern,
                                               const Eigen::Vector3f& color) {
	if (grid_->face_out_of_bounds(coords[0], coords[1], coords[2], coords[3]))
		return;

	Eigen::Vector3d node_pos;
	Eigen::Matrix3d node_frame;
	bool is_okay = getFaceOrientation(coords, &node_pos, &node_frame);

	auto node = root_node_->addNode(std::make_unique<scene::Node>(node_pos, node_frame));
	nodes_.push_back(node);

	auto inst = scene_->addInstance(
	    std::make_unique<scene::OverlayMeshInstance>(selected_face_mesh_.get(), node));
	inst->setColor(color);
	inst->setPattern(pattern);
	selection_inst_.push_back(inst);
}

bool GridTraversalTool::getFaceOrientation(const Eigen::Vector<long long, 4>& coords,
                                           Eigen::Vector3d* position,
                                           Eigen::Matrix3d* frame) const {
	*frame = Eigen::Matrix3d::Zero();
	(*frame)(coords[3], 2) = 1.;
	(*frame)((coords[3] + 1) % 3, 0) = 1.;
	(*frame)((coords[3] + 2) % 3, 1) = 1.;

	auto grid_origin = grid_->getOriginCoords();
	double cell_dx = grid_->get_cell_dx();
	*position << grid_origin[0] + coords(0) * cell_dx, grid_origin[1] + coords(1) * cell_dx,
	    grid_origin[2] + coords(2) * cell_dx;

	return true;
}

void GridTraversalTool::addVertexToVisualization(
    const Eigen::Vector<long long, 3>& coords, scene::OverlayMeshInstance::DitheringPattern pattern,
    const Eigen::Vector3f& color) {
	if (grid_->vertex_out_of_bounds(coords[0], coords[1], coords[2]))
		return;

	auto grid_origin = grid_->getOriginCoords();
	double cell_dx = grid_->get_cell_dx();
	Eigen::Vector3d node_pos(grid_origin[0] + coords(0) * cell_dx,
	                         grid_origin[1] + coords(1) * cell_dx,
	                         grid_origin[2] + coords(2) * cell_dx);

	auto node = root_node_->addNode(std::make_unique<scene::Node>(node_pos));
	nodes_.push_back(node);

	auto inst = scene_->addInstance(
	    std::make_unique<scene::OverlayMeshInstance>(selected_vertex_mesh_.get(), node));
	inst->setColor(color);
	inst->setPattern(pattern);
	selection_inst_.push_back(inst);
}

void GridTraversalTool::addEdgeToVisualization(const Eigen::Vector<long long, 4>& coords,
                                               DitheringPattern pattern,
                                               const Eigen::Vector3f& color) {
	if (grid_->edge_out_of_bounds(coords[0], coords[1], coords[2], coords[3]))
		return;

	Eigen::Vector3d node_pos;
	Eigen::Matrix3d node_frame;
	getEdgeOrientation(coords, &node_pos, &node_frame);

	auto node = root_node_->addNode(std::make_unique<scene::Node>(node_pos, node_frame));
	nodes_.push_back(node);

	auto inst = scene_->addInstance(
	    std::make_unique<scene::OverlayMeshInstance>(selected_edge_mesh_.get(), node));
	inst->setColor(color);
	inst->setPattern(pattern);
	selection_inst_.push_back(inst);
}
bool GridTraversalTool::getEdgeOrientation(const Eigen::Vector<long long, 4>& coords,
                                           Eigen::Vector3d* position,
                                           Eigen::Matrix3d* frame) const {
	Eigen::Vector3d direction = Eigen::Vector3d::Zero();
	direction(coords[3]) = 1.;
	*frame = geom::buildBasis(direction);

	auto grid_origin = grid_->getOriginCoords();
	double cell_dx = grid_->get_cell_dx();
	*position << grid_origin[0] + coords(0) * cell_dx, grid_origin[1] + coords(1) * cell_dx,
	    grid_origin[2] + coords(2) * cell_dx;

	return true;
}

void GridTraversalTool::addEdgeGridToVisualization(const Eigen::Vector<long long, 3>& p,
                                                   const Eigen::Vector<long long, 3>& sz,
                                                   DitheringPattern pattern,
                                                   const Eigen::Vector3f& color) {
	for (int di = 0; di < 3; di++) {
		int di1 = (di + 1) % 3;
		int di2 = (di + 2) % 3;
		for (long long xi = 0; xi < sz[di]; xi++) {
			for (long long yi = 0; yi <= sz[di1]; yi++) {
				for (long long zi = 0; zi <= sz[di2]; zi++) {
					Eigen::Vector<long long, 4> coord;
					coord[3] = di;
					coord[di] = p[di] + xi;
					coord[di1] = p[di1] + yi;
					coord[di2] = p[di2] + zi;
					addEdgeToVisualization(coord, pattern, color);
				}
			}
		}
	}
}

ToolResponse GridTraversalTool::cursorCallback(logic::CursorEvent event) {
	return ToolResponse::None;
}
ToolResponse GridTraversalTool::mouseButtonCallback(logic::MouseButtonEvent event) {
	if (!grid_)
		return ToolResponse::None;

	if (event.button == GLFW_MOUSE_BUTTON_LEFT && event.action == GLFW_PRESS) {
		unsigned int index = interface_->cursorIndex();
		unsigned int face_index = index - index_offset_;
		if (face_index >= complex_face_ids_.size()) {
			setSelection(-1, SelectionMode::None);
		} else {
			setSelection(complex_face_ids_[face_index], SelectionMode::Face);
		}
		return ToolResponse::InstantAction;
	} else {
		return ToolResponse::None;
	}
}
ToolResponse GridTraversalTool::scrollCallback(logic::ScrollEvent event) {
	return ToolResponse::None;
}
ToolResponse GridTraversalTool::keyCallback(logic::KeyEvent event) {
	if (event.action != GLFW_PRESS)
		return ToolResponse::None;

	if (event.key == GLFW_KEY_3) {
		if (selection_mode_ == SelectionMode::Face) {
			Eigen::Vector<long long, 4> coords;
			grid_->get_face_coords(selected_id_, coords(0), coords(1), coords(2), coords(3));
			coords(3) = (coords(3) + 1) % 3;
			long long new_id = grid_->get_face_id(coords(0), coords(1), coords(2), coords(3));
			setSelection(new_id, SelectionMode::Face);
			return ToolResponse::InstantAction;
		} else if (selection_mode_ == SelectionMode::Edge) {
			Eigen::Vector<long long, 4> coords;
			grid_->get_edge_coords(selected_id_, coords(0), coords(1), coords(2), coords(3));
			long long new_id = grid_->get_face_id(coords(0), coords(1), coords(2), coords(3));
			setSelection(new_id, SelectionMode::Face);
			return ToolResponse::InstantAction;
		} else if (selection_mode_ == SelectionMode::Vertex) {
			Eigen::Vector<long long, 3> coords;
			grid_->get_vertex_coords(selected_id_, coords(0), coords(1), coords(2));
			long long new_id = grid_->get_face_id(coords(0), coords(1), coords(2), 0);
			setSelection(new_id, SelectionMode::Face);
			return ToolResponse::InstantAction;
		} else if (selection_mode_ == SelectionMode::Cell) {
			Eigen::Vector<long long, 3> coords;
			grid_->get_cell_coords(selected_id_, coords(0), coords(1), coords(2));
			long long new_id = grid_->get_face_id(coords(0), coords(1), coords(2), 0);
			setSelection(new_id, SelectionMode::Face);
			return ToolResponse::InstantAction;
		}
	} else if (event.key == GLFW_KEY_2) {
		if (selection_mode_ == SelectionMode::Face) {
			Eigen::Vector<long long, 4> coords;
			grid_->get_face_coords(selected_id_, coords(0), coords(1), coords(2), coords(3));
			long long new_id = grid_->get_edge_id(coords(0), coords(1), coords(2), coords(3));
			setSelection(new_id, SelectionMode::Edge);
			return ToolResponse::InstantAction;
		} else if (selection_mode_ == SelectionMode::Edge) {
			Eigen::Vector<long long, 4> coords;
			grid_->get_edge_coords(selected_id_, coords(0), coords(1), coords(2), coords(3));
			coords(3) = (coords(3) + 1) % 3;
			long long new_id = grid_->get_edge_id(coords(0), coords(1), coords(2), coords(3));
			setSelection(new_id, SelectionMode::Edge);
			return ToolResponse::InstantAction;
		} else if (selection_mode_ == SelectionMode::Vertex) {
			Eigen::Vector<long long, 3> coords;
			grid_->get_vertex_coords(selected_id_, coords(0), coords(1), coords(2));
			long long new_id = grid_->get_edge_id(coords(0), coords(1), coords(2), 0);
			setSelection(new_id, SelectionMode::Edge);
			return ToolResponse::InstantAction;
		} else if (selection_mode_ == SelectionMode::Cell) {
			Eigen::Vector<long long, 3> coords;
			grid_->get_cell_coords(selected_id_, coords(0), coords(1), coords(2));
			long long new_id = grid_->get_edge_id(coords(0), coords(1), coords(2), 0);
			setSelection(new_id, SelectionMode::Edge);
			return ToolResponse::InstantAction;
		}
	} else if (event.key == GLFW_KEY_1) {
		if (selection_mode_ == SelectionMode::Face) {
			Eigen::Vector<long long, 4> coords;
			grid_->get_face_coords(selected_id_, coords(0), coords(1), coords(2), coords(3));
			long long new_id = grid_->get_vertex_id(coords(0), coords(1), coords(2));
			setSelection(new_id, SelectionMode::Vertex);
			return ToolResponse::InstantAction;
		} else if (selection_mode_ == SelectionMode::Edge) {
			Eigen::Vector<long long, 4> coords;
			grid_->get_edge_coords(selected_id_, coords(0), coords(1), coords(2), coords(3));
			long long new_id = grid_->get_vertex_id(coords(0), coords(1), coords(2));
			setSelection(new_id, SelectionMode::Vertex);
			return ToolResponse::InstantAction;
		} else if (selection_mode_ == SelectionMode::Cell) {
			Eigen::Vector<long long, 3> coords;
			grid_->get_cell_coords(selected_id_, coords(0), coords(1), coords(2));
			long long new_id = grid_->get_vertex_id(coords(0), coords(1), coords(2));
			setSelection(new_id, SelectionMode::Vertex);
			return ToolResponse::InstantAction;
		}
	} else if (event.key == GLFW_KEY_4) {
		if (selection_mode_ == SelectionMode::Face || selection_mode_ == SelectionMode::Edge) {
			Eigen::Vector<long long, 4> coords;
			if (selection_mode_ == SelectionMode::Face) {
				grid_->get_face_coords(selected_id_, coords(0), coords(1), coords(2), coords(3));
			} else {
				grid_->get_edge_coords(selected_id_, coords(0), coords(1), coords(2), coords(3));
			}
			coords(0) = std::min(coords(0), grid_->get_dim_nx() - 1);
			coords(1) = std::min(coords(1), grid_->get_dim_ny() - 1);
			coords(2) = std::min(coords(2), grid_->get_dim_nz() - 1);
			long long new_id = grid_->get_cell_id(coords(0), coords(1), coords(2));
			setSelection(new_id, SelectionMode::Cell);
			return ToolResponse::InstantAction;
		} else if (selection_mode_ == SelectionMode::Vertex) {
			Eigen::Vector<long long, 3> coords;
			grid_->get_vertex_coords(selected_id_, coords(0), coords(1), coords(2));
			coords(0) = std::min(coords(0), grid_->get_dim_nx() - 1);
			coords(1) = std::min(coords(1), grid_->get_dim_ny() - 1);
			coords(2) = std::min(coords(2), grid_->get_dim_nz() - 1);
			long long new_id = grid_->get_cell_id(coords(0), coords(1), coords(2));
			setSelection(new_id, SelectionMode::Cell);
			return ToolResponse::InstantAction;
		}
	}

	if (event.key == GLFW_KEY_X || event.key == GLFW_KEY_Y || event.key == GLFW_KEY_Z) {
		int displ_coord = event.key - GLFW_KEY_X;
		int displ_sign = (event.mods & GLFW_MOD_SHIFT) ? -1 : 1;

		if (selection_mode_ == SelectionMode::Face) {
			Eigen::Vector<long long, 4> coords;
			grid_->get_face_coords(selected_id_, coords(0), coords(1), coords(2), coords(3));
			coords(displ_coord) += displ_sign;
			if (!grid_->face_out_of_bounds(coords(0), coords(1), coords(2), coords(3))) {
				long long new_id = grid_->get_face_id(coords(0), coords(1), coords(2), coords(3));
				setSelection(new_id, SelectionMode::Face);
				return ToolResponse::InstantAction;
			}
		} else if (selection_mode_ == SelectionMode::Edge) {
			Eigen::Vector<long long, 4> coords;
			grid_->get_edge_coords(selected_id_, coords(0), coords(1), coords(2), coords(3));
			coords(displ_coord) += displ_sign;
			if (!grid_->edge_out_of_bounds(coords(0), coords(1), coords(2), coords(3))) {
				long long new_id = grid_->get_edge_id(coords(0), coords(1), coords(2), coords(3));
				setSelection(new_id, SelectionMode::Edge);
				return ToolResponse::InstantAction;
			}
		} else if (selection_mode_ == SelectionMode::Vertex) {
			Eigen::Vector<long long, 3> coords;
			grid_->get_vertex_coords(selected_id_, coords(0), coords(1), coords(2));
			coords(displ_coord) += displ_sign;
			if (!grid_->vertex_out_of_bounds(coords(0), coords(1), coords(2))) {
				long long new_id = grid_->get_vertex_id(coords(0), coords(1), coords(2));
				setSelection(new_id, SelectionMode::Vertex);
				return ToolResponse::InstantAction;
			}
		} else if (selection_mode_ == SelectionMode::Cell) {
			Eigen::Vector<long long, 3> coords;
			grid_->get_cell_coords(selected_id_, coords(0), coords(1), coords(2));
			coords(displ_coord) += displ_sign;
			if (!grid_->cell_out_of_bounds(coords(0), coords(1), coords(2))) {
				long long new_id = grid_->get_cell_id(coords(0), coords(1), coords(2));
				setSelection(new_id, SelectionMode::Cell);
				return ToolResponse::InstantAction;
			}
		}
	}

	return ToolResponse::None;
}

ToolResponse GridTraversalTool::commandCallback(logic::CommandEvent event) {
	auto tokens = tokenize(event.command);

	if (tokens.empty() || (tokens.size() > 0 && tokens[0] != "sg"))
		return ToolResponse::None;

	std::string usage_string = "Usage of selection command: sg {v|e|f|c} id";
	if (tokens.size() != 3 || (tokens.size() > 1 && tokens[1] != "v" && tokens[1] != "e" &&
	                           tokens[1] != "f" && tokens[1] != "c")) {
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
	if (!grid_) {
		command_response_ = "Grid is not loaded. Cannot execute selection command.";
		return ToolResponse::InstantAction;
	}

	Eigen::Vector<long long, 4> coords;
	if (tokens[1] == "v") {
		grid_->get_vertex_coords(sel_id, coords(0), coords(1), coords(2));
		if (grid_->vertex_out_of_bounds(coords(0), coords(1), coords(2))) {
			command_response_ = "Vertex id is out of bounds.";
			return ToolResponse::InstantAction;
		}
		interface_->clearSelection();
		setSelection(sel_id, SelectionMode::Vertex);
		return ToolResponse::InstantAction;
	} else if (tokens[1] == "e") {
		grid_->get_edge_coords(sel_id, coords(0), coords(1), coords(2), coords(3));
		if (grid_->edge_out_of_bounds(coords(0), coords(1), coords(2), coords(3))) {
			command_response_ = "Edge id is out of bounds.";
			return ToolResponse::InstantAction;
		}
		interface_->clearSelection();
		setSelection(sel_id, SelectionMode::Edge);
		return ToolResponse::InstantAction;
	} else if (tokens[1] == "f") {
		grid_->get_face_coords(sel_id, coords(0), coords(1), coords(2), coords(3));
		if (grid_->face_out_of_bounds(coords(0), coords(1), coords(2), coords(3))) {
			command_response_ = "Face id is out of bounds.";
			return ToolResponse::InstantAction;
		}
		interface_->clearSelection();
		setSelection(sel_id, SelectionMode::Face);
		return ToolResponse::InstantAction;
	} else if (tokens[1] == "c") {
		grid_->get_cell_coords(sel_id, coords(0), coords(1), coords(2));
		if (grid_->cell_out_of_bounds(coords(0), coords(1), coords(2))) {
			command_response_ = "Cell id is out of bounds.";
			return ToolResponse::InstantAction;
		}
		interface_->clearSelection();
		setSelection(sel_id, SelectionMode::Cell);
		return ToolResponse::InstantAction;
	}

	std::cout << "Unexpected use of the sg command." << std::endl;
	return ToolResponse::None;
}

bool GridTraversalTool::isActive() const { return false; }

void GridTraversalTool::initColors() {
	selection_colors_[0] = Eigen::Vector3f::Constant(1.f);
	selection_colors_[1] = Eigen::Vector3f(255, 225, 25) / 255.f;
}

}  // namespace sdtf::viewer::logic