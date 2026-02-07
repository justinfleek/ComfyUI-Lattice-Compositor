#include "GeometryFactory.h"

#include <Eigen/Dense>
#include <algorithm>
#include <unordered_set>

namespace sdtf::viewer::logic {
;

GeometryFactory::GeometryFactory(const LinearMesh3DView& mesh, const Grid3DInterface& grid)
    : mesh_(&mesh), grid_(&grid) {
	initColors();
}

std::unique_ptr<gl::TriangleMesh> GeometryFactory::makeTriangleMesh(float face_color_perturbation,
                                                                    unsigned int index_offset) {
	auto nt = mesh_->numTriangles();
	auto nc = mesh_color_map_.size();
	Eigen::Matrix<GLfloat, 3, -1> vertices(3, 3 * nt);
	Eigen::Matrix<GLuint, 1, -1> indices(1, 3 * nt);
	Eigen::Matrix<GLfloat, 3, -1> front_colors(3, 3 * nt);
	Eigen::Matrix<GLfloat, 3, -1> back_colors(3, 3 * nt);
	for (unsigned int ti = 0; ti < nt; ti++) {
		auto t = mesh_->triangle(ti);
		auto labels = t->getLabels();

		std::array<Eigen::Vector3f, 2> colors;
		for (unsigned int ci = 0; ci < 2; ci++) {
			colors[ci] = mesh_color_map_[labels.v[ci] % nc];
			colors[ci] += face_color_perturbation * Eigen::Vector3f::Random();
			colors[ci] = colors[ci].cwiseMax(0.0f).cwiseMin(1.0f);
		}

		for (unsigned vi = 0; vi < 3; vi++) {
			auto v = t->getVertex(vi);
			auto pos = v->getCoords();
			auto col_index = ti * 3 + vi;
			vertices.col(col_index) << pos.v[0], pos.v[1], pos.v[2];
			indices(col_index) = ti + index_offset;
			front_colors.col(col_index) = colors[0];
			back_colors.col(col_index) = colors[1];
		}
	}

	auto ret = std::make_unique<gl::TriangleMesh>(vertices);
	ret->setIndices(indices);
	ret->setFrontColor(front_colors);
	ret->setBackColor(back_colors);

	return ret;
}

std::unique_ptr<gl::LineMesh> GeometryFactory::makeLineMesh() {
	auto nv = mesh_->numVertices();
	auto nt = mesh_->numTriangles();
	Eigen::Matrix<GLfloat, 3, -1> vertices(3, nv);
	for (unsigned int vi = 0; vi < nv; vi++) {
		auto pos = mesh_->vertex(vi)->getCoords();
		vertices.col(vi) << pos.v[0], pos.v[1], pos.v[2];
	}
	std::vector<std::array<unsigned int, 2>> edges;
	edges.reserve(nt * 3);
	for (unsigned int ti = 0; ti < nt; ti++) {
		auto verts = mesh_->triangle(ti)->getVerts();
		std::array<unsigned int, 3> v_inds;
		for (unsigned vi = 0; vi < 3; vi++)
			v_inds[vi] = mesh_->vertexIndex(verts[vi]);
		std::sort(v_inds.begin(), v_inds.end());
		edges.push_back(std::array<unsigned int, 2>{v_inds[0], v_inds[1]});
		edges.push_back(std::array<unsigned int, 2>{v_inds[1], v_inds[2]});
		edges.push_back(std::array<unsigned int, 2>{v_inds[0], v_inds[2]});
	}
	std::sort(edges.begin(), edges.end());
	auto last = std::unique(edges.begin(), edges.end());
	edges.erase(last, edges.end());

	Eigen::Matrix<GLuint, 2, -1> e(2, edges.size());
	for (unsigned int ei = 0; ei < edges.size(); ei++)
		e.col(ei) << edges[ei][0], edges[ei][1];

	return std::make_unique<gl::LineMesh>(vertices, e);
}

void GeometryFactory::makeComplexCellSetBoundaryMeshes(
    std::unique_ptr<gl::TriangleMesh>* triangle_mesh, std::unique_ptr<gl::LineMesh>* line_mesh,
    std::vector<long long>* face_ids,
    unsigned int index_offset) {
	auto cell_set = grid_->getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed);
	cell_set.rehash(0);

	double square_hw = 0.3;
	Eigen::Matrix<double, 2, 6> vpos_local;
	vpos_local.col(0) << 0.5 + square_hw, 0.5 + square_hw;
	vpos_local.col(1) << 0.5 - square_hw, 0.5 + square_hw;
	vpos_local.col(2) << 0.5 - square_hw, 0.5 - square_hw;
	vpos_local.col(3) << 0.5 + square_hw, 0.5 + square_hw;
	vpos_local.col(4) << 0.5 - square_hw, 0.5 - square_hw;
	vpos_local.col(5) << 0.5 + square_hw, 0.5 - square_hw;


	auto faces_to_render = getCellSetBoundaryFaces(cell_set);
	face_ids->clear();
	face_ids->reserve(faces_to_render.size());
	Eigen::Matrix<GLfloat, 3, -1> vertices(3, 6 * faces_to_render.size());
	Eigen::Vector<GLuint, -1> indices(6 * faces_to_render.size());
	unsigned int col_offset = 0;
	unsigned int index = index_offset;
	for (const auto& tup : faces_to_render) {
		face_ids->push_back(std::get<0>(tup));
		Eigen::Matrix<double, 3, 6> fr = std::get<2>(tup) * vpos_local;
		fr.colwise() += std::get<1>(tup);
		vertices.template block<3, 6>(0, col_offset) = fr.cast<GLfloat>();
		indices.template block<6, 1>(col_offset, 0).fill(index);
		index++;
		col_offset += 6;
	}

	*triangle_mesh = std::make_unique<gl::TriangleMesh>(vertices);
	(*triangle_mesh)->setIndices(indices);

	std::vector<std::array<long long, 2>> edges;
	edges.reserve(4 * faces_to_render.size());
	Eigen::Matrix<unsigned int, 2, 4> vi_local;
	vi_local << 0, 0, 1, 2, 1, 2, 3, 3;
	for (const auto& tup : faces_to_render) {
		auto vis = grid_->get_verts_neighboring_face(std::get<0>(tup));
		for (int i = 0; i < 4; i++) {
			auto vi1 = vis[vi_local(0, i)];
			auto vi2 = vis[vi_local(1, i)];
			edges.push_back(vi1 < vi2 ? std::array<long long, 2>{vi1, vi2}
			                          : std::array<long long, 2>{vi2, vi1});
		}
	}
	std::sort(edges.begin(), edges.end());
	auto last = std::unique(edges.begin(), edges.end());
	edges.erase(last, edges.end());

	Eigen::Matrix<GLfloat, 3, -1> edge_pos(3, edges.size() * 2);
	for (unsigned int ei = 0; ei < edges.size(); ei++) {
		for (unsigned int vi = 0; vi < 2; vi++) {
			auto vpos = grid_->getVertexPosition(edges[ei][vi]);
			edge_pos.col(2 * ei + vi) << vpos[0], vpos[1], vpos[2];
		}
	}

	*line_mesh = std::make_unique<gl::LineMesh>(edge_pos);
}

std::vector<std::tuple<long long, Eigen::Vector3d, Eigen::Matrix<double, 3, 2>>>
GeometryFactory::getCellSetBoundaryFaces(const absl::flat_hash_set<long long>& cells) {
	std::vector<std::tuple<long long, Eigen::Vector3d, Eigen::Matrix<double, 3, 2>>> ret;
	for (long long ci : cells) {
		auto incident_faces = grid_->get_faces_neighboring_cell(ci);
		Vec3d cell_center3d = grid_->getCellCenter(ci);
		Eigen::Vector3d cell_center(cell_center3d[0], cell_center3d[1], cell_center3d[2]);
		for (long long fi : incident_faces) {
			auto ci_and_neighbor = grid_->get_cells_neighboring_face(fi);
			bool add_face = true;
			for (long long ci_other : ci_and_neighbor) {
				if (ci_other != ci && cells.contains(ci_other)) {
					add_face = false;
					break;
				}
			}
			if (add_face) {
				auto vis = grid_->get_verts_neighboring_face(fi);
				std::array<Eigen::Vector3d, 3> v_pos;
				for (int i = 0; i < 3; i++) {
					auto vpos3d = grid_->getVertexPosition(vis[i]);
					v_pos[i] << vpos3d[0], vpos3d[1], vpos3d[2];
				}
				Eigen::Vector3d to1 = v_pos[1] - v_pos[0];
				Eigen::Vector3d to2 = v_pos[2] - v_pos[0];
				Eigen::Vector3d face_normal = to1.cross(to2);
				bool facing_outwards = face_normal.dot(v_pos[0] - cell_center) > 0;
				Eigen::Matrix<double, 3, 2> basis;
				basis.col(facing_outwards ? 0 : 1) = to1;
				basis.col(facing_outwards ? 1 : 0) = to2;
				ret.push_back(std::tuple<long long, Eigen::Vector3d, Eigen::Matrix<double, 3, 2>>(
				    fi, v_pos[0], basis));
			}
		}
	}
	return ret;
}

void GeometryFactory::initColors() {
	// Source: https://sashamaps.net/docs/resources/20-colors/ (Color order "convenient", remove
	// b/w/gray/beige/yellow, put red at the end)
	mesh_color_map_ =
	    std::vector<Eigen::Vector3f>{Eigen::Vector3f(60, 180, 75),   
	                                 Eigen::Vector3f(0, 130, 200),   Eigen::Vector3f(245, 130, 48),
	                                 Eigen::Vector3f(145, 30, 180),  Eigen::Vector3f(70, 240, 240),
	                                 Eigen::Vector3f(240, 50, 230),  Eigen::Vector3f(210, 245, 60),
	                                 Eigen::Vector3f(250, 190, 212), Eigen::Vector3f(0, 128, 128),
	                                 Eigen::Vector3f(220, 190, 255), Eigen::Vector3f(170, 110, 40),
	                                 Eigen::Vector3f(128, 0, 0),     Eigen::Vector3f(170, 255, 195),
	                                 Eigen::Vector3f(128, 128, 0),   Eigen::Vector3f(255, 215, 180),
	                                 Eigen::Vector3f(0, 0, 128),     Eigen::Vector3f(230, 25, 75)};
	for (auto& c : mesh_color_map_)
		c /= 255.f;
}

}  // namespace sdtf::viewer::logic