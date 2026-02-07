#include "GridAdvect.h"

#include <filesystem>

#include "../utilities/cnpy/cnpy.h"

GridAdvectScene::GridAdvectScene(Mesh3DInterface* mesh, double max_sim_time,
                                 const std::string& grid_directory)
    : Scene(max_sim_time), grid_directory_(grid_directory), mesh_(mesh), current_step_(1) {}

void GridAdvectScene::step(double dt) {
	Grid3DSparseCubical grid = loadGrid(grid_directory_, current_step_);

	std::vector<Mesh3DVertex*> scripted_vertices;
	std::vector<Mesh3DVertex*> advected_vertices;

	for (Mesh3DVertex* v : mesh_->ListVertices()) {
		if (v->getYCoord() >= 0.0) {
			scripted_vertices.push_back(v);
		} else {
			advected_vertices.push_back(v);
		}
	}

	moveScripted(scripted_vertices);

	advectThroughGrid(advected_vertices, grid, dt);
	advanceTime(dt);
	current_step_++;
}

Grid3DSparseCubical GridAdvectScene::loadGrid(const std::string_view directory, const int step) {
	std::filesystem::path path(directory);

	std::string number = std::to_string(step);
	std::string prefix;
	for (int i = 0; i < 4 - number.length(); ++i) {
		prefix += "0";
	}
	std::string filename = "vel." + prefix + number + ".npz";
	path.append(filename);
	cnpy::npz_t npz = cnpy::npz_load(path.string());

	double dx = npz["dx"].data<double>()[0];
	std::vector<double> min_vec = npz["min_vec"].as_vec<double>();
	std::vector<long long> shape = npz["shape"].as_vec<long long>();

	Grid3DSparseCubical grid;
	grid.init(shape[0] - 1, shape[1] - 1, shape[2] - 1, min_vec[0], min_vec[1], min_vec[2], dx);
	double* samples = npz["samples"].data<double>();
	for (long long i = 0; i < shape[0]; i++) {
		for (long long j = 0; j < shape[1]; j++) {
			for (long long k = 0; k < shape[2]; k++) {
				long long sample_id = i * shape[1] * shape[2] * 3 + j * shape[2] * 3 + k * 3;
				Vec3d vel = Vec3d(samples[sample_id + 0], samples[sample_id + 1], samples[sample_id + 2]);
				grid.addInterpolatedVertPropsOnVertex(grid.get_vertex_id(i, j, k),
				                                      VertexProperties(vel, Vec3d(0.0), 0.0, 0.0));
			}
		}
	}
	return grid;
}

void GridAdvectScene::moveScripted(const std::vector<Mesh3DVertex*>& vertices) const {
	double offset_diff =
	    getScriptOffsetAtStep(current_step_ + 1) - getScriptOffsetAtStep(current_step_);
	double texture_offset = 1 / 24.0;
	std::cout << "Offset: " << offset_diff << std::endl;
	for (Mesh3DVertex* v : vertices) {
		v->setZCoord(v->getZCoord() + offset_diff);
	}
}

void GridAdvectScene::advectThroughGrid(const std::vector<Mesh3DVertex*>& vertices,
                                        Grid3DSparseCubical& grid, double dt) const {
	double max_vel = -1.0;
	double last_vel;
	for (Mesh3DVertex* v : vertices) {
		Vec3d pos = v->getCoords();
		Vec3d k1 = velocity(pos, grid);
		Vec3d k2 = velocity(pos + 0.5 * dt * k1, grid);
		Vec3d k3 = velocity(pos + 0.5 * dt * k2, grid);
		Vec3d k4 = velocity(pos + dt * k3, grid);
		Vec3d vel = (k1 + k2 * 2 + k3 * 2 + k4) / 6;
		v->setCoords(pos + dt * vel);

		last_vel = mag(vel);
		max_vel = std::max(max_vel, last_vel);
	}
	std::cout << "vels: " << last_vel << " " << max_vel << std::endl;
}

Vec3d GridAdvectScene::velocity(Vec3d pos, Grid3DSparseCubical& grid) const {
	long long cell_id;
	bool in_bounds = grid.getCellForPoint(pos[0], pos[1], pos[2], cell_id);
	if (!in_bounds) {
		return Vec3d(0.0);
	}

	std::vector<long long> vert_ids = grid.get_verts_neighboring_cell(cell_id);
	std::vector<Vec3d> vert_pos;
	std::vector<Vec3d> vels;
	for (long long vert_id : vert_ids) {
		vert_pos.push_back(grid.getVertexPosition(vert_id));
		VertexProperties vp = grid.getInterpolatedVertPropsFromVertex(vert_id);
		vels.push_back(vp.getVelocity());
	}

	Vec3d weights = (pos - vert_pos[0]) / grid.get_cell_dx();

	Vec3d vel = (1 - weights[0]) * (1 - weights[1]) * (1 - weights[2]) * vels[0] +
	            weights[0] * (1 - weights[1]) * (1 - weights[2]) * vels[1] +
	            (1 - weights[0]) * weights[1] * (1 - weights[2]) * vels[2] +
	            (1 - weights[0]) * (1 - weights[1]) * weights[2] * vels[3] +
	            weights[0] * weights[1] * (1 - weights[2]) * vels[4] +
	            (1 - weights[0]) * weights[1] * weights[2] * vels[5] +
	            weights[0] * (1 - weights[1]) * weights[2] * vels[6] +
	            weights[0] * weights[1] * weights[2] * vels[7];
	return vel;
}

double GridAdvectScene::getScriptOffsetAtStep(int step) const {
	double t;
	if (step < 48) {
		t = (step - 1.0) / 47.0;
		t = hermiteSpline(t);
	} else if (step < 60) {
		t = 1.0;
	} else {
		t = (step - 60.0) / 48.0;
		t = 1.0 - hermiteSpline(t);
	}
	return t;
}
