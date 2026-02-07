#include "MeshMultiplier.h"

#include <random>

MeshMultiplierScene::MeshMultiplierScene(Mesh3DInterface* mesh, double max_sim_time,
                                         const TopoFixerSettings& settings)
    : Scene(max_sim_time),
      mesh_(mesh),
      mesh_copy_(settings),
      random_gen_(111),
      is_copy_initialized_(false) {}

void MeshMultiplierScene::step(double dt) {
	if (!is_copy_initialized_) {
		mesh_copy_.restoreFromSaveState(mesh_->getCurrentSaveState());
		is_copy_initialized_ = true;
	}
	advanceTime(dt);

	std::uniform_real_distribution<> dist(0.0, 1.0);
	double phi = acos(2 * dist(random_gen_) - 1);
	double theta = 2 * M_PI * dist(random_gen_);

	Vec3d axis(cos(theta) * sin(phi), sin(theta) * sin(phi), cos(phi));
	double angle = 2 * M_PI * dist(random_gen_);

	std::cout << axis << " " << angle << std::endl;

	// Rotate
	std::vector<Vec3d> rot_mat = rotationMatrix(axis, angle);
	Vec3d center = mesh_copy_.getMeshCenter();
	std::cout << center << std::endl;
	for (Mesh3DVertex* v : mesh_copy_.ListVertices()) {
		Vec3d coords = v->getCoords();
		v->setCoords(center + rotate(rot_mat, coords - center));
	}

	// Increase materials
	int offset = mesh_copy_.getNumberLabels();
	for (Mesh3DTriangle* tri : mesh_copy_.ListTriangles()) {
		Vec2i labels = tri->getLabels();
		for (int i = 0; i < 2; ++i) {
			if (labels[i] != 0) {
				labels[i] += offset;
			}
		}
		tri->setLabels(labels);
	}
	// Append
	mesh_->appendFromSaveState(mesh_copy_.getCurrentSaveState());
}

std::vector<Vec3d> MeshMultiplierScene::rotationMatrix(Vec3d axis, double angle) const {
	double cos_th = cos(angle);
	double sin_th = sin(angle);
	return {
	    {cos_th + axis[0] * axis[0] * (1 - cos_th),
	     axis[0] * axis[1] * (1 - cos_th) - axis[2] * sin_th,
	     axis[0] * axis[2] * (1 - cos_th) + axis[1] * sin_th},
	    {axis[1] * axis[0] * (1 - cos_th) + axis[2] * sin_th,
	     cos_th + axis[1] * axis[1] * (1 - cos_th),
	     axis[1] * axis[2] * (1 - cos_th) - axis[0] * sin_th},
	    {axis[2] * axis[0] * (1 - cos_th) - axis[1] * sin_th,
	     axis[2] * axis[1] * (1 - cos_th) + axis[0] * sin_th,
	     cos_th + axis[2] * axis[2] * (1 - cos_th)},
	};
}

Vec3d MeshMultiplierScene::rotate(const std::vector<Vec3d>& rot_matrix, Vec3d point) const {
	Vec3d result(0.0);
	for (int i = 0; i < 3; ++i) {
		result[i] = dot(rot_matrix[i], point);
	}
	return result;
}
