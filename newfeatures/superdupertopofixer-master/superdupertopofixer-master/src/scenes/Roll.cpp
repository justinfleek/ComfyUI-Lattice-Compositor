#include "Roll.h"

#include <cmath>

#include "absl/container/flat_hash_set.h"
RollScene::RollScene(Mesh3DInterface* mesh, double max_sim_time)
    : Scene(max_sim_time), mesh_(mesh) {}

void RollScene::step(double dt) {
	if (getCurrentSimTime() == 0.0) {
		init(mesh_);
	}
	double cos_rot = cos(dt * one_over_radius_);
	double sin_rot = sin(dt * one_over_radius_);
	Vec3d offset(dt, 0.0, 0.0);

	for (Mesh3DVertex* v : mesh_->ListVertices()) {
		v->setCoords(rotate(v->getCoords() - rotation_center_, cos_rot, sin_rot) + offset +
		             rotation_center_);
	}
	rotation_center_ += offset;
	advanceTime(dt);
}

void RollScene::init(Mesh3DInterface* mesh) {
	// Figure out rolling radius.
	Vec3d mesh_min;
	Vec3d mesh_max;
	mesh->getMeshBounds(mesh_min, mesh_max);

	// For rolling along x-axis, only z-axis matters.
	one_over_radius_ = 2 / (mesh_max[2] - mesh_min[2]);
	rotation_center_ = (mesh_max + mesh_min) / 2;
}

Vec3d RollScene::rotate(Vec3d pos, double cos_rot, double sin_rot) {
	Vec3d res;
	res[0] = cos_rot * pos[0] + sin_rot * pos[2];
	res[1] = pos[1];
	res[2] = -sin_rot * pos[0] + cos_rot * pos[2];
	return res;
}

void TwoRollScene::step(double dt) {
	double sim_time = getCurrentSimTime();
	if (sim_time == 0) {
		init(mesh_);
	}

	if (sim_time < pill_start_time) {
		rollToCenter(dt);
	} else {
		rollPill(dt);
	}
	advanceTime(dt);
}

void TwoRollScene::init(Mesh3DInterface* mesh) {
	rotation_centers_[0] = mesh->getMeshCenter();
	rotation_centers_[1] = rotation_centers_[0] + Vec3d(5, 0, 0);

	Vec3d mesh_min;
	Vec3d mesh_max;
	mesh->getMeshBounds(mesh_min, mesh_max);
	one_over_radius_ = 2 / (mesh_max[2] - mesh_min[2]);

	Mesh3DSaveState state = mesh->getCurrentSaveState();
	for (Mesh3DVertex& v : state.vertices) {
		v.setXCoord(v.getXCoord() + 5);
	}

	for (Mesh3DTriangle& t : state.triangles) {
		Vec2i labels = t.getLabels();
		for (int i = 0; i < 2; ++i) {
			if (labels[i] == 1) {
				labels[i] = 2;
			}
		}

		t.setLabels(labels);
	}
	mesh->appendFromSaveState(state);
}

void TwoRollScene::rollToCenter(double dt) {
	double cos_rot = cos(dt * one_over_radius_);
	double sin_rot = sin(dt * one_over_radius_);
	Vec3d offset(dt, 0.0, 0.0);

	absl::flat_hash_set<Mesh3DVertex*> first_mat_verts;
	for (Mesh3DTriangle* tri : mesh_->ListTriangles()) {
		Vec2i labels = tri->getLabels();
		if (labels[0] == 1 || labels[1] == 1) {
			for (Mesh3DVertex* v : tri->getVerts()) {
				first_mat_verts.insert(v);
			}
		}
	}

	for (Mesh3DVertex* v : mesh_->ListVertices()) {
		if (first_mat_verts.contains(v)) {
			v->setCoords(rotate(v->getCoords() - rotation_centers_[0], cos_rot, sin_rot) + offset +
			             rotation_centers_[0]);
		} else {
			v->setCoords(rotate(v->getCoords() - rotation_centers_[1], cos_rot, -sin_rot) - offset +
			             rotation_centers_[1]);
		}
	}
	rotation_centers_[0] += offset;
	rotation_centers_[1] -= offset;
}

void TwoRollScene::rollPill(double dt) {
	double roll_time = getCurrentSimTime() - pill_start_time;
	double half_period = M_PI / one_over_radius_;
	int mode = (static_cast<int>(roll_time / half_period) + 1) % 2;

	double cos_rot = cos(dt * one_over_radius_);
	double sin_rot = sin(dt * one_over_radius_);
	Vec3d offset(dt, 0.0, 0.0);
	for (Mesh3DVertex* v : mesh_->ListVertices()) {
		v->setCoords(rotate(v->getCoords() - rotation_centers_[mode], cos_rot, sin_rot) + offset +
		             rotation_centers_[mode]);
	}

	rotation_centers_[(mode + 1) % 2] =
	    rotate(rotation_centers_[(mode + 1) % 2] - rotation_centers_[mode], cos_rot, sin_rot) +
	    rotation_centers_[mode];

	for (int i = 0; i < 2; ++i) {
		rotation_centers_[i] += offset;
	}
}

Vec3d TwoRollScene::rotate(Vec3d pos, double cos_rot, double sin_rot) {
	Vec3d res;
	res[0] = cos_rot * pos[0] + sin_rot * pos[2];
	res[1] = pos[1];
	res[2] = -sin_rot * pos[0] + cos_rot * pos[2];
	return res;
}
