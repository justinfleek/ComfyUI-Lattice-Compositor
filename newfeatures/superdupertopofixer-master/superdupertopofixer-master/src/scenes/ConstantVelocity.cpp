#include "ConstantVelocity.h"

#include "../datastructures/Mesh3DTriangle.h"
#include "../datastructures/Mesh3DVertex.h"

void ConstantVelocityScene::step(double dt) {
	absl::flat_hash_map<Mesh3DVertex*, Vec3d> vert_to_vel;

	for (Mesh3DTriangle* tri : mesh_->ListTriangles()) {
		int lr, ll;
		tri->getLabels(lr, ll);
		if (lr > ll) {
			std::swap(lr, ll);
		}
		// Don't move the interface.
		if (lr == 1 && ll == 2) {
			for (Mesh3DVertex* vert : tri->getVerts()) {
				vert_to_vel[vert] = Vec3d(0.0);
			}
		} else {
			Vec3d velocity{1, 0, 0};
			if (ll == 2) {
				velocity[0] = -1;
			}

			for (Mesh3DVertex* vert : tri->getVerts()) {
				vert_to_vel.insert({vert, velocity});
			}
		}
	}

	for (auto [vert, velocity] : vert_to_vel) {
		vert->setCoords(vert->getCoords() + dt * velocity);
	}
	advanceTime(dt);
}
