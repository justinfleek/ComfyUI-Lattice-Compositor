#include "NormalFlow.h"

#include <unordered_map>
#include <unordered_set>

#include "../datastructures/Mesh3DHalfCorner.h"
#include "../datastructures/Mesh3DTriangle.h"
#include "../datastructures/Mesh3DVertex.h"

void NormalFlow::step(double dt) {
	if (settings->verbosity >= 2) {
		std::cout << "-computing a step of normal flow\n";
	}

	absl::flat_hash_map<Mesh3DVertex*, Vec3d> vert_to_vel;

	size_t num_materials = 1010;
	std::vector<std::vector<double>> speeds(num_materials, std::vector<double>(num_materials, 0));
	for (size_t i = 0; i < num_materials; ++i) {
		speeds[i][0] = -1.0;
		speeds[0][i] = 1.0;
	}

	for (Mesh3DTriangle* tri : mesh_->ListTriangles()) {
		int lr, ll;
		tri->getLabels(lr, ll);
		Vec3d normal = tri->getNaiveNormal();
		if (mag2(normal) > 1e-10 * 1e-10) {
			normalize(normal);
		}

		Mesh3DHalfCorner* hfc = tri->getHalfCorner();
		for (int i = 0; i < 3; ++i, hfc = hfc->getNext()) {
			double angle = mesh_->getAngle(hfc);
			if (angle < 0) {
				continue;
			}
			Vec3d vel_update = (speeds[lr][ll] - speeds[ll][lr]) * angle * normal;
			Mesh3DVertex* vert = hfc->getVertex();
			auto it = vert_to_vel.find(vert);
			if (it != vert_to_vel.end()) {
				it->second += vel_update;
			} else {
				vert_to_vel[vert] = vel_update;
			}
		}
	}

	for (auto [vert, velocity] : vert_to_vel) {
		if (mag2(velocity) > 1e-10 * 1e-10) {
			normalize(velocity);
		}
		vert->setCoords(vert->getCoords() + dt * velocity);
	}
	advanceTime(dt);

	if (settings->verbosity >= 2) {
		std::cout << "-step of normal flow finished\n";
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
}
