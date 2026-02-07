#include "SmoothInverter.h"

void SmoothInverterScene::step(double dt) {
	if (getCurrentSimTime() == 0) {
		assignVelocities(mesh_);
	}
	for (Mesh3DVertex* v : mesh_->ListVertices()) {
		Vec3d pos = v->getCoords();
		Vec3d velocity = v->getVelocity();
		v->setCoords(pos + dt * velocity);
	}
	advanceTime(dt);
}

void SmoothInverterScene::assignVelocities(Mesh3DInterface* mesh) {
	for (Mesh3DVertex* v : mesh->ListVertices()) {
		Vec3d pos = v->getCoords();
		Vec3d pos2 = {pos[2] - 203.994, pos[0] + 169.47, pos[1] - 205.31};
		Vec3d pos3 = {pos[1] + 160.884, pos[2] - 181.94, pos[0] - 246.63};

		double scale = 1.0 / 5.5;

		Vec3d vel = {noise_(pos / scale), noise_(pos2 / scale), noise_(pos3 / scale)};
		v->setVelocity(vel);
	}
}
