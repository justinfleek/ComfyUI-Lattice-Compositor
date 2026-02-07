#include "Zalesak.h"

#include "../datastructures/Mesh3DVertex.h"

void ZalesakScene::step(double dt) {
	for (Mesh3DVertex* v : mesh_->ListVertices()) {
		Vec3d pos = v->getCoords();
		Vec3d k1 = velocity(pos);
		Vec3d k2 = velocity(pos + 0.5 * dt * k1);
		Vec3d k3 = velocity(pos + 0.5 * dt * k2);
		Vec3d k4 = velocity(pos + dt * k3);
		Vec3d vel = (k1 + k2 * 2 + k3 * 2 + k4) / 6;
		v->setCoords(pos + dt * vel);
	}
	advanceTime(dt);
}

Vec3d ZalesakScene::velocity(Vec3d pos) { return {pos[2] - 0.5, 0, 0.5 - pos[0]}; }
