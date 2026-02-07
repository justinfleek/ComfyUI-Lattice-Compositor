/* Zalesak.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2021-2022
 *
 * Sets up velocity field to rotate the Zalesak disk in around an axis.
 */
#pragma once

#include "../datastructures/Mesh3DInterface.h"
#include "Scene.h"
class ZalesakScene : public Scene {
 public:
	ZalesakScene(Mesh3DInterface* mesh, double max_sim_time) : Scene(max_sim_time), mesh_(mesh){};
	virtual void step(double dt) override;

 private:
	Vec3d velocity(Vec3d pos);

	Mesh3DInterface* mesh_;
};
