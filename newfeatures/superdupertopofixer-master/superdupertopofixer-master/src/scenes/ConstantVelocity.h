/* ConstantVelocity.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2021-2022
 *
 * This is the header for scene with 2 spheres flying at each other a constant speed.
 */
#pragma once

#include "../datastructures/Mesh3DInterface.h"
#include "Scene.h"
class ConstantVelocityScene : public Scene {
 public:
	ConstantVelocityScene(Mesh3DInterface* mesh, double max_sim_time)
	    : Scene(max_sim_time), mesh_(mesh){};
	virtual void step(double dt) override;

 private:
	Mesh3DInterface* mesh_;
};
