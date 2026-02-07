/* CurlNoise.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2021-2022
 *
 * Time-consistent curl noise.
 * Adapted from Los Topos.
 */
#pragma once

#include "../datastructures/Mesh3DInterface.h"
#include "CurlNoise.h"
#include "Scene.h"

class SmoothInverterScene : public Scene {
 public:
	SmoothInverterScene(Mesh3DInterface* mesh, double max_sim_time)
	    : Scene(max_sim_time), mesh_(mesh){};
	virtual void step(double dt) override;

 private:
	void assignVelocities(Mesh3DInterface* mesh);

	Mesh3DInterface* mesh_;
	Noise3 noise_;
};
