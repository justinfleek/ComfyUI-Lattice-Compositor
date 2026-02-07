/* NormalFlow.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2021-2022
 *
 * This is the header for scene where each vertex on the boundary with outside material is moved in
 * the direction of the normal.
 */
#pragma once

#include "../datastructures/Mesh3DInterface.h"
#include "../schemes/TopoFixerSettings.h"
#include "Scene.h"

class NormalFlow : public Scene {
 public:
	NormalFlow(Mesh3DInterface* mesh, double max_sim_time, const TopoFixerSettings& settings)
	    : Scene(max_sim_time), settings(&settings), mesh_(mesh){};
	virtual void step(double dt) override;

 private:
	const TopoFixerSettings* settings;
	Mesh3DInterface* mesh_;
};
