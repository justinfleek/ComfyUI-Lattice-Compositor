/* Roll.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2021-2022
 *
 * Moves vertices as if the object rolls in xz-plane.
 */
#pragma once

#include "../datastructures/Mesh3DInterface.h"
#include "Scene.h"

class RollScene : public Scene {
 public:
	RollScene(Mesh3DInterface* mesh, double max_sim_time);
	virtual void step(double dt) override;

 private:
	void init(Mesh3DInterface* mesh);

	// Rotates around y-axis by precomputed cos / sin amount.
	Vec3d rotate(Vec3d pos, double cos_rot, double sin_rot);

	double one_over_radius_;
	Vec3d rotation_center_;
	Mesh3DInterface* mesh_;
};

class TwoRollScene : public Scene {
 public:
	TwoRollScene(Mesh3DInterface* mesh, double max_sim_time) : Scene(max_sim_time), mesh_(mesh){};
	virtual void step(double dt) override;

 private:
	void init(Mesh3DInterface* mesh);
	void rollToCenter(double dt);
	void rollPill(double dt);

	// Rotates around y-axis by precomputed cos / sin amount.
	Vec3d rotate(Vec3d pos, double cos_rot, double sin_rot);

	double pill_start_time = 1.83;
	double one_over_radius_;
	std::array<Vec3d, 2> rotation_centers_;
	Mesh3DInterface* mesh_;
};