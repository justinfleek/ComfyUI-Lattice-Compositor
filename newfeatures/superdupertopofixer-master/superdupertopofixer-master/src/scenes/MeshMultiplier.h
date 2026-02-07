/* MeshMultiplier.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2021-2022
 *
 * Incrementally clones, perturbs and unions a given mesh with the current mesh resulting in
 * a complex union shape of the same mesh.
 */
#pragma once

#include <random>

#include "../datastructures/Mesh3DCornerTable.h"
#include "../datastructures/Mesh3DInterface.h"
#include "Scene.h"
#include "../schemes/TopoFixerSettings.h"

class MeshMultiplierScene : public Scene {
 public:
	MeshMultiplierScene(Mesh3DInterface* mesh, double max_sim_time, const TopoFixerSettings& settings);
	virtual void step(double dt) override;

 private:
	std::vector<Vec3d> rotationMatrix(Vec3d axis, double angle) const;
	Vec3d rotate(const std::vector<Vec3d>& rot_matrix, Vec3d point) const;

	Mesh3DInterface* mesh_;
	Mesh3DCornerTable mesh_copy_;
	std::mt19937 random_gen_;
	bool is_copy_initialized_;
};
