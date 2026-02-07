/* GridAdvect.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2021-2022
 *
 * Advects mesh through velocity stored on grids.
 */
#pragma once

#include "../datastructures/Grid3DSparseCubical.h"
#include "../datastructures/Mesh3DInterface.h"
#include "Scene.h"

class GridAdvectScene : public Scene {
 public:
	GridAdvectScene(Mesh3DInterface* mesh, double max_sim_time, const std::string& grid_directory);
	virtual void step(double dt) override;

 private:
	Grid3DSparseCubical loadGrid(const std::string_view directory, const int step);

	void moveScripted(const std::vector<Mesh3DVertex*>& vertices) const;
	void advectThroughGrid(const std::vector<Mesh3DVertex*>& vertices, Grid3DSparseCubical& grid,
	                       double dt) const;
	Vec3d velocity(Vec3d pos, Grid3DSparseCubical& grid) const;

	double getScriptOffsetAtStep(int step) const;
	double hermiteSpline(double x) const { return (3 - 2 * x) * x * x; };

	std::string grid_directory_;
	Mesh3DInterface* mesh_;
	int current_step_;
};
