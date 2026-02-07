
/* Smoother.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, 2021
 *
 * Submodule that smoothes mesh by changing mesh vertex positions. Does not affect connectivity.
 * Used to assign opposites after marching cubes, when some triangles are very small/degenerate.
 * Smoothing allows to find the combinatorial information to correctly assign half-corner pointers.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "../../abseil-cpp/absl/container/flat_hash_map.h"
#include "../../abseil-cpp/absl/container/flat_hash_set.h"
#include "../datastructures/Mesh3DHalfCorner.h"
#include "../datastructures/Mesh3DInterface.h"
#include "../datastructures/Mesh3DVertex.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

class JacobiSmoother {
 public:
	// For each vertex that is a map key sets the position to the average of the neighbours (either
	// unweighted, or weighted by distance from the vertex). Positions at time t+1 are calculated from
	// positions at time t, intermittent updates are not taken into account. Repeats for `num_iters`.
	void smooth(
	    const absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DVertex*>> vertex_to_neighs,
	    int num_iters);
};

class NormalFlowSmoother {
 public:
	void smooth(Mesh3DInterface& mesh, const std::vector<Mesh3DVertex*>& moving_vertices,
	            int num_iters, double min_edge_length);

	void bendGradients(Mesh3DInterface& mesh, const std::vector<Mesh3DVertex*>& moving_vertices,
	                   std::vector<Vec3d>& gradients);

	void flapNormals(Mesh3DHalfCorner* hfc, Vec3d& n0, Vec3d& n1);
	double dihedralAngle(Mesh3DHalfCorner* hfc, const Vec3d& n0, const Vec3d& n1,
	                     const Vec3d& edge_vec);

	double energy(Mesh3DInterface& mesh, const std::vector<Mesh3DVertex*>& moving_vertices);
};

class NonmanifoldCurveSmoother {
 public:
	void smooth(Mesh3DInterface& mesh, const std::vector<Mesh3DVertex*>& moving_vertices,
	            int num_iters);

 private:
	using Curves = absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DVertex*>>;
	using Gradient = absl::flat_hash_map<Mesh3DVertex*, Vec3d>;

	Curves buildCurves(Mesh3DInterface& mesh, const std::vector<Mesh3DVertex*>& moving_vertices);
	double energy(const Curves& curves);
	void gradient(const Curves& curves, Gradient& grad);

	double angle(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3);
	Vec3d normal(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3);
};

class MeanCurveSmoother {
 public:
	using Curves = absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DVertex*>>;
	void smooth(Mesh3DInterface& mesh, const std::vector<Mesh3DVertex*>& moving_vertices,
	            int num_iters);
	Curves buildCurves(Mesh3DInterface& mesh, const std::vector<Mesh3DVertex*>& moving_vertices);

 private:
	using Positions = absl::flat_hash_map<Mesh3DVertex*, Vec3d>;
};