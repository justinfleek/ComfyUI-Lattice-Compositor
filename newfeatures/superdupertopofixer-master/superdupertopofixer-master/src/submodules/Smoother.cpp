/* Smoother.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * Implementation of smoothing operations for the Smoother submodule.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "Smoother.h"

#include "../utilities/vec.h"
#include "absl/container/flat_hash_set.h"

//------------------------------------------------------------
// functions
//------------------------------------------------------------

void JacobiSmoother::smooth(
    const absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DVertex*>> vertex_to_neighs,
    int num_iters) {
	absl::flat_hash_map<Mesh3DVertex*, Vec3d> verts_updates;
	for (int i = 0; i < num_iters; ++i) {
		for (const auto& [vert, neighs] : vertex_to_neighs) {
			// Vec3d center_coords = vert->getCoords();
			Vec3d average_coords = {0, 0, 0};
			double sumdist = 0.0;
			for (Mesh3DVertex* nv : neighs) {
				Vec3d neigh_coords = nv->getCoords();

				// Uniform umbrella-operator
				double dist = 1.0;

				// Weighted umbrella-operator
				// Vec3d dx = neigh_coords - center_coords;
				// double dist = std::sqrt(dot(dx, dx));
				sumdist += dist;
				average_coords += neigh_coords * dist;
			}
			average_coords /= sumdist;
			verts_updates[vert] = average_coords;
		}

		for (auto& [vert, coords] : verts_updates) {
			vert->setCoords(coords);
		}
	}
}
void NormalFlowSmoother::smooth(Mesh3DInterface& mesh,
                                const std::vector<Mesh3DVertex*>& moving_vertices, int num_iters,
                                double min_edge_length) {
	for (Mesh3DVertex* v : mesh.ListVertices()) {
		v->setVelocity(Vec3d{0.0});
	}
	std::vector<Vec3d> gradients(moving_vertices.size(), Vec3d(0.0));
	std::vector<Vec3d> half_gradients(moving_vertices.size(), Vec3d(0.0));

	double original_dt = 1 * 1e-5;
	for (int iter = 0; iter < num_iters; ++iter) {
		// double dt = original_dt * (num_iters - iter) / (double)num_iters;
		double dt = original_dt;
		if (iter > 200) {
			dt /= 10;
		}
		std::cout << iter << " " << dt << " ";
		bendGradients(mesh, moving_vertices, gradients);
		for (size_t i = 0; i < moving_vertices.size(); ++i) {
			Mesh3DVertex* v = moving_vertices[i];
			v->setCoords(v->getCoords() - dt * gradients[i]);
		}
		bendGradients(mesh, moving_vertices, half_gradients);
		for (size_t i = 0; i < moving_vertices.size(); ++i) {
			Mesh3DVertex* v = moving_vertices[i];
			v->setCoords(v->getCoords() - dt / 2.0 * (half_gradients[i] - gradients[i]));
		}
		std::cout << energy(mesh, moving_vertices) << std::endl;
	}
}

void NormalFlowSmoother::bendGradients(Mesh3DInterface& mesh,
                                       const std::vector<Mesh3DVertex*>& moving_vertices,
                                       std::vector<Vec3d>& gradients) {
	for (size_t i = 0; i < moving_vertices.size(); ++i) {
		gradients[i] = Vec3d(0.0);
		Mesh3DVertex* v = moving_vertices[i];

		for (Mesh3DTriangle* tri : mesh.getTrianglesAroundVertex(v)) {
			Mesh3DHalfCorner* edge = tri->getHalfCornerAtVertex(v);
			Vec3d x0 = edge->getNext()->getVertex()->getCoords();
			Vec3d x1 = edge->getPrev()->getVertex()->getCoords();
			Vec3d edge_vec = x1 - x0;

			Vec3d normal;
			Vec3d neigh_normal;
			flapNormals(edge, normal, neigh_normal);
			double normal_mag2 = mag2(normal);
			// Skip small area triangles.
			if (normal_mag2 < 1e-15 * 1e-15) {
				continue;
			}
			if (mag2(neigh_normal) < 1e-15 * 1e-15) {
				continue;
			}

			double angle = dihedralAngle(edge, normal, neigh_normal, edge_vec);
			gradients[i] += angle * normal / mag(normal) * mag(edge_vec);

			// gradients[i] += gradient_sign * normal / normal_mag2 * edge_len;

			// gradients[i] += gradient_sign * normal / mag(normal) * mesh.getAngle(edge);
			// gradients[i] += gradient_sign * normal / mag(normal) * edge_len;
		}
		// if (mag2(gradients[i]) > 1e-100) {
		// 	gradients[i] = normalized(gradients[i]);
		// }
		v->setVelocity(gradients[i]);
	}
}

void NormalFlowSmoother::flapNormals(Mesh3DHalfCorner* hfc, Vec3d& n0, Vec3d& n1) {
	Vec3d x0 = hfc->getNext()->getVertex()->getCoords();
	Vec3d x1 = hfc->getPrev()->getVertex()->getCoords();
	Vec3d x2 = hfc->getVertex()->getCoords();
	Vec3d x3 = hfc->getOppos()->getVertex()->getCoords();

	Vec3d v02 = x2 - x0;
	Vec3d v03 = x3 - x0;

	Vec3d v12 = x2 - x1;
	Vec3d v13 = x3 - x1;

	n0 = cross(v12, v02);
	n1 = cross(v03, v13);
}

double NormalFlowSmoother::dihedralAngle(Mesh3DHalfCorner* hfc, const Vec3d& n0, const Vec3d& n1,
                                         const Vec3d& edge_vec) {
	double dot_prod = dot(n0, n1);
	Vec3d cross_prod = cross(n0, n1);
	int convexity = (dot(cross_prod, edge_vec)) > 0. ? 1 : -1;
	return atan2(convexity * mag(cross_prod), dot_prod);
}

double NormalFlowSmoother::energy(Mesh3DInterface& mesh,
                                  const std::vector<Mesh3DVertex*>& moving_vertices) {
	double energy = 0.0;
	for (size_t i = 0; i < moving_vertices.size(); ++i) {
		Mesh3DVertex* v = moving_vertices[i];

		for (Mesh3DTriangle* tri : mesh.getTrianglesAroundVertex(v)) {
			Mesh3DHalfCorner* edge = tri->getHalfCornerAtVertex(v);
			Vec3d x0 = edge->getNext()->getVertex()->getCoords();
			Vec3d x1 = edge->getPrev()->getVertex()->getCoords();
			Vec3d edge_vec = x1 - x0;

			Vec3d normal;
			Vec3d neigh_normal;
			flapNormals(edge, normal, neigh_normal);
			double angle = dihedralAngle(edge, normal, neigh_normal, edge_vec);
			energy += angle * angle * mag2(edge_vec) / mag(normal);
		}
	}
	return energy;
}

void NonmanifoldCurveSmoother::smooth(Mesh3DInterface& mesh,
                                      const std::vector<Mesh3DVertex*>& moving_vertices,
                                      int num_iters) {
	Curves curves = buildCurves(mesh, moving_vertices);
	for (Mesh3DVertex* v : mesh.ListVertices()) {
		v->setVelocity(Vec3d{0.0});
	}
	Gradient gradients;
	Gradient half_gradients;

	double original_dt = 1 * 1e-5;
	for (int iter = 0; iter < num_iters; ++iter) {
		// double dt = original_dt * (num_iters - iter) / (double)num_iters;
		double dt = original_dt;
		std::cout << iter << " " << dt << " ";
		gradient(curves, gradients);

		for (auto [vert, grad] : gradients) {
			vert->setCoords(vert->getCoords() - dt * grad);
		}
		// bendGradients(mesh, moving_vertices, half_gradients);
		// for (int i = 0; i < moving_vertices.size(); ++i) {
		// 	Mesh3DVertex* v = moving_vertices[i];
		// 	v->setCoords(v->getCoords() - dt / 2.0 * (half_gradients[i] - gradients[i]));
		// }
		std::cout << energy(curves) << std::endl;
	}
}

NonmanifoldCurveSmoother::Curves NonmanifoldCurveSmoother::buildCurves(
    Mesh3DInterface& mesh, const std::vector<Mesh3DVertex*>& moving_vertices) {
	Curves curves;
	for (Mesh3DVertex* vert : moving_vertices) {
		for (Mesh3DHalfCorner* hfc : mesh.getEdgesAroundVertex(vert)) {
			if (!mesh.isEdgeNonmanifold(hfc)) {
				continue;
			}
			Mesh3DVertex* v1 = hfc->getNext()->getVertex();
			Mesh3DVertex* v2 = hfc->getPrev()->getVertex();
			curves[v1].insert(v2);
			curves[v2].insert(v1);
		}
	}
	return curves;
}

double NonmanifoldCurveSmoother::energy(const Curves& curves) {
	double total = 0.0;
	for (auto& [vert, neighs] : curves) {
		for (Mesh3DVertex* neigh : neighs) {
			auto neigh_it = curves.find(neigh);
			if (neigh_it == curves.end()) {
				continue;
			}

			for (Mesh3DVertex* dist_neigh : neigh_it->second) {
				total += angle(vert, neigh, dist_neigh);
			}
		}
	}
	return total;
}

void NonmanifoldCurveSmoother::gradient(const Curves& curves, Gradient& grad) {
	grad.clear();
	for (auto& [vert, neighs] : curves) {
		grad[vert] = Vec3d(0.0);
		for (Mesh3DVertex* neigh : neighs) {
			auto neigh_it = curves.find(neigh);
			if (neigh_it == curves.end()) {
				continue;
			}
			for (Mesh3DVertex* dist_neigh : neigh_it->second) {
				double a = angle(vert, neigh, dist_neigh);
				Vec3d n = normal(vert, neigh, dist_neigh);
				grad[vert] += a * n;
			}
		}
	}
}

double NonmanifoldCurveSmoother::angle(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3) {
	Vec3d c1 = v1->getCoords();
	Vec3d c2 = v2->getCoords();
	Vec3d c3 = v3->getCoords();
	return atan2(mag(cross(c2 - c1, c3 - c2)), dot(c2 - c1, c3 - c2));
}

Vec3d NonmanifoldCurveSmoother::normal(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3) {
	Vec3d e1 = v2->getCoords() - v1->getCoords();
	Vec3d e2 = v3->getCoords() - v2->getCoords();

	Vec3d n = cross(cross(e1, e2), e1);
	double magnitude = mag(n);
	if (magnitude > 1e-10) {
		n /= magnitude;
	}
	return n;
}

void MeanCurveSmoother::smooth(Mesh3DInterface& mesh,
                               const std::vector<Mesh3DVertex*>& moving_vertices, int num_iters) {
	Curves curves = buildCurves(mesh, moving_vertices);
	Positions positions;

	for (int iter = 0; iter < num_iters; ++iter) {
		positions.clear();
		for (auto& [vert, neighs] : curves) {
			if (neighs.empty()) {
				continue;
			}

			Vec3d new_pos = Vec3d(0.0);
			for (Mesh3DVertex* neigh : neighs) {
				new_pos += neigh->getCoords();
			}
			new_pos /= neighs.size();
			positions[vert] = new_pos;
		}

		for (auto& [vert, new_pos] : positions) {
			vert->setCoords(new_pos);
		}
	}
}

MeanCurveSmoother::Curves MeanCurveSmoother::buildCurves(
    Mesh3DInterface& mesh, const std::vector<Mesh3DVertex*>& moving_vertices) {
	Curves curves;
	for (Mesh3DVertex* vert : moving_vertices) {
		for (Mesh3DHalfCorner* hfc : mesh.getEdgesAroundVertex(vert)) {
			if (!mesh.isEdgeNonmanifold(hfc)) {
				continue;
			}
			Mesh3DVertex* v1 = hfc->getNext()->getVertex();
			Mesh3DVertex* v2 = hfc->getPrev()->getVertex();
			curves[v1].insert(v2);
			curves[v2].insert(v1);
		}
	}
	return curves;
}
