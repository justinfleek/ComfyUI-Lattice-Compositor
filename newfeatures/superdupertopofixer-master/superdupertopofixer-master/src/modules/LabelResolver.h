/* LabelResolver.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2023
 *
 * This is the header for the module that resolves a material vector on each grid vertex into a
 * single material label.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------
#include <algorithm>
#include <array>
#include <cassert>
#include <iterator>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "ModuleInterface.h"
#include "absl/container/flat_hash_map.h"
#include "../schemes/TopoFixerSettings.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// Defined below.
class FastMarchingTrace;

// this class manages the flow of the label resolver module
class LabelResolver : public ModuleInterface {
 public:
	// constructors
	LabelResolver(const TopoFixerSettings& settings) : settings(&settings){};
	virtual ~LabelResolver() = default;

	// organizes the execution of individual tasks necessary for resolving material vectors on grid
	// vertices
	virtual int run(Mesh3DInterface& mesh, Grid3DInterface& grid, GridMeshIntersector& intersector,
	                int orientation) override;

	// clears all label resolution data structures
	void clearState();

 private:
	const TopoFixerSettings* settings;
	//
	class GridVertexTrace {
	 public:
		// default constructor
		GridVertexTrace() = default;
		// constructor used when generating a trace for a vertex given a complex neighbor with a unique
		// label; this new trace has to be combined with the trace of the neighbor vertex
		GridVertexTrace(long long id_, Vec3d position_) : id(id_), position(position_) {}
		// constructor used when generating a trace for a vertex given a non-complex neighbor; the
		// breaking point encountered when crossing from the non-complex neighbor to the current vertex
		// is stored and its label is set as the closest label
		GridVertexTrace(long long id_, Vec3d position_, int label_, Vec3d breaking_point_)
		    : id(id_), position(position_), closest_label(label_) {
			label_to_breaking_point[label_] = breaking_point_;
		}

		bool operator==(const GridVertexTrace& otherTrace) const { return this->id == otherTrace.id; }

		// check if `breaking_point` is closer to current grid vertex than the currently stored breaking
		// point associated to `closest_label`; if yes, update the saved information; if additionally
		// `breaking_point` became the closest breaking point stored on this vertex' trace and
		// `closest_label` is not set to `label`, update `closest_point` to `label`
		void updateBreakingPointForLabel(int label, Vec3d breaking_point) {
			// std::cout << "-updating trace " << id << " with pair (" << label << "," << breaking_point
			//          << ")\n";

			// check if this trace already has a breaking point associated to `label`
			auto label_to_breaking_point_it = label_to_breaking_point.find(label);
			if (label_to_breaking_point_it == label_to_breaking_point.end()) {
				// if this trace doesn't have a breaking point of type `label` yet, store the pair (`label`,
				// `breaking_point`)
				label_to_breaking_point[label] = breaking_point;
				// check if `breaking_point` is the closest label to the current vertex, and if yes, update
				// `closest_label`
				if (distanceSquaredToClosestLabel() > distanceSquaredToPoint(breaking_point)) {
					closest_label = label;
				}
			} else {
				// if this trace already has a breaking point associated to `label`, check if
				// `breaking_point` is closer, and if yes, update it
				if (distanceSquaredToPoint(breaking_point) <
				    distanceSquaredToPoint(label_to_breaking_point_it->second)) {
					label_to_breaking_point[label] = breaking_point;
					// if `closest_label` and `label` are equal, then `closest_point` doesn't need to be
					// updated; if they are different, we check whether `breaking_point` is the closest
					// breaking point recoreded on this trace, and if yes, we update `closest_label`
					if (label != closest_label &&
					    distanceSquaredToPoint(breaking_point) < distanceSquaredToClosestLabel()) {
						closest_label = label;
					}
				}
			}
		}

		void mergeTrace(const GridVertexTrace& other) {
			for (auto& [label, breaking_point] : other.label_to_breaking_point) {
				updateBreakingPointForLabel(label, breaking_point);
			}
		}

		int determineUniqueLabel() {
			double closest_distance_squared = mag2(position - label_to_breaking_point.begin()->second);
			closest_label = label_to_breaking_point.begin()->first;
			for (auto& [label, breaking_point] : label_to_breaking_point) {
				if (mag2(position - breaking_point) < closest_distance_squared) {
					closest_distance_squared = mag2(position - breaking_point);
					closest_label = label;
				}
			}
			return closest_label;
		}

		double distanceSquaredToClosestLabel() {
			return mag2(position - label_to_breaking_point[closest_label]);
		}

		double distanceSquaredToPoint(Vec3d point) const { return mag2(position - point); }

		void updateClosestLabel() const {}

		long long id;
		Vec3d position;
		int closest_label;
		absl::flat_hash_map<int, Vec3d> label_to_breaking_point;
	};

	// ---------------- functions for generating unique labeling

	// Runs a BFS flood fill on the grid vertices in the complex region. The BFS heuristic we use is
	// that for a complex grid vertex v0, we iterate over its 6 grid neighbors in a fixed order. If
	// a neighbor v1 of v0 has a unique label l assigned, if l != 0, v0 inherits l. If all adjacent
	// vertices of v0 that have a unique label assigned have their label == 0, v0 inherits label 0.
	// In other words, we try to assign a non-zero label to v0, and only assign the zero label to v0
	// if it is the only feasible candidate. Given the fixed order in which we traverse neighbors of
	// v0, we prioritize "earlier" directions over "later" ones. The assignment of unique labels to
	// grid ids is stored in the map `unique_labeling`.
	// NOTE: for a vertex v, we could also take the unique material that is saved on some neighbor of
	// v, and which also has the largest component value in v's material vector, and not take
	// materials that are negative in v's material vector.
	void generateUniqueLabelsOnGridVerticesNaiveFloodFill(
	    Grid3DInterface& grid, std::deque<long long>& vertices_to_process,
	    absl::flat_hash_map<long long, int>& unique_labeling) const;

	// do a BFS flood fill, but note when a breaking point occurs (point when a physically invalid
	// state is entered); if a vertex has several candidates for where to take a unique label from,
	// use the one with the closest breaking point; and as usual only spread global outside, if you
	// can't spread anything else
	void generateUniqueLabelsOnGridVerticesTrackingFloodFill(
	    Mesh3DInterface& mesh, Grid3DInterface& grid, std::deque<long long>& vertices_to_process,
	    absl::flat_hash_map<long long, int>& unique_labeling, const int path_tracing_method);

	void computeClosestBreakingPointsForGridVerticesNaive(
	    Grid3DInterface& grid, absl::flat_hash_map<long long, int>& unique_labeling);

	void findClosestBreakingPointForGridVertexNaive(Grid3DInterface& grid, long long grid_vertex,
	                                                int& closest_label, Vec3d& closest_BP) const;

	void findOptimizedMarchingCubesEdgeVertices(Grid3DInterface& grid,
	                                            absl::flat_hash_map<long long, int>& unique_labeling);

	void findMaterialSwitchingPoint(Grid3DInterface& grid,
	                                absl::flat_hash_map<long long, int>& unique_labeling,
	                                long long edge);

	// ---------------- helper functions

	// Assigns unique labels to simple vertices in the complex region, collects their complex
	// neighbors (i.e complex vertices neighboring simple vertices), and adds them into a queue that
	// will be used to facilitate the BFS flood fill based resolution of grid vertices (i.e. these
	// grid vertices will serve as BFS starting points). Simple vertices in complex region are
	// guaranteed to exist, eg. all grid vertices on front faces are simple. Grid vertices are added
	// to the output queue in increasing index order, ensuring that the function returns the same
	// output on the same input across repeated runs.
	std::deque<long long> preprocessMaterialFloodFill(
	    Grid3DInterface& grid, absl::flat_hash_map<long long, int>& unique_labeling) const;

	bool isIntersectionPhysical(Mesh3DInterface& mesh, Grid3DInterface& grid,
	                            bool aligned_edge_traversal,
	                            const GridEdgeMeshFaceIntersection& intersection,
	                            int& edge_label) const;

	double distanceToBreakingPoint(Grid3DInterface& grid, long long grid_vertex, Vec3d breaking_point,
	                               long long edge_orientation) const;

	void addBreakingPointToTrace(Mesh3DInterface& mesh, Grid3DInterface& grid,
	                             long long current_vertex, int label,
	                             const GridEdgeMeshFaceIntersection& intersection);

	// ---------------- fast marching method
	// Generates initial traces by considering the grid vertices directly adjacent to the edges where
	// breaking points are located.
	std::priority_queue<FastMarchingTrace> initFastMarching(
	    Grid3DInterface& grid, const absl::flat_hash_map<long long, int>& unique_labeling,
	    const std::vector<std::pair<GridEdgeMeshFaceIntersection, int>>& breaking_points);
	// Spread the distances from the initial traces in `queue` to the rest of the complex cell region.
	void propogateFastMarching(Grid3DInterface& grid, std::priority_queue<FastMarchingTrace>& queue,
	                           absl::flat_hash_map<long long, GridVertexTrace>& grid_vertex_traces,
	                           absl::flat_hash_map<long long, int>& unique_labeling);

	// ---------------- data members

	absl::flat_hash_map<long long, GridVertexTrace> grid_vertex_traces;

	// vector of breaking points, represented as pairs (position, label), where "label" is the
	// physically valid material configuration on a grid edge just before entering the breaking point;
	// used only for "naive" choice of "path_tracing_BFS_method"
	std::vector<std::pair<GridEdgeMeshFaceIntersection, int>> breaking_points;

	bool print_debug;
};

class FastMarchingTrace {
 public:
	FastMarchingTrace(long long vert_id, Vec3d breaking_pos, int label, double dist)
	    : vert_id_(vert_id), breaking_pos_(breaking_pos), label_(label), dist_(dist){};

	long long getVertexId() { return vert_id_; }
	Vec3d getBreakingPosition() { return breaking_pos_; }
	int getLabel() { return label_; }
	double getDistance() { return dist_; }

	// The distances are compared by greater sign to make priority queue extract the minimum.
	bool operator<(const FastMarchingTrace& other) const { return dist_ > other.dist_; }

 private:
	long long vert_id_;
	Vec3d breaking_pos_;
	int label_;
	double dist_;
};